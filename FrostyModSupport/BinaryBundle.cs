using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Diagnostics.Tracing;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using Frosty.ModSupport.Interfaces;
using Frosty.ModSupport.ModEntries;
using Frosty.ModSupport.ModInfos;
using Frosty.Sdk;
using Frosty.Sdk.DbObjectElements;
using Frosty.Sdk.Exceptions;
using Frosty.Sdk.IO;
using Frosty.Sdk.Managers;
using Frosty.Sdk.Utils;
using Microsoft.Extensions.Logging;
using Octokit;

namespace Frosty.ModSupport;

public class BinaryBundleHeader
{
    // we use big endian for default
    public static Endian endian = Endian.Big;
    public static uint headerSize = 0x24;

    public uint size;
    public Sdk.IO.BinaryBundle.Magic magic;
    public long startPos;
    public bool containsSha1;
    public uint totalCount;
    public int ebxCount;
    public int resCount;
    public int chunkCount;
    public long stringsOffset;
    public long metaOffset;
    public uint metaSize;

    public BinaryBundleHeader(BlockStream inStream) {

        size = inStream.ReadUInt32(Endian.Big);

        startPos = inStream.Position;

        magic = (Sdk.IO.BinaryBundle.Magic)(inStream.ReadUInt32(endian) ^ Sdk.IO.BinaryBundle.GetSalt());

        // check what endian its written in
        if (!Sdk.IO.BinaryBundle.IsValidMagic(magic))
        {
            endian = Endian.Little;
            uint value = (uint)magic ^ Sdk.IO.BinaryBundle.GetSalt();
            magic = (Sdk.IO.BinaryBundle.Magic)(BinaryPrimitives.ReverseEndianness(value) ^ Sdk.IO.BinaryBundle.GetSalt());

            if (!Sdk.IO.BinaryBundle.IsValidMagic(magic))
            {
                throw new InvalidDataException("magic");
            }
        }

        containsSha1 = magic == Sdk.IO.BinaryBundle.Magic.Standard;

        totalCount = inStream.ReadUInt32(endian);
        ebxCount = inStream.ReadInt32(endian);
        resCount = inStream.ReadInt32(endian);
        chunkCount = inStream.ReadInt32(endian);
        stringsOffset = inStream.ReadUInt32(endian) + startPos;
        metaOffset = inStream.ReadUInt32(endian) + startPos;
        metaSize = inStream.ReadUInt32(endian);
    }

    public void WriteToStream(BlockStream outStream) {
        long currentPos = outStream.Position;
        outStream.Position = 0;
        outStream.WriteUInt32((uint)(size - startPos), Endian.Big);
        outStream.WriteUInt32((uint)magic ^ Sdk.IO.BinaryBundle.GetSalt(), endian);

        outStream.WriteUInt32(totalCount, endian);
        outStream.WriteInt32(ebxCount, endian);
        outStream.WriteInt32(resCount, endian);
        outStream.WriteInt32(chunkCount, endian);

        outStream.WriteUInt32((uint)(stringsOffset - startPos), endian); // warning : in relation to start pos
        outStream.WriteUInt32((uint)(metaOffset - startPos), endian);
        outStream.WriteUInt32(metaSize, endian);
        outStream.Position = currentPos;
    }
}

public class BinaryBundle {
    BinaryBundleHeader header;
    List<EbxModEntry> ebx;
    List<ResModEntry> res;
    List<ChunkModEntry> chunks;

    DbObjectList? chunkMeta = null;

    Dictionary<string, uint> strings;

    /// Helper method to retrieve strings in the string store part of the bundle
    /// Needs initialised header
    string GetString(BlockStream inStream, long offset) {
        long currentPosition = inStream.Position;
        inStream.Position = header.stringsOffset + offset;
        string str = inStream.ReadNullTerminatedString();
        inStream.Position = currentPosition;
        return str;
    }

    void ParseEbxSection(BlockStream inStream, Sha1[] hashes) {
        // parse ebxs
        for(int i = 0; i < header.ebxCount; i++)
        {
            uint nameOffset = inStream.ReadUInt32(BinaryBundleHeader.endian);
            uint originalSize = inStream.ReadUInt32(BinaryBundleHeader.endian);
            string name = GetString(inStream, nameOffset);
            ebx.Add(new EbxModEntry(name, hashes[i], originalSize));
        }
    }

        // Section structure : 
        // {nameOffset, size}[resCount]
        // resType[resCount]
        // resMeta[resCount]
        // resRid[resCount]
    void ParseResSection(BlockStream inStream, Sha1[] hashes) {
        uint[] nameOffsets = new uint[header.resCount];
        uint[] originalSizes = new uint[header.resCount];

        uint[] resTypes = new uint[header.resCount];
        byte[][] resMetas = new byte[header.resCount][];
        ulong[] resRids = new ulong[header.resCount];

        for(int i = 0; i < header.resCount; i++)
        {
            nameOffsets[i] = inStream.ReadUInt32(BinaryBundleHeader.endian);
            originalSizes[i] = inStream.ReadUInt32(BinaryBundleHeader.endian);
        }
        for(int i = 0; i < header.resCount; i++)
        {
            resTypes[i] = inStream.ReadUInt32(BinaryBundleHeader.endian);
        }
        for(int i = 0; i < header.resCount; i++)
        {
            resMetas[i] = inStream.ReadBytes(0x10);
        }
        for(int i = 0; i < header.resCount; i++)
        {
            resRids[i] = inStream.ReadUInt64(BinaryBundleHeader.endian);
        }
        
        // assemble everything for a new ResModEntry
        for(int i = 0; i < header.resCount; i++)
        {
            res.Add(new ResModEntry(GetString(inStream, nameOffsets[i]), hashes[header.ebxCount + i], originalSizes[i], resRids[i], resTypes[i], resMetas[i]));
        }
    }

    void ParseChunkSection(BlockStream inStream, Sha1[] hashes) {
        for (int i = 0; i < header.chunkCount; i++)
        {
            Guid id = inStream.ReadGuid(BinaryBundleHeader.endian);
            uint logicalOffset = inStream.ReadUInt32(BinaryBundleHeader.endian);
            uint logicalSize = inStream.ReadUInt32(BinaryBundleHeader.endian);
            chunks.Add(new ChunkModEntry(id, hashes[header.ebxCount + header.resCount + i], logicalOffset, logicalSize));
        }
    }

    void TryParseMeta(BlockStream inStream) {
        if (header.metaSize > 0)
        {
            long currentPos = inStream.Position;
            inStream.Position = header.metaOffset;
            chunkMeta = DbObject.Deserialize(inStream)!.AsList();
            inStream.Position = currentPos;
        }
    }

    void TryDecrypt(BlockStream inStream) {
        // decrypt the data
        if (header.magic == Sdk.IO.BinaryBundle.Magic.Encrypted)
        {
            if (!KeyManager.HasKey("BundleEncryptionKey"))
            {
                throw new MissingEncryptionKeyException("bundles");
            }

            inStream.Decrypt(KeyManager.GetKey("BundleEncryptionKey"), (int)(header.size - 0x20), PaddingMode.None);
        }
    }

    public BinaryBundle(BlockStream inStream) {
        header = new BinaryBundleHeader(inStream);

        TryDecrypt(inStream);

        ebx = new List<EbxModEntry>(header.ebxCount);
        res = new List<ResModEntry>(header.resCount);
        chunks = new List<ChunkModEntry>(header.chunkCount);

        // read sha1s
        Sha1[] hashes = new Sha1[header.totalCount];
        for (int i = 0; i < header.totalCount; i++)
        {
            hashes[i] = header.containsSha1 ? inStream.ReadSha1() : Sha1.Zero;
        }

        ParseEbxSection(inStream, hashes);
        ParseResSection(inStream, hashes);
        ParseChunkSection(inStream, hashes);
        TryParseMeta(inStream);

        inStream.Position = header.startPos + header.size;
    }

    void ModifyEbxList(int offset, BundleModInfo inModInfo, Dictionary<string, EbxModEntry> inModifiedEbx, Action<IModEntry, int, bool, bool, uint> modify) {
        for (int i = 0; i < ebx.Count; i++) {
            if (inModInfo.Modified.Ebx.Contains(ebx[i].Name)) {
                ebx[i] = inModifiedEbx[ebx[i].Name];
                modify(ebx[i], offset, false, true, (uint)ebx[i].OriginalSize);
            } else {
                modify(ebx[i], offset, false, false, (uint)ebx[i].OriginalSize);
            }
        }
    }

    void ModifyResList(int offset, BundleModInfo inModInfo, Dictionary<string, ResModEntry> inModifiedRes, Action<IModEntry, int, bool, bool, uint> modify) {
        for (int i = 0; i < res.Count; i++) {
            if (inModInfo.Modified.Res.Contains(res[i].Name)) {
                res[i] = inModifiedRes[res[i].Name];
                modify(res[i], offset, false, true, (uint)res[i].OriginalSize);
            } else {
                modify(res[i], offset, false, false, (uint)ebx[i].OriginalSize);
            }
        }
    }

    void ModifyChunkList(int offset, BundleModInfo inModInfo, Dictionary<Guid, ChunkModEntry> inModifiedChunks, Action<IModEntry, int, bool, bool, uint> modify) {
        for (int i = 0; i < chunks.Count; i++) {
            if (inModInfo.Modified.Chunks.Contains(chunks[i].Id)) {
                chunks[i] = inModifiedChunks[chunks[i].Id];
                modify(chunks[i], offset, false, true, (chunks[i].LogicalOffset & 0xFFFF) | chunks[i].LogicalSize);
                if (chunks[i].FirstMip != -1)
                {
                    DbObjectDict? meta = chunkMeta?.FirstOrDefault(m => m.AsDict().AsInt("h32") == chunks[i].H32)?.AsDict();
                    if (meta is null)
                    {
                        meta = DbObject.CreateDict( 2);
                        meta.Set("h32", chunks[i].H32);
                        meta.Set("meta", DbObject.CreateDict("meta", 1));
                        chunkMeta ??= DbObject.CreateList(1);
                        chunkMeta.Add(meta);
                    }
                    meta.AsDict("meta").Set("firstMip", chunks[i].FirstMip);
                }
            } else {
                modify(chunks[i], offset, false, false, (chunks[i].LogicalOffset & 0xFFFF) | chunks[i].LogicalSize);
            }
        }
    }

    void AddEbxList(int offset, BundleModInfo inModInfo, Dictionary<string, EbxModEntry> inModifiedEbx, Action<IModEntry, int, bool, bool, uint> modify) {
        int i = 0;
        foreach (string name in inModInfo.Added.Ebx)
        {
            EbxModEntry modEntry = inModifiedEbx[name];
            ebx.Add(modEntry);
            modify(modEntry, offset + i, true, true, 0);
            i++;
        }
    }

    void AddResList(int offset, BundleModInfo inModInfo, Dictionary<string, ResModEntry> inModifiedRes, Action<IModEntry, int, bool, bool, uint> modify) {
        int i = 0;
        foreach (string name in inModInfo.Added.Res)
        {
            ResModEntry modEntry = inModifiedRes[name];
            res.Add(modEntry);
            modify(modEntry, offset + i, true, true, 0);
            i++;
        }
    }

    void AddChunkList(int offset, BundleModInfo inModInfo, Dictionary<Guid, ChunkModEntry> inModifiedChunks, Action<IModEntry, int, bool, bool, uint> modify) {
        int i = 0;
        foreach (Guid id in inModInfo.Added.Chunks)
        {
            ChunkModEntry modEntry = inModifiedChunks[id];
            chunks.Add(modEntry);
            modify(modEntry, offset +i, true, true, 0);

            DbObjectDict meta = DbObject.CreateDict(2);
            meta.Set("h32", modEntry.H32);
            if (modEntry.FirstMip != -1)
            {
                DbObjectDict firstMip = DbObject.CreateDict("meta", 1);
                firstMip.Set("firstMip", modEntry.FirstMip);
                meta.Set("meta", firstMip);
            }
            chunkMeta!.Add(meta);
        }
    }

    public void Modify(BundleModInfo inModInfo, Dictionary<string, EbxModEntry> inModifiedEbx, Dictionary<string, ResModEntry> inModifiedRes, 
        Dictionary<Guid, ChunkModEntry> inModifiedChunks, Action<IModEntry, int, bool, bool, uint> modify) {

        ModifyEbxList(0, inModInfo, inModifiedEbx, modify);
        AddEbxList(ebx.Count, inModInfo, inModifiedEbx, modify);

        ModifyResList(ebx.Count, inModInfo, inModifiedRes, modify);
        AddResList(ebx.Count + res.Count, inModInfo, inModifiedRes, modify);

        ModifyChunkList(ebx.Count + res.Count, inModInfo, inModifiedChunks, modify);
        AddChunkList(ebx.Count + res.Count + chunks.Count, inModInfo, inModifiedChunks, modify);
    }

    void WriteEbxHashesToStream(BlockStream outStream) {
        foreach (EbxModEntry entry in ebx) {
            outStream.WriteSha1(entry.Sha1);
        }
    }

    void WriteResHashesToStream(BlockStream outStream) {
        foreach (ResModEntry entry in res) {
            outStream.WriteSha1(entry.Sha1);
        }
    }

    void WriteChunkHashesToStream(BlockStream outStream) {
        foreach (ChunkModEntry entry in chunks) {
            outStream.WriteSha1(entry.Sha1);
        }
    }

    void WriteEbxEntriesToStream(BlockStream outStream) {
        foreach (EbxModEntry entry in ebx)
        {
            outStream.WriteUInt32(strings[entry.Name], BinaryBundleHeader.endian);
            outStream.WriteUInt32((uint)entry.OriginalSize, BinaryBundleHeader.endian);
        }
    }

    void WriteResEntriesToStream(BlockStream outStream) {

        List<uint> resTypes = new List<uint>(res.Count);
        List<byte[]> resMetas = new List<byte[]>(res.Count);
        List<ulong> resRids = new List<ulong>(res.Count);

        foreach (ResModEntry entry in res)
        {
            outStream.WriteUInt32(strings[entry.Name], BinaryBundleHeader.endian);
            outStream.WriteUInt32((uint)entry.OriginalSize,  BinaryBundleHeader.endian);
            resTypes.Add(entry.ResType);
            resMetas.Add(entry.ResMeta);
            resRids.Add(entry.ResRid);
        }

        foreach (uint resType in resTypes) {
            outStream.WriteUInt32(resType, BinaryBundleHeader.endian);
        }

        foreach (byte[] resMeta in resMetas) {
            outStream.Write(resMeta);
        }

        foreach (ulong resRid in resRids) {
            outStream.WriteUInt64(resRid, BinaryBundleHeader.endian);
        }
    }

    void WriteChunkEntriesToStream(BlockStream outStream) {
        foreach (ChunkModEntry entry in chunks)
        {
            outStream.WriteGuid(entry.Id, BinaryBundleHeader.endian);
            outStream.WriteUInt32(entry.LogicalOffset, BinaryBundleHeader.endian);
            outStream.WriteUInt32(entry.LogicalSize, BinaryBundleHeader.endian);
        }
    }

    void TrySerializeMeta(BlockStream outStream) {
        if (chunkMeta is not null)
        {
            DbObject.Serialize(outStream, chunkMeta);
        }
    }

    Dictionary<string, uint> GenStringsOffsets() {
        Dictionary<string, uint> offsets = new Dictionary<string, uint>();
        uint currentOffset = 0;
        foreach (EbxModEntry entry in ebx) {
            offsets.TryAdd(entry.Name, currentOffset);
            currentOffset += (uint)entry.Name.Length + 1;
        }
        foreach (ResModEntry entry in res) {
            offsets.TryAdd(entry.Name, currentOffset);
            currentOffset += (uint)entry.Name.Length + 1;
        }
        return offsets;
    }

    void WriteStringsToStream(BlockStream outStream) {
        foreach (KeyValuePair<string,uint> pair in strings)
        {
            outStream.WriteNullTerminatedString(pair.Key);
        }
    }

    public void WriteToStream(BlockStream outStream) {
        outStream.Position = BinaryBundleHeader.headerSize;

        WriteEbxHashesToStream(outStream);
        WriteResHashesToStream(outStream);
        WriteChunkHashesToStream(outStream);

        strings = GenStringsOffsets();

        WriteEbxEntriesToStream(outStream);
        WriteResEntriesToStream(outStream);
        WriteChunkEntriesToStream(outStream);

        header.metaOffset = (uint)outStream.Position;
        TrySerializeMeta(outStream);
        header.metaSize = (uint)(outStream.Position - header.metaOffset);

        WriteStringsToStream(outStream);

        // Pad with 0
        while (((outStream.Position - 0x24) & 15) != 0)
        {
            outStream.WriteByte(0);
        }

        header.size = (uint)outStream.Length - 4 ;
        header.stringsOffset = header.metaOffset + header.metaSize;
        header.WriteToStream(outStream);
    }

}