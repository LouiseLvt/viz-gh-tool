<#
.SYNOPSIS
    GHTool - read, analyse and replace images in a Viz Graphic Hub data folder.

.DESCRIPTION
    Command-line tool to explore a Graphic Hub data folder
    (default "VizGHData"): analysis, tree view, search, media export.

    The tool writes to the Graphic Hub folder ONLY for "gh replace ... -Apply" and
    "gh restore" (after taking a backup). All other commands are read-only,
    and exports are refused if they point inside that folder.

    The .vdb format is not documented by Vizrt: decoding is based on the analysis
    of one image file (Viz 3.6). Other object types (scenes, geometries, fonts...)
    are exported as raw decompressed data.

.EXAMPLE
    .\GHTool.ps1                      # starts the interactive console  GH>
    .\GHTool.ps1 analyse -Deep        # runs one command and exits
    . .\GHTool.ps1                    # loads the 'gh' function into the current session
    gh set D:\Backup\VizGHData
    gh export 2EEBEAC8A5FAB54893FBA784A05E52B2 -Out C:\Temp\GH
#>
# No param() block: options such as -Out / -Kind arrive as-is in $args.
$Command = @($args | ForEach-Object { "$_" })

$script:GhVersion = '1.13'

# ---------------------------------------------------------------------------
#  Binary engine (C#): .vdb reading, decompression, PNG writing
# ---------------------------------------------------------------------------
function Stop-GhFatal([string]$Msg, $Err) {
    Write-Host ''
    Write-Host "  ERROR: $Msg" -ForegroundColor Red
    if ($Err) { Write-Host ($Err | Out-String) -ForegroundColor DarkRed }
    Write-Host "  PowerShell $($PSVersionTable.PSVersion) - $([Environment]::OSVersion.VersionString)" -ForegroundColor DarkGray
    if (-not $Command -or -not $Command.Count) { Write-Host ''; Read-Host '  Press Enter to close' | Out-Null }
    exit 1
}

if (-not ('GhTool.Vdb' -as [type])) {
try {
Add-Type -ErrorAction Stop -TypeDefinition @'
using System;
using System.IO;
using System.IO.Compression;
using System.Text;
using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace GhTool
{
    public class Thumb  { public long Offset; public int Length; public int Width; public int Height; public string Name; public byte[] Bytes; }
    public class Chunk  { public long Offset; public int CompLen; public int RawLen; }

    public class VdbInfo
    {
        public string Uuid, Path, Bucket, Name, Name2, Sections, Kind, PixelFormat;
        public string AppName, AppVersion, DbVersion, SysName, SysVersion, Error;
        public long Size, RawSize;
        public DateTime? Created, Modified;
        public int Width, Height, GlFormat, Channels, PixelOffset, PixelLength;
        public List<Thumb> Thumbs = new List<Thumb>();
        public List<Chunk> Chunks = new List<Chunk>();
        public int MipLevels, TypeCode;
        public string PixelSection, PreviewSize;
        public List<Vdb.Sec> SectionList;
        public int ThumbCount { get { return Thumbs.Count; } }
        public int ChunkCount { get { return Chunks.Count; } }
    }

    public static class Vdb
    {
        const int HeadMax = 65536;

        static uint U32(byte[] b, int o) { return (uint)(b[o] | (b[o + 1] << 8) | (b[o + 2] << 16) | (b[o + 3] << 24)); }
        static int  U16(byte[] b, int o) { return b[o] | (b[o + 1] << 8); }

        static DateTime? Ts(uint v)
        {
            if (v < 946684800u || v > 2208988800u) return null;   // 2000 .. 2040
            return new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc).AddSeconds(v);
        }

        public static FileStream OpenRead(string path)
        {
            return new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite | FileShare.Delete);
        }

        public static byte[] ReadAt(FileStream fs, long off, int len)
        {
            if (off < 0) off = 0;
            if (off + len > fs.Length) len = (int)Math.Max(0, fs.Length - off);
            byte[] b = new byte[len];
            fs.Seek(off, SeekOrigin.Begin);
            int t = 0;
            while (t < len) { int n = fs.Read(b, t, len - t); if (n <= 0) break; t += n; }
            return b;
        }

        static string DecodeName(byte[] b, int o, int len)
        {
            string s;
            try { s = new UTF8Encoding(false, true).GetString(b, o, len); }
            catch { s = Encoding.GetEncoding(28591).GetString(b, o, len); }
            s = s.TrimEnd('\0');
            foreach (char c in s) if (char.IsControl(c)) return null;
            return s;
        }

        static byte[] Inflate(byte[] buf, int off, int len, int expected)
        {
            try
            {
                using (MemoryStream ms = new MemoryStream(buf, off, len))
                using (DeflateStream ds = new DeflateStream(ms, CompressionMode.Decompress))
                {
                    byte[] o = new byte[expected];
                    int t = 0;
                    while (t < expected) { int n = ds.Read(o, t, expected - t); if (n <= 0) break; t += n; }
                    return t == expected ? o : null;
                }
            }
            catch { return null; }
        }

        static bool ChunkHeaderOk(byte[] h, int p, long posInFile, long fileLen)
        {
            if (p + 10 > h.Length) return false;
            uint c = U32(h, p), r = U32(h, p + 4);
            if (c < 10 || posInFile + c > fileLen) return false;
            if (r == 0 || r > 536870912u) return false;
            if (h[p + 8] != 0x78) return false;
            if (((0x78 << 8) | h[p + 9]) % 31 != 0) return false;
            return true;
        }

        // End of a JPEG (index after FFD9) or -1; also returns the dimensions.
        static int JpegEnd(byte[] b, int s, int limit, out int w, out int h)
        {
            w = 0; h = 0;
            int i = s + 2;
            while (i + 4 <= limit)
            {
                if (b[i] != 0xFF) return -1;
                byte m = b[i + 1];
                if (m == 0xFF) { i++; continue; }
                if (m == 0xD9) return i + 2;
                if ((m >= 0xD0 && m <= 0xD7) || m == 0x01) { i += 2; continue; }
                int L = (b[i + 2] << 8) | b[i + 3];
                if (L < 2) return -1;
                if (m >= 0xC0 && m <= 0xC3 && i + 9 < limit)
                {
                    h = (b[i + 5] << 8) | b[i + 6];
                    w = (b[i + 7] << 8) | b[i + 8];
                }
                if (m == 0xDA)
                {
                    int j = i + 2 + L;
                    while (j + 1 < limit)
                    {
                        if (b[j] == 0xFF)
                        {
                            byte n = b[j + 1];
                            if (n == 0x00 || (n >= 0xD0 && n <= 0xD7)) { j += 2; continue; }
                            if (n == 0xFF) { j++; continue; }
                            break;
                        }
                        j++;
                    }
                    i = j;
                    continue;
                }
                i += 2 + L;
            }
            return -1;
        }

        static int Find(byte[] b, int max, params byte[] seq)
        {
            int lim = Math.Min(b.Length, max) - seq.Length;
            for (int i = 0; i <= lim; i++)
            {
                bool ok = true;
                for (int k = 0; k < seq.Length; k++) if (b[i + k] != seq[k]) { ok = false; break; }
                if (ok) return i;
            }
            return -1;
        }

        public static string GlName(int gl, out int ch)
        {
            switch (gl)
            {
                case 0x1907: ch = 3; return "RGB";
                case 0x1908: ch = 4; return "RGBA";
                case 0x80E0: ch = 3; return "BGR";
                case 0x80E1: ch = 4; return "BGRA";
                case 0x1909: ch = 1; return "LUMINANCE";
                case 0x190A: ch = 2; return "LUMINANCE_ALPHA";
                case 0x1906: ch = 1; return "ALPHA";
                default: ch = 0; return gl == 0 ? null : "GL 0x" + gl.ToString("X4");
            }
        }

        public static void ParsePayloadHeaderPublic(byte[] pl, VdbInfo info) { ParsePayloadHeader(pl, info); }

        static void ParsePayloadHeader(byte[] pl, VdbInfo info)
        {
            int lim = Math.Min(pl.Length, 16384);
            int p = Find(pl, lim, 0xFE, 0x05, 0x99);
            if (p >= 0 && p + 5 < pl.Length)
            {
                int l = U16(pl, p + 3);
                if (l > 0 && l < 1024 && p + 5 + l <= pl.Length) info.Name2 = DecodeName(pl, p + 5, l);
            }
            p = Find(pl, lim, 0xFE, 0x05, 0x94);
            if (p >= 0 && p + 11 <= pl.Length) { info.Width = (int)U32(pl, p + 3); info.Height = (int)U32(pl, p + 7); }
            p = Find(pl, lim, 0xFE, 0x05, 0x97);
            if (p >= 0 && p + 7 <= pl.Length) info.GlFormat = (int)U32(pl, p + 3);
            p = Find(pl, lim, 0xFE, 0x05, 0x93, 0xFE, 0x00, 0x05);
            if (p >= 0 && p + 10 <= pl.Length) { info.PixelLength = (int)U32(pl, p + 6); info.PixelOffset = p + 10; }

            int ch;
            info.PixelFormat = GlName(info.GlFormat, out ch);
            info.Channels = ch;
            if (info.Width > 0 && info.Height > 0 && info.PixelLength > 0 && info.Width < 65536 && info.Height < 65536)
            {
                long px = (long)info.Width * info.Height;
                if (info.Channels == 0 && info.PixelLength % px == 0) info.Channels = (int)(info.PixelLength / px);
                info.Kind = "Image";
            }
            else info.Kind = "Other";
        }

        public static VdbInfo Inspect(string path)
        {
            VdbInfo info = new VdbInfo();
            info.Path = path;
            info.Uuid = System.IO.Path.GetFileNameWithoutExtension(path).ToUpperInvariant();
            DirectoryInfo di = new FileInfo(path).Directory;
            info.Bucket = di == null ? "" : di.Name;
            info.Kind = "Unknown";
            try
            {
                using (FileStream fs = OpenRead(path))
                {
                    info.Size = fs.Length;
                    int headLen = (int)Math.Min(fs.Length, HeadMax);
                    byte[] head = ReadAt(fs, 0, headLen);

                    if (headLen >= 0x80)
                    {
                        uint nl = U32(head, 0x6E);
                        if (nl > 0 && nl <= 512 && 0x72 + nl <= headLen) info.Name = DecodeName(head, 0x72, (int)nl);
                    }
                    if (headLen >= 0x194)
                    {
                        info.Created = Ts(U32(head, 0x28));
                        info.Modified = Ts(U32(head, 0x190));
                    }

                    if (!TryContainer(fs, head, info))
                    {
                    // Section table: [u16 count][u16 idx][u32 flag][u32 len][name] ...
                    int scanStart = Math.Min(headLen, 0x2A0);
                    if (headLen >= 8)
                    {
                        uint st = U32(head, 4);
                        if (st >= 8 && st + 2 < headLen)
                        {
                            int p = (int)st, cnt = U16(head, p); p += 2;
                            List<string> names = new List<string>();
                            bool ok = cnt > 0 && cnt <= 64;
                            for (int i = 0; ok && i < cnt; i++)
                            {
                                if (p + 10 > headLen) { ok = false; break; }
                                p += 2 + 4;
                                uint l = U32(head, p); p += 4;
                                if (l == 0 || l > 64 || p + l > headLen) { ok = false; break; }
                                string n = Encoding.ASCII.GetString(head, p, (int)l);
                                if (!Regex.IsMatch(n, "^[A-Za-z0-9_]+$")) { ok = false; break; }
                                names.Add(n); p += (int)l;
                            }
                            if (ok) { info.Sections = string.Join(",", names.ToArray()); scanStart = p; }
                        }
                    }

                    // JPEG thumbnails
                    int lastThumbEnd = scanStart;
                    for (int i = scanStart; i + 4 < headLen && info.Thumbs.Count < 8; i++)
                    {
                        if (head[i] == 0xFF && head[i + 1] == 0xD8 && head[i + 2] == 0xFF &&
                            (head[i + 3] == 0xE0 || head[i + 3] == 0xE1 || head[i + 3] == 0xDB))
                        {
                            int w, h;
                            int e = JpegEnd(head, i, headLen, out w, out h);
                            if (e > 0)
                            {
                                Thumb t = new Thumb(); t.Offset = i; t.Length = e - i; t.Width = w; t.Height = h;
                                info.Thumbs.Add(t); lastThumbEnd = e; i = e - 1;
                            }
                        }
                    }

                    // Data chunks: [u32 total length][u32 uncompressed size][zlib stream]
                    for (int p = lastThumbEnd; p + 10 <= headLen; p++)
                    {
                        if (!ChunkHeaderOk(head, p, p, fs.Length)) continue;
                        int c = (int)U32(head, p), r = (int)U32(head, p + 4);
                        byte[] comp = (p + c <= headLen) ? head : ReadAt(fs, p, c);
                        int baseOff = (comp == head) ? p : 0;
                        byte[] raw = Inflate(comp, baseOff + 10, c - 10, r);
                        if (raw == null) continue;

                        long q = p;
                        while (q + 10 <= fs.Length)
                        {
                            byte[] hh = ReadAt(fs, q, 10);
                            if (!ChunkHeaderOk(hh, 0, q, fs.Length)) break;
                            Chunk ck = new Chunk(); ck.Offset = q; ck.CompLen = (int)U32(hh, 0); ck.RawLen = (int)U32(hh, 4);
                            info.Chunks.Add(ck); info.RawSize += ck.RawLen;
                            q += ck.CompLen;
                        }
                        ParsePayloadHeader(raw, info);
                        break;
                    }

                    }

                    // XML version block (at the end of the file)
                    int tl = (int)Math.Min(fs.Length, 16384);
                    string tail = info.AppName != null ? "" : Encoding.GetEncoding(28591).GetString(ReadAt(fs, fs.Length - tl, tl));
                    Match m = Regex.Match(tail, "<version>(.*?)</version>", RegexOptions.Singleline);
                    if (m.Success)
                    {
                        string x = m.Groups[1].Value;
                        Match a;
                        a = Regex.Match(x, "<dbi>.*?<ver>(.*?)</ver>"); if (a.Success) info.DbVersion = a.Groups[1].Value;
                        a = Regex.Match(x, "<app>.*?<name>(.*?)</name>.*?<ver>(.*?)</ver>");
                        if (a.Success) { info.AppName = a.Groups[1].Value; info.AppVersion = a.Groups[2].Value; }
                        a = Regex.Match(x, "<sys>.*?<name>(.*?)</name>.*?<ver>(.*?)</ver>");
                        if (a.Success) { info.SysName = a.Groups[1].Value; info.SysVersion = a.Groups[2].Value; }
                    }
                    if (info.Sections == null) { info.Name = null; info.Created = null; info.Modified = null; }
                    if (info.Chunks.Count == 0 && info.Sections == null) info.Kind = "Unknown";
                    else if (info.Chunks.Count == 0 && info.Kind != "Image" && info.Kind != "Scene" && info.Kind != "Material" && info.Kind != "Font" && info.Kind != "Other") info.Kind = "No data";
                }
            }
            catch (Exception ex) { info.Error = ex.Message; info.Kind = "Error"; }
            return info;
        }

        // ---- Container reading (section table + directory), works for old and new .vdb ----
        public class Sec { public int Id; public string Name; public string Attr; public long Offset; public long Length; }

        static bool ChunkOkAny(byte[] h, int p, long posInFile, long limit)
        {
            if (p + 10 > h.Length) return false;
            uint c = U32(h, p), r = U32(h, p + 4);
            if (c < 9 || posInFile + c > limit) return false;
            if (r == 0 || r > 536870912u) return false;
            if (c - 8 == r) return true;                       // stored (uncompressed) chunk
            if (h[p + 8] != 0x78) return false;
            return ((0x78 << 8) | h[p + 9]) % 31 == 0;
        }

        public static List<Sec> ReadSections(FileStream fs, byte[] head)
        {
            if (head.Length < 0x20) return null;
            uint st = U32(head, 4), dir = U32(head, 8), tail = U32(head, 0x10);
            if (st < 8 || st + 2 >= head.Length || dir >= fs.Length || tail > fs.Length || tail <= dir) return null;
            // section table: u16 count; entries: u16 idx, u32 type, u32 len, name [, u16 nAttr, (u32 len, text)*]
            int p = (int)st, cnt = U16(head, p); p += 2;
            if (cnt < 1 || cnt > 256) return null;
            Dictionary<int, Sec> byId = new Dictionary<int, Sec>();
            for (int i = 0; i < cnt; i++)
            {
                if (p + 10 > head.Length) return null;
                int idx = U16(head, p); uint type = U32(head, p + 2), l = U32(head, p + 6); p += 10;
                if (l == 0 || l > 64 || p + l > head.Length) return null;
                Sec s = new Sec(); s.Id = idx; s.Name = Encoding.ASCII.GetString(head, p, (int)l); p += (int)l;
                if (!Regex.IsMatch(s.Name, "^[A-Za-z0-9_.]+$")) return null;
                if (type < 1 || type > 64) return null;
                List<string> at = new List<string>();
                for (int k = 1; k < type; k++)
                {
                    if (p + 6 > head.Length) return null;
                    uint al = U32(head, p + 2); p += 6;
                    if (al > 256 || p + al > head.Length) return null;
                    at.Add(Encoding.ASCII.GetString(head, p, (int)al)); p += (int)al;
                }
                if (at.Count > 0) s.Attr = string.Join(";", at.ToArray());
                byId[idx] = s;
            }
            // directory
            byte[] d = ReadAt(fs, dir, (int)(tail - dir));
            int q = 0, n = U16(d, q); q += 2;
            List<Sec> res = new List<Sec>();
            for (int s = 0; s < n; s++)
            {
                if (q + 6 > d.Length) return null;
                int id = U16(d, q); int pages = (int)U32(d, q + 2); q += 6;
                long start = -1, len = 0, expect = -1;
                for (int k = 0; k < pages; k++)
                {
                    if (q + 13 > d.Length) return null;
                    uint size = U32(d, q + 4), off = U32(d, q + 8); q += 13;
                    if (start < 0) start = off;
                    if (expect >= 0 && off != expect) return null;
                    len += size; expect = off + size;
                }
                Sec sec;
                if (!byId.TryGetValue(id, out sec)) { sec = new Sec(); sec.Id = id; sec.Name = "Section" + id; }
                sec.Offset = start < 0 ? 0 : start; sec.Length = len;
                res.Add(sec);
            }
            if (q != d.Length) return null;
            return res;
        }

        public static List<Chunk> SectionChunks(FileStream fs, Sec s)
        {
            List<Chunk> list = new List<Chunk>();
            long q = s.Offset, end = s.Offset + s.Length;
            while (q + 10 <= end)
            {
                byte[] hh = ReadAt(fs, q, 10);
                if (!ChunkOkAny(hh, 0, q, end)) return null;
                Chunk ck = new Chunk(); ck.Offset = q; ck.CompLen = (int)U32(hh, 0); ck.RawLen = (int)U32(hh, 4);
                list.Add(ck); q += ck.CompLen;
            }
            return q == end ? list : null;
        }

        static byte[] ReadChunk(FileStream fs, Chunk c)
        {
            byte[] comp = ReadAt(fs, c.Offset, c.CompLen);
            if (c.CompLen - 8 == c.RawLen) { byte[] r = new byte[c.RawLen]; Buffer.BlockCopy(comp, 8, r, 0, c.RawLen); return r; }
            return Inflate(comp, 10, c.CompLen - 10, c.RawLen);
        }

        static bool TryContainer(FileStream fs, byte[] head, VdbInfo info)
        {
            List<Sec> secs;
            try { secs = ReadSections(fs, head); } catch { return false; }
            if (secs == null || secs.Count == 0) return false;
            info.SectionList = secs;
            List<string> names = new List<string>();
            foreach (Sec s in secs) names.Add(s.Name);
            info.Sections = string.Join(",", names.ToArray());

            VdbInfo preview = null;
            foreach (Sec s in secs)
            {
                if (s.Name.StartsWith("Icon") && s.Length > 0 && s.Length < 8388608)
                {
                    List<Chunk> ch = SectionChunks(fs, s);
                    if (ch == null) continue;
                    MemoryStream ms = new MemoryStream();
                    foreach (Chunk c in ch) { byte[] cb = ReadChunk(fs, c); if (cb != null) ms.Write(cb, 0, cb.Length); }
                    byte[] b = ms.ToArray();
                    if (info.TypeCode == 0 && b.Length > 3 && b[0] == 0xFE) info.TypeCode = (b[1] << 8) | b[2];
                    for (int i = 0; i + 4 < b.Length; i++)
                    {
                        if (b[i] == 0xFF && b[i + 1] == 0xD8 && b[i + 2] == 0xFF)
                        {
                            int w, h; int e = JpegEnd(b, i, b.Length, out w, out h);
                            if (e > 0)
                            {
                                Thumb t = new Thumb(); t.Length = e - i; t.Width = w; t.Height = h; t.Name = s.Name;
                                t.Bytes = new byte[e - i]; Buffer.BlockCopy(b, i, t.Bytes, 0, e - i);
                                info.Thumbs.Add(t);
                            }
                            break;
                        }
                    }
                }
                else if (s.Name.StartsWith("MMLevel")) info.MipLevels++;
                else if (s.Name == "VERSION" && s.Length > 0 && s.Length < 1048576)
                {
                    string x = Encoding.GetEncoding(28591).GetString(ReadAt(fs, s.Offset, (int)s.Length));
                    Match a;
                    a = Regex.Match(x, "<dbi>.*?<ver>(.*?)</ver>"); if (a.Success) info.DbVersion = a.Groups[1].Value;
                    a = Regex.Match(x, "<app>.*?<name>(.*?)</name>.*?<ver>(.*?)</ver>");
                    if (a.Success) { info.AppName = a.Groups[1].Value; info.AppVersion = a.Groups[2].Value; }
                    a = Regex.Match(x, "<sys>.*?<name>(.*?)</name>.*?<ver>(.*?)</ver>");
                    if (a.Success) { info.SysName = a.Groups[1].Value; info.SysVersion = a.Groups[2].Value; }
                }
            }

            // Pixel source: "Original" (full resolution, newer files) or "Data" (older files / preview)
            VdbInfo best = null; List<Chunk> bestChunks = null; Sec bestSec = null;
            foreach (string want in new string[] { "Data", "Original" })
            {
                foreach (Sec s in secs)
                {
                    if (s.Name != want || s.Length < 10) continue;
                    List<Chunk> ch = SectionChunks(fs, s);
                    if (ch == null || ch.Count == 0) continue;
                    byte[] raw = ReadChunk(fs, ch[0]);
                    if (raw == null) continue;
                    VdbInfo t = new VdbInfo(); ParsePayloadHeader(raw, t);
                    if (want == "Data") { info.Name2 = t.Name2; if (raw.Length > 3 && raw[0] == 0xFE) info.TypeCode = (raw[1] << 8) | raw[2]; if (best == null) { info.Chunks = ch; foreach (Chunk c in ch) info.RawSize += c.RawLen; } }
                    if (t.Kind == "Image")
                    {
                        if (want == "Data") preview = t;
                        if (best == null || (long)t.Width * t.Height > (long)best.Width * best.Height) { best = t; bestChunks = ch; bestSec = s; }
                    }
                }
            }
            if (best != null)
            {
                info.Kind = "Image"; info.Width = best.Width; info.Height = best.Height; info.GlFormat = best.GlFormat;
                info.Channels = best.Channels; info.PixelFormat = best.PixelFormat; info.PixelOffset = best.PixelOffset; info.PixelLength = best.PixelLength;
                info.Chunks = bestChunks; info.RawSize = 0; foreach (Chunk c in bestChunks) info.RawSize += c.RawLen;
                info.PixelSection = bestSec.Name;
                if (preview != null && bestSec.Name != "Data") info.PreviewSize = preview.Width + "x" + preview.Height;
            }
            else if (info.TypeCode == 0x0690) info.Kind = "Scene";
            else if (info.TypeCode == 0x0480) info.Kind = "Font";
            else if (info.TypeCode == 0x0600) info.Kind = "Material";
            else if (info.Chunks.Count > 0 || info.Thumbs.Count > 0) info.Kind = "Other";
            else info.Kind = "No data";
            return true;
        }

        // ---- Scene summary (names found in the scene data; format not documented) ----
        public class SceneSummary
        {
            public List<string> Containers = new List<string>();
            public List<string> Plugins = new List<string>();
            public List<string> Directors = new List<string>();
            public List<string> ControlFields = new List<string>();
            public List<string> References = new List<string>();
            public int TypeCode;
        }

        static List<string> TagStrings(byte[] d, int hi, int lo)
        {
            List<string> r = new List<string>();
            for (int i = 0; i + 5 < d.Length; i++)
            {
                if (d[i] != 0xFE || d[i + 1] != hi || d[i + 2] != lo) continue;
                int L = d[i + 3] | (d[i + 4] << 8);
                if (L < 1 || L > 512 || i + 5 + L > d.Length) continue;
                bool ok = true;
                for (int k = 0; k < L; k++) { byte c = d[i + 5 + k]; if (c < 32 && c != 9) { ok = false; break; } }
                if (!ok) continue;
                r.Add(Encoding.UTF8.GetString(d, i + 5, L));
                i += 4 + L;
            }
            return r;
        }

        public static byte[] ReadSectionPayload(VdbInfo info, string name)
        {
            if (info.SectionList == null) return null;
            using (FileStream fs = OpenRead(info.Path))
            {
                foreach (Sec s in info.SectionList)
                {
                    if (s.Name != name || s.Length == 0) continue;
                    List<Chunk> ch = SectionChunks(fs, s);
                    if (ch == null) return null;
                    MemoryStream o = new MemoryStream();
                    foreach (Chunk c in ch) { byte[] b = ReadChunk(fs, c); if (b == null) return null; o.Write(b, 0, b.Length); }
                    return o.ToArray();
                }
            }
            return null;
        }

        public static SceneSummary Scene(VdbInfo info)
        {
            SceneSummary r = new SceneSummary();
            r.TypeCode = info.TypeCode;
            byte[] d = ReadSectionPayload(info, "Data");
            if (d != null)
            {
                r.Containers = TagStrings(d, 0x03, 0x17);
                foreach (string p in TagStrings(d, 0x06, 0x23)) if (!r.Plugins.Contains(p)) r.Plugins.Add(p);
                r.Directors = TagStrings(d, 0x04, 0x22);
                foreach (Match m in Regex.Matches(Encoding.GetEncoding(28591).GetString(d), "(IMAGE|GEOM|FONT|MATERIAL|SCENE|MAT|AUDIO)\\*[^\\x00-\\x1f*:\"<>]{1,200}"))
                    if (!r.References.Contains(m.Value) && !m.Value.Contains(" ")) r.References.Add(m.Value);
            }
            byte[] x = ReadSectionPayload(info, "ExtraData");
            if (x != null)
            {
                string t = Encoding.UTF8.GetString(x);
                foreach (Match m in Regex.Matches(t, "<fielddef name=\"([^\"]*)\"(?: label=\"([^\"]*)\")?"))
                    r.ControlFields.Add(m.Groups[2].Success && m.Groups[2].Value != "" ? m.Groups[1].Value + " (" + m.Groups[2].Value + ")" : m.Groups[1].Value);
            }
            return r;
        }

        // ---- Scene data: nested tag stream (FE + u16 tag opens, FE + ~tag closes, FE 00 05 + u32 len = blob) ----
        public class TNode { public int Tag; public List<byte> Data = new List<byte>(); public List<TNode> Kids = new List<TNode>(); }

        public static TNode ParseTags(byte[] d)
        {
            TNode root = new TNode(); root.Tag = -1;
            List<TNode> st = new List<TNode>(); st.Add(root);
            int i = 0, n = d.Length;
            while (i < n)
            {
                if (d[i] == 0xFE && i + 2 < n)
                {
                    int t = (d[i + 1] << 8) | d[i + 2];
                    if (t == 0x0005 && i + 7 <= n)
                    {
                        int L = (int)U32(d, i + 3);
                        if (L < 0 || i + 7 + L > n) L = Math.Max(0, n - i - 7);
                        TNode b = new TNode(); b.Tag = 5;
                        for (int k = 0; k < L; k++) b.Data.Add(d[i + 7 + k]);
                        st[st.Count - 1].Kids.Add(b);
                        i += 7 + L;
                        if (i + 3 <= n && d[i] == 0xFE && d[i + 1] == 0xFF && d[i + 2] == 0xFA) i += 3;
                        continue;
                    }
                    int inv = (~t) & 0xFFFF;
                    if (st.Count > 1 && st[st.Count - 1].Tag == inv) { st.RemoveAt(st.Count - 1); i += 3; continue; }
                    int found = -1;
                    for (int k = st.Count - 1; k > 0; k--) if (st[k].Tag == inv) { found = k; break; }
                    if (found > 0 && t >= 0x8000) { st.RemoveRange(found, st.Count - found); i += 3; continue; }
                    TNode nd = new TNode(); nd.Tag = t;
                    st[st.Count - 1].Kids.Add(nd); st.Add(nd); i += 3; continue;
                }
                st[st.Count - 1].Data.Add(d[i]); i++;
            }
            return root;
        }

        static void JsonNode(TNode nd, StringBuilder sb)
        {
            sb.Append('[').Append(nd.Tag).Append(",\"");
            foreach (byte b in nd.Data) sb.Append(b.ToString("x2"));
            sb.Append('"');
            if (nd.Kids.Count > 0)
            {
                sb.Append(",[");
                for (int k = 0; k < nd.Kids.Count; k++) { if (k > 0) sb.Append(','); JsonNode(nd.Kids[k], sb); }
                sb.Append(']');
            }
            sb.Append(']');
        }

        // Returns "tree":...,"stage":... JSON fragments for the scene, or null
        public static string SceneTreeJson(VdbInfo info)
        {
            byte[] d = ReadSectionPayload(info, "Data");
            if (d == null) return null;
            TNode r = ParseTags(d);
            if (r.Kids.Count == 0) return null;
            TNode top = r.Kids[0], tree = null, stage = null;
            foreach (TNode k in top.Kids) { if (k.Tag == 0x07c0 && tree == null) tree = k; if (k.Tag == 0x0740 && stage == null) stage = k; }
            if (tree == null) return null;
            StringBuilder sb = new StringBuilder();
            sb.Append("\"tree\":"); JsonNode(tree, sb);
            sb.Append(",\"stage\":"); if (stage != null) JsonNode(stage, sb); else sb.Append("null");
            return sb.ToString();
        }

        // Heuristic: GH objects mentioned (as raw 16-byte UUIDs) near the scene's UUID in a GH table
        public static List<string> FindReferences(string table, string sceneUuid, HashSet<string> known, int window)
        {
            List<string> res = new List<string>();
            if (!File.Exists(table)) return res;
            byte[] d;
            using (FileStream fs = OpenRead(table)) d = ReadAt(fs, 0, (int)Math.Min(fs.Length, 536870912));
            byte[] u = new byte[16];
            for (int k = 0; k < 16; k++) u[k] = Convert.ToByte(sceneUuid.Substring(k * 2, 2), 16);
            for (int i = 0; i + 16 <= d.Length; i++)
            {
                bool hit = true;
                for (int k = 0; k < 16; k++) if (d[i + k] != u[k]) { hit = false; break; }
                if (!hit) continue;
                int a = Math.Max(0, i - window), b = Math.Min(d.Length - 16, i + window);
                for (int j = a; j <= b; j++)
                {
                    if (j == i) continue;
                    StringBuilder sb = new StringBuilder(32);
                    for (int k = 0; k < 16; k++) sb.Append(d[j + k].ToString("X2"));
                    string s = sb.ToString();
                    if (known.Contains(s) && s != sceneUuid && !res.Contains(s)) res.Add(s);
                }
            }
            return res;
        }

        // ---- Viz scripts stored in a scene: Script plugins (0700 > 0704 > 0704 > 0702 code) ----
        static string TagText(TNode n)
        {
            if (n == null || n.Data.Count < 2) return "";
            int L = n.Data[0] | (n.Data[1] << 8);
            int len = Math.Min(L, n.Data.Count - 2);
            return Encoding.UTF8.GetString(n.Data.GetRange(2, len).ToArray());
        }

        static void WalkScripts(TNode n, string owner, List<string[]> res)
        {
            if (n.Tag == 0x0300)
                foreach (TNode k in n.Kids) if (k.Tag == 0x0317) { owner = TagText(k); break; }
            if (n.Tag == 0x0702)
            {
                string code = TagText(n);
                if (code.Trim().Length > 0) res.Add(new string[] { owner ?? "(scene)", code });
            }
            foreach (TNode k in n.Kids) WalkScripts(k, owner, res);
        }

        public static List<string[]> SceneScripts(VdbInfo info)
        {
            List<string[]> res = new List<string[]>();
            byte[] d = ReadSectionPayload(info, "Data");
            if (d == null) return res;
            WalkScripts(ParseTags(d), null, res);
            return res;
        }

        // ---- ReferenceCollection.vdb.dat: one record per object
        //      [16-byte object UUID][u32 n][n folder UUIDs][u32 n][n "used by" UUIDs][u32 n][n "uses" UUIDs]
        public class RefTable
        {
            public Dictionary<string, List<string>> Uses = new Dictionary<string, List<string>>();
            public Dictionary<string, List<string>> UsedBy = new Dictionary<string, List<string>>();
            public Dictionary<string, List<string>> Folders = new Dictionary<string, List<string>>();
            public int Records, Skipped;
        }

        static List<string> RefList(byte[] d, ref int q, int max)
        {
            if (q + 4 > d.Length) return null;
            uint n = U32(d, q); q += 4;
            if (n > max || q + 16L * n > d.Length) return null;
            List<string> r = new List<string>((int)n);
            StringBuilder sb = new StringBuilder(32);
            for (int k = 0; k < n; k++)
            {
                sb.Length = 0;
                for (int j = 0; j < 16; j++) sb.Append(d[q + j].ToString("X2"));
                r.Add(sb.ToString()); q += 16;
            }
            return r;
        }

        public static RefTable ReadRefs(string path, HashSet<string> known)
        {
            RefTable t = new RefTable();
            byte[] d;
            using (FileStream fs = OpenRead(path)) d = ReadAt(fs, 0, (int)Math.Min(fs.Length, 1073741824));
            int p = 0;
            StringBuilder sb = new StringBuilder(32);
            while (p + 28 <= d.Length)
            {
                sb.Length = 0;
                for (int j = 0; j < 16; j++) sb.Append(d[p + j].ToString("X2"));
                string key = sb.ToString();
                int q = p + 16;
                List<string> f = RefList(d, ref q, 64), a = f == null ? null : RefList(d, ref q, 100000), u = a == null ? null : RefList(d, ref q, 100000);
                bool ok = f != null && a != null && u != null && f.Count >= 1;
                if (ok && known != null && known.Count > 0)
                {
                    if (!known.Contains(key)) { foreach (string x in a) if (!known.Contains(x)) { ok = false; break; } if (ok) foreach (string x in u) if (!known.Contains(x)) { ok = false; break; } if (a.Count + u.Count == 0) ok = false; }
                }
                if (!ok) { p += 4; t.Skipped += 4; continue; }
                t.Folders[key] = f; t.UsedBy[key] = a; t.Uses[key] = u; t.Records++;
                p = q;
            }
            return t;
        }

        public static byte[] ReadPayload(VdbInfo info)
        {
            using (FileStream fs = OpenRead(info.Path))
            using (MemoryStream all = new MemoryStream((int)Math.Min(info.RawSize, int.MaxValue)))
            {
                foreach (Chunk c in info.Chunks)
                {
                    byte[] raw = ReadChunk(fs, c);
                    if (raw == null) throw new InvalidDataException("Unreadable chunk at offset " + c.Offset);
                    all.Write(raw, 0, raw.Length);
                }
                return all.ToArray();
            }
        }

        public static byte[] ReadThumb(VdbInfo info, int index)
        {
            Thumb t = info.Thumbs[index];
            if (t.Bytes != null) return t.Bytes;
            using (FileStream fs = OpenRead(info.Path)) return ReadAt(fs, t.Offset, t.Length);
        }

        // ---- PNG ----
        static uint[] crcTable;
        static uint Crc(byte[] b, int o, int l, uint c)
        {
            if (crcTable == null)
            {
                crcTable = new uint[256];
                for (uint n = 0; n < 256; n++)
                {
                    uint x = n;
                    for (int k = 0; k < 8; k++) x = (x & 1) != 0 ? 0xEDB88320u ^ (x >> 1) : x >> 1;
                    crcTable[n] = x;
                }
            }
            for (int i = o; i < o + l; i++) c = crcTable[(c ^ b[i]) & 0xFF] ^ (c >> 8);
            return c;
        }
        static void BE(Stream s, uint v) { s.WriteByte((byte)(v >> 24)); s.WriteByte((byte)(v >> 16)); s.WriteByte((byte)(v >> 8)); s.WriteByte((byte)v); }
        static void PngChunk(Stream s, string type, byte[] data)
        {
            BE(s, (uint)data.Length);
            byte[] t = Encoding.ASCII.GetBytes(type);
            s.Write(t, 0, 4); s.Write(data, 0, data.Length);
            uint c = Crc(t, 0, 4, 0xFFFFFFFFu); c = Crc(data, 0, data.Length, c);
            BE(s, c ^ 0xFFFFFFFFu);
        }

        // Resamples (area average); returns top-down pixels in RGB(A) order.
        public static byte[] Resample(VdbInfo info, byte[] payload, bool flip, int tw, int th)
        {
            int w = info.Width, h = info.Height, ch = info.Channels;
            if (ch < 1 || ch > 4) throw new NotSupportedException("Unsupported pixel format: " + info.PixelFormat);
            if (tw < 1) tw = 1; if (th < 1) th = 1;
            int need = w * ch;
            int srcStride = (info.PixelLength % h == 0 && info.PixelLength / h >= need) ? info.PixelLength / h : need;
            if (info.PixelOffset + (long)srcStride * h > payload.Length) throw new InvalidDataException("Incomplete pixel data.");
            bool bgr = (info.GlFormat == 0x80E0 || info.GlFormat == 0x80E1) && ch >= 3;
            byte[] dst = new byte[tw * th * ch];
            double sx = (double)w / tw, sy = (double)h / th;
            long[] acc = new long[4];
            for (int ty = 0; ty < th; ty++)
            {
                int y0 = (int)(ty * sy), y1 = Math.Min(h, Math.Max(y0 + 1, (int)((ty + 1) * sy)));
                int stepY = Math.Max(1, (y1 - y0) / 6);
                for (int tx = 0; tx < tw; tx++)
                {
                    int x0 = (int)(tx * sx), x1 = Math.Min(w, Math.Max(x0 + 1, (int)((tx + 1) * sx)));
                    int stepX = Math.Max(1, (x1 - x0) / 6);
                    acc[0] = acc[1] = acc[2] = acc[3] = 0; int n = 0;
                    for (int y = y0; y < y1; y += stepY)
                    {
                        int row = info.PixelOffset + (flip ? h - 1 - y : y) * srcStride;
                        for (int x = x0; x < x1; x += stepX)
                        {
                            int p = row + x * ch;
                            for (int c = 0; c < ch; c++) acc[c] += payload[p + c];
                            n++;
                        }
                    }
                    int d = (ty * tw + tx) * ch;
                    for (int c = 0; c < ch; c++) dst[d + c] = (byte)(acc[c] / n);
                    if (bgr) { byte t = dst[d]; dst[d] = dst[d + 2]; dst[d + 2] = t; }
                }
            }
            return dst;
        }

        public static void FitSize(int w, int h, int max, out int tw, out int th)
        {
            if (w <= max && h <= max) { tw = w; th = h; return; }
            double s = (double)max / Math.Max(w, h);
            tw = Math.Max(1, (int)Math.Round(w * s)); th = Math.Max(1, (int)Math.Round(h * s));
        }

        public static void WritePng(string outPath, int w, int h, int ch, byte[] px)
        {
            int need = w * ch;
            byte colorType = (byte)(ch == 1 ? 0 : ch == 2 ? 4 : ch == 3 ? 2 : 6);
            byte[] rows = new byte[(need + 1) * h];
            for (int y = 0; y < h; y++) Buffer.BlockCopy(px, y * need, rows, y * (need + 1) + 1, need);
            uint s1 = 1, s2 = 0;
            for (int i = 0; i < rows.Length; i++) { s1 = (s1 + rows[i]) % 65521; s2 = (s2 + s1) % 65521; }
            byte[] idat;
            using (MemoryStream z = new MemoryStream())
            {
                z.WriteByte(0x78); z.WriteByte(0x9C);
                using (DeflateStream ds = new DeflateStream(z, CompressionLevel.Optimal, true)) ds.Write(rows, 0, rows.Length);
                BE(z, (s2 << 16) | s1);
                idat = z.ToArray();
            }
            using (FileStream o = new FileStream(outPath, FileMode.Create, FileAccess.Write))
            {
                byte[] sig = { 0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A };
                o.Write(sig, 0, 8);
                using (MemoryStream ih = new MemoryStream())
                {
                    BE(ih, (uint)w); BE(ih, (uint)h);
                    ih.WriteByte(8); ih.WriteByte(colorType); ih.WriteByte(0); ih.WriteByte(0); ih.WriteByte(0);
                    PngChunk(o, "IHDR", ih.ToArray());
                }
                PngChunk(o, "IDAT", idat);
                PngChunk(o, "IEND", new byte[0]);
            }
        }

        public static void WriteImagePng(VdbInfo info, byte[] payload, string outPath, bool flip)
        {
            WritePng(outPath, info.Width, info.Height, info.Channels, Resample(info, payload, flip, info.Width, info.Height));
        }

        public static void WriteThumbPng(VdbInfo info, byte[] payload, string outPath, bool flip, int max)
        {
            int tw, th; FitSize(info.Width, info.Height, max, out tw, out th);
            WritePng(outPath, tw, th, info.Channels, Resample(info, payload, flip, tw, th));
        }

        // Terminal preview: ▀ half blocks in 24-bit colour (ANSI sequences).
        public static string Ansi(VdbInfo info, byte[] payload, bool flip, int cols)
        {
            int w = info.Width, h = info.Height, ch = info.Channels;
            if (cols < 4) cols = 4; if (cols > w) cols = w;
            int rows = Math.Max(2, (int)Math.Round((double)h * cols / w));
            if (rows % 2 == 1) rows++;
            byte[] px = Resample(info, payload, flip, cols, rows);
            StringBuilder sb = new StringBuilder();
            string e = "\u001b[";
            for (int y = 0; y < rows; y += 2)
            {
                for (int x = 0; x < cols; x++)
                {
                    int r1, g1, b1, r2, g2, b2;
                    Rgb(px, (y * cols + x) * ch, ch, x, y, out r1, out g1, out b1);
                    Rgb(px, ((y + 1) * cols + x) * ch, ch, x, y + 1, out r2, out g2, out b2);
                    sb.Append(e).Append("38;2;").Append(r1).Append(';').Append(g1).Append(';').Append(b1).Append('m');
                    sb.Append(e).Append("48;2;").Append(r2).Append(';').Append(g2).Append(';').Append(b2).Append('m');
                    sb.Append('▀');
                }
                sb.Append(e).Append("0m").Append('\n');
            }
            return sb.ToString();
        }

        static void Rgb(byte[] px, int p, int ch, int x, int y, out int r, out int g, out int b)
        {
            int a = 255;
            if (ch <= 2) { r = g = b = px[p]; if (ch == 2) a = px[p + 1]; }
            else { r = px[p]; g = px[p + 1]; b = px[p + 2]; if (ch == 4) a = px[p + 3]; }
            if (a < 255)
            {
                int bg = (((x / 2) + (y / 2)) % 2 == 0) ? 60 : 90;   // checkerboard for transparency
                r = (r * a + bg * (255 - a)) / 255; g = (g * a + bg * (255 - a)) / 255; b = (b * a + bg * (255 - a)) / 255;
            }
        }

        [System.Runtime.InteropServices.DllImport("kernel32.dll")] static extern IntPtr GetStdHandle(int n);
        [System.Runtime.InteropServices.DllImport("kernel32.dll")] static extern bool GetConsoleMode(IntPtr h, out uint m);
        [System.Runtime.InteropServices.DllImport("kernel32.dll")] static extern bool SetConsoleMode(IntPtr h, uint m);

        // Enables ANSI colour processing in the classic Windows console.
        public static bool EnableVt()
        {
            if (Environment.OSVersion.Platform != PlatformID.Win32NT) return true;
            try
            {
                IntPtr hOut = GetStdHandle(-11); uint m;
                if (!GetConsoleMode(hOut, out m)) return false;
                return SetConsoleMode(hOut, m | 0x0004);
            }
            catch { return false; }
        }

        // ASCII and UTF-16LE string extraction (exploring undocumented files)
        public static List<string> Strings(string path, int min)
        {
            List<string> res = new List<string>();
            byte[] b;
            using (FileStream fs = OpenRead(path)) b = ReadAt(fs, 0, (int)Math.Min(fs.Length, 268435456));
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i <= b.Length; i++)
            {
                byte c = i < b.Length ? b[i] : (byte)0;
                if (c >= 0x20 && c < 0x7F) sb.Append((char)c);
                else { if (sb.Length >= min) res.Add(sb.ToString()); sb.Length = 0; }
            }
            sb.Length = 0;
            for (int i = 0; i + 1 <= b.Length; i += 2)
            {
                int c = i + 1 < b.Length ? (b[i] | (b[i + 1] << 8)) : 0;
                bool ok = (c >= 0x20 && c < 0x7F) || (c >= 0xC0 && c <= 0x17F);
                if (ok) sb.Append((char)c);
                else { if (sb.Length >= min) res.Add(sb.ToString()); sb.Length = 0; }
            }
            if (sb.Length >= min) res.Add(sb.ToString());
            return res;
        }
    }

    // =====================================================================
    //  Writing: .vdb container structure (inferred from one Viz 3.6 image file)
    //  [header][sections...][directory][references block]
    //  Header: u32@8 = directory offset, u32@0x0C = end-4, u32@0x10 = references offset,
    //          u32@0x2E and u32@0x184 = sum of section sizes.
    //  Directory: u16 sectionCount; for each section: u16 idx, u32 pageCount,
    //             pages: u32 idx, u32 size, u32 offset, u8 more (0 for the last page).
    // =====================================================================
    public class VdbLayout
    {
        public byte[] Header;
        public List<byte[]> Sections = new List<byte[]>();
        public List<int> SectionIds = new List<int>();
        public byte[] Tail;
        public int PageSize;
        public uint TrailField;   // original value of u32@0x0C
        public uint TailOffset;   // original value of u32@0x10
    }

    public static class VdbWriter
    {
        static uint U32(byte[] b, int o) { return (uint)(b[o] | (b[o + 1] << 8) | (b[o + 2] << 16) | (b[o + 3] << 24)); }
        static void P32(byte[] b, int o, uint v) { b[o] = (byte)v; b[o + 1] = (byte)(v >> 8); b[o + 2] = (byte)(v >> 16); b[o + 3] = (byte)(v >> 24); }
        static void W32(Stream s, uint v) { s.WriteByte((byte)v); s.WriteByte((byte)(v >> 8)); s.WriteByte((byte)(v >> 16)); s.WriteByte((byte)(v >> 24)); }
        static void W16(Stream s, int v) { s.WriteByte((byte)v); s.WriteByte((byte)(v >> 8)); }

        public static VdbLayout Parse(byte[] f)
        {
            if (f.Length < 0x200) throw new InvalidDataException("File too small.");
            uint dir = U32(f, 8), trail = U32(f, 0x0C), tail = U32(f, 0x10);
            if (dir >= f.Length || tail > f.Length || tail <= dir) throw new InvalidDataException("Inconsistent header offsets.");
            int p = (int)dir;
            int nSec = f[p] | (f[p + 1] << 8); p += 2;
            if (nSec < 1 || nSec > 32) throw new InvalidDataException("Unreadable section directory.");
            VdbLayout L = new VdbLayout();
            long expected = -1; int first = -1; int pageSize = 0;
            for (int s = 0; s < nSec; s++)
            {
                int id = f[p] | (f[p + 1] << 8); p += 2;
                int n = (int)U32(f, p); p += 4;
                if (n < 0 || n > 100000) throw new InvalidDataException("Invalid page count.");
                MemoryStream sec = new MemoryStream();
                for (int k = 0; k < n; k++)
                {
                    uint idx = U32(f, p), size = U32(f, p + 4), off = U32(f, p + 8); p += 13;
                    if (idx != k) throw new InvalidDataException("Unexpected page index.");
                    if (first < 0) first = (int)off;
                    if (expected >= 0 && off != expected) throw new InvalidDataException("Non-contiguous pages.");
                    if (off + size > dir) throw new InvalidDataException("Page out of bounds.");
                    if (k < n - 1) { if (pageSize == 0) pageSize = (int)size; else if (size != pageSize) throw new InvalidDataException("Variable page size."); }
                    sec.Write(f, (int)off, (int)size);
                    expected = off + size;
                }
                L.SectionIds.Add(id); L.Sections.Add(sec.ToArray());
            }
            if (p != tail) throw new InvalidDataException("Unexpected end of directory.");
            if (expected != dir) throw new InvalidDataException("The directory does not follow the sections.");
            L.Header = new byte[first]; Buffer.BlockCopy(f, 0, L.Header, 0, first);
            L.Tail = new byte[f.Length - tail]; Buffer.BlockCopy(f, (int)tail, L.Tail, 0, L.Tail.Length);
            L.PageSize = pageSize == 0 ? 0xC800 : pageSize;
            L.TrailField = trail; L.TailOffset = tail;
            long sum = 0; foreach (byte[] b in L.Sections) sum += b.Length;
            if (U32(f, 0x2E) != sum || U32(f, 0x184) != sum) throw new InvalidDataException("Unexpected total size field.");
            return L;
        }

        public static byte[] Build(VdbLayout L)
        {
            byte[] h = (byte[])L.Header.Clone();
            long sum = 0; foreach (byte[] b in L.Sections) sum += b.Length;
            uint dir = (uint)(h.Length + sum);
            MemoryStream d = new MemoryStream();
            W16(d, L.Sections.Count);
            long off = h.Length;
            int totalPages = 0;
            List<int> counts = new List<int>();
            foreach (byte[] b in L.Sections) { int n = b.Length == 0 ? 0 : (b.Length + L.PageSize - 1) / L.PageSize; counts.Add(n); totalPages += n; }
            int seen = 0;
            for (int s = 0; s < L.Sections.Count; s++)
            {
                W16(d, L.SectionIds[s]); W32(d, (uint)counts[s]);
                byte[] b = L.Sections[s];
                for (int k = 0; k < counts[s]; k++)
                {
                    int size = Math.Min(L.PageSize, b.Length - k * L.PageSize);
                    W32(d, (uint)k); W32(d, (uint)size); W32(d, (uint)off);
                    seen++; d.WriteByte((byte)(seen < totalPages ? 1 : 0));
                    off += size;
                }
            }
            byte[] dirBytes = d.ToArray();
            uint tail = (uint)(dir + dirBytes.Length);
            P32(h, 8, dir); P32(h, 0x10, tail);
            P32(h, 0x0C, (uint)(L.TrailField - L.TailOffset + tail));
            P32(h, 0x2E, (uint)sum); P32(h, 0x184, (uint)sum);
            MemoryStream o = new MemoryStream();
            o.Write(h, 0, h.Length);
            foreach (byte[] b in L.Sections) o.Write(b, 0, b.Length);
            o.Write(dirBytes, 0, dirBytes.Length);
            o.Write(L.Tail, 0, L.Tail.Length);
            return o.ToArray();
        }

        public static void BgraToRgba(byte[] b) { for (int i = 0; i + 3 < b.Length; i += 4) { byte t = b[i]; b[i] = b[i + 2]; b[i + 2] = t; } }

        public static bool SameBytes(byte[] a, byte[] b)
        {
            if (a.Length != b.Length) return false;
            for (int i = 0; i < a.Length; i++) if (a[i] != b[i]) return false;
            return true;
        }

        // ---- zlib ----
        public static byte[] Zlib(byte[] raw, int off, int len)
        {
            uint s1 = 1, s2 = 0;
            for (int i = off; i < off + len; i++) { s1 = (s1 + raw[i]) % 65521; s2 = (s2 + s1) % 65521; }
            using (MemoryStream z = new MemoryStream())
            {
                z.WriteByte(0x78); z.WriteByte(0x01);
                using (DeflateStream ds = new DeflateStream(z, CompressionLevel.Optimal, true)) ds.Write(raw, off, len);
                uint a = (s2 << 16) | s1;
                z.WriteByte((byte)(a >> 24)); z.WriteByte((byte)(a >> 16)); z.WriteByte((byte)(a >> 8)); z.WriteByte((byte)a);
                return z.ToArray();
            }
        }

        public static byte[] BuildDataSection(byte[] payload, int rawChunk)
        {
            MemoryStream o = new MemoryStream();
            for (int p = 0; p < payload.Length; p += rawChunk)
            {
                int n = Math.Min(rawChunk, payload.Length - p);
                byte[] z = Zlib(payload, p, n);
                W32(o, (uint)(z.Length + 8)); W32(o, (uint)n);
                o.Write(z, 0, z.Length);
            }
            return o.ToArray();
        }

        // ---- helpers for multi-section (newer) files ----
        public static byte[] DecodeSection(byte[] sec)
        {
            MemoryStream o = new MemoryStream();
            int p = 0;
            while (p + 8 <= sec.Length)
            {
                int c = (int)U32(sec, p), r = (int)U32(sec, p + 4);
                if (c < 9 || p + c > sec.Length) throw new InvalidDataException("Bad chunk in section.");
                if (c - 8 == r) o.Write(sec, p + 8, r);
                else
                {
                    using (MemoryStream ms = new MemoryStream(sec, p + 10, c - 10))
                    using (DeflateStream ds = new DeflateStream(ms, CompressionMode.Decompress))
                    {
                        byte[] buf = new byte[r]; int t = 0;
                        while (t < r) { int n = ds.Read(buf, t, r - t); if (n <= 0) break; t += n; }
                        if (t != r) throw new InvalidDataException("Bad zlib chunk in section.");
                        o.Write(buf, 0, r);
                    }
                }
                p += c;
            }
            if (p != sec.Length) throw new InvalidDataException("Section does not end on a chunk boundary.");
            return o.ToArray();
        }

        public static int FirstRawChunk(byte[] sec) { return sec.Length >= 8 ? (int)U32(sec, 4) : 0; }

        public static VdbInfo ParsePixels(byte[] payload)
        {
            VdbInfo t = new VdbInfo();
            Vdb.ParsePayloadHeaderPublic(payload, t);
            return t;
        }

        // Mip level payload: FE 0B 61 FE 0B 63 [u32 w][u32 h] ... FE 00 05 [u32 len] <BC1 blocks>
        public static int[] FindMip(byte[] pl)
        {
            if (pl.Length < 40 || pl[0] != 0xFE || pl[1] != 0x0B || pl[2] != 0x61 || pl[3] != 0xFE || pl[4] != 0x0B || pl[5] != 0x63) return null;
            int w = (int)U32(pl, 6), h = (int)U32(pl, 10);
            for (int i = 14; i + 7 <= Math.Min(pl.Length, 64); i++)
            {
                if (pl[i] == 0xFE && pl[i + 1] == 0x00 && pl[i + 2] == 0x05)
                {
                    int len = (int)U32(pl, i + 3);
                    if (i + 7 + (long)len > pl.Length) return null;
                    return new int[] { w, h, i + 7, len };
                }
            }
            return null;
        }

        // BC1 (DXT1) encoder, opaque 4-colour mode; flip = rows stored bottom-up
        public static void EncodeBC1(byte[] rgba, int w, int h, bool flip, byte[] dst, int off)
        {
            int bw = (w + 3) / 4, bh = (h + 3) / 4;
            int[] r = new int[16], g = new int[16], b = new int[16];
            int p = off;
            for (int by = 0; by < bh; by++)
                for (int bx = 0; bx < bw; bx++)
                {
                    int minR = 255, minG = 255, minB = 255, maxR = 0, maxG = 0, maxB = 0;
                    for (int j = 0; j < 16; j++)
                    {
                        int x = Math.Min(w - 1, bx * 4 + (j & 3)), y = Math.Min(h - 1, by * 4 + (j >> 2));
                        int sy = flip ? h - 1 - y : y;
                        int s = (sy * w + x) * 4;
                        r[j] = rgba[s]; g[j] = rgba[s + 1]; b[j] = rgba[s + 2];
                        if (r[j] < minR) minR = r[j]; if (g[j] < minG) minG = g[j]; if (b[j] < minB) minB = b[j];
                        if (r[j] > maxR) maxR = r[j]; if (g[j] > maxG) maxG = g[j]; if (b[j] > maxB) maxB = b[j];
                    }
                    // inset the bounding box slightly, then pick the diagonal that follows the colour covariance
                    int iR = (maxR - minR) >> 4, iG = (maxG - minG) >> 4, iB = (maxB - minB) >> 4;
                    minR += iR; minG += iG; minB += iB; maxR -= iR; maxG -= iG; maxB -= iB;
                    double mr = 0, mg = 0, mb = 0; for (int j = 0; j < 16; j++) { mr += r[j]; mg += g[j]; mb += b[j]; }
                    mr /= 16; mg /= 16; mb /= 16;
                    double crg = 0, cbg = 0; for (int j = 0; j < 16; j++) { crg += (r[j] - mr) * (g[j] - mg); cbg += (b[j] - mb) * (g[j] - mg); }
                    int r0 = maxR, g0 = maxG, b0 = maxB, r1 = minR, g1 = minG, b1 = minB;
                    if (crg < 0) { int t = r0; r0 = r1; r1 = t; }
                    if (cbg < 0) { int t = b0; b0 = b1; b1 = t; }
                    int c0 = ((r0 >> 3) << 11) | ((g0 >> 2) << 5) | (b0 >> 3);
                    int c1 = ((r1 >> 3) << 11) | ((g1 >> 2) << 5) | (b1 >> 3);
                    uint idx = 0;
                    if (c0 == c1)
                    {
                        if (c0 == 0xFFFF) c1 = 0xFFFE; else c0 = c0 + 1;   // keep 4-colour mode (c0 > c1)
                    }
                    if (c0 < c1) { int t = c0; c0 = c1; c1 = t; }
                    int[] pr = new int[4], pg = new int[4], pb = new int[4];
                    pr[0] = ((c0 >> 11) & 31) * 255 / 31; pg[0] = ((c0 >> 5) & 63) * 255 / 63; pb[0] = (c0 & 31) * 255 / 31;
                    pr[1] = ((c1 >> 11) & 31) * 255 / 31; pg[1] = ((c1 >> 5) & 63) * 255 / 63; pb[1] = (c1 & 31) * 255 / 31;
                    pr[2] = (2 * pr[0] + pr[1]) / 3; pg[2] = (2 * pg[0] + pg[1]) / 3; pb[2] = (2 * pb[0] + pb[1]) / 3;
                    pr[3] = (pr[0] + 2 * pr[1]) / 3; pg[3] = (pg[0] + 2 * pg[1]) / 3; pb[3] = (pb[0] + 2 * pb[1]) / 3;
                    for (int j = 0; j < 16; j++)
                    {
                        int bi = 0, bd = int.MaxValue;
                        for (int k = 0; k < 4; k++)
                        {
                            int dr = r[j] - pr[k], dg = g[j] - pg[k], db = b[j] - pb[k];
                            int dd = dr * dr * 3 + dg * dg * 4 + db * db * 2;
                            if (dd < bd) { bd = dd; bi = k; }
                        }
                        idx |= (uint)bi << (2 * j);
                    }
                    dst[p] = (byte)c0; dst[p + 1] = (byte)(c0 >> 8); dst[p + 2] = (byte)c1; dst[p + 3] = (byte)(c1 >> 8);
                    dst[p + 4] = (byte)idx; dst[p + 5] = (byte)(idx >> 8); dst[p + 6] = (byte)(idx >> 16); dst[p + 7] = (byte)(idx >> 24);
                    p += 8;
                }
        }

        public static byte[] DecodeBC1(byte[] src, int off, int w, int h, bool flip)
        {
            byte[] o = new byte[w * h * 4];
            int bw = (w + 3) / 4, bh = (h + 3) / 4, p = off;
            int[] pr = new int[4], pg = new int[4], pb = new int[4];
            for (int by = 0; by < bh; by++)
                for (int bx = 0; bx < bw; bx++)
                {
                    int c0 = src[p] | (src[p + 1] << 8), c1 = src[p + 2] | (src[p + 3] << 8);
                    uint idx = U32(src, p + 4); p += 8;
                    pr[0] = ((c0 >> 11) & 31) * 255 / 31; pg[0] = ((c0 >> 5) & 63) * 255 / 63; pb[0] = (c0 & 31) * 255 / 31;
                    pr[1] = ((c1 >> 11) & 31) * 255 / 31; pg[1] = ((c1 >> 5) & 63) * 255 / 63; pb[1] = (c1 & 31) * 255 / 31;
                    if (c0 > c1) { pr[2] = (2 * pr[0] + pr[1]) / 3; pg[2] = (2 * pg[0] + pg[1]) / 3; pb[2] = (2 * pb[0] + pb[1]) / 3; pr[3] = (pr[0] + 2 * pr[1]) / 3; pg[3] = (pg[0] + 2 * pg[1]) / 3; pb[3] = (pb[0] + 2 * pb[1]) / 3; }
                    else { pr[2] = (pr[0] + pr[1]) / 2; pg[2] = (pg[0] + pg[1]) / 2; pb[2] = (pb[0] + pb[1]) / 2; pr[3] = pg[3] = pb[3] = 0; }
                    for (int j = 0; j < 16; j++)
                    {
                        int x = bx * 4 + (j & 3), y = by * 4 + (j >> 2);
                        if (x >= w || y >= h) continue;
                        int sy = flip ? h - 1 - y : y, k = (int)((idx >> (2 * j)) & 3), d = (sy * w + x) * 4;
                        o[d] = (byte)pr[k]; o[d + 1] = (byte)pg[k]; o[d + 2] = (byte)pb[k]; o[d + 3] = 255;
                    }
                }
            return o;
        }

        public static byte[] BuildDataSectionLevel(byte[] payload, int rawChunk, bool fast)
        {
            MemoryStream o = new MemoryStream();
            for (int p = 0; p < payload.Length; p += rawChunk)
            {
                int n = Math.Min(rawChunk, payload.Length - p);
                byte[] z = ZlibLevel(payload, p, n, fast);
                if (z.Length >= n) { W32(o, (uint)(n + 8)); W32(o, (uint)n); o.Write(payload, p, n); }   // store when it does not compress
                else { W32(o, (uint)(z.Length + 8)); W32(o, (uint)n); o.Write(z, 0, z.Length); }
            }
            return o.ToArray();
        }

        static byte[] ZlibLevel(byte[] raw, int off, int len, bool fast)
        {
            uint s1 = 1, s2 = 0;
            for (int i = off; i < off + len; i++) { s1 = (s1 + raw[i]) % 65521; s2 = (s2 + s1) % 65521; }
            using (MemoryStream z = new MemoryStream())
            {
                z.WriteByte(0x78); z.WriteByte(0x01);
                using (DeflateStream ds = new DeflateStream(z, fast ? CompressionLevel.Fastest : CompressionLevel.Optimal, true)) ds.Write(raw, off, len);
                uint a = (s2 << 16) | s1;
                z.WriteByte((byte)(a >> 24)); z.WriteByte((byte)(a >> 16)); z.WriteByte((byte)(a >> 8)); z.WriteByte((byte)a);
                return z.ToArray();
            }
        }

        // ---- thumbnail sections are chunk streams; the JPEG block is
        //      04 00 "JPEG" [u32 J][u16 w][u16 h] FE 00 05 [u32 J] <JPEG> FE FF FA
        //      stored in its own chunk(s) of at most 51192 bytes ----
        static int IconMarker(byte[] pl)
        {
            for (int k = 0; k + 21 < pl.Length && k < 96; k++)
                if (pl[k] == 4 && pl[k + 1] == 0 && pl[k + 2] == 0x4A && pl[k + 3] == 0x50 && pl[k + 4] == 0x45 && pl[k + 5] == 0x47) return k;
            return -1;
        }

        public static byte[] RebuildIconSection(byte[] sec, byte[] jpeg, int w, int h)
        {
            byte[] pl;
            try { pl = DecodeSection(sec); } catch { return null; }
            int k = IconMarker(pl);
            if (k < 0) return null;
            int J = (int)U32(pl, k + 6);
            if (U32(pl, k + 17) != J || pl[k + 14] != 0xFE || pl[k + 15] != 0x00 || pl[k + 16] != 0x05) return null;
            int blockEnd = k + 21 + J + 3;
            if (blockEnd > pl.Length || pl[blockEnd - 3] != 0xFE || pl[blockEnd - 2] != 0xFF || pl[blockEnd - 1] != 0xFA) return null;
            // chunk boundaries in the section (file bytes) and in the payload (raw bytes)
            int p = 0; long raw = 0; int cutA = -1, cutB = -1;
            while (p + 8 <= sec.Length)
            {
                if (raw == k) cutA = p;
                if (raw == blockEnd) cutB = p;
                int c = (int)U32(sec, p), r = (int)U32(sec, p + 4);
                p += c; raw += r;
            }
            if (raw == blockEnd) cutB = p;
            if (cutA < 0 || cutB < 0) return null;
            int N = jpeg.Length;
            byte[] blk = new byte[21 + N + 3];
            Buffer.BlockCopy(pl, k, blk, 0, 6);
            P32(blk, 6, (uint)N); blk[10] = (byte)w; blk[11] = (byte)(w >> 8); blk[12] = (byte)h; blk[13] = (byte)(h >> 8);
            blk[14] = 0xFE; blk[15] = 0x00; blk[16] = 0x05; P32(blk, 17, (uint)N);
            Buffer.BlockCopy(jpeg, 0, blk, 21, N);
            blk[21 + N] = 0xFE; blk[22 + N] = 0xFF; blk[23 + N] = 0xFA;
            MemoryStream o = new MemoryStream();
            o.Write(sec, 0, cutA);
            for (int q = 0; q < blk.Length; q += 51192)
            {
                int n = Math.Min(51192, blk.Length - q);
                W32(o, (uint)(n + 8)); W32(o, (uint)n); o.Write(blk, q, n);
            }
            o.Write(sec, cutB, sec.Length - cutB);
            return o.ToArray();
        }

        public static int IconWidth(byte[] sec) { try { byte[] pl = DecodeSection(sec); int k = IconMarker(pl); return k < 0 ? 0 : pl[k + 10] | (pl[k + 11] << 8); } catch { return 0; } }
        public static int IconHeight(byte[] sec) { try { byte[] pl = DecodeSection(sec); int k = IconMarker(pl); return k < 0 ? 0 : pl[k + 12] | (pl[k + 13] << 8); } catch { return 0; } }
        public static byte[] IconJpeg(byte[] sec) { try { byte[] pl = DecodeSection(sec); int k = IconMarker(pl); if (k < 0) return null; int J = (int)U32(pl, k + 6); byte[] r = new byte[J]; Buffer.BlockCopy(pl, k + 21, r, 0, J); return r; } catch { return null; } }

        // ---- PNG decoding (non-interlaced) -> RGBA ----
        public static byte[] DecodePng(byte[] f, out int w, out int h)
        {
            w = 0; h = 0;
            byte[] sig = { 0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A };
            for (int i = 0; i < 8; i++) if (f[i] != sig[i]) throw new InvalidDataException("Not a PNG file.");
            int p = 8, depth = 0, ct = 0, inter = 0;
            byte[] pal = null, trns = null;
            MemoryStream idat = new MemoryStream();
            while (p + 8 <= f.Length)
            {
                int len = (f[p] << 24) | (f[p + 1] << 16) | (f[p + 2] << 8) | f[p + 3];
                string t = Encoding.ASCII.GetString(f, p + 4, 4);
                int d = p + 8;
                if (t == "IHDR")
                {
                    w = (f[d] << 24) | (f[d + 1] << 16) | (f[d + 2] << 8) | f[d + 3];
                    h = (f[d + 4] << 24) | (f[d + 5] << 16) | (f[d + 6] << 8) | f[d + 7];
                    depth = f[d + 8]; ct = f[d + 9]; inter = f[d + 12];
                }
                else if (t == "PLTE") { pal = new byte[len]; Buffer.BlockCopy(f, d, pal, 0, len); }
                else if (t == "tRNS") { trns = new byte[len]; Buffer.BlockCopy(f, d, trns, 0, len); }
                else if (t == "IDAT") idat.Write(f, d, len);
                else if (t == "IEND") break;
                p = d + len + 4;
            }
            if (inter != 0) throw new NotSupportedException("Interlaced PNG not supported (save it again without interlacing).");
            if (depth != 8 && depth != 16 && !(ct == 3 && depth <= 8)) throw new NotSupportedException("Unsupported PNG bit depth: " + depth);
            int chans = ct == 0 ? 1 : ct == 2 ? 3 : ct == 3 ? 1 : ct == 4 ? 2 : 4;
            int bpp = Math.Max(1, chans * depth / 8);
            int stride = (w * chans * depth + 7) / 8;
            byte[] z = idat.ToArray();
            byte[] raw = new byte[(stride + 1) * h];
            using (MemoryStream ms = new MemoryStream(z, 2, z.Length - 2))
            using (DeflateStream ds = new DeflateStream(ms, CompressionMode.Decompress))
            {
                int t = 0; while (t < raw.Length) { int n = ds.Read(raw, t, raw.Length - t); if (n <= 0) break; t += n; }
            }
            byte[] cur = new byte[stride], prev = new byte[stride];
            byte[] o = new byte[w * h * 4];
            for (int y = 0; y < h; y++)
            {
                int ft = raw[y * (stride + 1)];
                Buffer.BlockCopy(raw, y * (stride + 1) + 1, cur, 0, stride);
                for (int x = 0; x < stride; x++)
                {
                    int a = x >= bpp ? cur[x - bpp] : 0, b = prev[x], c = x >= bpp ? prev[x - bpp] : 0;
                    int v = cur[x];
                    switch (ft)
                    {
                        case 1: v += a; break;
                        case 2: v += b; break;
                        case 3: v += (a + b) >> 1; break;
                        case 4: { int pp = a + b - c, pa = Math.Abs(pp - a), pb = Math.Abs(pp - b), pc = Math.Abs(pp - c); v += (pa <= pb && pa <= pc) ? a : (pb <= pc ? b : c); } break;
                    }
                    cur[x] = (byte)v;
                }
                for (int x = 0; x < w; x++)
                {
                    int q = (y * w + x) * 4;
                    if (ct == 3)
                    {
                        int bitPos = x * depth, by = cur[bitPos >> 3], sh = 8 - depth - (bitPos & 7);
                        int idx = (by >> sh) & ((1 << depth) - 1);
                        o[q] = pal[idx * 3]; o[q + 1] = pal[idx * 3 + 1]; o[q + 2] = pal[idx * 3 + 2];
                        o[q + 3] = (trns != null && idx < trns.Length) ? trns[idx] : (byte)255;
                    }
                    else
                    {
                        int step = depth / 8, s = x * chans * step;
                        byte c0 = cur[s], c1 = chans > 1 ? cur[s + step] : (byte)0, c2 = chans > 2 ? cur[s + 2 * step] : (byte)0, c3 = chans > 3 ? cur[s + 3 * step] : (byte)255;
                        if (chans == 1) { o[q] = o[q + 1] = o[q + 2] = c0; o[q + 3] = 255; }
                        else if (chans == 2) { o[q] = o[q + 1] = o[q + 2] = c0; o[q + 3] = c1; }
                        else { o[q] = c0; o[q + 1] = c1; o[q + 2] = c2; o[q + 3] = chans == 4 ? c3 : (byte)255; }
                    }
                }
                byte[] t2 = prev; prev = cur; cur = t2;
            }
            return o;
        }

        // ---- RGBA resizing (premultiplied alpha) ----
        // mode: "stretch", "fit" (borders in the bg colour), "fill" (centred crop)
        public static byte[] Resize(byte[] src, int sw, int sh, int tw, int th, string mode, byte br, byte bgc, byte bb, byte ba)
        {
            double cx0 = 0, cy0 = 0, cw = sw, chh = sh;     // source area used
            int dx0 = 0, dy0 = 0, dw = tw, dh = th;          // target area filled
            double sa = (double)sw / sh, ta = (double)tw / th;
            if (mode == "fill")
            {
                if (sa > ta) { cw = sh * ta; cx0 = (sw - cw) / 2; } else { chh = sw / ta; cy0 = (sh - chh) / 2; }
            }
            else if (mode == "fit")
            {
                if (sa > ta) { dh = Math.Max(1, (int)Math.Round(tw / sa)); dy0 = (th - dh) / 2; } else { dw = Math.Max(1, (int)Math.Round(th * sa)); dx0 = (tw - dw) / 2; }
            }
            byte[] o = new byte[tw * th * 4];
            for (int i = 0; i < tw * th; i++) { o[i * 4] = br; o[i * 4 + 1] = bgc; o[i * 4 + 2] = bb; o[i * 4 + 3] = ba; }
            double fx = cw / dw, fy = chh / dh;
            int nx = Math.Max(1, Math.Min(8, (int)Math.Ceiling(fx))), ny = Math.Max(1, Math.Min(8, (int)Math.Ceiling(fy)));
            for (int y = 0; y < dh; y++)
            {
                for (int x = 0; x < dw; x++)
                {
                    double r = 0, g = 0, b = 0, a = 0;
                    for (int j = 0; j < ny; j++)
                    {
                        double sy = cy0 + (y + (j + 0.5) / ny) * fy - 0.5;
                        for (int i = 0; i < nx; i++)
                        {
                            double sx = cx0 + (x + (i + 0.5) / nx) * fx - 0.5;
                            // bilinear
                            int x0 = (int)Math.Floor(sx), y0 = (int)Math.Floor(sy);
                            double ax = sx - x0, ay = sy - y0;
                            for (int k = 0; k < 4; k++)
                            {
                                int xx = Math.Max(0, Math.Min(sw - 1, x0 + (k & 1))), yy = Math.Max(0, Math.Min(sh - 1, y0 + (k >> 1)));
                                double wgt = ((k & 1) == 1 ? ax : 1 - ax) * ((k >> 1) == 1 ? ay : 1 - ay);
                                int q = (yy * sw + xx) * 4;
                                double al = src[q + 3] / 255.0 * wgt;
                                r += src[q] * al; g += src[q + 1] * al; b += src[q + 2] * al; a += al;
                            }
                        }
                    }
                    double n = nx * ny;
                    int t = ((y + dy0) * tw + (x + dx0)) * 4;
                    if (a > 1e-9) { o[t] = Clamp(r / a); o[t + 1] = Clamp(g / a); o[t + 2] = Clamp(b / a); }
                    double alpha = a / n;
                    if (ba == 255 || alpha >= 0.999) o[t + 3] = Clamp(alpha * 255);
                    else o[t + 3] = Clamp(alpha * 255);
                    if (alpha < 0.999 && ba == 255)
                    {   // composite over the background
                        o[t] = Clamp(o[t] * alpha + br * (1 - alpha)); o[t + 1] = Clamp(o[t + 1] * alpha + bgc * (1 - alpha)); o[t + 2] = Clamp(o[t + 2] * alpha + bb * (1 - alpha)); o[t + 3] = 255;
                    }
                }
            }
            return o;
        }
        static byte Clamp(double v) { return (byte)(v < 0 ? 0 : v > 255 ? 255 : (int)(v + 0.5)); }

        // RGBA (top-down) -> pixels in the GL format, rows bottom-up
        public static void WritePixels(byte[] rgba, int w, int h, int gl, int channels, bool flip, byte[] payload, int off, int stride, byte br, byte bgc, byte bb)
        {
            for (int y = 0; y < h; y++)
            {
                int row = off + (flip ? h - 1 - y : y) * stride;
                for (int x = 0; x < w; x++)
                {
                    int s = (y * w + x) * 4, d = row + x * channels;
                    byte r = rgba[s], g = rgba[s + 1], b = rgba[s + 2], a = rgba[s + 3];
                    if (channels < 4 && channels != 2 && a < 255 && gl != 0x1906)
                    {   // format without alpha: composite over the background
                        r = (byte)((r * a + br * (255 - a)) / 255); g = (byte)((g * a + bgc * (255 - a)) / 255); b = (byte)((b * a + bb * (255 - a)) / 255);
                    }
                    byte lum = (byte)((r * 299 + g * 587 + b * 114) / 1000);
                    switch (gl)
                    {
                        case 0x1907: payload[d] = r; payload[d + 1] = g; payload[d + 2] = b; break;
                        case 0x1908: payload[d] = r; payload[d + 1] = g; payload[d + 2] = b; payload[d + 3] = a; break;
                        case 0x80E0: payload[d] = b; payload[d + 1] = g; payload[d + 2] = r; break;
                        case 0x80E1: payload[d] = b; payload[d + 1] = g; payload[d + 2] = r; payload[d + 3] = a; break;
                        case 0x1909: payload[d] = lum; break;
                        case 0x190A: payload[d] = lum; payload[d + 1] = a; break;
                        case 0x1906: payload[d] = a; break;
                        default: throw new NotSupportedException("Pixel format not supported for writing.");
                    }
                }
            }
        }

        // ---- baseline JPEG encoder (4:4:4) ----
        static readonly int[] ZZ = { 0,1,8,16,9,2,3,10,17,24,32,25,18,11,4,5,12,19,26,33,40,48,41,34,27,20,13,6,7,14,21,28,35,42,49,56,57,50,43,36,29,22,15,23,30,37,44,51,58,59,52,45,38,31,39,46,53,60,61,54,47,55,62,63 };
        static readonly int[] QL = { 16,11,10,16,24,40,51,61,12,12,14,19,26,58,60,55,14,13,16,24,40,57,69,56,14,17,22,29,51,87,80,62,18,22,37,56,68,109,103,77,24,35,55,64,81,104,113,92,49,64,78,87,103,121,120,101,72,92,95,98,112,100,103,99 };
        static readonly int[] QC = { 17,18,24,47,99,99,99,99,18,21,26,66,99,99,99,99,24,26,56,99,99,99,99,99,47,66,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99,99 };
        static readonly byte[] DcLb = { 0,1,5,1,1,1,1,1,1,0,0,0,0,0,0,0 }, DcLv = { 0,1,2,3,4,5,6,7,8,9,10,11 };
        static readonly byte[] DcCb = { 0,3,1,1,1,1,1,1,1,1,1,0,0,0,0,0 }, DcCv = { 0,1,2,3,4,5,6,7,8,9,10,11 };
        static readonly byte[] AcLb = { 0,2,1,3,3,2,4,3,5,5,4,4,0,0,1,0x7d };
        static readonly byte[] AcLv = { 0x01,0x02,0x03,0x00,0x04,0x11,0x05,0x12,0x21,0x31,0x41,0x06,0x13,0x51,0x61,0x07,0x22,0x71,0x14,0x32,0x81,0x91,0xa1,0x08,0x23,0x42,0xb1,0xc1,0x15,0x52,0xd1,0xf0,0x24,0x33,0x62,0x72,0x82,0x09,0x0a,0x16,0x17,0x18,0x19,0x1a,0x25,0x26,0x27,0x28,0x29,0x2a,0x34,0x35,0x36,0x37,0x38,0x39,0x3a,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5a,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8a,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9a,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,0xa8,0xa9,0xaa,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,0xb8,0xb9,0xba,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7,0xc8,0xc9,0xca,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7,0xd8,0xd9,0xda,0xe1,0xe2,0xe3,0xe4,0xe5,0xe6,0xe7,0xe8,0xe9,0xea,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,0xf8,0xf9,0xfa };
        static readonly byte[] AcCb = { 0,2,1,2,4,4,3,4,7,5,4,4,0,1,2,0x77 };
        static readonly byte[] AcCv = { 0x00,0x01,0x02,0x03,0x11,0x04,0x05,0x21,0x31,0x06,0x12,0x41,0x51,0x07,0x61,0x71,0x13,0x22,0x32,0x81,0x08,0x14,0x42,0x91,0xa1,0xb1,0xc1,0x09,0x23,0x33,0x52,0xf0,0x15,0x62,0x72,0xd1,0x0a,0x16,0x24,0x34,0xe1,0x25,0xf1,0x17,0x18,0x19,0x1a,0x26,0x27,0x28,0x29,0x2a,0x35,0x36,0x37,0x38,0x39,0x3a,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5a,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8a,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9a,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,0xa8,0xa9,0xaa,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,0xb8,0xb9,0xba,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7,0xc8,0xc9,0xca,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7,0xd8,0xd9,0xda,0xe2,0xe3,0xe4,0xe5,0xe6,0xe7,0xe8,0xe9,0xea,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,0xf8,0xf9,0xfa };

        static void BuildHuff(byte[] bits, byte[] vals, int[] code, int[] size)
        {
            int c = 0, k = 0;
            for (int l = 1; l <= 16; l++) { for (int i = 0; i < bits[l - 1]; i++) { code[vals[k]] = c; size[vals[k]] = l; k++; c++; } c <<= 1; }
        }

        class BitW
        {
            public MemoryStream S = new MemoryStream(); int acc = 0, n = 0;
            public void Put(int code, int len)
            {
                for (int i = len - 1; i >= 0; i--)
                {
                    acc = (acc << 1) | ((code >> i) & 1); n++;
                    if (n == 8) { S.WriteByte((byte)acc); if (acc == 0xFF) S.WriteByte(0); acc = 0; n = 0; }
                }
            }
            public void Flush() { while (n != 0) Put(1, 1); }
        }

        static void Seg(MemoryStream o, int marker, byte[] data)
        {
            o.WriteByte(0xFF); o.WriteByte((byte)marker);
            o.WriteByte((byte)((data.Length + 2) >> 8)); o.WriteByte((byte)(data.Length + 2));
            o.Write(data, 0, data.Length);
        }

        public static byte[] EncodeJpeg(byte[] rgba, int w, int h, int quality)
        {
            int sc = quality < 50 ? 5000 / quality : 200 - quality * 2;
            int[] ql = new int[64], qc = new int[64];
            for (int i = 0; i < 64; i++) { ql[i] = Math.Max(1, Math.Min(255, (QL[i] * sc + 50) / 100)); qc[i] = Math.Max(1, Math.Min(255, (QC[i] * sc + 50) / 100)); }
            int[] dcLc = new int[256], dcLs = new int[256], dcCc = new int[256], dcCs = new int[256], acLc = new int[256], acLs = new int[256], acCc = new int[256], acCs = new int[256];
            BuildHuff(DcLb, DcLv, dcLc, dcLs); BuildHuff(DcCb, DcCv, dcCc, dcCs); BuildHuff(AcLb, AcLv, acLc, acLs); BuildHuff(AcCb, AcCv, acCc, acCs);

            MemoryStream o = new MemoryStream();
            o.WriteByte(0xFF); o.WriteByte(0xD8);
            Seg(o, 0xE0, new byte[] { 0x4A, 0x46, 0x49, 0x46, 0, 1, 1, 1, 0, 72, 0, 72, 0, 0 });
            byte[] dqt = new byte[130];
            dqt[0] = 0; for (int i = 0; i < 64; i++) dqt[1 + i] = (byte)ql[ZZ[i]];
            dqt[65] = 1; for (int i = 0; i < 64; i++) dqt[66 + i] = (byte)qc[ZZ[i]];
            Seg(o, 0xDB, dqt);
            Seg(o, 0xC0, new byte[] { 8, (byte)(h >> 8), (byte)h, (byte)(w >> 8), (byte)w, 3, 1, 0x11, 0, 2, 0x11, 1, 3, 0x11, 1 });
            MemoryStream ht = new MemoryStream();
            byte[][] tb = { DcLb, AcLb, DcCb, AcCb }; byte[][] tv = { DcLv, AcLv, DcCv, AcCv }; byte[] cls = { 0x00, 0x10, 0x01, 0x11 };
            for (int t = 0; t < 4; t++) { ht.WriteByte(cls[t]); ht.Write(tb[t], 0, 16); ht.Write(tv[t], 0, tv[t].Length); }
            Seg(o, 0xC4, ht.ToArray());
            Seg(o, 0xDA, new byte[] { 3, 1, 0x00, 2, 0x11, 3, 0x11, 0, 63, 0 });

            BitW bw = new BitW();
            int[] pred = new int[3];
            double[] blk = new double[64]; int[] q = new int[64];
            for (int by = 0; by < h; by += 8)
                for (int bx = 0; bx < w; bx += 8)
                    for (int comp = 0; comp < 3; comp++)
                    {
                        for (int y = 0; y < 8; y++)
                            for (int x = 0; x < 8; x++)
                            {
                                int xx = Math.Min(w - 1, bx + x), yy = Math.Min(h - 1, by + y), s = (yy * w + xx) * 4;
                                double r = rgba[s], g = rgba[s + 1], b = rgba[s + 2];
                                double v = comp == 0 ? 0.299 * r + 0.587 * g + 0.114 * b - 128
                                         : comp == 1 ? -0.168736 * r - 0.331264 * g + 0.5 * b
                                         : 0.5 * r - 0.418688 * g - 0.081312 * b;
                                blk[y * 8 + x] = v;
                            }
                        int[] qt = comp == 0 ? ql : qc;
                        for (int v = 0; v < 8; v++)
                            for (int u = 0; u < 8; u++)
                            {
                                double sum = 0;
                                for (int y = 0; y < 8; y++)
                                    for (int x = 0; x < 8; x++)
                                        sum += blk[y * 8 + x] * Math.Cos((2 * x + 1) * u * Math.PI / 16) * Math.Cos((2 * y + 1) * v * Math.PI / 16);
                                double cu = u == 0 ? 1 / Math.Sqrt(2) : 1, cv = v == 0 ? 1 / Math.Sqrt(2) : 1;
                                q[v * 8 + u] = (int)Math.Round(0.25 * cu * cv * sum / qt[v * 8 + u]);
                            }
                        int[] dcc = comp == 0 ? dcLc : dcCc, dcs = comp == 0 ? dcLs : dcCs, acc = comp == 0 ? acLc : acCc, acs = comp == 0 ? acLs : acCs;
                        int diff = q[0] - pred[comp]; pred[comp] = q[0];
                        EncNum(bw, diff, dcc, dcs, 0);
                        int run = 0;
                        for (int k = 1; k < 64; k++)
                        {
                            int c = q[ZZ[k]];
                            if (c == 0) { run++; continue; }
                            while (run > 15) { bw.Put(acc[0xF0], acs[0xF0]); run -= 16; }
                            EncNum(bw, c, acc, acs, run);
                            run = 0;
                        }
                        if (run > 0) bw.Put(acc[0], acs[0]);
                    }
            bw.Flush();
            byte[] sd = bw.S.ToArray(); o.Write(sd, 0, sd.Length);
            o.WriteByte(0xFF); o.WriteByte(0xD9);
            return o.ToArray();
        }

        static void EncNum(BitW bw, int v, int[] code, int[] size, int run)
        {
            int a = Math.Abs(v), n = 0; while (a > 0) { n++; a >>= 1; }
            int sym = (run << 4) | n;
            bw.Put(code[sym], size[sym]);
            if (n > 0) bw.Put(v < 0 ? v + (1 << n) - 1 : v, n);
        }
    }
}
'@
} catch { Stop-GhFatal 'Could not compile the reading engine (Add-Type).' $_ }
}

# ---------------------------------------------------------------------------
#  Configuration and utilities
# ---------------------------------------------------------------------------
$script:ConfigDir = Join-Path ([Environment]::GetFolderPath('LocalApplicationData')) 'GHTool'
if (-not [Environment]::GetFolderPath('LocalApplicationData')) { $script:ConfigDir = Join-Path $HOME '.ghtool' }
$script:ConfigFile = Join-Path $script:ConfigDir 'config.json'
$script:GhRoot = $null
$script:Index = $null
$script:IndexRoot = $null

function Write-Gh([string]$Text, [string]$Color = 'Gray', [switch]$NoNewline) {
    if ($NoNewline) { Write-Host $Text -ForegroundColor $Color -NoNewline } else { Write-Host $Text -ForegroundColor $Color }
}
function Write-GhTitle([string]$Text) { Write-Host ''; Write-Host $Text -ForegroundColor Cyan; Write-Host ('-' * [Math]::Min(78, $Text.Length)) -ForegroundColor DarkCyan }
function Write-GhWarn([string]$Text) { Write-Host "  ! $Text" -ForegroundColor Yellow }
function Write-GhErr([string]$Text) { Write-Host "  x $Text" -ForegroundColor Red }
function Write-GhOk([string]$Text) { Write-Host "  v $Text" -ForegroundColor Green }

function Format-Size([double]$b) {
    if ($b -ge 1TB) { return '{0:N2} TB' -f ($b / 1TB) }
    if ($b -ge 1GB) { return '{0:N2} GB' -f ($b / 1GB) }
    if ($b -ge 1MB) { return '{0:N1} MB' -f ($b / 1MB) }
    if ($b -ge 1KB) { return '{0:N1} KB' -f ($b / 1KB) }
    return '{0:N0} B' -f $b
}

function Save-GhConfig {
    if (-not (Test-Path -LiteralPath $script:ConfigDir)) { New-Item -ItemType Directory -Path $script:ConfigDir -Force | Out-Null }
    @{ Path = $script:GhRoot } | ConvertTo-Json | Set-Content -LiteralPath $script:ConfigFile -Encoding UTF8
}
function Import-GhConfig {
    if (Test-Path -LiteralPath $script:ConfigFile) {
        try {
            $c = Get-Content -LiteralPath $script:ConfigFile -Raw | ConvertFrom-Json
            if ($c.Path -and (Test-Path -LiteralPath $c.Path)) { $script:GhRoot = $c.Path }
        } catch { }
    }
}

function Test-GhDataFolder([string]$p) {
    if (-not (Test-Path -LiteralPath $p -PathType Container)) { return $false }
    if (Test-Path -LiteralPath (Join-Path $p 'VizDbTables')) { return $true }
    if (Test-Path -LiteralPath (Join-Path $p 'TreeNodeCollection.dat')) { return $true }
    $b = @(Get-ChildItem -LiteralPath $p -Directory -ErrorAction SilentlyContinue | Where-Object { $_.Name -match '^[0-9A-F]$' })
    return ($b.Count -ge 8)
}

function Resolve-GhRoot([string]$Name) {
    $cands = New-Object System.Collections.Generic.List[string]
    if ([IO.Path]::IsPathRooted($Name)) { $cands.Add($Name) }
    else {
        $cands.Add((Join-Path (Get-Location).ProviderPath $Name))
        foreach ($base in @($env:ProgramData, $env:ProgramFiles, ${env:ProgramFiles(x86)}, 'C:\', 'D:\')) {
            if (-not $base -or -not (Test-Path -LiteralPath $base)) { continue }
            $cands.Add((Join-Path $base $Name))
            foreach ($v in @('vizrt', 'Vizrt')) {
                $vz = Join-Path $base $v
                if (Test-Path -LiteralPath $vz) {
                    Get-ChildItem -LiteralPath $vz -Directory -ErrorAction SilentlyContinue | ForEach-Object { $cands.Add((Join-Path $_.FullName $Name)) }
                }
            }
        }
    }
    foreach ($c in $cands) {
        if (-not (Test-Path -LiteralPath $c -PathType Container)) { continue }
        $full = (Resolve-Path -LiteralPath $c).ProviderPath
        if (Test-GhDataFolder $full) { return $full }
        # nested folder (e.g. a copy VizGHData\VizGHData)
        foreach ($sub in Get-ChildItem -LiteralPath $full -Directory -ErrorAction SilentlyContinue) {
            if (Test-GhDataFolder $sub.FullName) { return $sub.FullName }
        }
    }
    return $null
}

function Get-GhRoot {
    if (-not $script:GhRoot) { Import-GhConfig }
    if (-not $script:GhRoot) {
        $r = Resolve-GhRoot 'VizGHData'
        if ($r) { $script:GhRoot = $r }
    }
    if (-not $script:GhRoot) { throw "No Graphic Hub folder set. Use: gh set <folder>" }
    return $script:GhRoot
}

function Get-RelPath([string]$root, [string]$full) {
    if ($full.StartsWith($root, [StringComparison]::OrdinalIgnoreCase)) { return $full.Substring($root.Length).TrimStart('\', '/') }
    return $full
}

function Get-GhCategory([string]$rel, [string]$root) {
    $parts = $rel -split '[\\/]'
    if ($parts.Count -eq 1) { if ($rel -match '\.vdb$') { return 'Catalogue (root .vdb)' } return 'HQL tables (root)' }
    $top = $parts[0]
    if ($top -cmatch '^[0-9A-F]$') { return 'Objects (.vdb)' }
    switch ($top) {
        'VizDbTables' { return 'Data tables (VizDbTables)' }
        'LogFiles' { return 'Logs (LogFiles)' }
        'VizDbRecover' { return 'Recovery (VizDbRecover)' }
        'VizDbUnitIndex' { return 'Index (VizDbUnitIndex)' }
    }
    if (Test-Path -LiteralPath (Join-Path (Join-Path $root $top) 'CURRENT')) { return 'RocksDB' }
    return "Other ($top)"
}

# ---------------------------------------------------------------------------
#  Object index (.vdb)
# ---------------------------------------------------------------------------
function Get-GhIndexStamp($files) {
    $n = 0; $s = [long]0; $t = [long]0
    foreach ($f in $files) { $n++; $s += $f.Length; if ($f.LastWriteTimeUtc.Ticks -gt $t) { $t = $f.LastWriteTimeUtc.Ticks } }
    return "v$($script:GhVersion)|$n|$s|$t"
}

function Get-GhVdbFiles([string]$root) {
    Get-ChildItem -LiteralPath $root -Directory | Where-Object { $_.Name -cmatch '^[0-9A-F]$' } |
        ForEach-Object { Get-ChildItem -LiteralPath $_.FullName -File -Filter '*.vdb' -ErrorAction SilentlyContinue }
}

function ConvertTo-GhRow($i) {
    [pscustomobject]@{
        Uuid = $i.Uuid; Bucket = $i.Bucket; Name = $i.Name; Kind = $i.Kind
        Width = $i.Width; Height = $i.Height; PixelFormat = $i.PixelFormat
        Size = $i.Size; RawSize = $i.RawSize
        Created = $(if ($null -ne $i.Created) { ([datetime]$i.Created).ToString('yyyy-MM-dd HH:mm:ss') } else { '' })
        Modified = $(if ($null -ne $i.Modified) { ([datetime]$i.Modified).ToString('yyyy-MM-dd HH:mm:ss') } else { '' })
        Sections = $i.Sections; Thumbs = $i.ThumbCount; Chunks = $i.ChunkCount
        App = $(if ($i.AppName) { "$($i.AppName) $($i.AppVersion)" } else { '' })
        DbVersion = $i.DbVersion; Error = $i.Error; Path = $i.Path
    }
}

function Get-GhIndex([switch]$Refresh) {
    $root = Get-GhRoot
    if ($script:Index -and $script:IndexRoot -eq $root -and -not $Refresh) { return $script:Index }

    $files = @(Get-GhVdbFiles $root)
    $stamp = Get-GhIndexStamp $files
    $md5 = [Security.Cryptography.MD5]::Create()
    $hash = ([BitConverter]::ToString($md5.ComputeHash([Text.Encoding]::UTF8.GetBytes($root.ToLowerInvariant())))).Replace('-', '').Substring(0, 12)
    $cache = Join-Path $script:ConfigDir "index_$hash.csv"
    $stampFile = "$cache.stamp"

    if (-not $Refresh -and (Test-Path -LiteralPath $cache) -and (Test-Path -LiteralPath $stampFile) -and
        ((Get-Content -LiteralPath $stampFile -Raw).Trim() -eq $stamp)) {
        Write-Gh "  Index loaded from cache ($($files.Count) objects)." DarkGray
        $rows = Import-Csv -LiteralPath $cache -Encoding UTF8
        foreach ($r in $rows) {
            $r.Width = [int]$r.Width; $r.Height = [int]$r.Height; $r.Size = [long]$r.Size; $r.RawSize = [long]$r.RawSize
            $r.Thumbs = [int]$r.Thumbs; $r.Chunks = [int]$r.Chunks
        }
        $script:Index = @($rows); $script:IndexRoot = $root
        return $script:Index
    }

    Write-Gh "  Indexing $($files.Count) objects (reading headers)..." DarkGray
    $list = New-Object System.Collections.Generic.List[object]
    $n = 0; $sw = [Diagnostics.Stopwatch]::StartNew()
    foreach ($f in $files) {
        $n++
        if ($sw.ElapsedMilliseconds -gt 250) {
            Write-Progress -Activity 'Indexing Graphic Hub' -Status "$n / $($files.Count)" -PercentComplete ([int](100 * $n / [Math]::Max([double]1, [double]$files.Count)))
            $sw.Restart()
        }
        $list.Add((ConvertTo-GhRow ([GhTool.Vdb]::Inspect($f.FullName))))
    }
    Write-Progress -Activity 'Indexing Graphic Hub' -Completed
    $script:Index = $list.ToArray(); $script:IndexRoot = $root
    try {
        if (-not (Test-Path -LiteralPath $script:ConfigDir)) { New-Item -ItemType Directory -Path $script:ConfigDir -Force | Out-Null }
        $script:Index | Export-Csv -LiteralPath $cache -NoTypeInformation -Encoding UTF8
        Set-Content -LiteralPath $stampFile -Value $stamp -Encoding ASCII
    } catch { Write-GhWarn "Cache not saved: $($_.Exception.Message)" }
    return $script:Index
}

function Resolve-GhObject([string]$Id) {
    $root = Get-GhRoot
    if (-not $Id) { throw 'Missing identifier (UUID, start of a UUID, name or file path).' }
    if (Test-Path -LiteralPath $Id -PathType Leaf) { return (Resolve-Path -LiteralPath $Id).ProviderPath }
    $u = $Id.Trim('{', '}', ' ').Replace('-', '').ToUpperInvariant()
    if ($u -match '^[0-9A-F]{32}$') {
        $p = Join-Path (Join-Path $root $u.Substring(0, 1)) "$u.vdb"
        if (Test-Path -LiteralPath $p) { return $p }
        throw "Object $u not found ($p)."
    }
    if ($u -match '^[0-9A-F]{4,31}$') {
        $m = @(Get-ChildItem -LiteralPath (Join-Path $root $u.Substring(0, 1)) -Filter "$u*.vdb" -File -ErrorAction SilentlyContinue)
        if ($m.Count -eq 1) { return $m[0].FullName }
        if ($m.Count -gt 1) { throw "Ambiguous prefix: $($m.Count) objects start with $u." }
    }
    $idx = Get-GhIndex
    $m = @($idx | Where-Object { $_.Name -eq $Id })
    if ($m.Count -eq 0) { $m = @($idx | Where-Object { $_.Name -like "*$Id*" }) }
    if ($m.Count -eq 1) { return $m[0].Path }
    if ($m.Count -gt 1) {
        Write-GhWarn "$($m.Count) objects match '$Id':"
        $m | Select-Object -First 20 Uuid, Name, Kind, @{n = 'Size'; e = { Format-Size $_.Size } } | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
        throw 'Please specify the UUID.'
    }
    throw "No object matches '$Id'."
}


# ---------------------------------------------------------------------------
#  References between objects (ReferenceCollection.vdb.dat)
# ---------------------------------------------------------------------------
$script:Refs = $null; $script:RefsRoot = $null
function Get-GhRefs {
    $root = Get-GhRoot
    if ($script:Refs -and $script:RefsRoot -eq $root) { return $script:Refs }
    $tbl = @(Get-ChildItem -LiteralPath $root -File -Filter 'ReferenceCollection*.dat' -ErrorAction SilentlyContinue | Where-Object { $_.Name -notmatch 'Ext' } | Sort-Object Length -Descending)
    if (-not $tbl.Count) { return $null }
    $known = New-Object 'System.Collections.Generic.HashSet[string]'
    foreach ($f in (Get-GhVdbFiles $root)) { [void]$known.Add($f.BaseName.ToUpperInvariant()) }
    $script:Refs = [GhTool.Vdb]::ReadRefs($tbl[0].FullName, $known); $script:RefsRoot = $root
    return $script:Refs
}
function Get-GhRefList([string]$uuid, [string]$which) {
    $r = Get-GhRefs; if (-not $r) { return @() }
    $d = if ($which -eq 'uses') { $r.Uses } else { $r.UsedBy }
    $l = $null
    if ($d.TryGetValue($uuid.ToUpperInvariant(), [ref]$l)) { return @($l) }
    return @()
}
function Get-GhObjectLabel([string]$uuid) {
    $p = Join-Path (Join-Path (Get-GhRoot) $uuid.Substring(0, 1)) "$uuid.vdb"
    if (-not (Test-Path -LiteralPath $p)) { return [pscustomobject]@{ Uuid = $uuid; Name = '(missing)'; Kind = '?'; Path = $null } }
    $i = [GhTool.Vdb]::Inspect($p)
    return [pscustomobject]@{ Uuid = $uuid; Name = $i.Name; Kind = $i.Kind; Path = $p }
}

# ---------------------------------------------------------------------------
#  Commands
# ---------------------------------------------------------------------------
function Invoke-GhSet($a) {
    $name = if ($a.Pos.Count -gt 0) { $a.Pos[0] } else { 'VizGHData' }
    $r = Resolve-GhRoot $name
    if (-not $r) {
        if (Test-Path -LiteralPath $name -PathType Container) {
            Write-GhWarn "'$name' exists but does not look like a Graphic Hub data folder (no VizDbTables and no 0-F folders)."
            if (-not $a.Opt.force) { Write-Gh '  Add -Force to use it anyway.'; return }
            $r = (Resolve-Path -LiteralPath $name).ProviderPath
        } else { Write-GhErr "Folder not found: $name"; return }
    }
    $script:GhRoot = $r; $script:Index = $null
    Save-GhConfig
    Write-GhOk "Graphic Hub : $r"
}

function Invoke-GhStatus {
    $root = Get-GhRoot
    Write-GhTitle 'Current Graphic Hub'
    Write-Gh "  Folder: $root" White
    $b = @(Get-ChildItem -LiteralPath $root -Directory | Where-Object { $_.Name -cmatch '^[0-9A-F]$' })
    Write-Gh "  Object buckets (0-F): $($b.Count)"
    if ($script:Index -and $script:IndexRoot -eq $root) { Write-Gh "  Index in memory: $($script:Index.Count) objects" }
    else { Write-Gh '  Index: not loaded (gh scan)' }
}

function Invoke-GhAnalyse($a) {
    $root = Get-GhRoot
    Write-GhTitle "Analysis of $root"
    $files = @(Get-ChildItem -LiteralPath $root -Recurse -File -Force -ErrorAction SilentlyContinue)
    $total = [long]0; foreach ($f in $files) { $total += $f.Length }
    Write-Gh ("  {0:N0} files, {1}" -f $files.Count, (Format-Size $total)) White
    try {
        $drv = New-Object IO.DriveInfo ([IO.Path]::GetPathRoot($root))
        Write-Gh ("  Disk {0}: {1} free of {2}" -f $drv.Name, (Format-Size $drv.AvailableFreeSpace), (Format-Size $drv.TotalSize))
        if ($drv.AvailableFreeSpace -lt $total * 0.2) { Write-GhWarn 'Free space is less than 20% of the Graphic Hub size.' }
    } catch { }

    $tagged = foreach ($f in $files) { $rel = Get-RelPath $root $f.FullName; [pscustomobject]@{ F = $f; Rel = $rel; Cat = Get-GhCategory $rel $root } }
    Write-GhTitle 'Breakdown'
    $tagged | Group-Object Cat | ForEach-Object {
        $s = [long]0; foreach ($x in $_.Group) { $s += $x.F.Length }
        [pscustomobject]@{ Category = $_.Name; Files = $_.Count; Size = Format-Size $s; '%' = '{0:N1}' -f (100.0 * $s / [Math]::Max([double]1, [double]$total)); _s = $s }
    } | Sort-Object _s -Descending | Select-Object Category, Files, Size, '%' | Format-Table -AutoSize | Out-String -Width 300 | Write-Host

    # Objects
    $obj = @($tagged | Where-Object { $_.Cat -eq 'Objects (.vdb)' })
    Write-GhTitle 'Objects (.vdb)'
    if ($obj.Count) {
        $sizes = @($obj | ForEach-Object { $_.F.Length } | Sort-Object)
        Write-Gh ("  {0:N0} objects; median size {1}, max {2}" -f $obj.Count, (Format-Size $sizes[[int]($sizes.Count / 2)]), (Format-Size $sizes[-1]))
        $byB = $obj | Group-Object { ($_.Rel -split '[\\/]')[0] }
        $min = ($byB | Measure-Object Count -Minimum).Minimum; $max = ($byB | Measure-Object Count -Maximum).Maximum
        Write-Gh "  Objects per bucket: $min to $max"
        $bad = @($obj | Where-Object { $_.F.Name -notmatch '^[0-9A-Fa-f]{32}\.vdb$' -or $_.F.Name.Substring(0, 1).ToUpper() -ne ($_.Rel -split '[\\/]')[0] })
        if ($bad.Count) { Write-GhWarn "$($bad.Count) file(s) badly named or in the wrong bucket:"; $bad | Select-Object -First 10 | ForEach-Object { Write-Gh "      $($_.Rel)" Yellow } }
        else { Write-GhOk 'Object names and buckets are consistent' }
        $empty = @($obj | Where-Object { $_.F.Length -eq 0 })
        if ($empty.Count) { Write-GhWarn "$($empty.Count) zero-size object(s)" }
    } else { Write-GhWarn 'No .vdb object found.' }

    # Tables
    Write-GhTitle 'Tables (.dat / .idx / .idx.fid)'
    $dat = @($tagged | Where-Object { $_.F.Name -match '\.dat$' })
    $orphans = @($dat | Where-Object { -not (Test-Path -LiteralPath ($_.F.FullName -replace '\.dat$', '.idx')) })
    Write-Gh "  $($dat.Count) data tables"
    if ($orphans.Count) { Write-GhWarn "$($orphans.Count) .dat without .idx: $((@($orphans | Select-Object -First 5 | ForEach-Object { $_.Rel })) -join ', ')" }
    else { Write-GhOk 'Every .dat has its .idx' }
    $seg = @($dat | Where-Object { $_.F.Length -ge 1610612736 - 1MB })
    if ($seg.Count) { Write-Gh "  $($seg.Count) segment(s) reached the ~1.5 GB limit (normal _N splitting)" DarkGray }

    # Logs
    $logs = @($tagged | Where-Object { $_.Cat -like 'Logs*' } | ForEach-Object { $_.F } | Sort-Object Name)
    Write-GhTitle 'Logs'
    if ($logs.Count) {
        $ls = [long]0; foreach ($l in $logs) { $ls += $l.Length }
        Write-Gh "  $($logs.Count) files, $(Format-Size $ls), from $($logs[0].BaseName) to $($logs[-1].BaseName)"
    } else { Write-Gh '  No logs.' }

    # RocksDB
    Write-GhTitle 'RocksDB databases'
    Get-ChildItem -LiteralPath $root -Directory | Where-Object { Test-Path -LiteralPath (Join-Path $_.FullName 'CURRENT') } | ForEach-Object {
        $fs = @(Get-ChildItem -LiteralPath $_.FullName -File -ErrorAction SilentlyContinue)
        $sst = @($fs | Where-Object { $_.Extension -eq '.sst' }).Count
        $blob = @($fs | Where-Object { $_.Extension -eq '.blob' }).Count
        $sz = [long]0; foreach ($x in $fs) { $sz += $x.Length }
        $state = if ($sst -eq 0 -and $blob -eq 0) { 'empty' } else { "$sst .sst, $blob .blob" }
        [pscustomobject]@{ Database = $_.Name; Files = $fs.Count; Size = Format-Size $sz; State = $state }
    } | Format-Table -AutoSize | Out-String -Width 300 | Write-Host

    if ($a.Opt.deep) { Invoke-GhDeep } else { Write-Gh '  Tip: gh analyse -Deep reads the header of every object (types, dates, versions).' DarkGray }
}

function Invoke-GhDeep {
    $idx = @(Get-GhIndex)
    Write-GhTitle 'Detailed object analysis'
    Write-Gh '  By type:' White
    $idx | Group-Object Kind | Sort-Object Count -Descending | ForEach-Object {
        $s = [long]0; foreach ($x in $_.Group) { $s += $x.Size }
        Write-Gh ("    {0,-14} {1,8:N0}  {2,10}" -f $_.Name, $_.Count, (Format-Size $s))
    }
    Write-Gh '  Section signatures (internal structure):' White
    $idx | Group-Object Sections | Sort-Object Count -Descending | Select-Object -First 10 | ForEach-Object {
        $n = if ($_.Name) { $_.Name } else { '(none)' }
        Write-Gh ("    {0,8:N0}  {1}" -f $_.Count, $n)
    }
    $img = @($idx | Where-Object { $_.Kind -eq 'Image' })
    if ($img.Count) {
        Write-Gh '  Images by pixel format:' White
        $img | Group-Object PixelFormat | Sort-Object Count -Descending | ForEach-Object { Write-Gh ("    {0,-16} {1,8:N0}" -f $_.Name, $_.Count) }
        $big = $img | Sort-Object { $_.Width * $_.Height } -Descending | Select-Object -First 1
        Write-Gh ("  Largest image: {0} ({1}×{2})" -f $big.Name, $big.Width, $big.Height)
    }
    Write-Gh '  By creation year:' White
    $idx | Where-Object { $_.Created } | Group-Object { $_.Created.Substring(0, 4) } | Sort-Object Name | ForEach-Object {
        $bar = '#' * [Math]::Max(1, [int](40 * $_.Count / [Math]::Max([double]1, [double]$idx.Count)))
        Write-Gh ("    {0}  {1,7:N0}  {2}" -f $_.Name, $_.Count, $bar)
    }
    Write-Gh '  By Viz version (at creation):' White
    $idx | Group-Object App | Sort-Object Count -Descending | Select-Object -First 10 | ForEach-Object {
        $n = if ($_.Name) { $_.Name } else { '(unknown)' }
        Write-Gh ("    {0,-24} {1,8:N0}" -f $n, $_.Count)
    }
    Write-Gh '  10 largest objects:' White
    $idx | Sort-Object Size -Descending | Select-Object -First 10 |
        Select-Object Uuid, Name, Kind, @{n = 'Size'; e = { Format-Size $_.Size } }, Created | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
    $err = @($idx | Where-Object { $_.Kind -in 'Error', 'Unknown' })
    if ($err.Count) { Write-GhWarn "$($err.Count) unreadable object(s) or unknown structure (gh browse -Kind Unknown)" }
    else { Write-GhOk 'All headers were read' }
}

function Format-GhLine($r) {
    $dim = if ($r.Kind -eq 'Image') { "$($r.Width)×$($r.Height) $($r.PixelFormat)" } elseif ($r.Kind -in 'Scene', 'Material') { '' } else { $r.Sections }
    $date = if ($r.Created) { $r.Created.Substring(0, 10) } else { '' }
    $nm = if ($r.Name) { $r.Name } else { '(no name)' }
    return ('{0}  [{1}]  {2}  {3}  {4}' -f $nm, $r.Uuid.Substring(0, 8), $dim, (Format-Size $r.Size), $date)
}

function Get-GhFiltered($a) {
    $idx = @(Get-GhIndex)
    if ($a.Opt.kind) { $idx = @($idx | Where-Object { $_.Kind -like $a.Opt.kind }) }
    if ($a.Opt.name) { $p = $a.Opt.name; if ($p -notmatch '[\*\?]') { $p = "*$p*" }; $idx = @($idx | Where-Object { $_.Name -like $p }) }
    if ($a.Opt.bucket) { $idx = @($idx | Where-Object { $_.Bucket -eq $a.Opt.bucket.ToUpper() }) }
    if ($a.Opt.year) { $idx = @($idx | Where-Object { $_.Created -like "$($a.Opt.year)*" }) }
    return , $idx
}

function Invoke-GhBrowse($a) {
    $root = Get-GhRoot
    $T = [char]0x251C + [char]0x2500 + ' '; $L = [char]0x2514 + [char]0x2500 + ' '; $V = [char]0x2502 + '  '

    if ($a.Opt.physical) {
        Write-GhTitle "Physical tree: $root"
        $dirs = @(Get-ChildItem -LiteralPath $root -Directory | Sort-Object Name)
        $rootFiles = @(Get-ChildItem -LiteralPath $root -File)
        $items = @($dirs) + @(if ($rootFiles.Count) { 'RACINE' })
        for ($i = 0; $i -lt $items.Count; $i++) {
            $last = ($i -eq $items.Count - 1); $pre = if ($last) { $L } else { $T }; $sub = if ($last) { '   ' } else { $V }
            if ($items[$i] -is [string]) { $fs = $rootFiles; $label = '(files at the root)' }
            else { $fs = @(Get-ChildItem -LiteralPath $items[$i].FullName -File -Recurse -ErrorAction SilentlyContinue); $label = $items[$i].Name }
            $s = [long]0; foreach ($f in $fs) { $s += $f.Length }
            Write-Gh ("$pre{0}  ({1:N0} files, {2})" -f $label, $fs.Count, (Format-Size $s)) White
            if ($a.Opt.all) {
                $fl = @($fs | Sort-Object Name)
                for ($j = 0; $j -lt $fl.Count; $j++) {
                    $p2 = if ($j -eq $fl.Count - 1) { $L } else { $T }
                    Write-Gh ("$sub$p2{0}  {1}" -f $fl[$j].Name, (Format-Size $fl[$j].Length))
                }
            }
        }
        if (-not $a.Opt.all) { Write-Gh '  (gh browse -Physical -All to list the files)' DarkGray }
        return
    }

    $idx = Get-GhFiltered $a
    if ($a.Opt.grid) {
        if (-not (Get-Command Out-GridView -ErrorAction SilentlyContinue)) { Write-GhErr 'Out-GridView is not available on this system.'; return }
        $sel = @($idx | Select-Object Name, Kind, Width, Height, PixelFormat, @{n = 'Size'; e = { Format-Size $_.Size } }, Created, App, Uuid |
            Out-GridView -Title "Graphic Hub - $root  (select, then OK to export)" -PassThru)
        if ($sel.Count) {
            $out = if ($a.Opt.out) { $a.Opt.out } else { Join-Path (Get-Location).ProviderPath 'GH_Export' }
            foreach ($s in $sel) { Export-GhObject (Resolve-GhObject $s.Uuid) $out $a }
        }
        return
    }

    $top = if ($a.Opt.all) { [int]::MaxValue } elseif ($a.Opt.top) { [int]$a.Opt.top } else { 15 }
    Write-GhTitle "Graphic Hub : $root"
    Write-Gh "$($idx.Count) objects" White
    $groups = @($idx | Group-Object Kind | Sort-Object Count -Descending)
    for ($g = 0; $g -lt $groups.Count; $g++) {
        $lastG = ($g -eq $groups.Count - 1); $pre = if ($lastG) { $L } else { $T }; $sub = if ($lastG) { '   ' } else { $V }
        $s = [long]0; foreach ($x in $groups[$g].Group) { $s += $x.Size }
        Write-Gh ("$pre{0}  ({1:N0}, {2})" -f $groups[$g].Name, $groups[$g].Count, (Format-Size $s)) Cyan
        $items = @($groups[$g].Group | Sort-Object Name | Select-Object -First $top)
        $more = $groups[$g].Count - $items.Count
        for ($i = 0; $i -lt $items.Count; $i++) {
            $p2 = if ($i -eq $items.Count - 1 -and $more -le 0) { $L } else { $T }
            Write-Gh ("$sub$p2" + (Format-GhLine $items[$i]))
        }
        if ($more -gt 0) { Write-Gh ("$sub$L... and {0:N0} more (-All, -Top N, -Name, -Kind, -Year, -Bucket)" -f $more) DarkGray }
    }
    Write-Gh ''
    Write-Gh '  Note: the logical tree (GH folders/projects) is stored in FolderCollection/TreeNodeCollection,' DarkGray
    Write-Gh '  whose format is not decoded yet, so objects are grouped by type. See gh folders.' DarkGray
}

function Invoke-GhFind($a) {
    $q = ($a.Pos -join ' ')
    if (-not $q) { Write-GhErr 'Usage: gh find <text>'; return }
    $idx = @(Get-GhIndex)
    $u = $q.Replace('-', '').ToUpperInvariant()
    $res = @($idx | Where-Object { $_.Name -like "*$q*" -or $_.Uuid -like "$u*" })
    if ($a.Opt.kind) { $res = @($res | Where-Object { $_.Kind -like $a.Opt.kind }) }
    Write-Gh "  $($res.Count) result(s)" White
    $res | Sort-Object Name | Select-Object -First 200 Name, Kind,
        @{n = 'Dimensions'; e = { if ($_.Kind -eq 'Image') { "$($_.Width)×$($_.Height)" } } },
        @{n = 'Size'; e = { Format-Size $_.Size } }, Created, Uuid | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
}

function Invoke-GhShow($a) {
    $path = Resolve-GhObject ($a.Pos -join ' ')
    $i = [GhTool.Vdb]::Inspect($path)
    Write-GhTitle "Object $($i.Uuid)"
    $rows = [ordered]@{
        'Name' = $i.Name
        'Name (data)' = $i.Name2
        'Type' = $i.Kind
        'File' = $i.Path
        'File size' = Format-Size $i.Size
        'Uncompressed size' = $(if ($i.RawSize) { Format-Size $i.RawSize } else { '' })
        'Created (UTC)' = $(if ($null -ne $i.Created) { ([datetime]$i.Created).ToString('yyyy-MM-dd HH:mm:ss') })
        'Modified (UTC)' = $(if ($null -ne $i.Modified) { ([datetime]$i.Modified).ToString('yyyy-MM-dd HH:mm:ss') })
        'Sections' = $i.Sections
        'Thumbnails' = (($i.Thumbs | ForEach-Object { "$(if ($_.Name) { "$($_.Name) " })$($_.Width)×$($_.Height) JPEG ($($_.Length) B)" }) -join '; ')
        'zlib chunks' = $i.ChunkCount
        'Pixel source' = $(if ($i.PixelSection) { "section $($i.PixelSection)" + $(if ($i.PreviewSize) { " (Data holds a $($i.PreviewSize) preview)" } else { '' }) } else { '' })
        'Mipmap levels' = $(if ($i.MipLevels) { "$($i.MipLevels) (DXT1/BC1)" } else { '' })
        'Image' = $(if ($i.Kind -eq 'Image') { "$($i.Width)×$($i.Height), $($i.PixelFormat) (GL 0x$('{0:X4}' -f $i.GlFormat)), $($i.Channels) channels, $(Format-Size $i.PixelLength) of pixels" } else { '' })
        'Application' = $(if ($i.AppName) { "$($i.AppName) $($i.AppVersion)" } else { '' })
        'DB engine' = $i.DbVersion
        'System' = $(if ($i.SysName) { "$($i.SysName) $($i.SysVersion)" } else { '' })
        'Error' = $i.Error
    }
    foreach ($k in $rows.Keys) { if ("$($rows[$k])" -ne '') { Write-Gh ("  {0,-20} {1}" -f $k, $rows[$k]) } }
    if ($i.TypeCode) { Write-Gh ("  {0,-20} 0x{1:X4}" -f 'Object type code', $i.TypeCode) }
    $uses = @(Get-GhRefList $i.Uuid 'uses'); $usedBy = @(Get-GhRefList $i.Uuid 'usedby')
    if ($uses.Count) { Write-Gh ''; Write-Gh "  Uses ($($uses.Count)):" White; foreach ($u in $uses) { $o = Get-GhObjectLabel $u; Write-Gh ("    {0,-9} {1}  [{2}]" -f $o.Kind, $o.Name, $u.Substring(0, 8)) } }
    if ($usedBy.Count) { Write-Gh ''; Write-Gh "  Used by ($($usedBy.Count)):" White; foreach ($u in $usedBy) { $o = Get-GhObjectLabel $u; Write-Gh ("    {0,-9} {1}  [{2}]" -f $o.Kind, $o.Name, $u.Substring(0, 8)) } }
    if ($i.Kind -ne 'Image' -and $i.SectionList) {
        $sc = [GhTool.Vdb]::Scene($i)
        $max = if ($a.Opt.all) { [int]::MaxValue } else { 40 }
        if ($sc.Containers.Count) {
            Write-Gh ''
            Write-Gh "  Containers ($($sc.Containers.Count), in file order):" White
            $sc.Containers | Select-Object -First $max | ForEach-Object { Write-Gh "    $_" }
            if ($sc.Containers.Count -gt $max) { Write-Gh "    ... ($($sc.Containers.Count - $max) more, use -All)" DarkGray }
        }
        if ($sc.Plugins.Count) { Write-Gh ''; Write-Gh '  Plugins:' White; Write-Gh ("    " + ($sc.Plugins -join ', ')) }
        if ($sc.Directors.Count) { Write-Gh ''; Write-Gh '  Directors:' White; Write-Gh ("    " + ($sc.Directors -join ', ')) }
        if ($sc.ControlFields.Count) { Write-Gh ''; Write-Gh '  Control object fields (name (label)):' White; $sc.ControlFields | ForEach-Object { Write-Gh "    $_" } }
        if ($i.Kind -eq 'Scene') { Write-Gh ''; Write-Gh '  (Names are read from the scene data; the scene format is not documented, so the hierarchy is not shown.)' DarkGray }
    }
}

function Assert-GhOutside([string]$out) {
    $root = Get-GhRoot
    $full = [IO.Path]::GetFullPath($out)
    if ($full.StartsWith($root, [StringComparison]::OrdinalIgnoreCase)) { throw 'Export refused: the output folder is inside the Graphic Hub.' }
    if (-not (Test-Path -LiteralPath $full)) { New-Item -ItemType Directory -Path $full -Force | Out-Null }
    return $full
}

function Get-SafeName([string]$n) {
    if (-not $n) { return 'no_name' }
    foreach ($c in [IO.Path]::GetInvalidFileNameChars()) { $n = $n.Replace($c, '_') }
    return $n.Trim()
}

function Export-GhObject([string]$path, [string]$out, $a) {
    $i = [GhTool.Vdb]::Inspect($path)
    $base = Join-Path $out ("{0}_{1}" -f (Get-SafeName $i.Name), $i.Uuid.Substring(0, 8))
    $done = New-Object System.Collections.Generic.List[string]
    if ($i.Error) { Write-GhErr "$($i.Uuid) : $($i.Error)"; return $false }
    $payload = $null
    if ($i.ChunkCount -gt 0) { $payload = [GhTool.Vdb]::ReadPayload($i) }

    if ($i.Kind -eq 'Image' -and $payload -and $i.Channels -ge 1 -and $i.Channels -le 4) {
        [GhTool.Vdb]::WriteImagePng($i, $payload, "$base.png", -not $a.Opt.noflip)
        $done.Add("$base.png")
    } elseif ($payload) {
        [IO.File]::WriteAllBytes("$base.data.bin", $payload); $done.Add("$base.data.bin")
    }
    if ($a.Opt.raw -and $payload -and $i.Kind -eq 'Image') { [IO.File]::WriteAllBytes("$base.data.bin", $payload); $done.Add("$base.data.bin") }
    if ($a.Opt.thumbs -or -not $payload -or $i.Kind -ne 'Image') {
        for ($t = 0; $t -lt $i.ThumbCount; $t++) {
            $tp = "$base.thumb$t.jpg"; [IO.File]::WriteAllBytes($tp, [GhTool.Vdb]::ReadThumb($i, $t)); $done.Add($tp)
        }
    }
    $meta = ConvertTo-GhRow $i
    $meta | ConvertTo-Json | Set-Content -LiteralPath "$base.json" -Encoding UTF8
    $done.Add("$base.json")
    if ($done.Count -le 1) { Remove-Item -LiteralPath "$base.json" -ErrorAction SilentlyContinue; Write-GhWarn "$($i.Uuid): nothing to export (metadata only)."; return $false }
    Write-GhOk ("{0} [{1}] -> {2}" -f $i.Name, $i.Uuid.Substring(0, 8), (($done | ForEach-Object { Split-Path $_ -Leaf }) -join ', '))
    return $true
}

function Invoke-GhExport($a) {
    $out = Assert-GhOutside $(if ($a.Opt.out) { $a.Opt.out } else { Join-Path (Get-Location).ProviderPath 'GH_Export' })
    if ($a.Opt.all) {
        $list = Get-GhFiltered $a
        if (-not $a.Opt.kind -and -not $a.Opt.name) { $list = @($list | Where-Object { $_.Kind -eq 'Image' }); Write-Gh '  (images only; -Kind * to export everything)' DarkGray }
        if ($list.Count -gt 100 -and -not $a.Opt.force) {
            $ans = Read-Host "  Export $($list.Count) objects to $out? (y/N)"
            if ($ans -notmatch '^[yY]') { Write-Gh '  Cancelled.'; return }
        }
        $ok = 0; $n = 0
        foreach ($r in $list) {
            $n++; Write-Progress -Activity 'Export' -Status "$n / $($list.Count)" -PercentComplete ([int](100 * $n / $list.Count))
            try { if (Export-GhObject $r.Path $out $a) { $ok++ } } catch { Write-GhErr "$($r.Uuid) : $($_.Exception.Message)" }
        }
        Write-Progress -Activity 'Export' -Completed
        Write-Gh "  $ok / $($list.Count) objects exported to $out" White
        return
    }
    if ($a.Pos.Count -eq 0) { Write-GhErr 'Usage: gh export <uuid|name> [-Out folder] [-Thumbs] [-Raw]   or   gh export -All [-Kind Image]'; return }
    foreach ($id in $a.Pos) {
        try { [void](Export-GhObject (Resolve-GhObject $id) $out $a) } catch { Write-GhErr $_.Exception.Message }
    }
    Write-Gh "  Export folder: $out" DarkGray
}

function Get-GhLogFiles {
    $d = Join-Path (Get-GhRoot) 'LogFiles'
    if (-not (Test-Path -LiteralPath $d)) { return @() }
    return @(Get-ChildItem -LiteralPath $d -File | Sort-Object Name)
}

function Get-GhLogFile($a) {
    $logs = Get-GhLogFiles
    if (-not $logs.Count) { throw 'No log files in LogFiles.' }
    if ($a.Opt.file) {
        $m = @($logs | Where-Object { $_.Name -like "*$($a.Opt.file)*" })
        if ($m.Count -ne 1) { throw "Log '$($a.Opt.file)': $($m.Count) match(es)." }
        return $m[0]
    }
    return $logs[-1]
}

function Read-GhTail([string]$path, [long]$bytes) {
    $fs = [GhTool.Vdb]::OpenRead($path)
    try {
        $len = [long][Math]::Min([double]$fs.Length, [double]$bytes)
        $buf = [GhTool.Vdb]::ReadAt($fs, $fs.Length - $len, [int]$len)
        $txt = [Text.Encoding]::GetEncoding(28591).GetString($buf)
        $lines = $txt -split "`r?`n"
        if ($len -lt $fs.Length -and $lines.Count -gt 1) { $lines = $lines[1..($lines.Count - 1)] }
        return , $lines
    } finally { $fs.Dispose() }
}

function Invoke-GhLogs($a) {
    if ($a.Opt.grep) {
        $files = if ($a.Opt.all) { Get-GhLogFiles } else { @(Get-GhLogFile $a) }
        foreach ($f in $files) {
            $hits = @(Select-String -LiteralPath $f.FullName -Pattern $a.Opt.grep -Encoding Default -ErrorAction SilentlyContinue)
            if ($hits.Count) {
                Write-Gh "  $($f.Name): $($hits.Count) line(s)" Cyan
                $max = if ($a.Opt.top) { [int]$a.Opt.top } else { 50 }
                $hits | Select-Object -Last $max | ForEach-Object { Write-Gh ("    {0,8}: {1}" -f $_.LineNumber, $_.Line) }
            }
        }
        return
    }
    if ($a.Opt.tail -or $a.Opt.file) {
        $f = Get-GhLogFile $a
        $n = if ($a.Opt.tail -and $a.Opt.tail -ne $true) { [int]$a.Opt.tail } else { 40 }
        Write-GhTitle "$($f.Name) (last $n lines)"
        $lines = Read-GhTail $f.FullName ([long]($n * 600 + 4096))
        $lines | Where-Object { $_ -ne '' } | Select-Object -Last $n | ForEach-Object {
            $c = if ($_ -match 'error|erreur|fail|exception|\[(?!OK\])[A-Z]+\]\s+TC\(') { 'Yellow' } else { 'Gray' }
            Write-Gh "  $_" $c
        }
        return
    }
    Write-GhTitle 'Logs (LogFiles)'
    Get-GhLogFiles | Select-Object Name, @{n = 'Size'; e = { Format-Size $_.Length } } | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
    Write-Gh '  gh logs -Tail 50 [-File name]   |   gh logs -Grep "pattern" [-All]' DarkGray
}

function Invoke-GhHealth($a) {
    $f = Get-GhLogFile $a
    $n = if ($a.Opt.last) { [int]$a.Opt.last } else { 20 }
    $lines = Read-GhTail $f.FullName ([long]8MB)
    $rx = '^(?<t>.*?\d{1,2}:\d{2}:\d{2}(?:\.\d+)?)\s*:.*?\[(?<st>[A-Za-z]+)\]\s*TC\((?<tc>\d+)\)\s*TCC\((?<tcc>\d+)\)\s*HQL\((?<hql>[\d/]+)\)\s*TS\((?<ts>[\d/]+)\)\s*TF\((?<tf>[\d/]+)\)'
    $rows = foreach ($l in $lines) {
        $m = [regex]::Match($l, $rx)
        if ($m.Success) {
            $nz = { param($s) @($s -split '/' | Where-Object { [int]$_ -ne 0 }).Count -gt 0 }
            [pscustomobject]@{
                Time = $m.Groups['t'].Value; State = $m.Groups['st'].Value
                TC = [int]$m.Groups['tc'].Value; TCC = [int]$m.Groups['tcc'].Value; HQL = $m.Groups['hql'].Value
                TS = $m.Groups['ts'].Value; TF = $m.Groups['tf'].Value
                Alert = ($m.Groups['st'].Value -ne 'OK') -or ([int]$m.Groups['tcc'].Value -ne 0) -or (& $nz $m.Groups['ts'].Value) -or (& $nz $m.Groups['tf'].Value)
            }
        }
    }
    $rows = @($rows)
    Write-GhTitle "Status lines in $($f.Name) (end of file)"
    if (-not $rows.Count) { Write-GhWarn 'No status line recognised (expected format: ... [OK] TC(n) TCC(n) HQL(...) TS(...) TF(...)).'; return }
    $rows | Select-Object -Last $n | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
    $al = @($rows | Where-Object { $_.Alert })
    if ($al.Count) { Write-GhWarn "$($al.Count) of $($rows.Count) line(s) with a non-OK state or non-zero TCC/TS/TF counters (last: $($al[-1].Time))" }
    else { Write-GhOk "$($rows.Count) status lines read: all OK, TCC/TS/TF at zero" }
    Write-Gh '  Exact meaning of the counters is undocumented: TS/TF/TCC at zero and [OK] = the normal state observed.' DarkGray
}

function Invoke-GhTables {
    $root = Get-GhRoot
    Write-GhTitle 'Root tables (HQL catalogue)'
    Get-ChildItem -LiteralPath $root -File | Where-Object { $_.Extension -in '.dat', '.vdb' } | Sort-Object Length -Descending |
        Select-Object Name, @{n = 'Size'; e = { Format-Size $_.Length } } | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
    $vt = Join-Path $root 'VizDbTables'
    if (Test-Path -LiteralPath $vt) {
        Write-GhTitle 'VizDbTables (grouped by table)'
        Get-ChildItem -LiteralPath $vt -File -Filter '*.dat' | Group-Object { $_.BaseName -replace '_\d+$', '' } | ForEach-Object {
            $s = [long]0; foreach ($x in $_.Group) { $s += $x.Length }
            [pscustomobject]@{ Table = $_.Name; Segments = $_.Count; Size = Format-Size $s; _s = $s }
        } | Sort-Object _s -Descending | Select-Object Table, Segments, Size | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
    }
}

function Invoke-GhFolders($a) {
    $root = Get-GhRoot
    $min = if ($a.Opt.min) { [int]$a.Opt.min } else { 3 }
    $file = if ($a.Pos.Count) { $a.Pos[0] } else { 'FolderCollection.dat' }
    $p = if (Test-Path -LiteralPath $file) { $file } else { Join-Path $root $file }
    if (-not (Test-Path -LiteralPath $p)) { Write-GhErr "File not found: $p"; return }
    Write-GhTitle "Readable strings in $(Split-Path $p -Leaf) (EXPERIMENTAL)"
    Write-Gh '  Undocumented format: raw extraction of ASCII/UTF-16 text, without the hierarchy.' DarkGray
    $s = [GhTool.Vdb]::Strings($p, $min) | Where-Object { $_ -match '[A-Za-z]' } | Sort-Object -Unique
    $s | Select-Object -First $(if ($a.Opt.all) { [int]::MaxValue } else { 200 }) | ForEach-Object { Write-Gh "  $_" }
    Write-Gh "  $(@($s).Count) unique string(s)" White
}

function Invoke-GhHex($a) {
    $path = Resolve-GhObject ($a.Pos -join ' ')
    $off = if ($a.Opt.offset) { [long]$a.Opt.offset } else { 0 }
    $len = if ($a.Opt.length) { [int]$a.Opt.length } else { 256 }
    $fs = [GhTool.Vdb]::OpenRead($path)
    try { $b = [GhTool.Vdb]::ReadAt($fs, $off, $len) } finally { $fs.Dispose() }
    Write-GhTitle "$(Split-Path $path -Leaf) @ $off"
    for ($i = 0; $i -lt $b.Length; $i += 16) {
        $n = [Math]::Min(16, $b.Length - $i)
        $hex = (($b[$i..($i + $n - 1)] | ForEach-Object { '{0:x2}' -f $_ }) -join ' ')
        $asc = -join ($b[$i..($i + $n - 1)] | ForEach-Object { if ($_ -ge 32 -and $_ -lt 127) { [char]$_ } else { '.' } })
        Write-Gh ('  {0:x8}  {1,-47}  {2}' -f ($off + $i), $hex, $asc)
    }
}

function Invoke-GhPreview($a) {
    $path = Resolve-GhObject ($a.Pos -join ' ')
    $i = [GhTool.Vdb]::Inspect($path)
    if ($i.Kind -ne 'Image' -or $i.Channels -lt 1) {
        Write-GhWarn "No terminal preview for this object type ($($i.Kind)). Use gh gallery -Kind * (embedded JPEG thumbnails)."
        return
    }
    $cols = if ($a.Opt.width) { [int]$a.Opt.width } else {
        $ww = 80; try { if ([Console]::WindowWidth -gt 10) { $ww = [Console]::WindowWidth } } catch { }
        [Math]::Min(100, $ww - 4)
    }
    [void][GhTool.Vdb]::EnableVt()
    $payload = [GhTool.Vdb]::ReadPayload($i)
    $txt = [GhTool.Vdb]::Ansi($i, $payload, -not $a.Opt.noflip, $cols)
    Write-Host ''
    [Console]::Out.Write($txt)
    Write-Gh ("  {0}  [{1}]  {2}×{3} {4}  {5}" -f $i.Name, $i.Uuid, $i.Width, $i.Height, $i.PixelFormat, (Format-Size $i.Size)) White
    Write-Gh '  (approximate colours; if you see codes like [38;2;..., use Windows Terminal or gh gallery)' DarkGray
}

function Invoke-GhGallery($a) {
    $root = Get-GhRoot
    $md5 = [Security.Cryptography.MD5]::Create()
    $hash = ([BitConverter]::ToString($md5.ComputeHash([Text.Encoding]::UTF8.GetBytes($root.ToLowerInvariant())))).Replace('-', '').Substring(0, 12)
    $outDir = if ($a.Opt.out) { $a.Opt.out } else { Join-Path ([IO.Path]::GetTempPath()) "GHTool\gallery_$hash" }
    $outDir = Assert-GhOutside $outDir
    $thumbDir = Join-Path $outDir 'thumbs'; $fullDir = Join-Path $outDir 'full'
    if (-not (Test-Path -LiteralPath $thumbDir)) { New-Item -ItemType Directory -Path $thumbDir -Force | Out-Null }
    if ($a.Opt.full -and -not (Test-Path -LiteralPath $fullDir)) { New-Item -ItemType Directory -Path $fullDir -Force | Out-Null }
    $size = if ($a.Opt.size) { [int]$a.Opt.size } else { 256 }

    $list = Get-GhFiltered $a
    if (-not $a.Opt.kind) { $list = @($list | Where-Object { $_.Kind -eq 'Image' }) }
    if (-not $list.Count) { Write-GhWarn 'No objects to show (filters too restrictive?).'; return }
    Write-Gh "  Preparing the gallery: $($list.Count) objects -> $outDir" DarkGray

    $data = New-Object System.Collections.Generic.List[object]
    $made = 0; $reused = 0; $errs = 0; $n = 0
    $sw = [Diagnostics.Stopwatch]::StartNew()
    foreach ($r in $list) {
        $n++
        if ($sw.ElapsedMilliseconds -gt 300) {
            Write-Progress -Activity 'Graphic Hub gallery' -Status "$n / $($list.Count)  ($($r.Name))" -PercentComplete ([int](100 * $n / [double]$list.Count))
            $sw.Restart()
        }
        $thumbRel = $null; $fullRel = $null; $err = $null
        try {
            $png = Join-Path $thumbDir "$($r.Uuid)_$size.png"
            $jpg = Join-Path $thumbDir "$($r.Uuid).jpg"
            $full = Join-Path $fullDir "$($r.Uuid).png"
            $useFast = $a.Opt.fast -or $r.Kind -ne 'Image'
            $needFull = $a.Opt.full -and $r.Kind -eq 'Image' -and ($a.Opt.refresh -or -not (Test-Path -LiteralPath $full))
            if (-not $useFast -and -not $needFull -and -not (Test-Path -LiteralPath $png)) {
                # Newer files carry a large JPEG preview (IconLarge): use it when it is big enough
                $ljpg = Join-Path $thumbDir "$($r.Uuid)_e$size.jpg"
                if (-not $a.Opt.refresh -and (Test-Path -LiteralPath $ljpg)) { $reused++; $useFast = $true }
                else {
                    $i = [GhTool.Vdb]::Inspect($r.Path)
                    $best = -1; for ($t = 0; $t -lt $i.ThumbCount; $t++) { if ($best -lt 0 -or $i.Thumbs[$t].Width -gt $i.Thumbs[$best].Width) { $best = $t } }
                    if ($best -ge 0 -and [Math]::Max($i.Thumbs[$best].Width, $i.Thumbs[$best].Height) -ge $size) {
                        [IO.File]::WriteAllBytes($ljpg, [GhTool.Vdb]::ReadThumb($i, $best)); $made++; $useFast = $true
                    }
                }
                if ($useFast) { $thumbRel = "thumbs/$($r.Uuid)_e$size.jpg" }
            }
            if ($useFast) {
                if ($thumbRel) { }
                elseif ([int]$r.Thumbs -gt 0) {
                    if ($a.Opt.refresh -or -not (Test-Path -LiteralPath $jpg)) {
                        $i = [GhTool.Vdb]::Inspect($r.Path)
                        $best = 0; for ($t = 1; $t -lt $i.ThumbCount; $t++) { if ($i.Thumbs[$t].Width -gt $i.Thumbs[$best].Width) { $best = $t } }
                        [IO.File]::WriteAllBytes($jpg, [GhTool.Vdb]::ReadThumb($i, $best)); $made++
                    } else { $reused++ }
                    $thumbRel = "thumbs/$($r.Uuid).jpg"
                }
            } else {
                if ($a.Opt.refresh -or -not (Test-Path -LiteralPath $png) -or $needFull) {
                    $i = [GhTool.Vdb]::Inspect($r.Path)
                    $payload = [GhTool.Vdb]::ReadPayload($i)
                    if ($a.Opt.refresh -or -not (Test-Path -LiteralPath $png)) { [GhTool.Vdb]::WriteThumbPng($i, $payload, $png, -not $a.Opt.noflip, $size); $made++ } else { $reused++ }
                    if ($needFull) { [GhTool.Vdb]::WriteImagePng($i, $payload, $full, -not $a.Opt.noflip) }
                    $payload = $null
                } else { $reused++ }
                $thumbRel = "thumbs/$($r.Uuid)_$size.png"
            }
            if ($a.Opt.full -and (Test-Path -LiteralPath $full)) { $fullRel = "full/$($r.Uuid).png" }
        } catch { $errs++; $err = $_.Exception.Message }
        $data.Add([ordered]@{
            u = $r.Uuid; n = "$($r.Name)"; k = $r.Kind; w = [int]$r.Width; h = [int]$r.Height; f = "$($r.PixelFormat)"
            s = [long]$r.Size; d = "$($r.Created)"; a = "$($r.App)"; t = $thumbRel; p = $fullRel; e = $err
        })
    }
    Write-Progress -Activity 'Graphic Hub gallery' -Completed

    $json = ConvertTo-Json -InputObject $data.ToArray() -Compress -Depth 3
    $json = $json.Replace('</', '<\/')
    $html = $script:GhGalleryTemplate.Replace('__TITLE__', [Net.WebUtility]::HtmlEncode($root)).Replace('__DATA__', $json).Replace('__GEN__', (Get-Date).ToString('yyyy-MM-dd HH:mm'))
    $index = Join-Path $outDir 'index.html'
    [IO.File]::WriteAllText($index, $html, (New-Object Text.UTF8Encoding($false)))

    Write-GhOk "Gallery: $($list.Count) objects ($made thumbnails created, $reused reused$(if ($errs) { ", $errs error(s)" }))"
    Write-Gh "  $index" White
    if (-not $a.Opt.noopen) {
        try { Invoke-Item -LiteralPath $index } catch { Write-GhWarn "Could not open it automatically: open the file above in a browser." }
    }
}

$script:GhGalleryTemplate = @'
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Graphic Hub – gallery</title>
<style>
  :root { --bg:#121417; --panel:#1b1e23; --line:#2b3038; --text:#e6e8eb; --mute:#8b929c; --acc:#4da3ff; --tile:180px; }
  * { box-sizing:border-box; }
  body { margin:0; background:var(--bg); color:var(--text); font:14px/1.4 "Segoe UI", system-ui, sans-serif; }
  header { position:sticky; top:0; z-index:5; background:rgba(18,20,23,.96); border-bottom:1px solid var(--line); padding:10px 16px; display:flex; flex-wrap:wrap; gap:10px; align-items:center; }
  header h1 { font-size:15px; font-weight:600; margin:0 12px 0 0; white-space:nowrap; }
  header .src { color:var(--mute); font-size:12px; flex-basis:100%; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
  input, select { background:var(--panel); color:var(--text); border:1px solid var(--line); border-radius:6px; padding:6px 8px; font:inherit; }
  input[type=search] { width:260px; }
  label { color:var(--mute); font-size:12px; display:flex; align-items:center; gap:6px; }
  #count { margin-left:auto; color:var(--mute); }
  main { padding:16px; display:grid; grid-template-columns:repeat(auto-fill, minmax(var(--tile), 1fr)); gap:12px; }
  .card { background:var(--panel); border:1px solid var(--line); border-radius:8px; overflow:hidden; cursor:pointer; transition:border-color .12s; }
  .card:hover, .card:focus { border-color:var(--acc); outline:none; }
  .thumb { aspect-ratio:1; display:flex; align-items:center; justify-content:center; background:
      conic-gradient(#2a2e35 25%, #22262c 0 50%, #2a2e35 0 75%, #22262c 0) 0 0/16px 16px; }
  .thumb img { max-width:100%; max-height:100%; display:block; }
  .thumb .none { color:var(--mute); font-size:12px; padding:8px; text-align:center; }
  .meta { padding:6px 8px 8px; }
  .name { font-weight:600; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .sub { color:var(--mute); font-size:12px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  #more { grid-column:1/-1; height:40px; }
  #empty { padding:40px; color:var(--mute); text-align:center; display:none; }
  #lb { position:fixed; inset:0; background:rgba(0,0,0,.86); display:none; z-index:10; align-items:center; justify-content:center; gap:24px; padding:24px; }
  #lb.on { display:flex; }
  #lb .view { flex:1; height:100%; display:flex; align-items:center; justify-content:center; min-width:0; }
  #lb .view img { max-width:100%; max-height:100%; image-rendering:auto; background:
      conic-gradient(#2a2e35 25%, #22262c 0 50%, #2a2e35 0 75%, #22262c 0) 0 0/16px 16px; }
  #lb aside { width:340px; flex:none; background:var(--panel); border:1px solid var(--line); border-radius:8px; padding:16px; max-height:100%; overflow:auto; }
  #lb h2 { font-size:16px; margin:0 0 12px; word-break:break-word; }
  #lb table { border-collapse:collapse; width:100%; font-size:13px; table-layout:fixed; }
  #lb td { padding:4px 0; vertical-align:top; word-break:break-all; }
  #lb td:first-child { color:var(--mute); width:110px; }
  #lb code { display:block; margin-top:12px; background:#0d0f12; border:1px solid var(--line); border-radius:6px; padding:8px; font-size:12px; word-break:break-all; }
  #lb button { margin-top:8px; background:var(--acc); color:#06121f; border:0; border-radius:6px; padding:6px 10px; font-weight:600; cursor:pointer; }
  #lb .hint { color:var(--mute); font-size:12px; margin-top:12px; }
  .nav { position:absolute; top:50%; transform:translateY(-50%); font-size:32px; color:#fff; opacity:.6; cursor:pointer; user-select:none; padding:8px; }
  .nav:hover { opacity:1; } #prev { left:4px; } #next { right:372px; }
  @media (max-width:800px) { #lb { flex-direction:column; } #lb aside { width:100%; } #next { right:4px; } }
</style>
</head>
<body>
<header>
  <h1>Graphic Hub</h1>
  <input type="search" id="q" placeholder="Search a name or a UUID…" autofocus>
  <select id="kind"></select>
  <select id="year"></select>
  <select id="sort">
    <option value="name">Sort: name</option>
    <option value="date">Sort: date (newest)</option>
    <option value="size">Sort: size</option>
    <option value="px">Sort: dimensions</option>
  </select>
  <label>Size <input type="range" id="zoom" min="110" max="360" value="180"></label>
  <span id="count"></span>
  <div class="src">__TITLE__ · generated __GEN__</div>
</header>
<main id="grid"></main>
<div id="empty">No results.</div>
<div id="lb">
  <span class="nav" id="prev">‹</span>
  <div class="view"><img id="lbimg" alt=""></div>
  <aside>
    <h2 id="lbname"></h2>
    <table id="lbmeta"></table>
    <code id="lbcmd"></code>
    <button id="copy">Copy command</button>
    <div class="hint">Esc to close · ← → to navigate</div>
  </aside>
  <span class="nav" id="next">›</span>
</div>
<script type="application/json" id="data">__DATA__</script>
<script>
(function () {
  var all = JSON.parse(document.getElementById('data').textContent || '[]');
  if (!Array.isArray(all)) all = [all];
  var $ = function (id) { return document.getElementById(id); };
  var grid = $('grid'), shown = [], rendered = 0, PAGE = 300, cur = -1;

  function fmtSize(b) { var u = ['B','KB','MB','GB']; var i = 0; while (b >= 1024 && i < 3) { b /= 1024; i++; } return (i ? b.toFixed(1) : b) + ' ' + u[i]; }
  function esc(s) { return String(s == null ? '' : s).replace(/[&<>"]/g, function (c) { return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]; }); }
  function dims(o) { return o.k === 'Image' ? o.w + '×' + o.h + (o.f ? ' ' + o.f : '') : o.k; }

  function fill(sel, label, values) {
    sel.innerHTML = '<option value="">' + label + '</option>' + values.map(function (v) { return '<option>' + esc(v) + '</option>'; }).join('');
  }
  function uniq(f) { var m = {}; all.forEach(function (o) { var v = f(o); if (v) m[v] = 1; }); return Object.keys(m).sort(); }
  fill($('kind'), 'All types', uniq(function (o) { return o.k; }));
  fill($('year'), 'All years', uniq(function (o) { return (o.d || '').slice(0, 4); }).reverse());

  function apply() {
    var q = $('q').value.trim().toLowerCase(), k = $('kind').value, y = $('year').value, s = $('sort').value;
    shown = all.filter(function (o) {
      if (k && o.k !== k) return false;
      if (y && (o.d || '').slice(0, 4) !== y) return false;
      if (q && (o.n || '').toLowerCase().indexOf(q) < 0 && o.u.toLowerCase().indexOf(q.replace(/-/g, '')) !== 0) return false;
      return true;
    });
    var cmp = {
      name: function (a, b) { return (a.n || '').localeCompare(b.n || '', 'en', { sensitivity: 'base', numeric: true }); },
      date: function (a, b) { return (b.d || '').localeCompare(a.d || ''); },
      size: function (a, b) { return b.s - a.s; },
      px:   function (a, b) { return b.w * b.h - a.w * a.h; }
    }[s];
    shown.sort(cmp);
    grid.innerHTML = ''; rendered = 0;
    $('count').textContent = shown.length.toLocaleString('en-US') + ' / ' + all.length.toLocaleString('en-US') + ' objects';
    $('empty').style.display = shown.length ? 'none' : 'block';
    more();
  }

  function card(o, idx) {
    var d = document.createElement('div');
    d.className = 'card'; d.tabIndex = 0; d.dataset.i = idx;
    d.innerHTML = '<div class="thumb">' + (o.t ? '<img loading="lazy" src="' + esc(o.t) + '" alt="">' : '<div class="none">' + esc(o.e || 'no thumbnail') + '</div>') + '</div>' +
      '<div class="meta"><div class="name" title="' + esc(o.n) + '">' + esc(o.n || '(no name)') + '</div>' +
      '<div class="sub">' + esc(dims(o)) + ' · ' + fmtSize(o.s) + (o.d ? ' · ' + o.d.slice(0, 10) : '') + '</div></div>';
    return d;
  }

  function more() {
    var old = $('more'); if (old) old.remove();
    var frag = document.createDocumentFragment(), end = Math.min(shown.length, rendered + PAGE);
    for (var i = rendered; i < end; i++) frag.appendChild(card(shown[i], i));
    rendered = end; grid.appendChild(frag);
    if (rendered < shown.length) { var s = document.createElement('div'); s.id = 'more'; grid.appendChild(s); io.observe(s); }
  }
  var io = new IntersectionObserver(function (e) { if (e.some(function (x) { return x.isIntersecting; })) more(); }, { rootMargin: '800px' });

  function open(i) {
    if (i < 0 || i >= shown.length) return;
    cur = i; var o = shown[i];
    var src = o.p || o.t || ''; $('lbimg').style.display = src ? '' : 'none'; $('lbimg').src = src;
    $('lbname').textContent = o.n || '(no name)';
    var rows = [['Type', o.k], ['Dimensions', o.k === 'Image' ? o.w + ' × ' + o.h : ''], ['Format', o.f], ['Size', fmtSize(o.s)],
                ['Created (UTC)', o.d], ['Application', o.a], ['UUID', o.u], ['Preview', o.p ? 'full resolution' : (o.t ? 'thumbnail' : '')], ['Error', o.e]];
    $('lbmeta').innerHTML = rows.filter(function (r) { return r[1]; }).map(function (r) { return '<tr><td>' + r[0] + '</td><td>' + esc(r[1]) + '</td></tr>'; }).join('');
    $('lbcmd').textContent = 'gh export ' + o.u + ' -Out .\\GH_Export';
    $('lb').classList.add('on');
  }
  function close() { $('lb').classList.remove('on'); cur = -1; }

  grid.addEventListener('click', function (e) { var c = e.target.closest('.card'); if (c) open(+c.dataset.i); });
  grid.addEventListener('keydown', function (e) { if (e.key === 'Enter') { var c = e.target.closest('.card'); if (c) open(+c.dataset.i); } });
  $('lb').addEventListener('click', function (e) { if (e.target === this || e.target.classList.contains('view')) close(); });
  $('prev').onclick = function () { open(cur - 1); }; $('next').onclick = function () { open(cur + 1); };
  $('copy').onclick = function () {
    var t = $('lbcmd').textContent, b = this;
    function ok() { b.textContent = 'Copied'; setTimeout(function () { b.textContent = 'Copy command'; }, 1200); }
    if (navigator.clipboard) navigator.clipboard.writeText(t).then(ok, function () {}); else ok();
  };
  document.addEventListener('keydown', function (e) {
    if (cur < 0) return;
    if (e.key === 'Escape') close(); else if (e.key === 'ArrowLeft') open(cur - 1); else if (e.key === 'ArrowRight') open(cur + 1);
  });
  var t; $('q').addEventListener('input', function () { clearTimeout(t); t = setTimeout(apply, 150); });
  ['kind', 'year', 'sort'].forEach(function (id) { $(id).addEventListener('change', apply); });
  $('zoom').addEventListener('input', function () { document.documentElement.style.setProperty('--tile', this.value + 'px'); });
  apply();
})();
</script>
</body>
</html>
'@

# ---------------------------------------------------------------------------
#  Image replacement (writes directly into the .vdb, bypassing the GH)
# ---------------------------------------------------------------------------
$script:BackupDir = Join-Path $script:ConfigDir 'backups'
$script:StagingDir = Join-Path $script:ConfigDir 'staging'

function Read-GhImageFile([string]$path) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) { throw "Image not found: $path" }
    $full = (Resolve-Path -LiteralPath $path).ProviderPath
    $bytes = [IO.File]::ReadAllBytes($full)
    if ($bytes.Length -gt 8 -and $bytes[0] -eq 0x89 -and $bytes[1] -eq 0x50) {
        try {
            $w = 0; $h = 0
            $px = [GhTool.VdbWriter]::DecodePng($bytes, [ref]$w, [ref]$h)
            return @{ W = $w; H = $h; Rgba = $px }
        } catch { if ($_.Exception.InnerException -isnot [NotSupportedException] -and $_.Exception -isnot [NotSupportedException]) { throw } }
    }
    return (Read-GhImageViaDrawing $full)
}

# Kept separate so System.Drawing is only loaded when needed (JPG, BMP, TIFF, GIF...).
function Read-GhImageViaDrawing([string]$full) {
    try { Add-Type -AssemblyName System.Drawing -ErrorAction Stop } catch { throw "Image format not supported here (only PNG can be read without System.Drawing)." }
    $bmp = New-Object System.Drawing.Bitmap $full
    try {
        $rect = New-Object System.Drawing.Rectangle 0, 0, $bmp.Width, $bmp.Height
        $data = $bmp.LockBits($rect, [System.Drawing.Imaging.ImageLockMode]::ReadOnly, [System.Drawing.Imaging.PixelFormat]::Format32bppArgb)
        try {
            $buf = New-Object byte[] ($bmp.Width * $bmp.Height * 4)
            for ($y = 0; $y -lt $bmp.Height; $y++) {
                [Runtime.InteropServices.Marshal]::Copy([IntPtr]::Add($data.Scan0, $y * $data.Stride), $buf, $y * $bmp.Width * 4, $bmp.Width * 4)
            }
        } finally { $bmp.UnlockBits($data) }
        [GhTool.VdbWriter]::BgraToRgba($buf)
        return @{ W = $bmp.Width; H = $bmp.Height; Rgba = $buf }
    } finally { $bmp.Dispose() }
}

function ConvertFrom-GhColor([string]$hex) {
    $h = "$hex".TrimStart('#')
    if ($h -notmatch '^[0-9A-Fa-f]{6}$') { throw "Invalid colour: $hex (format RRGGBB)" }
    return @([Convert]::ToByte($h.Substring(0, 2), 16), [Convert]::ToByte($h.Substring(2, 2), 16), [Convert]::ToByte($h.Substring(4, 2), 16))
}

function Get-GhServerProcesses {
    @(Get-Process -ErrorAction SilentlyContinue | Where-Object { $_.ProcessName -match '^(VizDb|VizGH|GraphicHub|Viz ?GH|VizDbServer)' })
}

function Test-GhFileFree([string]$path) {
    try { $fs = [IO.File]::Open($path, 'Open', 'ReadWrite', 'None'); $fs.Dispose(); return $true } catch { return $false }
}

function Assert-GhWritable([string]$target, $a) {
    $procs = Get-GhServerProcesses
    if ($procs.Count) {
        $names = ($procs | ForEach-Object { "$($_.ProcessName) (PID $($_.Id))" }) -join ', '
        if (-not $a.Opt.force) { throw "Graphic Hub processes running: $names. Stop the server (or add -Force if you know what you are doing)." }
        Write-GhWarn "Running Graphic Hub processes ignored (-Force): $names"
    }
    if (-not (Test-GhFileFree $target)) { throw "The file is open in another program: $target" }
}

function Backup-GhObject([string]$path) {
    if (-not (Test-Path -LiteralPath $script:BackupDir)) { New-Item -ItemType Directory -Path $script:BackupDir -Force | Out-Null }
    $fi = Get-Item -LiteralPath $path
    $uuid = $fi.BaseName.ToUpperInvariant()
    $bk = Join-Path $script:BackupDir ("{0}_{1}.vdb" -f $uuid, (Get-Date).ToString('yyyyMMdd-HHmmss'))
    Copy-Item -LiteralPath $path -Destination $bk -Force
    @{ Original = $fi.FullName; Root = (Get-GhRoot); LastWriteTimeUtc = $fi.LastWriteTimeUtc.ToString('o'); CreationTimeUtc = $fi.CreationTimeUtc.ToString('o'); Length = $fi.Length; Date = (Get-Date).ToString('o') } |
        ConvertTo-Json | Set-Content -LiteralPath "$bk.json" -Encoding UTF8
    return $bk
}

function Write-GhFileAtomic([string]$target, [byte[]]$bytes, [bool]$keepTime) {
    $fi = Get-Item -LiteralPath $target
    $lw = $fi.LastWriteTimeUtc; $ct = $fi.CreationTimeUtc
    $tmp = "$target.ghtool.tmp"
    [IO.File]::WriteAllBytes($tmp, $bytes)
    try {
        if ($env:OS -eq 'Windows_NT') { [IO.File]::Replace($tmp, $target, $null) }
        else { Move-Item -LiteralPath $tmp -Destination $target -Force }
    } catch {
        Remove-Item -LiteralPath $tmp -ErrorAction SilentlyContinue
        throw
    }
    if ($keepTime) {
        $n = Get-Item -LiteralPath $target
        $n.CreationTimeUtc = $ct; $n.LastWriteTimeUtc = $lw
    }
}

function New-GhReplacement([string]$path, [string]$imagePath, $a) {
    $info = [GhTool.Vdb]::Inspect($path)
    if ($info.Kind -ne 'Image') { throw "Object $($info.Uuid) is not an image ($($info.Kind))." }
    if (-not $info.SectionList) { throw "Section table not readable: replacement refused." }
    foreach ($sn in ($info.Sections -split ',')) {
        if ($sn -notmatch '^(IconSmall|Icon|IconLarge|Data|Original|VERSION|MMLevel\.\d+)$') { throw "Unrecognised section '$sn': replacement refused." }
    }
    if ($info.Channels -lt 1 -or $info.Channels -gt 4) { throw "Unsupported pixel format: $($info.PixelFormat)" }

    $orig = [IO.File]::ReadAllBytes($path)
    try { $layout = [GhTool.VdbWriter]::Parse($orig) } catch { throw "Unrecognised internal structure ($($_.Exception.Message)): replacement refused." }
    if (-not [GhTool.VdbWriter]::SameBytes($orig, [GhTool.VdbWriter]::Build($layout))) { throw "Identical rebuild failed: unknown format variant, replacement refused." }
    $secNames = @($info.SectionList | ForEach-Object { $_.Name })
    if ($secNames.Count -ne $layout.Sections.Count) { throw "Section count mismatch: replacement refused." }

    $mode = if ($a.Opt.mode) { "$($a.Opt.mode)".ToLower() } else { 'fit' }
    if ($mode -notin 'fit', 'fill', 'stretch') { throw "Unknown mode: $mode (fit, fill or stretch)" }
    $hasAlpha = $info.GlFormat -in 0x1908, 0x80E1, 0x190A, 0x1906
    $bg = ConvertFrom-GhColor $(if ($a.Opt.background) { $a.Opt.background } else { '000000' })
    $bgA = if ($hasAlpha -and -not $a.Opt.background) { [byte]0 } else { [byte]255 }
    $flip = -not $a.Opt.noflip

    Write-Gh "  Reading the new image..." DarkGray
    $src = Read-GhImageFile $imagePath

    # 1) main pixel section (Original in newer files, Data in older ones)
    $mainIdx = [array]::IndexOf($secNames, $info.PixelSection)
    if ($mainIdx -lt 0) { throw 'Pixel section not found: replacement refused.' }
    $mainPl = [GhTool.VdbWriter]::DecodeSection($layout.Sections[$mainIdx])
    $mi = [GhTool.VdbWriter]::ParsePixels($mainPl)
    $after = $mainPl.Length - ($mi.PixelOffset + $mi.PixelLength)
    if ($mi.Kind -ne 'Image' -or $after -lt 0 -or $after -gt 2048) { throw "Unexpected data around the pixels ($after B): replacement refused." }
    $w = $mi.Width; $h = $mi.Height
    Write-Gh "  Resizing to $w×$h ($mode)..." DarkGray
    $main = [GhTool.VdbWriter]::Resize($src.Rgba, $src.W, $src.H, $w, $h, $mode, $bg[0], $bg[1], $bg[2], $bgA)
    $src = $null
    $results = @{}
    $newMainPl = [byte[]]$mainPl.Clone()
    $stride = if ($mi.PixelLength % $h -eq 0 -and $mi.PixelLength / $h -ge $w * $mi.Channels) { $mi.PixelLength / $h } else { $w * $mi.Channels }
    [GhTool.VdbWriter]::WritePixels($main, $w, $h, $mi.GlFormat, $mi.Channels, $flip, $newMainPl, $mi.PixelOffset, [int]$stride, $bg[0], $bg[1], $bg[2])
    $big = $newMainPl.Length -gt 16MB
    Write-Gh "  Compressing $($info.PixelSection) ($(Format-Size $newMainPl.Length))..." DarkGray
    $layout.Sections[$mainIdx] = [GhTool.VdbWriter]::BuildDataSectionLevel($newMainPl, [GhTool.VdbWriter]::FirstRawChunk($layout.Sections[$mainIdx]), $big)
    $results[$info.PixelSection] = $newMainPl

    $notes = New-Object System.Collections.Generic.List[string]
    $prev = $main; $pw = $w; $ph = $h
    for ($k = 0; $k -lt $secNames.Count; $k++) {
        $n = $secNames[$k]; $sec = $layout.Sections[$k]
        if ($k -eq $mainIdx -or $sec.Length -eq 0) { continue }
        if ($n -eq 'Data' -or $n -eq 'Original') {
            # secondary pixel section (preview in newer files)
            $pl = [GhTool.VdbWriter]::DecodeSection($sec)
            $pi = [GhTool.VdbWriter]::ParsePixels($pl)
            if ($pi.Kind -ne 'Image') { continue }
            $rgba = [GhTool.VdbWriter]::Resize($main, $w, $h, $pi.Width, $pi.Height, 'stretch', $bg[0], $bg[1], $bg[2], 255)
            $st = if ($pi.PixelLength % $pi.Height -eq 0 -and $pi.PixelLength / $pi.Height -ge $pi.Width * $pi.Channels) { $pi.PixelLength / $pi.Height } else { $pi.Width * $pi.Channels }
            [GhTool.VdbWriter]::WritePixels($rgba, $pi.Width, $pi.Height, $pi.GlFormat, $pi.Channels, $flip, $pl, $pi.PixelOffset, [int]$st, $bg[0], $bg[1], $bg[2])
            $layout.Sections[$k] = [GhTool.VdbWriter]::BuildDataSectionLevel($pl, [GhTool.VdbWriter]::FirstRawChunk($sec), $false)
            $notes.Add("$n preview $($pi.Width)×$($pi.Height)")
        }
        elseif ($n -match '^MMLevel\.') {
            $pl = [GhTool.VdbWriter]::DecodeSection($sec)
            $m = [GhTool.VdbWriter]::FindMip($pl)
            if (-not $m) { throw "Mipmap section $n not recognised: replacement refused." }
            $mw = $m[0]; $mh = $m[1]
            if ($m[3] -ne ([Math]::Floor(($mw + 3) / 4) * [Math]::Floor(($mh + 3) / 4) * 8)) { throw "Mipmap $n is not DXT1/BC1: replacement refused." }
            $rgba = [GhTool.VdbWriter]::Resize($prev, $pw, $ph, $mw, $mh, 'stretch', $bg[0], $bg[1], $bg[2], 255)
            [GhTool.VdbWriter]::EncodeBC1($rgba, $mw, $mh, $flip, $pl, $m[2])
            $layout.Sections[$k] = [GhTool.VdbWriter]::BuildDataSectionLevel($pl, [GhTool.VdbWriter]::FirstRawChunk($sec), ($pl.Length -gt 16MB))
            $results[$n] = $pl
            $prev = $rgba; $pw = $mw; $ph = $mh
        }
    }
    if ($info.MipLevels) { $notes.Add("$($info.MipLevels) mipmap levels regenerated") }

    $thumbNote = 'thumbnails regenerated'
    for ($k = 0; $k -lt $secNames.Count; $k++) {
        if ($secNames[$k] -notmatch '^Icon') { continue }
        $sec = $layout.Sections[$k]
        $tw = [GhTool.VdbWriter]::IconWidth($sec); $th = [GhTool.VdbWriter]::IconHeight($sec)
        if ($tw -lt 1 -or $th -lt 1 -or $tw -gt 4096 -or $th -gt 4096) { $thumbNote = 'original thumbnails kept (unknown template)'; continue }
        $t = [GhTool.VdbWriter]::Resize($main, $w, $h, $tw, $th, 'stretch', 0, 0, 0, 255)
        $jpg = [GhTool.VdbWriter]::EncodeJpeg($t, $tw, $th, 90)
        $ns = [GhTool.VdbWriter]::RebuildIconSection($sec, $jpg, $tw, $th)
        if ($ns) { $layout.Sections[$k] = $ns } else { $thumbNote = 'original thumbnails kept (unknown template)' }
    }
    $notes.Insert(0, $thumbNote)
    $main = $null; $prev = $null
    $newBytes = [GhTool.VdbWriter]::Build($layout)

    # Verification: re-read the new file with the independent reader
    if (-not (Test-Path -LiteralPath $script:StagingDir)) { New-Item -ItemType Directory -Path $script:StagingDir -Force | Out-Null }
    $staged = Join-Path $script:StagingDir "$($info.Uuid).vdb"
    [IO.File]::WriteAllBytes($staged, $newBytes)
    $chk = [GhTool.Vdb]::Inspect($staged)
    if ($chk.Kind -ne 'Image' -or $chk.Width -ne $info.Width -or $chk.Height -ne $info.Height -or $chk.GlFormat -ne $info.GlFormat -or $chk.Name -ne $info.Name -or $chk.Sections -ne $info.Sections) { throw 'Verification failed: the rebuilt file does not read back correctly.' }
    if ($chk.ThumbCount -ne $info.ThumbCount) { throw 'Verification failed: unreadable thumbnails.' }
    if (-not [GhTool.VdbWriter]::SameBytes([GhTool.Vdb]::ReadPayload($chk), $newMainPl)) { throw 'Verification failed: decompressed data differs.' }
    $re = [GhTool.VdbWriter]::Parse($newBytes)
    for ($k = 0; $k -lt $secNames.Count; $k++) {
        if ($results.ContainsKey($secNames[$k]) -and $secNames[$k] -ne $info.PixelSection) {
            if (-not [GhTool.VdbWriter]::SameBytes([GhTool.VdbWriter]::DecodeSection($re.Sections[$k]), $results[$secNames[$k]])) { throw "Verification failed: section $($secNames[$k]) differs." }
        }
    }
    $oldPl = [GhTool.Vdb]::ReadPayload($info)

    return [pscustomobject]@{ Info = $info; Check = $chk; Path = $path; Bytes = $newBytes; Staged = $staged; Payload = $oldPl; NewPayload = $newMainPl
        Mode = $mode; Source = "$($imagePath)"; Thumbs = ($notes -join ', '); OldSize = $orig.Length; SrcSize = '' }
}

function Invoke-GhReplace($a) {
    if ($a.Pos.Count -lt 2) { Write-GhErr 'Usage: gh replace <id> <new_image> [-Mode fit|fill|stretch] [-Background RRGGBB] [-Apply] [-Force]'; return }
    $path = Resolve-GhObject $a.Pos[0]
    $img = $a.Pos[1]
    Write-GhTitle "Replacing $(Split-Path $path -Leaf)"
    $r = New-GhReplacement $path $img $a
    $i = $r.Info
    Write-Gh ("  Object     : {0}  [{1}]  {2}×{3} {4}" -f $i.Name, $i.Uuid, $i.Width, $i.Height, $i.PixelFormat)
    Write-Gh ("  Source     : {0} -> {1}×{2}, mode {3}" -f (Split-Path $img -Leaf), $i.Width, $i.Height, $r.Mode)
    Write-Gh ("  File       : {0} -> {1}  ({2})" -f (Format-Size $r.OldSize), (Format-Size $r.Bytes.Length), $r.Thumbs)
    Write-GhOk 'Structure rebuilt and read back successfully'

    $prev = Join-Path $script:StagingDir "$($i.Uuid)_before.png"; $next = Join-Path $script:StagingDir "$($i.Uuid)_after.png"
    [GhTool.Vdb]::WriteThumbPng($i, $r.Payload, $prev, $true, 1024)
    [GhTool.Vdb]::WriteThumbPng($r.Check, $r.NewPayload, $next, $true, 1024)
    Write-Gh "  Previews   : $prev" DarkGray
    Write-Gh "               $next" DarkGray

    $users = @(Get-GhRefList $i.Uuid 'usedby')
    if ($users.Count) { Write-Gh ("  Used by    : {0} object(s): {1}" -f $users.Count, ((@($users | Select-Object -First 8 | ForEach-Object { (Get-GhObjectLabel $_).Name })) -join ', ')) }
    if (-not $a.Opt.apply) {
        Write-Gh ''
        Write-Gh "  DRY RUN: nothing was changed in the Graphic Hub." Yellow
        Write-Gh "  Prepared file: $($r.Staged)" DarkGray
        Write-Gh '  Add -Apply to write it (automatic backup; to undo: gh restore <uuid>).' DarkGray
        if (-not $a.Opt.noopen) { try { Invoke-Item -LiteralPath $next } catch { } }
        return
    }

    Assert-GhWritable $path $a
    $bk = Backup-GhObject $path
    Write-GhOk "Backup: $bk"
    Write-GhFileAtomic $path $r.Bytes (-not $a.Opt.touch)
    $final = [IO.File]::ReadAllBytes($path)
    if (-not [GhTool.VdbWriter]::SameBytes($final, $r.Bytes)) {
        Copy-Item -LiteralPath $bk -Destination $path -Force
        throw 'The written file does not match: original restored from the backup.'
    }
    $script:Index = $null
    Write-GhOk "Image replaced: $path"
    Write-Gh '  Viz Engines that already loaded the image may keep the old version in memory until they reload it.' DarkGray
}

function Get-GhBackups([string]$uuid) {
    if (-not (Test-Path -LiteralPath $script:BackupDir)) { return @() }
    $f = if ($uuid) { "$uuid*.vdb" } else { '*.vdb' }
    return @(Get-ChildItem -LiteralPath $script:BackupDir -Filter $f -File | Sort-Object Name)
}

function Invoke-GhBackups($a) {
    $u = if ($a.Pos.Count) { $a.Pos[0].Replace('-', '').ToUpperInvariant() } else { '' }
    $b = Get-GhBackups $u
    Write-GhTitle "Backups ($script:BackupDir)"
    if (-not $b.Count) { Write-Gh '  No backups.'; return }
    $b | Select-Object @{n = 'File'; e = { $_.Name } }, @{n = 'Size'; e = { Format-Size $_.Length } } | Format-Table -AutoSize | Out-String -Width 300 | Write-Host
}

function Invoke-GhRestore($a) {
    if (-not $a.Pos.Count) { Write-GhErr 'Usage: gh restore <uuid> [-File backup_name] [-Force]'; return }
    $u = $a.Pos[0].Trim('{', '}').Replace('-', '').ToUpperInvariant()
    $list = Get-GhBackups $u
    if ($a.Opt.file) { $list = @($list | Where-Object { $_.Name -like "*$($a.Opt.file)*" }) }
    if (-not $list.Count) { throw "No backup for $u." }
    $bk = $list[-1]
    $meta = $null; if (Test-Path -LiteralPath "$($bk.FullName).json") { $meta = Get-Content -LiteralPath "$($bk.FullName).json" -Raw | ConvertFrom-Json }
    $uuid = ($bk.BaseName -split '_')[0]
    $target = if ($meta -and $meta.Original -and (Test-Path -LiteralPath (Split-Path $meta.Original))) { $meta.Original } else { Join-Path (Join-Path (Get-GhRoot) $uuid.Substring(0, 1)) "$uuid.vdb" }
    Write-GhTitle "Restoring $uuid"
    Write-Gh "  From: $($bk.FullName)"
    Write-Gh "  To  : $target"
    if (Test-Path -LiteralPath $target) { Assert-GhWritable $target $a }
    $bytes = [IO.File]::ReadAllBytes($bk.FullName)
    if (Test-Path -LiteralPath $target) { Write-GhFileAtomic $target $bytes $false } else { [IO.File]::WriteAllBytes($target, $bytes) }
    if ($meta) {
        $n = Get-Item -LiteralPath $target
        try { $n.CreationTimeUtc = [datetime]::Parse($meta.CreationTimeUtc).ToUniversalTime(); $n.LastWriteTimeUtc = [datetime]::Parse($meta.LastWriteTimeUtc).ToUniversalTime() } catch { }
    }
    if (-not [GhTool.VdbWriter]::SameBytes([IO.File]::ReadAllBytes($target), $bytes)) { throw 'Verification failed after restoring.' }
    $script:Index = $null
    Write-GhOk 'Original restored (content identical to the backup)'
}

function ConvertTo-GhJsonString([string]$s) { return ($s | ConvertTo-Json -Compress) }

function Invoke-GhScene2Html($a) {
    $root = Get-GhRoot
    $path = Resolve-GhObject ($a.Pos -join ' ')
    $i = [GhTool.Vdb]::Inspect($path)
    if ($i.Kind -ne 'Scene') { throw "Object $($i.Uuid) is not a scene ($($i.Kind))." }
    Write-GhTitle "Scene to HTML: $($i.Name)"
    $tree = [GhTool.Vdb]::SceneTreeJson($i)
    if (-not $tree) { throw 'The scene data could not be read.' }

    # preview (largest thumbnail) for the overlay
    $prev = ''
    $best = -1; for ($t = 0; $t -lt $i.ThumbCount; $t++) { if ($best -lt 0 -or $i.Thumbs[$t].Width -gt $i.Thumbs[$best].Width) { $best = $t } }
    if ($best -ge 0) { $prev = [Convert]::ToBase64String([GhTool.Vdb]::ReadThumb($i, $best)) }

    # images / fonts referenced by the scene (searched in the GH reference table)
    $images = New-Object System.Collections.Generic.List[string]
    $fonts = New-Object System.Collections.Generic.List[string]
    if (-not $a.Opt.norefs) {
        $refs = New-Object System.Collections.Generic.List[string]
        $rt = Get-GhRefs
        if ($rt) {
            foreach ($u in (Get-GhRefList $i.Uuid 'uses')) {
                if (-not $refs.Contains($u)) { $refs.Add($u) }
                # one level deeper: materials and other objects used by the scene can carry images
                foreach ($u2 in (Get-GhRefList $u 'uses')) { if (-not $refs.Contains($u2)) { $refs.Add($u2) } }
            }
            Write-Gh "  Objects used by this scene (ReferenceCollection): $($refs.Count)" DarkGray
        } else { Write-Gh '  No ReferenceCollection table in this Graphic Hub.' DarkGray }
        $tmp = Join-Path ([IO.Path]::GetTempPath()) "ghtool_s2h_$([Guid]::NewGuid().ToString('N')).png"
        foreach ($u in $refs) {
            $p = Join-Path (Join-Path $root $u.Substring(0, 1)) "$u.vdb"
            if (-not (Test-Path -LiteralPath $p)) { Write-Gh "    missing [$($u.Substring(0, 8))] (listed in ReferenceCollection but not in this Graphic Hub)" DarkGray; continue }
            $ri = [GhTool.Vdb]::Inspect($p)
            if ($ri.Kind -eq 'Image' -and $ri.Channels -ge 1) {
                try {
                    [GhTool.Vdb]::WriteThumbPng($ri, [GhTool.Vdb]::ReadPayload($ri), $tmp, $true, 1920)
                    $src = 'data:image/png;base64,' + [Convert]::ToBase64String([IO.File]::ReadAllBytes($tmp))
                    $images.Add('{"u":' + (ConvertTo-GhJsonString $u) + ',"n":' + (ConvertTo-GhJsonString "$($ri.Name)") + ',"src":' + (ConvertTo-GhJsonString $src) + '}')
                    Write-Gh "    image  $($ri.Name)  [$($u.Substring(0, 8))]  $($ri.Width)×$($ri.Height)"
                } catch { Write-GhWarn "Image $u could not be decoded: $($_.Exception.Message)" }
            } elseif ($ri.Kind -eq 'Font') {
                $fonts.Add('{"u":' + (ConvertTo-GhJsonString $u) + ',"n":' + (ConvertTo-GhJsonString "$($ri.Name)") + '}')
                Write-Gh "    font   $($ri.Name)  [$($u.Substring(0, 8))]"
            } else { Write-Gh "    $($ri.Kind.ToLower())  $($ri.Name)  [$($u.Substring(0, 8))]" DarkGray }
        }
        # 2) by name: Viz names a container after the image dropped on it, so look for images with the same name
        $names = @([GhTool.Vdb]::Scene($i).Containers | ForEach-Object { "$_" } | Sort-Object -Unique)
        $imgIdx = @(Get-GhIndex | Where-Object { $_.Kind -eq 'Image' -and $_.Name })
        $byName = @{}
        foreach ($im in $imgIdx) { $k = $im.Name.ToLowerInvariant(); if (-not $byName.ContainsKey($k)) { $byName[$k] = New-Object System.Collections.Generic.List[object] }; $byName[$k].Add($im) }
        $nameHits = 0
        foreach ($cn in $names) {
            $k = ($cn -replace '_\(\d+\)$', '' -replace '\.(png|jpe?g|tga|tiff?|bmp|psd)$', '').ToLowerInvariant()
            if (-not $byName.ContainsKey($k)) { continue }
            foreach ($im in $byName[$k]) {
                if ($refs.Contains($im.Uuid)) { continue }
                $refs.Add($im.Uuid); $nameHits++
                try {
                    $ri = [GhTool.Vdb]::Inspect($im.Path)
                    [GhTool.Vdb]::WriteThumbPng($ri, [GhTool.Vdb]::ReadPayload($ri), $tmp, $true, 1920)
                    $src = 'data:image/png;base64,' + [Convert]::ToBase64String([IO.File]::ReadAllBytes($tmp))
                    $images.Add('{"u":' + (ConvertTo-GhJsonString $im.Uuid) + ',"n":' + (ConvertTo-GhJsonString "$cn") + ',"src":' + (ConvertTo-GhJsonString $src) + '}')
                    Write-Gh "    image  $($ri.Name)  [$($im.Uuid.Substring(0, 8))]  $($ri.Width)×$($ri.Height)  (same name as container '$cn')"
                } catch { Write-GhWarn "Image $($im.Uuid) could not be decoded: $($_.Exception.Message)" }
            }
        }
        if ($nameHits) { Write-Gh "  Images matched by container name: $nameHits" DarkGray }
        Remove-Item -LiteralPath $tmp -ErrorAction SilentlyContinue
        if (-not $refs.Count) { Write-Gh '  (No references found: textures will be placeholders you can replace in the page.)' DarkGray }
    }

    $viz = 0; if ($i.AppVersion -match '^(\d+)') { $viz = [int]$Matches[1] }
    $font = if ($a.Opt.font) { "$($a.Opt.font), Arial, sans-serif" } else { '' }
    $json = '{"viz":' + $viz + ',"name":' + (ConvertTo-GhJsonString "$($i.Name)") + ',"uuid":' + (ConvertTo-GhJsonString $i.Uuid) +
        ',"font":' + (ConvertTo-GhJsonString $font) + ',"preview":' + (ConvertTo-GhJsonString $prev) +
        ',"images":[' + ($images -join ',') + '],"fonts":[' + ($fonts -join ',') + '],' + $tree + '}'
    $json = $json.Replace('</', '<\/')
    $html = $script:GhSceneTemplate.Replace('__TITLE__', [Net.WebUtility]::HtmlEncode("$($i.Name)")).Replace('__SCENE__', $json)

    $out = if ($a.Opt.out) { $a.Opt.out } else { Join-Path (Get-Location).ProviderPath ("{0}_{1}.html" -f (Get-SafeName $i.Name), $i.Uuid.Substring(0, 8)) }
    if ($out -notmatch '\.html?$') { $dir = Assert-GhOutside $out; $out = Join-Path $dir ("{0}_{1}.html" -f (Get-SafeName $i.Name), $i.Uuid.Substring(0, 8)) }
    else { [void](Assert-GhOutside (Split-Path -Parent ([IO.Path]::GetFullPath($out)))) }
    [IO.File]::WriteAllText($out, $html, (New-Object Text.UTF8Encoding($false)))
    Write-GhOk "HTML written: $out ($(Format-Size (Get-Item -LiteralPath $out).Length))"
    if (-not $a.Opt.noopen) { try { Invoke-Item -LiteralPath $out } catch { } }
}

$script:GhSceneTemplate = @'
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITLE__ – Viz scene preview</title>
<style>
  :root { --bg:#121417; --panel:#1b1e23; --line:#2b3038; --text:#e6e8eb; --mute:#8b929c; --acc:#4da3ff; }
  * { box-sizing:border-box; }
  html, body { margin:0; height:100%; background:var(--bg); color:var(--text); font:13px/1.4 "Segoe UI", system-ui, sans-serif; }
  #app { display:grid; grid-template-columns:1fr 340px; grid-template-rows:auto 1fr auto; height:100%; }
  header { grid-column:1/-1; display:flex; align-items:center; gap:12px; padding:8px 14px; border-bottom:1px solid var(--line); }
  header h1 { font-size:14px; margin:0; font-weight:600; }
  header .mute { color:var(--mute); font-size:12px; }
  #viewport { position:relative; overflow:hidden; display:flex; align-items:center; justify-content:center; padding:12px; }
  #frame { position:relative; width:1920px; height:1080px; transform-origin:0 0; flex:none; overflow:hidden; }
  #frame.bg-checker { background:conic-gradient(#3a3f47 25%, #2c3037 0 50%, #3a3f47 0 75%, #2c3037 0) 0 0/40px 40px; }
  #frame.bg-black { background:#000; }
  #frame.bg-transparent { background:transparent; }
  #stage { position:absolute; left:960px; top:540px; width:0; height:0; transform-style:preserve-3d; }
  #cv { position:absolute; inset:0; width:100%; height:100%; }
  .g { position:absolute; }
  .txt { white-space:pre; font-family:Arial, "Helvetica Neue", sans-serif; line-height:1; transform-origin:0 0; }
  .ph { background:repeating-linear-gradient(45deg,#666a 0 12px,#8889 12px 24px); outline:2px dashed #ffffff80; outline-offset:-2px;
        display:flex; align-items:center; justify-content:center; overflow:hidden; background-size:cover; background-position:center; }
  .ph span { font:600 22px Arial; color:#fff; text-shadow:0 0 4px #000; padding:4px; text-align:center; }
  #ref { position:absolute; inset:0; width:100%; height:100%; opacity:0; pointer-events:none; }
  aside { grid-row:2/4; grid-column:2; border-left:1px solid var(--line); background:var(--panel); overflow:auto; padding:12px; }
  aside h2 { font-size:12px; text-transform:uppercase; letter-spacing:.06em; color:var(--mute); margin:14px 0 8px; }
  aside h2:first-child { margin-top:0; }
  label.f { display:block; margin-bottom:10px; }
  label.f span { display:block; color:var(--mute); font-size:12px; margin-bottom:3px; }
  input[type=text], textarea, select { width:100%; background:#0d0f12; color:var(--text); border:1px solid var(--line); border-radius:6px; padding:6px 8px; font:inherit; }
  textarea { resize:vertical; min-height:34px; }
  footer { grid-column:1; display:flex; align-items:center; gap:10px; padding:8px 14px; border-top:1px solid var(--line); }
  button { background:var(--panel); color:var(--text); border:1px solid var(--line); border-radius:6px; padding:5px 12px; font:inherit; cursor:pointer; }
  button.primary { background:var(--acc); color:#06121f; border-color:var(--acc); font-weight:600; }
  #time { flex:1; }
  #clock { font-variant-numeric:tabular-nums; color:var(--mute); width:120px; text-align:right; }
  .tree { font:12px/1.5 ui-monospace, Consolas, monospace; }
  .tree div { white-space:nowrap; overflow:hidden; text-overflow:ellipsis; cursor:default; }
  .tree div.off { color:var(--mute); text-decoration:line-through; }
  .tree div:hover { color:var(--acc); }
  .note { color:var(--mute); font-size:12px; }
  .hl { outline:2px solid var(--acc) !important; }
</style>
</head>
<body>
<div id="app">
  <header>
    <h1>__TITLE__</h1>
    <span class="mute" id="summary"></span>
    <span style="flex:1"></span>
    <label class="mute">Background
      <select id="bg" style="width:auto"><option value="checker">Checker</option><option value="black">Black</option><option value="transparent">Transparent</option></select>
    </label>
    <label class="mute"><input type="checkbox" id="minv"> Invert masks</label>
    <label class="mute">Viz preview overlay <input type="range" id="refop" min="0" max="100" value="0" style="vertical-align:middle"></label>
  </header>
  <div id="viewport"><div id="frame" class="bg-checker"><canvas id="cv" width="1920" height="1080"></canvas><img id="ref" alt=""></div></div>
  <aside>
    <h2>Data</h2>
    <div id="form"></div>
    <h2>Layers</h2>
    <div class="tree" id="tree"></div>
    <h2>About this preview</h2>
    <p class="note">Generated by GHTool from the Viz scene data. Approximations: fonts are replaced with Arial, images used by the
      scene are shown as placeholders (load your own in the form), Viz scripts and some plugins are not executed.</p>
    <div id="skipped" class="note"></div>
  </aside>
  <footer>
    <button class="primary" id="play">▶ Play</button>
    <button id="cont">⏭ Continue</button>
    <button id="stop">■ Stop</button>
    <label class="mute"><input type="checkbox" id="loop"> Loop</label>
    <input type="range" id="time" min="0" max="1000" value="0">
    <span id="clock">0.00 s</span>
  </footer>
</div>
<script type="application/json" id="scene">__SCENE__</script>
<script>
(function () {
  'use strict';
  var S = JSON.parse(document.getElementById('scene').textContent);
  var FONT = S.font || 'Arial, "Helvetica Neue", sans-serif';
  var UNIT = 1080 / 414.2135;          // Viz units -> pixels (default camera: z=500, vertical FOV 45 degrees)
  var PERSP = 500 * UNIT;

  // ---------- raw tree helpers ----------
  function hexBytes(h) { var b = new Uint8Array(h.length / 2); for (var i = 0; i < b.length; i++) b[i] = parseInt(h.substr(i * 2, 2), 16); return b; }
  function N(a) { return { tag: a[0], hex: a[1], kids: (a[2] || []).map(N) }; }
  function kid(n, tag) { if (!n) return null; for (var i = 0; i < n.kids.length; i++) if (n.kids[i].tag === tag) return n.kids[i]; return null; }
  function kidsOf(n, tag) { return n ? n.kids.filter(function (k) { return k.tag === tag; }) : []; }
  function path(n) { for (var i = 1; i < arguments.length && n; i++) n = kid(n, arguments[i]); return n; }
  function dv(n) { var b = hexBytes(n.hex); return new DataView(b.buffer); }
  function f32(n, i) { return n && n.hex.length >= (i + 1) * 8 ? dv(n).getFloat32(i * 4, true) : null; }
  function f3(n) { return n && n.hex.length >= 24 ? [f32(n, 0), f32(n, 1), f32(n, 2)] : null; }
  function f4(n) { return n && n.hex.length >= 32 ? [f32(n, 0), f32(n, 1), f32(n, 2), f32(n, 3)] : null; }
  function i32(n) { return n && n.hex.length >= 8 ? dv(n).getInt32(0, true) : null; }
  function u8(n) { return n && n.hex.length >= 2 ? parseInt(n.hex.substr(0, 2), 16) : null; }
  function f64(n) { return n && n.hex.length >= 16 ? dv(n).getFloat64(0, true) : null; }
  function str(n) {
    if (!n || n.hex.length < 4) return '';
    var b = hexBytes(n.hex), L = b[0] | (b[1] << 8);
    try { return new TextDecoder('utf-8').decode(b.subarray(2, 2 + L)); } catch (e) { return ''; }
  }
  function findAll(n, tag, acc) { acc = acc || []; if (n.tag === tag) acc.push(n); n.kids.forEach(function (k) { findAll(k, tag, acc); }); return acc; }
  function wrapped(n) { var w = kid(n, 0x0001); return w && w.kids[0] ? w.kids[0] : null; }   // 0650 > 0001 > 0650

  // generic plugin parameter list: 062e name, 0631 type, then value
  function params(list) {
    var p = {}, cur = null;
    if (!list) return p;
    list.kids.forEach(function (k) {
      if (k.tag === 0x062e) { cur = str(k); return; }
      if (cur === null || k.tag === 0x0631) return;
      var v;
      switch (k.tag) {
        case 0x062a: v = f32(k, 0); break;
        case 0x062d: v = i32(k); break;
        case 0x0625: v = u8(k) === 1; break;
        case 0x0626: var b = hexBytes(k.hex); v = [b[0], b[1], b[2], b[3]]; break;
        case 0x062f: v = str(k); break;
        default: v = k.hex.length === 24 ? f3(k) : (k.hex || null);
      }
      p[cur] = v; cur = null;
    });
    return p;
  }

  // ---------- animation channels ----------
  function readChannels(holder, prop) {
    var out = [], ch = kid(holder, 0x0223);
    if (!ch) return out;
    kidsOf(ch, 0x02a0).forEach(function (grp) {
      grp.kids.forEach(function (c) {
        var keysNode = kid(c, 0x02ae);
        if (!keysNode) return;
        var name = str(kid(c, 0x02b1)) || prop;
        var pathPts = findAll(c, 0x0614).map(function (p) { return f3(kid(p, 0x0615)); });
        var keys = keysNode.kids.map(function (k) {
          var t = f64(kid(k, 0x05c6)), vn = kid(k, 0x05c7), v = null;
          if (vn) {
            if (vn.kids.length) { var s3 = path(vn, 0x0680, 0x0410) || wrapped(vn) || vn.kids[0]; v = f3(s3) || f4(s3); }
            else if (vn.hex.length === 24) v = f3(vn);
            else if (vn.hex.length === 32) v = f4(vn);
            else if (vn.hex.length === 8) v = f32(vn, 0);
          }
          return { t: t || 0, v: v };
        }).filter(function (k) { return k.v !== null; });
        if (keys.length) out.push({ name: name, prop: prop, keys: keys, path: pathPts });
      });
    });
    return out;
  }

  // ---------- containers ----------
  var all = [], skipped = {};
  function readContainer(c) {
    var o = { node: c, name: str(kid(c, 0x0317)) || 'noname', active: u8(kid(c, 0x0301)) !== 0, kids: [], anims: [], funcs: [] };
    var t = path(c, 0x07b0, 0x07b0);
    o.pos = f3(wrapped(kid(t, 0x0650))) || [0, 0, 0];
    o.rot = f3(wrapped(kid(t, 0x0670))) || [0, 0, 0];
    o.scale = f3(path(t, 0x0680, 0x0680, 0x0410)) || [1, 1, 1];
    o.center = f3(wrapped(kid(t, 0x0290))) || [0, 0, 0];
    if (t) o.anims = readChannels(t, 'transform');
    // material
    var m = path(c, 0x0314, 0x0600);
    if (m) {
      var col = f4(wrapped(kid(m, 0x0603))) || f4(wrapped(kid(m, 0x0604)));
      o.color = col; var a = f32(kid(m, 0x0601), 0); o.matAlpha = a === null ? 1 : a;
    }
    // alpha
    var al = path(c, 0x0302, 0x0220);
    if (al) { var a0 = f32(kid(al, 0x0226), 0); o.alpha = a0 === null ? undefined : a0 * 100;   // stored as 0..1, keyframes use 0..100
      o.anims = o.anims.concat(readChannels(al, 'alpha')); }
    // texture
    if (kid(c, 0x0322)) o.texture = true;
    // geometry
    var g = path(c, 0x030d, 0x030d, 0x0581);
    if (g) {
      var kind = str(kid(g, 0x0522));
      if (kind === 'Plugin') { var pl = path(g, 0x0500, 0x0524); o.geom = { type: str(kid(pl, 0x0623)), p: params(kid(pl, 0x0624)) }; }
      else if (kind === 'ClassicText' || path(g, 0x0500, 0x0550)) {
        var tx = path(g, 0x0500, 0x0550);
        var jb = kid(tx, 0x0557), jv = jb ? dv(jb) : null;
        o.geom = { type: 'Text', text: str(kid(tx, 0x056e)).replace(/\n$/, ''), h: jv && jb.hex.length >= 8 ? jv.getInt32(0, true) : 1, v: jv && jb.hex.length >= 16 ? jv.getInt32(4, true) : 6 };
      } else o.geom = { type: kind || 'Geometry' };
    }
    // function plugins
    var fl = path(c, 0x030c, 0x04e0, 0x04e1);
    if (fl) kidsOf(fl, 0x0001).forEach(function (w) { var f = w.kids[0]; if (f) o.funcs.push({ type: str(kid(f, 0x0623)), p: params(kid(f, 0x0624)) }); });
    // clipping to a reference container (Viz "clip" option: the container is cut to another container's shape)
    var cl = path(c, 0x0331, 0x0a00);
    if (cl && u8(kid(cl, 0x0a06)) === 1) { var ref = str(kid(cl, 0x0a07)); if (ref) o.clipRef = ref.replace(/^CONTAINER\|/, ''); }
    // script
    var sc = findAll(c, 0x0702)[0];
    if (sc && kid(c, 0x0700)) o.script = str(sc);
    all.push(o);
    return o;
  }
  function readList(list, parent) {
    var last = null;
    list.kids.forEach(function (k) {
      if (k.tag === 0x07c4) { var cn = kid(k, 0x0300); if (cn) { last = readContainer(cn); last.parent = parent; parent.kids.push(last); } }
      else if (k.tag === 0x07c5 && last) readList(k, last);
    });
  }
  var raw = N(S.tree), rootList = findAll(raw, 0x07c5)[0];
  var root = { name: 'scene', kids: [], anims: [], funcs: [], pos: [0, 0, 0], rot: [0, 0, 0], scale: [1, 1, 1], center: [0, 0, 0], active: true };
  if (rootList) readList(rootList, root);

  // ---------- clip references: "T0/1/2/3/1" = 1-based child indices from the top of the scene tree ----------
  all.forEach(function (o) {
    if (!o.clipRef) return;
    var parts = o.clipRef.split('/'), cur = root;
    for (var i = 1; i < parts.length && cur; i++) cur = cur.kids[parseInt(parts[i], 10) - 1];
    o.clipTo = cur && cur !== root ? cur : null;
  });
  // ---------- masks, stop points ----------
  all.forEach(function (o) { o.maskSrc = 0; o.maskDst = 0; });
  (function scanMasks(list) {
    list.kids.forEach(function (k) {
      if (k.tag === 0x07c4) { var cn = kid(k, 0x0300), o = cn && all.find(function (x) { return x.node === cn; });
        if (o) { var ms = path(cn, 0x0304, 0x0261), md = path(cn, 0x0306, 0x0262); if (ms) o.maskSrc = i32(kid(ms, 0x0260)) || 0; if (md) o.maskDst = i32(kid(md, 0x0260)) || 0; /* bits 0 = mask switched off */ } }
      else if (k.tag === 0x07c5) scanMasks(k);
    });
  })(rootList || { kids: [] });
  var stops = [];
  if (S.stage) findAll(N(S.stage), 0x05b7).forEach(function (ev) {
    var t = f64(kid(ev, 0x05c6)), kind = i32(kid(ev, 0x05c7));
    if (t > 0.001 && kind === 0 && stops.indexOf(t) < 0) stops.push(t);
  });
  stops.sort(function (a, b) { return a - b; });

  // ---------- 2D renderer (canvas, Viz units, y up) ----------
  var cv = document.getElementById('cv'), ctx = cv.getContext('2d');
  function mul(m, n) { return [m[0] * n[0] + m[2] * n[1], m[1] * n[0] + m[3] * n[1], m[0] * n[2] + m[2] * n[3], m[1] * n[2] + m[3] * n[3], m[0] * n[4] + m[2] * n[5] + m[4], m[1] * n[4] + m[3] * n[5] + m[5]]; }
  var D2R = Math.PI / 180;
  function localMatrix(st) {
    var r = st.rot[2] * D2R, cs = Math.cos(r), sn = Math.sin(r);
    var sx = st.scale[0] * Math.cos(st.rot[1] * D2R), sy = st.scale[1] * Math.cos(st.rot[0] * D2R);
    var m = [cs * sx, sn * sx, -sn * sy, cs * sy, st.pos[0], st.pos[1]];
    return mul(m, [1, 0, 0, 1, -st.center[0], -st.center[1]]);
  }
  function css(c, a) { return 'rgba(' + Math.round(c[0] * 255) + ',' + Math.round(c[1] * 255) + ',' + Math.round(c[2] * 255) + ',' + a + ')'; }
  function rgba8(c) { return 'rgba(' + c[0] + ',' + c[1] + ',' + c[2] + ',' + (c[3] / 255) + ')'; }
  // Shape of a geometry in its own units: box (cx, cy = centre offset from the origin), corner radii, shear, outline, crop
  function geomBox(o) {
    var g = o.geom, p = (g && g.p) || {};
    if (!g) return null;
    var sh = { w: 100, h: 100, cx: 0, cy: 0, round: false, r: [0, 0, 0, 0], shear: 0, outline: 0, crop: null };
    if (/circle|disc|ring/i.test(g.type)) { var rr = p.radius || p.outer_radius || 50; sh.w = sh.h = 2 * rr; sh.round = true; return sh; }
    if (g.type === 'Image') { sh.w = 100; sh.h = 56.25; return sh; }
    if (!(p.width !== undefined || /rect|noggi|clip|image/i.test(g.type))) return null;
    sh.w = p.width === undefined ? 100 : p.width; sh.h = p.height === undefined ? 100 : p.height;
    if (g.type === 'Noggi') {
      // Viz order: bevel top/right, top/left, bottom/left, bottom/right; alignment 0 = left/bottom, 1 = centre/middle, 2 = right/top
      sh.r = [p.bevel_0 || 0, p.bevel_1 || 0, p.bevel_2 || 0, p.bevel_3 || 0];
      var ha = p.hAlignment === undefined ? 1 : p.hAlignment, va = p.vAlignment === undefined ? 1 : p.vAlignment;
      sh.cx = ha === 0 ? sh.w / 2 : ha === 2 ? -sh.w / 2 : 0;
      sh.cy = va === 0 ? sh.h / 2 : va === 2 ? -sh.h / 2 : 0;
      sh.shear = (p.stretch || 0) / 100;
      if (p.geomType === 1) sh.outline = p.outlineWidth || 1;
      if (p.doCrop) sh.crop = [p.crop_left, p.crop_right, p.crop_bottom, p.crop_top];   // percent of the size, from the centre
    } else if (/rect/i.test(g.type) && p.bevel) {
      sh.r = [p.bevel, p.bevel, p.bevel, p.bevel];
    }
    return sh;
  }
  function tracePath(sh) {
    if (sh.round) { ctx.ellipse(sh.cx, sh.cy, sh.w / 2, sh.h / 2, 0, 0, 7); return; }
    var w = sh.w / 2, h = sh.h / 2, x = sh.cx, y = sh.cy, k = sh.shear;
    var lim = Math.min(w, h);
    var tr = Math.min(lim, Math.max(0, sh.r[0])), tl = Math.min(lim, Math.max(0, sh.r[1])), bl = Math.min(lim, Math.max(0, sh.r[2])), br = Math.min(lim, Math.max(0, sh.r[3]));
    function P(px, py) { return [x + px + k * py, y + py]; }            // shear for the stretch parameter
    var pts = [], seg = 6;
    function corner(cx, cy, r, a0) {
      if (r <= 0) { pts.push(P(cx, cy)); return; }
      var ox = cx - Math.sign(cx) * r, oy = cy - Math.sign(cy) * r;
      for (var i = 0; i <= seg; i++) { var a = a0 + (Math.PI / 2) * i / seg; pts.push(P(ox + r * Math.cos(a), oy + r * Math.sin(a))); }
    }
    corner(w, h, tr, 0); corner(-w, h, tl, Math.PI / 2); corner(-w, -h, bl, Math.PI); corner(w, -h, br, 1.5 * Math.PI);
    ctx.moveTo(pts[0][0], pts[0][1]);
    for (var i = 1; i < pts.length; i++) ctx.lineTo(pts[i][0], pts[i][1]);
    ctx.closePath();
  }
  function cropClip(sh) {
    if (!sh.crop) return;
    var c = sh.crop, x0 = sh.cx + (c[0] / 100) * sh.w, x1 = sh.cx + (c[1] / 100) * sh.w, y0 = sh.cy + (c[2] / 100) * sh.h, y1 = sh.cy + (c[3] / 100) * sh.h;
    ctx.beginPath(); ctx.rect(Math.min(x0, x1), Math.min(y0, y1), Math.abs(x1 - x0), Math.abs(y1 - y0)); ctx.clip();
  }
  var maskInvert = false;  // user override of the automatic mask mode (see clipTo)
  var hatch = null;
  function hatchPattern() {
    if (hatch) return hatch;
    var c = document.createElement('canvas'); c.width = c.height = 24; var x = c.getContext('2d');
    x.fillStyle = '#777'; x.fillRect(0, 0, 24, 24); x.strokeStyle = '#999'; x.lineWidth = 8;
    x.beginPath(); x.moveTo(-6, 30); x.lineTo(30, -6); x.stroke(); hatch = ctx.createPattern(c, 'repeat'); return hatch;
  }
  function setT(m, f) { var s = [UNIT * f, 0, 0, -UNIT * f, 960, 540], t = mul(s, m); ctx.setTransform(t[0], t[1], t[2], t[3], t[4], t[5]); }

  function evalState(o, t) {
    var st = { pos: o.pos.slice(), rot: o.rot.slice(), scale: o.scale.slice(), center: o.center, alpha: o.alpha === undefined ? 100 : o.alpha };
    o.anims.forEach(function (a) {
      var v = sample(a, t), n = a.name.toLowerCase();
      if (a.prop === 'alpha' || n === 'alpha') { if (typeof v === 'number') st.alpha = v; return; }
      if (n.indexOf('position') === 0) {
        if (a.path.length >= 2 && typeof v === 'number') { var pp = pathPoint(a.path, v); if (pp) st.pos = pp; }
        else if (Array.isArray(v)) st.pos = v.slice(0, 3);
        else if (/x$/.test(n)) st.pos[0] = v; else if (/y$/.test(n)) st.pos[1] = v; else if (/z$/.test(n)) st.pos[2] = v;
      } else if (n.indexOf('scal') === 0) {
        if (Array.isArray(v)) st.scale = v.slice(0, 3); else if (/x$/.test(n)) st.scale[0] = v; else if (/y$/.test(n)) st.scale[1] = v; else st.scale = [v, v, v];
      } else if (n.indexOf('rot') === 0) {
        if (Array.isArray(v)) st.rot = v.slice(0, 3); else if (/x$/.test(n)) st.rot[0] = v; else if (/y$/.test(n)) st.rot[1] = v; else st.rot[2] = v;
      }
    });
    return st;
  }

  // world transforms for every container (needed first, because masks can come later in the tree)
  function layout(o, M, z, zs, t) {
    o.kids.forEach(function (k) {
      var st = evalState(k, t);
      k.M = mul(M, localMatrix(st));
      k.z = z + st.pos[2] * zs; k.zs = zs * st.scale[2];
      k.f = 500 / Math.max(50, 500 - k.z);
      k.a = st.alpha / 100;
      k.visible = k.active && !k.hidden;
      layout(k, k.M, k.z, k.zs, t);
    });
  }
  function shapes(o, acc) {   // rectangles of a mask source and its children
    if (!o.visible) return acc;
    var b = geomBox(o); if (b) acc.push({ M: o.M, f: o.f, sh: b });
    o.kids.forEach(function (k) { shapes(k, acc); }); return acc;
  }
  var items = [];
  function collect(o, alpha, color, clips, crops) {
    o.kids.forEach(function (k) {
      if (!k.visible) return;
      var a = alpha * k.a * (k.matAlpha === undefined ? 1 : k.matAlpha);
      if (a <= 0.001) return;
      var col = k.color || color, cl = clips, cr = crops;
      if (k.maskDst) cl = clips.concat([{ bits: k.maskDst, o: k }]);
      if (k.clipTo) cr = crops.concat([k.clipTo]);
      if (!k.maskSrc) items.push({ o: k, a: a, col: col, clips: cl, crops: cr, z: k.z, i: items.length });
      collect(k, a, col, cl, cr);
    });
  }
  // Masks, as the sample scenes behave (Viz 3 and Viz 5): a target is cut by the sources whose mask bits are exactly
  // the same as its own, and it is hidden where they are. The "Invert masks" box shows it only inside them instead.
  function clipTo(c) {
    var bits = c.bits, sh = [], srcs = all.filter(function (m) { return m.maskSrc && m.maskSrc === bits; });
    var inv = !maskInvert;
    srcs.forEach(function (m) { shapes(m, sh); });
    ctx.beginPath();
    sh.forEach(function (s) { setT(s.M, s.f); tracePath(s.sh); });
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    if (inv) { ctx.rect(-10, -10, 1940, 1100); ctx.clip('evenodd'); } else if (sh.length) ctx.clip(); else { ctx.rect(0, 0, 0, 0); ctx.clip(); }
  }
  function draw() {
    items = []; collect(root, 1, null, [], []);
    items.sort(function (x, y) { return (x.z - y.z) || (x.i - y.i); });
    items.forEach(function (it) {
      ctx.save();
      it.clips.forEach(clipTo);
      it.crops.forEach(function (r) {           // cut to the reference container's shape (even when it is hidden)
        var b = geomBox(r) || (function () { var ib = innerBox(r, true); return ib && { w: ib[1] - ib[0], h: ib[3] - ib[2], cx: (ib[0] + ib[1]) / 2, cy: (ib[2] + ib[3]) / 2, round: false, r: [0, 0, 0, 0], shear: 0 }; })();
        if (!b || !r.M) return;
        setT(r.M, r.f); ctx.beginPath(); tracePath(b); ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.clip();
      });
      ctx.globalAlpha = Math.min(1, it.a);
      drawGeom(it.o, it.col);
      ctx.restore();
    });
  }
  function drawGeom(o, col) {
    var g = o.geom; if (!g) return;
    setT(o.M, o.f);
    var b = geomBox(o), p = g.p || {};
    if (g.type === 'Text') {
      var lines = (o.text !== undefined ? o.text : g.text).split('\n'), size = 55, lh = size * 1.1;
      ctx.transform(1, 0, 0, -1, 0, 0);
      ctx.font = (window.ghBold ? 'bold ' : '') + size + 'px ' + FONT;
      ctx.fillStyle = col ? css(col, 1) : '#fff';
      ctx.textAlign = g.h === 3 ? 'right' : g.h === 2 ? 'center' : 'left';
      ctx.textBaseline = g.v === 3 ? 'middle' : g.v === 1 ? 'top' : 'alphabetic';
      var y0 = g.v === 3 ? -(lines.length - 1) * lh / 2 : 0;
      lines.forEach(function (ln, i) { ctx.fillText(ln, 0, y0 + i * lh); });
      return;
    }
    if (!b) { skipped[g.type] = 1; return; }
    var w = b.w, h = b.h, cx = b.cx, cy = b.cy;
    ctx.save();
    cropClip(b);
    ctx.beginPath(); tracePath(b);
    if (o.texture || g.type === 'Image') {
      if (!o.img && /flare|glow|shine|light|blur|shadow|reflex/i.test(o.name)) { ctx.restore(); return; }
      if (o.img && o.img.complete) { ctx.clip(); ctx.transform(1, 0, 0, -1, 0, 0); ctx.drawImage(o.img, cx - w / 2, -cy - h / 2, w, h); }
      else {
        ctx.fillStyle = hatchPattern(); ctx.fill();
        ctx.transform(1, 0, 0, -1, 0, 0); ctx.fillStyle = 'rgba(255,255,255,.35)'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
        ctx.font = Math.max(4, Math.min(h * 0.18, w / Math.max(4, o.name.length) * 1.6)) + 'px Arial'; ctx.fillText(o.name, cx, -cy);
      }
      ctx.restore(); return;
    }
    if (p.use_vertexcolors && p.upperleft) {
      var gr = ctx.createLinearGradient(0, cy + h / 2, 0, cy - h / 2);
      gr.addColorStop(0, rgba8(p.upperleft)); gr.addColorStop(1, rgba8(p.lowerleft || p.upperleft));
      if (b.outline) ctx.strokeStyle = gr; else ctx.fillStyle = gr;
    } else { var cs = col ? css(col, 1) : '#fff'; if (b.outline) ctx.strokeStyle = cs; else ctx.fillStyle = cs; }
    if (b.outline) { ctx.lineWidth = b.outline; ctx.stroke(); } else ctx.fill();
    ctx.restore();
  }
  function render(t) {
    ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.clearRect(0, 0, 1920, 1080);
    runPlugins();
    layout(root, [1, 0, 0, 1, 0, 0], 0, 1, t);
    draw();
  }

  // ---------- animation ----------
  var duration = 0;
  all.forEach(function (o) { o.anims.forEach(function (a) { a.keys.sort(function (x, y) { return x.t - y.t; }); duration = Math.max(duration, a.keys[a.keys.length - 1].t); }); });
  stops.forEach(function (s) { duration = Math.max(duration, s); });
  function ease(x) { return x * x * (3 - 2 * x); }
  function lerp(a, b, x) { if (typeof a === 'number') return a + (b - a) * x; return a.map(function (v, i) { return v + ((b[i] === undefined ? v : b[i]) - v) * x; }); }
  function sample(a, t) {
    var k = a.keys;
    if (t <= k[0].t) return k[0].v;
    if (t >= k[k.length - 1].t) return k[k.length - 1].v;
    for (var i = 0; i < k.length - 1; i++) if (t >= k[i].t && t <= k[i + 1].t) return lerp(k[i].v, k[i + 1].v, ease((t - k[i].t) / Math.max(1e-9, k[i + 1].t - k[i].t)));
    return k[k.length - 1].v;
  }
  function pathPoint(pts, pct) {
    var seg = [], tot = 0, i;
    for (i = 0; i < pts.length - 1; i++) { var d = Math.hypot(pts[i + 1][0] - pts[i][0], pts[i + 1][1] - pts[i][1], pts[i + 1][2] - pts[i][2]); seg.push(d); tot += d; }
    var want = tot * Math.max(0, Math.min(100, pct)) / 100;
    for (i = 0; i < seg.length; i++) { if (want <= seg[i] || i === seg.length - 1) return lerp(pts[i], pts[i + 1], seg[i] ? Math.min(1, want / seg[i]) : 0); want -= seg[i]; }
    return pts[0];
  }
  function apply(t) { render(t); }

  // ---------- form (control plugins) ----------
  var form = document.getElementById('form'), fields = [];
  var byKey = {};
  all.forEach(function (o) {
    o.funcs.forEach(function (f) {
      var id = f.p.field_id, label = f.p.description || o.name, kind = null;
      if (f.type === 'ControlText') kind = 'text';
      else if (f.type === 'ControlKeyframe') kind = 'number';
      else if (f.type === 'ControlImage') kind = 'image';
      else if (f.type === 'ControlContainer' && f.p.active === true) { kind = 'visible'; label = (label || o.name) + ' – visible'; }
      if (!kind) return;
      var key = kind + '|' + (id || o.name);
      if (byKey[key]) { byKey[key].os.push(o); return; }
      byKey[key] = { id: id, label: label, kind: kind, o: o, os: [o] }; fields.push(byKey[key]);
    });
  });
  fields.sort(function (a, b) { return String(a.id).localeCompare(String(b.id), 'en', { numeric: true }); });
  if (!fields.length) form.innerHTML = '<p class="note">This scene has no control fields.</p>';
  function findText(o) { if (o.geom && o.geom.type === 'Text') return o; for (var i = 0; i < o.kids.length; i++) { var t = findText(o.kids[i]); if (t) return t; } return null; }
  function findTex(o) { if (o.texture || (o.geom && o.geom.type === 'Image')) return o; for (var i = 0; i < o.kids.length; i++) { var t = findTex(o.kids[i]); if (t) return t; } return null; }
  fields.forEach(function (fd) {
    var l = document.createElement('label'); l.className = 'f';
    l.innerHTML = '<span>' + (fd.id ? fd.id + ' · ' : '') + fd.label + '</span>';
    var inp;
    if (fd.kind === 'text') {
      var tos = fd.os.map(findText).filter(Boolean), to = tos[0];
      inp = document.createElement('textarea'); inp.rows = Math.max(1, Math.min(4, ((to && to.geom.text) || '').split('\n').length));
      inp.value = to ? (to.text !== undefined ? to.text : to.geom.text) : '';
      inp.oninput = function () { fd.os.forEach(function (x) { setText(x, inp.value); }); apply(cur); };
    } else if (fd.kind === 'number') {
      inp = document.createElement('input'); inp.type = 'text'; inp.inputMode = 'decimal';
      inp.value = textOf(fd.o) || '';
      inp.oninput = function () { fd.os.forEach(function (x) { x.rawValue = num(inp.value); setText(x, plug(x, 'Advanced_Counter') ? counterFormat(x, inp.value) : inp.value); }); apply(cur); };
    } else if (fd.kind === 'image') {
      var ios = fd.os.map(findTex).filter(Boolean);
      inp = document.createElement('input'); inp.type = 'file'; inp.accept = 'image/*';
      inp.onchange = function () {
        var file = inp.files[0]; if (!file || !ios.length) return;
        var img = new Image(); img.onload = function () { ios.forEach(function (x) { x.img = img; }); apply(cur); }; img.src = URL.createObjectURL(file);
      };
    } else {
      inp = document.createElement('input'); inp.type = 'checkbox'; inp.checked = true; l.style.display = 'flex'; l.style.gap = '8px';
      inp.onchange = function () { fd.os.forEach(function (x) { x.hidden = !inp.checked; }); apply(cur); };
    }
    l.appendChild(inp); form.appendChild(l);
  });

  // ---------- Viz function plug-ins (emulated) and Viz scripts ported to JavaScript ----------
  function plug(o, type) { for (var i = 0; i < o.funcs.length; i++) if (o.funcs[i].type === type) return o.funcs[i].p; return null; }
  function byName(n) { for (var i = 0; i < all.length; i++) if (all[i].name === n) return all[i]; return null; }
  function textOf(o) { var t = o && findText(o); return t ? (t.text !== undefined ? t.text : t.geom.text) : ''; }
  function num(s) { var v = parseFloat(String(s).replace(/\s/g, '').replace(',', '.')); return isNaN(v) ? 0 : v; }
  var textHooks = {};                         // container name -> [handlers] (RegisterTextChangedCallback)
  function onText(name, fn) { (textHooks[name] = textHooks[name] || []).push(fn); }
  function setText(o, v, quiet) {
    var t = o && findText(o); if (!t) return;
    t.text = v;
    if (quiet) return;
    var names = [o.name]; if (t !== o) names.push(t.name);
    names.forEach(function (n) { (textHooks[n] || []).forEach(function (fn) { fn(o); }); });
  }
  // Advanced_Counter: number formatting with a mask (#####.##) and a decimal separator
  function counterFormat(o, value) {
    var p = plug(o, 'Advanced_Counter'); if (!p) return String(value);
    var m = String(p.inpmask || '').split('.'), dec = m.length > 1 ? m[1].length : 0;
    var s = num(value).toFixed(dec);
    return p.decsep === 1 ? s.replace('.', ',') : s;
  }
  function reformatCounter(o) { var p = plug(o, 'Advanced_Counter'); if (!p) return; setText(o, counterFormat(o, num(o.rawValue !== undefined ? o.rawValue : textOf(o))), false); }

  var anims = [];                             // running parameter animations (Bar plug-in)
  function animateTo(o, key, target, dur) {
    var from = o[key] === undefined ? target : o[key];
    anims = anims.filter(function (a) { return !(a.o === o && a.key === key); });
    anims.push({ o: o, key: key, from: from, to: target, t0: performance.now(), dur: dur });
    if (!playing) requestAnimationFrame(stepAnims);
  }
  function stepAnims(now) {
    var live = false;
    anims.forEach(function (a) { var x = Math.min(1, (now - a.t0) / a.dur); a.o[a.key] = a.from + (a.to - a.from) * ease(x); if (x < 1) live = true; });
    anims = anims.filter(function (a) { return now - a.t0 < a.dur; });
    apply(cur);
    if (live && !playing) requestAnimationFrame(stepAnims);
  }

  function hasGeom(o) { return !!o.geom || o.kids.some(hasGeom); }
  // Runs before each frame: plug-ins that move or show/hide containers
  function runPlugins() {
    runPerField();
    all.forEach(function (o) {
      var omo = plug(o, 'Omo');
      if (omo) o.kids.forEach(function (k, i) { if (i > 0) k.active = omo.keep_vis ? i <= omo.vis_con : i === omo.vis_con; });
      var grid = plug(o, 'Grid');
      if (grid) o.kids.forEach(function (k, i) {
        var cols = Math.max(1, grid.num_col || 1);
        k.pos[0] = (i % cols) * (grid.col_offset || 0); k.pos[1] = -Math.floor(i / cols) * (grid.row_offset || 0);
      });
      var bv = plug(o, 'BarValues');
      if (bv) {
        var bars = []; (function f(n) { n.kids.forEach(function (k) { if (plug(k, 'Bar')) bars.push(k); f(k); }); })(o);
        bars.forEach(function (b, i) {
          var v = bv['Bar_Value__' + (i + 1)] || 0, bp = plug(b, 'Bar');
          if (bv.Scale) v = v / 100 * (bv.BarMax || bp.BarMax || 100);
          var r = Math.max(0, Math.min(1, (v - (bp.BarMin || 0)) / Math.max(1e-9, (bp.BarMax || 100) - (bp.BarMin || 0))));
          var target = (bp.ObjMin || 0) + ((bp.ObjMax || 1) - (bp.ObjMin || 0)) * r;
          if (b.barTarget !== target) { b.barTarget = target; animateTo(b, 'barNow', target, 500); }
        });
      }
      var bp2 = plug(o, 'Bar');
      if (bp2 && o.barNow !== undefined) { var ax = bp2.ScaleParam === 1 ? 0 : bp2.ScaleParam === 3 ? 2 : 1; o.scale[ax] = Math.max(1e-6, o.barNow); }
    });
    // bottom-up so that children are placed before their parents are justified
    all.slice().reverse().forEach(function (o) {
      var af = plug(o, 'Autofollow');
      if (af && o.parent && af.REFER_CONTAINER === '0000') {
        var sib = o.parent.kids, i = sib.indexOf(o), prev = null;
        for (var j = i - 1; j >= 0; j--) if (sib[j].active && !sib[j].hidden) { prev = sib[j]; break; }
        var d = af.DIRECTION === 0 ? 0 : 1, pb = prev && outerBox(prev), mb = innerBox(o);
        if (pb && mb) o.pos[d] = pb[d * 2 + 1] + (af.DEFAULT_DISTANCE || 0) - mb[d * 2] * o.scale[d];
      }
      var ju = plug(o, 'Justifier');
      if (ju && ju.aox === 3) {                       // centre the container's content on its origin (x)
        var ib = innerBox(o, true);
        if (ib) o.pos[0] = -(ib[0] + ib[1]) / 2 * o.scale[0];
      }
    });
  }
  // Bounding boxes ([x0, x1, y0, y1]) ignoring rotation: innerBox in the container's own space, outerBox in its parent's
  function textBox(o) {
    var g = o.geom, txt = o.text !== undefined ? o.text : g.text || '', size = 55;
    ctx.save(); ctx.font = (window.ghBold ? 'bold ' : '') + size + 'px ' + FONT;
    var w = Math.max.apply(null, txt.split('\n').map(function (l) { return ctx.measureText(l).width; })); ctx.restore();
    var x0 = g.h === 3 ? -w : g.h === 2 ? -w / 2 : 0;
    var y0 = g.v === 3 ? -size * 0.36 : g.v === 1 ? -size * 0.72 : 0;
    return [x0, x0 + w, y0, y0 + size * 0.72];
  }
  function innerBox(o, kidsOnly) {
    var bx = null;
    function add(b) { if (!b) return; if (!bx) bx = b.slice(); else { bx[0] = Math.min(bx[0], b[0]); bx[1] = Math.max(bx[1], b[1]); bx[2] = Math.min(bx[2], b[2]); bx[3] = Math.max(bx[3], b[3]); } }
    if (o.geom && !kidsOnly) {
      if (o.geom.type === 'Text') add(textBox(o));
      else { var g = geomBox(o); if (g) add([g.cx - g.w / 2, g.cx + g.w / 2, g.cy - g.h / 2, g.cy + g.h / 2]); }
    }
    o.kids.forEach(function (k) { if (k.active && !k.hidden) add(outerBox(k)); });
    return bx;
  }
  function outerBox(o) {
    var b = innerBox(o); if (!b) return null;
    var sx = o.scale[0], sy = o.scale[1], cx = (o.center && o.center[0]) || 0, cy = (o.center && o.center[1]) || 0;
    return [o.pos[0] + (b[0] - cx) * sx, o.pos[0] + (b[1] - cx) * sx, o.pos[1] + (b[2] - cy) * sy, o.pos[1] + (b[3] - cy) * sy];
  }

  // ---------- Viz Script interpreter: runs the scene's own scripts in the page ----------
  // Supports the VBScript-like Viz Script language: dim, if/elseif/else, for/next, do/loop, while/wend,
  // select case, sub/function, string methods, and the scene objects scripts use most
  // (Scene.FindContainer, containers, geometry text, plug-in parameters, position/scaling/rotation/alpha).
  var VS = (function () {
    // ---- tokenizer ----
    function tokenize(src) {
      var toks = [], i = 0, n = src.length, line = 1;
      function push(t, v) { toks.push({ t: t, v: v, line: line }); }
      while (i < n) {
        var c = src[i];
        if (c === '\r') { i++; continue; }
        if (c === '\n') { push('nl'); line++; i++; continue; }
        if (c === ' ' || c === '\t' || c === '﻿' || c === ' ') { i++; continue; }
        if (c === "'") { while (i < n && src[i] !== '\n') i++; continue; }
        if (c === '_' && /^_[ \t]*\r?\n/.test(src.substr(i, 4))) { i = src.indexOf('\n', i) + 1; line++; continue; }
        if (c === ':') { push('nl'); i++; continue; }
        if (c === '"') {
          var s = ''; i++;
          while (i < n) { if (src[i] === '"') { if (src[i + 1] === '"') { s += '"'; i += 2; continue; } i++; break; } if (src[i] === '\n') break; s += src[i++]; }
          push('str', s); continue;
        }
        var m = /^(\d+\.?\d*(?:[eE][-+]?\d+)?|\.\d+(?:[eE][-+]?\d+)?)/.exec(src.substr(i, 40));
        if (m && !(c === '.' && toks.length && /^(id|\)|\])$/.test(toks[toks.length - 1].t === 'op' ? toks[toks.length - 1].v : toks[toks.length - 1].t))) { push('num', parseFloat(m[1])); i += m[1].length; continue; }
        m = /^[A-Za-z_À-ɏ][\wÀ-ɏ]*/.exec(src.substr(i, 200));
        if (m) {
          var w = m[0].toLowerCase();
          if (w === 'rem') { while (i < n && src[i] !== '\n') i++; continue; }
          push('id', w); toks[toks.length - 1].raw = m[0]; i += m[0].length; continue;
        }
        var two = src.substr(i, 2);
        if (two === '<>' || two === '<=' || two === '>=' || two === '==' || two === '!=') { push('op', two === '==' ? '=' : two === '!=' ? '<>' : two); i += 2; continue; }
        if ('+-*/\\^&=<>(),.[]'.indexOf(c) >= 0) { push('op', c); i++; continue; }
        i++;  // unknown character: skip
      }
      push('nl'); push('eof');
      return toks;
    }

    // ---- parser ----
    function parse(src) {
      var T = tokenize(src), p = 0, subs = {};
      function peek(o) { return T[p + (o || 0)]; }
      function isId(v, o) { var t = peek(o); return t.t === 'id' && t.v === v; }
      function isOp(v, o) { var t = peek(o); return t.t === 'op' && t.v === v; }
      function next() { return T[p++]; }
      function err(msg) { throw new Error('line ' + peek().line + ': ' + msg); }
      function expectId(v) { if (!isId(v)) err('expected ' + v); return next(); }
      function expectOp(v) { if (!isOp(v)) err('expected ' + v); return next(); }
      function skipNl() { while (peek().t === 'nl') p++; }
      function eol() { if (peek().t !== 'nl' && peek().t !== 'eof') err('unexpected ' + (peek().v || peek().t)); while (peek().t === 'nl') p++; }
      function atEnd() { return peek().t === 'nl' || peek().t === 'eof' || isId('else'); }
      function skipType() {          // "as Integer", "as Array[String]"
        if (!isId('as')) return null;
        next(); var ty = peek().v; var depth = 0;
        while (peek().t !== 'eof') {
          if (peek().t === 'nl' && depth === 0) break;
          if (depth === 0 && (isOp(',') || isOp('=') || isOp(')'))) break;
          if (isOp('[')) depth++; if (isOp(']')) depth--;
          next();
        }
        return ty;
      }
      // expressions
      function expr() { return binary(0); }
      var LEVELS = [['or'], ['xor'], ['and'], ['not'], ['=', '<>', '<', '>', '<=', '>=', 'is'], ['&'], ['+', '-'], ['mod'], ['\\'], ['*', '/'], ['neg'], ['^']];
      function binary(lv) {
        if (lv >= LEVELS.length) return postfix();
        var ops = LEVELS[lv];
        if (ops[0] === 'not') { if (isId('not')) { next(); return { t: 'un', op: 'not', a: binary(lv) }; } return binary(lv + 1); }
        if (ops[0] === 'neg') { if (isOp('-')) { next(); return { t: 'un', op: '-', a: binary(lv) }; } if (isOp('+')) { next(); return binary(lv); } return binary(lv + 1); }
        var a = binary(lv + 1);
        for (;;) {
          var t = peek(), op = (t.t === 'op' || t.t === 'id') && ops.indexOf(t.v) >= 0 ? t.v : null;
          if (!op) return a;
          next(); a = { t: 'bin', op: op, a: a, b: binary(lv + 1) };
        }
      }
      function args(close) {
        var list = [];
        if (isOp(close)) { next(); return list; }
        for (;;) { list.push(expr()); if (isOp(',')) { next(); continue; } expectOp(close); return list; }
      }
      function primary() {
        var t = next();
        if (t.t === 'num') return { t: 'lit', v: t.v };
        if (t.t === 'str') return { t: 'lit', v: t.v };
        if (t.t === 'op' && t.v === '(') {
          var e = expr();
          if (isOp(',')) { var items = [e]; while (isOp(',')) { next(); items.push(expr()); } expectOp(')'); return { t: 'tuple', items: items }; }
          expectOp(')'); return e;
        }
        if (t.t === 'op' && t.v === '.') { var nm = next(); return { t: 'mem', obj: { t: 'with' }, name: nm.v }; }
        if (t.t === 'id') {
          if (t.v === 'true') return { t: 'lit', v: true };
          if (t.v === 'false') return { t: 'lit', v: false };
          if (t.v === 'null' || t.v === 'nothing') return { t: 'lit', v: null };
          if (t.v === 'new') { var ty = next(); while (isOp('[')) { next(); while (!isOp(']')) next(); next(); } return { t: 'new', ty: ty.v }; }
          return { t: 'id', name: t.v };
        }
        err('unexpected ' + (t.v || t.t));
      }
      function postfix() {
        var e = primary();
        for (;;) {
          if (isOp('.')) { next(); var nm = next(); if (nm.t !== 'id') err('expected a name after .'); e = { t: 'mem', obj: e, name: nm.v }; continue; }
          if (isOp('(')) { next(); e = { t: 'call', f: e, args: args(')') }; continue; }
          if (isOp('[')) { next(); e = { t: 'idx', obj: e, args: args(']') }; continue; }
          return e;
        }
      }
      // statements
      function block(enders) {
        var body = [];
        for (;;) {
          skipNl();
          if (peek().t === 'eof') return body;
          for (var k = 0; k < enders.length; k++) {
            var en = enders[k].split(' ');
            var ok = en.every(function (w, j) { return isId(w, j); });
            if (ok) return body;
          }
          var s = statement(); if (s) body.push(s);
        }
      }
      function endPair(w) { expectId('end'); expectId(w); }
      function statement() {
        var t = peek();
        if (t.t !== 'id') { var e0 = postfix(); return exprStatement(e0); }
        switch (t.v) {
          case 'dim': case 'const': case 'static': case 'private': case 'public': case 'global': {
            next(); if (isId('dim')) next();
            var decls = [];
            do {
              if (isOp(',')) next();
              var nm = next().v, size = null;
              if (isOp('[') || isOp('(')) { var cl = isOp('[') ? ']' : ')'; next(); size = args(cl); }
              var ty = skipType(), init = null;
              if (isOp('=')) { next(); init = expr(); }
              decls.push({ name: nm, ty: ty, init: init, size: size });
            } while (isOp(','));
            eol(); return { t: 'dim', decls: decls };
          }
          case 'set': case 'let': next(); return statement();
          case 'call': next(); var ce = postfix(); eol(); return { t: 'expr', e: ce.t === 'call' ? ce : { t: 'call', f: ce, args: [] } };
          case 'if': {
            next(); var cond = expr(); expectId('then');
            if (peek().t !== 'nl') {           // single-line if
              var th = [simple()], el = [];
              if (isId('else')) { next(); el.push(simple()); }
              if (isId('end') && isId('if', 1)) { next(); next(); }
              eol(); return { t: 'if', arms: [{ c: cond, b: th }], els: el };
            }
            eol();
            var arms = [{ c: cond, b: block(['elseif', 'else', 'end if']) }], els = null;
            for (;;) {
              if (isId('elseif') || (isId('else') && isId('if', 1))) { if (isId('else')) next(); next(); var c2 = expr(); expectId('then'); eol(); arms.push({ c: c2, b: block(['elseif', 'else', 'end if']) }); continue; }
              if (isId('else')) { next(); eol(); els = block(['end if']); }
              endPair('if'); eol(); return { t: 'if', arms: arms, els: els };
            }
          }
          case 'for': {
            next();
            if (isId('each')) { next(); var v0 = next().v; skipType(); expectId('in'); var coll = expr(); eol(); var bd = block(['next']); expectId('next'); if (peek().t === 'id') next(); eol(); return { t: 'foreach', v: v0, coll: coll, body: bd }; }
            var v = next().v; skipType(); expectOp('='); var from = expr(); expectId('to'); var to = expr(), step = null;
            if (isId('step')) { next(); step = expr(); }
            eol(); var body = block(['next']); expectId('next'); if (peek().t === 'id') next(); eol();
            return { t: 'for', v: v, from: from, to: to, step: step, body: body };
          }
          case 'do': {
            next(); var pre = null, until = false;
            if (isId('while') || isId('until')) { until = next().v === 'until'; pre = expr(); }
            eol(); var b = block(['loop']); expectId('loop'); var post = null, puntil = false;
            if (isId('while') || isId('until')) { puntil = next().v === 'until'; post = expr(); }
            eol(); return { t: 'do', pre: pre, until: until, post: post, puntil: puntil, body: b };
          }
          case 'while': {
            next(); var wc = expr(); eol(); var wb = block(['wend', 'end while', 'loop']);
            if (isId('end')) { next(); next(); } else next(); eol();
            return { t: 'do', pre: wc, until: false, body: wb };
          }
          case 'select': {
            next(); expectId('case'); var sel = expr(); eol(); var cases = [], def = null;
            skipNl();
            while (isId('case')) {
              next();
              if (isId('else')) { next(); eol(); def = block(['case', 'end select']); continue; }
              var tests = [];
              do {
                if (isOp(',')) next();
                if (isId('is')) { next(); var op = next().v; tests.push({ op: op, e: expr() }); }
                else { var a = expr(); if (isId('to')) { next(); tests.push({ lo: a, hi: expr() }); } else tests.push({ op: '=', e: a }); }
              } while (isOp(','));
              eol(); cases.push({ tests: tests, body: block(['case', 'end select']) });
            }
            endPair('select'); eol(); return { t: 'select', e: sel, cases: cases, def: def };
          }
          case 'exit': next(); var what = next().v; eol(); return { t: 'exit', what: what };
          case 'return': next(); var rv = atEnd() ? null : expr(); eol(); return { t: 'return', e: rv };
          case 'sub': case 'function': {
            var isF = next().v === 'function', name = next().v, prm = [];
            if (isOp('(')) {
              next();
              while (!isOp(')')) {
                if (isOp(',')) { next(); continue; }
                var byref = false;
                if (isId('byref')) { next(); byref = true; } else if (isId('byval')) next();
                var pn = next().v; skipType(); if (isOp('=')) { next(); expr(); }
                prm.push({ name: pn, byref: byref });
              }
              next();
            }
            skipType(); eol();
            var sb = block([isF ? 'end function' : 'end sub']); endPair(isF ? 'function' : 'sub'); eol();
            subs[name] = { name: name, params: prm, body: sb, isF: isF };
            return null;
          }
          case 'structure': case 'class': { while (!(isId('end') && (isId('structure', 1) || isId('class', 1)))) { if (peek().t === 'eof') return null; next(); } next(); next(); eol(); return null; }
          case 'with': { next(); var we = expr(); eol(); var wbd = block(['end with']); endPair('with'); eol(); return { t: 'with', e: we, body: wbd }; }
          case 'end': err('unexpected end ' + (peek(1).v || ''));
        }
        return simple(true);
      }
      function simple(needEol) {          // assignment or call
        var e = postfix(), s = exprStatement(e, true);
        if (needEol) eol();
        return s;
      }
      function exprStatement(e, noEol) {
        var s;
        if (isOp('=')) { next(); s = { t: 'set', lhs: e, e: expr() }; }
        else if (atEnd()) s = { t: 'expr', e: e.t === 'call' ? e : { t: 'call', f: e, args: [], bare: true } };
        else {                             // call without parentheses: Foo a, b
          var a = [expr()]; while (isOp(',')) { next(); a.push(expr()); }
          s = { t: 'expr', e: { t: 'call', f: e, args: a } };
        }
        if (!noEol) eol();
        return s;
      }
      var main = block([]);
      return { main: main, subs: subs };
    }

    // ---- values ----
    function VArray(n) { this.items = []; for (var i = 0; i < (n || 0); i++) this.items.push(null); }
    function Vec(get, set) { this.get3 = get; this.set3 = set; }
    function num(v) {
      if (typeof v === 'number') return v;
      if (typeof v === 'boolean') return v ? 1 : 0;
      if (v === null || v === undefined) return 0;
      var f = parseFloat(String(v).trim()); return isNaN(f) ? 0 : f;
    }
    function str(v) {
      if (v === null || v === undefined) return '';
      if (typeof v === 'boolean') return v ? 'TRUE' : 'FALSE';
      if (typeof v === 'number') return Number.isInteger(v) ? String(v) : String(+v.toFixed(6));
      if (v instanceof Vec) return v.get3().join(' ');
      return String(v);
    }
    function isNumLike(v) { return typeof v === 'number' || typeof v === 'boolean' || (typeof v === 'string' && v.trim() !== '' && !isNaN(+v)); }
    function eq(a, b) {
      if (typeof a === 'string' && typeof b === 'string') return a === b;
      if (isNumLike(a) && isNumLike(b)) return num(a) === num(b);
      if (a === null || b === null) return a === b;
      return a === b || str(a) === str(b);
    }
    function cmp(a, b) {
      if (typeof a === 'string' && typeof b === 'string') return a < b ? -1 : a > b ? 1 : 0;
      var x = num(a), y = num(b); return x < y ? -1 : x > y ? 1 : 0;
    }
    function truthy(v) { return typeof v === 'string' ? v !== '' && v.toLowerCase() !== 'false' && v !== '0' : !!v; }

    // ---- string methods (Viz strings are mutable: mutating methods write the result back) ----
    var STR = {
      length: function (s) { return s.length; },
      find: function (s, a) { return s.indexOf(str(a[0]), a[1] ? num(a[1]) : 0); },
      findlastof: function (s, a) { return s.lastIndexOf(str(a[0])); },
      findfirstof: function (s, a) { var set = str(a[0]), b = -1; for (var i = 0; i < s.length; i++) if (set.indexOf(s[i]) >= 0) { b = i; break; } return b; },
      getchar: function (s, a) { return s.charAt(num(a[0])); },
      getsubstring: function (s, a) { return s.substr(num(a[0]), a.length > 1 ? num(a[1]) : undefined); },
      left: function (s, a) { return s.substr(0, num(a[0])); },
      right: function (s, a) { return s.substr(Math.max(0, s.length - num(a[0]))); },
      mid: function (s, a) { return s.substr(num(a[0]), a.length > 1 ? num(a[1]) : undefined); },
      startswith: function (s, a) { return s.indexOf(str(a[0])) === 0; },
      endswith: function (s, a) { var x = str(a[0]); return s.slice(-x.length) === x; },
      match: function (s, a) { try { return new RegExp('^' + str(a[0]).replace(/[.+^${}()|\\]/g, '\\$&').replace(/\*/g, '.*').replace(/\?/g, '.') + '$').test(s); } catch (e) { return false; } },
      isempty: function (s) { return s === ''; },
      tostring: function (s) { return s; },
      split: function (s, a, self) { var parts = s.split(str(a[0]) || ' '); if (a[1] instanceof VArray) a[1].items = parts; return parts.length; }
    };
    var STRMUT = {
      replacechar: function (s, a) { var i = num(a[0]); return i < 0 || i >= s.length ? s : s.substr(0, i) + str(a[1]).charAt(0) + s.substr(i + 1); },
      substitute: function (s, a) { var f = str(a[0]), r = str(a[1]); if (!f) return s; return a[2] === false ? s.replace(f, r) : s.split(f).join(r); },
      replace: function (s, a) { return STRMUT.substitute(s, a); },
      trim: function (s) { return s.trim(); }, trimleft: function (s) { return s.replace(/^\s+/, ''); }, trimright: function (s) { return s.replace(/\s+$/, ''); },
      makeupper: function (s) { return s.toUpperCase(); }, makelower: function (s) { return s.toLowerCase(); },
      toupper: function (s) { return s.toUpperCase(); }, tolower: function (s) { return s.toLowerCase(); },
      upcase: function (s) { return s.toUpperCase(); }, downcase: function (s) { return s.toLowerCase(); },
      insert: function (s, a) { var i = num(a[0]); return s.substr(0, i) + str(a[1]) + s.substr(i); },
      erase: function (s, a) { var i = num(a[0]); return s.substr(0, i) + s.substr(i + (a.length > 1 ? num(a[1]) : s.length)); },
      append: function (s, a) { return s + str(a[0]); },
      set: function (s, a) { return str(a[0]); },
      clear: function () { return ''; }
    };

    // ---- built-in functions ----
    var rnd = Math.random;
    var BUILTIN = {
      cint: function (a) { var v = a[0]; return typeof v === 'string' ? (parseInt(v, 10) || 0) : Math.round(num(v)); },
      cdbl: function (a) { return num(a[0]); }, cstr: function (a) { return str(a[0]); }, cbool: function (a) { return truthy(a[0]); },
      cfloat: function (a) { return num(a[0]); },
      max: function (a) { return Math.max.apply(null, a.map(num)); }, min: function (a) { return Math.min.apply(null, a.map(num)); },
      abs: function (a) { return Math.abs(num(a[0])); }, sqrt: function (a) { return Math.sqrt(num(a[0])); }, sqr: function (a) { return num(a[0]) * num(a[0]); },
      sin: function (a) { return Math.sin(num(a[0]) * Math.PI / 180); }, cos: function (a) { return Math.cos(num(a[0]) * Math.PI / 180); },
      tan: function (a) { return Math.tan(num(a[0]) * Math.PI / 180); }, atan: function (a) { return Math.atan(num(a[0])) * 180 / Math.PI; },
      round: function (a) { var d = a.length > 1 ? Math.pow(10, num(a[1])) : 1; return Math.round(num(a[0]) * d) / d; },
      floor: function (a) { return Math.floor(num(a[0])); }, ceil: function (a) { return Math.ceil(num(a[0])); }, int: function (a) { return Math.floor(num(a[0])); },
      fix: function (a) { return Math.trunc(num(a[0])); }, sgn: function (a) { return Math.sign(num(a[0])); },
      random: function (a) { return a.length ? Math.floor(rnd() * num(a[0])) : rnd(); }, rnd: function () { return rnd(); },
      doubletostring: function (a) { return num(a[0]).toFixed(a.length > 1 ? num(a[1]) : 2); },
      inttostring: function (a) { return String(Math.round(num(a[0]))); },
      len: function (a) { return str(a[0]).length; }, ucase: function (a) { return str(a[0]).toUpperCase(); }, lcase: function (a) { return str(a[0]).toLowerCase(); },
      left: function (a) { return str(a[0]).substr(0, num(a[1])); }, right: function (a) { var s = str(a[0]); return s.substr(Math.max(0, s.length - num(a[1]))); },
      mid: function (a) { return str(a[0]).substr(num(a[1]) - 1, a.length > 2 ? num(a[2]) : undefined); },
      instr: function (a) { return str(a[0]).indexOf(str(a[1])) + 1; }, trim: function (a) { return str(a[0]).trim(); },
      asc: function (a) { return str(a[0]).charCodeAt(0) || 0; }, chr: function (a) { return String.fromCharCode(num(a[0])); },
      isnumeric: function (a) { return isNumLike(a[0]); }, isempty: function (a) { return a[0] === null || a[0] === ''; },
      vertex: function (a) { var v = [num(a[0]), num(a[1]), num(a[2])]; return new Vec(function () { return v; }, function (x) { v = x; }); }
    };

    // ---- scene objects ----
    function lower(n) { return String(n).toLowerCase(); }
    function vec3(arr, onSet) {
      return new Vec(function () { return arr.slice(0, 3); }, function (v) { for (var i = 0; i < 3; i++) arr[i] = v[i]; if (onSet) onSet(); });
    }
    function toVec(v) { if (v instanceof Vec) return v.get3(); if (Array.isArray(v)) return v.map(num); var n = num(v); return [n, n, n]; }

    function make(env) {           // env: hooks to the page renderer
      var wrapCache = new Map();
      function C(o) {
        if (!o) return null;
        if (wrapCache.has(o)) return wrapCache.get(o);
        var w = { kind: 'container', o: o }; wrapCache.set(o, w); return w;
      }
      function plugin(o, type, p) { return { kind: 'plugin', o: o, type: type, p: p }; }
      function geo(o) { return { kind: 'geometry', o: o }; }
      function findIn(list, name) {
        for (var i = 0; i < list.length; i++) if (list[i].name === name) return list[i];
        var l = lower(name); for (i = 0; i < list.length; i++) if (lower(list[i].name) === l) return list[i];
        return null;
      }
      function subTree(o) { var r = []; (function f(n) { n.kids.forEach(function (k) { r.push(k); f(k); }); })(o); return r; }
      var scene = { kind: 'scene' };

      function getMember(obj, name, owner) {
        if (obj === null || obj === undefined) throw new Error('cannot read .' + name + ' of an empty object');
        if (typeof obj === 'string') {
          if (STR[name]) return STR[name](obj, []);
          throw new Error('unknown string property ' + name);
        }
        if (obj instanceof Vec) {
          var v = obj.get3();
          if (name === 'x') return v[0]; if (name === 'y') return v[1]; if (name === 'z') return v[2]; if (name === 'xyz') return obj;
          throw new Error('unknown vector property ' + name);
        }
        if (obj instanceof VArray) { if (name === 'size' || name === 'ubound' || name === 'length') return obj.items.length; throw new Error('unknown array property ' + name); }
        switch (obj.kind) {
          case 'scene':
            if (name === 'stage') return { kind: 'stage' };
            break;
          case 'container': {
            var o = obj.o;
            switch (name) {
              case 'name': return o.name;
              case 'active': return !!o.active;
              case 'visible': return !!o.active && !o.hidden;
              case 'position': return vec3(o.pos, env.changed);
              case 'scaling': return vec3(o.scale, env.changed);
              case 'rotation': return vec3(o.rot, env.changed);
              case 'center': return vec3(o.center, env.changed);
              case 'alpha': return { kind: 'alpha', o: o };
              case 'geometry': return geo(o);
              case 'material': return { kind: 'material', o: o };
              case 'childcontainer': return C(o.kids[0]);
              case 'parentcontainer': return o.parent && o.parent.name !== 'scene' ? C(o.parent) : null;
              case 'nextcontainer': case 'previouscontainer': {
                var sib = o.parent ? o.parent.kids : [], i = sib.indexOf(o);
                return C(sib[name === 'nextcontainer' ? i + 1 : i - 1]);
              }
              case 'childcontainercount': return o.kids.length;
              case 'vispath': case 'path': return o.name;
            }
            break;
          }
          case 'geometry': {
            var go = obj.o;
            if (name === 'text') return env.textOf(go);
            if (name === 'plugininstance') return go.geom ? plugin(go, go.geom.type, go.geom.p || (go.geom.p = {})) : null;
            if (name === 'type') return go.geom ? go.geom.type : '';
            break;
          }
          case 'alpha': if (name === 'value') return obj.o.alpha === undefined ? 100 : obj.o.alpha; break;
          case 'material':
            if (name === 'color') return obj.o.color ? vec3(obj.o.color, env.changed) : null;
            if (name === 'alpha') return (obj.o.matAlpha === undefined ? 1 : obj.o.matAlpha) * 100;
            break;
          case 'stage': break;
          case 'script': if (owner && obj.vars.has(name)) return obj.vars.get(name); break;
        }
        throw new Error('unsupported property .' + name + ' on ' + (obj.kind || typeof obj));
      }
      function setMember(obj, name, val) {
        if (obj === null || obj === undefined) throw new Error('cannot set .' + name + ' of an empty object');
        if (obj instanceof Vec) {
          var v = obj.get3();
          if (name === 'x') v[0] = num(val); else if (name === 'y') v[1] = num(val); else if (name === 'z') v[2] = num(val);
          else if (name === 'xyz') v = toVec(val); else throw new Error('unknown vector property ' + name);
          obj.set3(v); return;
        }
        switch (obj.kind) {
          case 'container': {
            var o = obj.o;
            switch (name) {
              case 'active': o.active = truthy(val); env.changed(); return;
              case 'visible': o.hidden = !truthy(val); env.changed(); return;
              case 'name': o.name = str(val); return;
              case 'position': case 'scaling': case 'rotation': case 'center': {
                var arr = { position: o.pos, scaling: o.scale, rotation: o.rot, center: o.center }[name], nv = toVec(val);
                for (var i = 0; i < 3; i++) arr[i] = nv[i]; env.changed(); return;
              }
            }
            break;
          }
          case 'geometry': if (name === 'text') { env.setText(obj.o, str(val)); return; } break;
          case 'alpha': if (name === 'value') { obj.o.alpha = num(val); env.changed(); return; } break;
          case 'material':
            if (name === 'color') { obj.o.color = toVec(val).concat([1]).slice(0, 4); env.changed(); return; }
            if (name === 'alpha') { obj.o.matAlpha = num(val) / 100; env.changed(); return; }
            break;
        }
        throw new Error('cannot set .' + name + ' on ' + (obj.kind || typeof obj));
      }
      function callMethod(obj, name, a, ctx) {
        if (obj === null || obj === undefined) throw new Error('cannot call ' + name + '() on an empty object (container not found?)');
        if (obj instanceof Vec) { if (name === 'set') { obj.set3([num(a[0]), num(a[1]), num(a[2])]); return null; } if (name === 'get') return obj.get3(); }
        if (obj instanceof VArray) {
          switch (name) {
            case 'push': obj.items.push(a[0]); return null;
            case 'pop': return obj.items.pop();
            case 'clear': obj.items = []; return null;
            case 'size': case 'ubound': return obj.items.length;
            case 'insert': obj.items.splice(num(a[0]), 0, a[1]); return null;
            case 'erase': obj.items.splice(num(a[0]), 1); return null;
          }
        }
        switch (obj.kind) {
          case 'scene':
            if (name === 'findcontainer') return C(findIn(env.all, str(a[0])));
            if (name === 'updatescenetree' || name === 'update') return null;
            break;
          case 'container': {
            var o = obj.o;
            switch (name) {
              case 'getfunctionplugininstance': { var t = str(a[0]); for (var i = 0; i < o.funcs.length; i++) if (lower(o.funcs[i].type) === lower(t)) return plugin(o, o.funcs[i].type, o.funcs[i].p); return null; }
              case 'getgeometryplugininstance': return o.geom ? plugin(o, o.geom.type, o.geom.p || (o.geom.p = {})) : null;
              case 'findsubcontainer': {
                var parts = str(a[0]).split('$'), cur = o;
                for (var j = 0; j < parts.length && cur; j++) cur = findIn(cur.kids, parts[j]) || (j === 0 ? findIn(subTree(o), parts[j]) : null);
                return C(cur);
              }
              case 'getchildcontainerbyindex': return C(o.kids[num(a[0])]);
              case 'getchildcontainercount': return o.kids.length;
              case 'getdirector': return null;
              case 'getgeometryname': case 'getgeometrytype': return o.geom ? o.geom.type : '';
            }
            break;
          }
          case 'geometry': {
            var go = obj.o;
            if (name === 'registertextchangedcallback') { env.watchText(go, ctx); return null; }
            if (name === 'unregistertextchangedcallback') { env.unwatchText(go, ctx); return null; }
            if (name === 'getplugininstance') return go.geom ? plugin(go, go.geom.type, go.geom.p || (go.geom.p = {})) : null;
            if (name === 'settext') { env.setText(go, str(a[0])); return null; }
            if (name === 'gettext') return env.textOf(go);
            break;
          }
          case 'plugin': {
            var m = /^(set|get)parameter(double|int|integer|float|string|bool|boolean|color|vertex)?$/.exec(name);
            if (m) {
              var key = str(a[0]);
              if (m[1] === 'get') { var cur2 = obj.p[key]; if (/double|float|int/.test(m[2] || '')) return num(cur2); if (m[2] === 'string') return str(cur2); return cur2; }
              var val = a[1];
              if (m[2] === 'int' || m[2] === 'integer') val = Math.round(num(val));
              else if (m[2] === 'double' || m[2] === 'float') val = num(val);
              else if (m[2] === 'string') val = str(val);
              else if (m[2] === 'bool' || m[2] === 'boolean') val = truthy(val);
              else if (m[2] === 'vertex' || m[2] === 'color') val = toVec(val);
              obj.p[key] = val; env.pluginChanged(obj.o, obj.type, key); return null;
            }
            if (name === 'pushbutton' || name === 'updateparameters' || name === 'initialize' || name === 'reset') { env.pluginChanged(obj.o, obj.type, name); return null; }
            break;
          }
          case 'stage': return null;
        }
        throw new Error('unsupported method ' + name + '() on ' + (obj.kind || typeof obj));
      }
      return { C: C, scene: scene, getMember: getMember, setMember: setMember, callMethod: callMethod };
    }

    // ---- interpreter ----
    function Script(o, src, env, host) {
      this.o = o; this.env = env; this.host = host;
      this.prog = parse(src);
      this.vars = new Map(); this.params = {}; this.dimmed = new Set();
      this.steps = 0;
    }
    var EXIT = {}, RETURN = {};
    Script.prototype.run = function (body, frame) {
      for (var i = 0; i < body.length; i++) {
        var r = this.exec(body[i], frame);
        if (r) return r;
      }
      return null;
    };
    Script.prototype.tick = function () { if (++this.steps > 2e5) throw new Error('script stopped: too many steps (endless loop?)'); };
    Script.prototype.lookup = function (name, frame) {
      if (frame && frame.vars.has(name)) return frame.vars;
      if (this.vars.has(name)) return this.vars;
      return null;
    };
    Script.prototype.defaultOf = function (ty, size) {
      if (size) return new VArray(size.length ? num(this.eval(size[0], null)) : 0);
      switch (lower(ty || '')) {
        case 'integer': case 'int': case 'double': case 'float': case 'long': return 0;
        case 'string': return '';
        case 'boolean': case 'bool': return false;
        case 'array': return new VArray(0);
        case 'vertex': return BUILTIN.vertex([0, 0, 0]);
      }
      return null;
    };
    Script.prototype.exec = function (s, frame) {
      this.tick();
      var self = this, i, r;
      switch (s.t) {
        case 'dim':
          s.decls.forEach(function (d) {
            var target = frame ? frame.vars : self.vars;
            if (!frame) self.dimmed.add(d.name);
            target.set(d.name, d.init ? self.coerce(self.eval(d.init, frame), d.ty) : self.defaultOf(d.ty, d.size));
          });
          return null;
        case 'set': this.assign(s.lhs, this.eval(s.e, frame), frame); return null;
        case 'expr': this.eval(s.e, frame); return null;
        case 'if':
          for (i = 0; i < s.arms.length; i++) if (truthy(this.eval(s.arms[i].c, frame))) return this.run(s.arms[i].b, frame);
          return s.els ? this.run(s.els, frame) : null;
        case 'for': {
          var from = num(this.eval(s.from, frame)), to = num(this.eval(s.to, frame)), step = s.step ? num(this.eval(s.step, frame)) : 1;
          // a loop counter inside a sub is local unless it was declared with dim at script level
          var vars = frame ? (frame.vars.has(s.v) || !this.dimmed.has(s.v) ? frame.vars : this.vars) : this.vars;
          for (var x = from; step >= 0 ? x <= to : x >= to; x += step) {
            vars.set(s.v, x);
            r = this.run(s.body, frame);
            if (r === EXIT) { if (this.exitWhat === 'for') { r = null; break; } return r; }
            if (r) return r;
            x = num(vars.get(s.v));
            if (step === 0) break;
          }
          return null;
        }
        case 'foreach': {
          var coll = this.eval(s.coll, frame), items = coll instanceof VArray ? coll.items.slice() : Array.isArray(coll) ? coll : [];
          var fv = this.lookup(s.v, frame) || (frame ? frame.vars : this.vars);
          for (i = 0; i < items.length; i++) { fv.set(s.v, items[i]); r = this.run(s.body, frame); if (r === EXIT && this.exitWhat === 'for') break; if (r) return r; }
          return null;
        }
        case 'do':
          for (;;) {
            if (s.pre && truthy(this.eval(s.pre, frame)) === s.until) break;
            r = this.run(s.body, frame);
            if (r === EXIT) { if (this.exitWhat === 'do' || this.exitWhat === 'while') break; return r; }
            if (r) return r;
            if (s.post && truthy(this.eval(s.post, frame)) === s.puntil) break;
            this.tick();
          }
          return null;
        case 'select': {
          var v = this.eval(s.e, frame);
          for (i = 0; i < s.cases.length; i++) {
            var hit = s.cases[i].tests.some(function (t) {
              if (t.lo) return cmp(v, self.eval(t.lo, frame)) >= 0 && cmp(v, self.eval(t.hi, frame)) <= 0;
              return self.compare(t.op, v, self.eval(t.e, frame));
            });
            if (hit) return this.run(s.cases[i].body, frame);
          }
          return s.def ? this.run(s.def, frame) : null;
        }
        case 'exit': this.exitWhat = s.what; return EXIT;
        case 'return': if (frame && s.e) frame.ret = this.eval(s.e, frame); this.exitWhat = 'function'; return EXIT;
        case 'with': { var saved = this.withObj; this.withObj = this.eval(s.e, frame); r = this.run(s.body, frame); this.withObj = saved; return r; }
      }
      throw new Error('unknown statement ' + s.t);
    };
    Script.prototype.coerce = function (v, ty) {
      switch (lower(ty || '')) {
        case 'integer': case 'int': case 'long': return typeof v === 'string' ? (parseInt(v, 10) || 0) : Math.round(num(v));
        case 'double': case 'float': return num(v);
        case 'string': return str(v);
        case 'boolean': case 'bool': return truthy(v);
      }
      return v;
    };
    Script.prototype.compare = function (op, a, b) {
      switch (op) {
        case '=': return eq(a, b); case '<>': return !eq(a, b);
        case '<': return cmp(a, b) < 0; case '>': return cmp(a, b) > 0;
        case '<=': return cmp(a, b) <= 0; case '>=': return cmp(a, b) >= 0;
        case 'is': return a === b;
      }
      return false;
    };
    Script.prototype.assign = function (lhs, val, frame) {
      if (val instanceof Vec && lhs.t === 'id') val = BUILTIN.vertex(val.get3());
      if (lhs.t === 'id') {
        var vars = this.lookup(lhs.name, frame);
        if (!vars && frame && frame.fn === lhs.name) { frame.ret = val; return; }
        (vars || (frame ? frame.vars : this.vars)).set(lhs.name, vars && vars.get(lhs.name) instanceof VArray && !(val instanceof VArray) ? val : val);
        return;
      }
      if (lhs.t === 'mem') { this.host.setMember(this.evalObj(lhs.obj, frame), lhs.name, val); return; }
      if (lhs.t === 'idx' || (lhs.t === 'call' && lhs.f.t === 'id')) {
        var arr = this.eval(lhs.t === 'idx' ? lhs.obj : lhs.f, frame);
        if (arr instanceof VArray) { var k = num(this.eval(lhs.args[0], frame)); while (arr.items.length <= k) arr.items.push(null); arr.items[k] = val; return; }
      }
      throw new Error('cannot assign to this expression');
    };
    Script.prototype.evalObj = function (e, frame) { return e.t === 'with' ? this.withObj : this.eval(e, frame); };
    Script.prototype.eval = function (e, frame) {
      var self = this;
      switch (e.t) {
        case 'lit': return e.v;
        case 'tuple': var tv = e.items.map(function (x) { return num(self.eval(x, frame)); }); return BUILTIN.vertex(tv);
        case 'new': return e.ty === 'array' ? new VArray(0) : this.defaultOf(e.ty);
        case 'id': {
          var vars = this.lookup(e.name, frame);
          if (vars) return vars.get(e.name);
          if (frame && frame.fn === e.name) return frame.ret;
          switch (e.name) {
            case 'scene': return this.host.scene;
            case 'this': return this.host.C(this.o);
            case 'system': case 'stage': return { kind: 'stage' };
          }
          if (this.prog.subs[e.name]) return this.callSub(e.name, [], frame);
          if (BUILTIN[e.name]) return BUILTIN[e.name]([]);
          return null;                     // undeclared variable: empty, like VBScript
        }
        case 'un': { var a = this.eval(e.a, frame); return e.op === 'not' ? (typeof a === 'number' && !Number.isInteger(a) ? !a : typeof a === 'number' ? ~a : !truthy(a)) : -num(a); }
        case 'bin': {
          if (e.op === 'and' || e.op === 'or' || e.op === 'xor') {
            var l = this.eval(e.a, frame), r = this.eval(e.b, frame);
            if (typeof l === 'number' && typeof r === 'number') return e.op === 'and' ? l & r : e.op === 'or' ? l | r : l ^ r;
            l = truthy(l); r = truthy(r); return e.op === 'and' ? l && r : e.op === 'or' ? l || r : l !== r;
          }
          var x = this.eval(e.a, frame), y = this.eval(e.b, frame);
          switch (e.op) {
            case '&': return str(x) + str(y);
            case '+':
              if (x instanceof Vec || y instanceof Vec) { var p = toVec(x), q = toVec(y); return BUILTIN.vertex([p[0] + q[0], p[1] + q[1], p[2] + q[2]]); }
              if (typeof x === 'string' && typeof y === 'string') return x + y;
              return num(x) + num(y);
            case '-':
              if (x instanceof Vec || y instanceof Vec) { var p2 = toVec(x), q2 = toVec(y); return BUILTIN.vertex([p2[0] - q2[0], p2[1] - q2[1], p2[2] - q2[2]]); }
              return num(x) - num(y);
            case '*':
              if (x instanceof Vec || y instanceof Vec) { var p3 = toVec(x), q3 = toVec(y); return BUILTIN.vertex([p3[0] * q3[0], p3[1] * q3[1], p3[2] * q3[2]]); }
              return num(x) * num(y);
            case '/': return num(x) / num(y);
            case '\\': return Math.trunc(num(x) / num(y));
            case 'mod': return num(x) % num(y);
            case '^': return Math.pow(num(x), num(y));
          }
          return this.compare(e.op, x, y);
        }
        case 'mem': {
          var obj = this.evalObj(e.obj, frame);
          if (typeof obj === 'string' && (STR[e.name] || STRMUT[e.name])) return this.strCall(e, obj, e.name, [], frame);
          return this.host.getMember(obj, e.name);
        }
        case 'idx': {
          var arr = this.eval(e.obj, frame), k = num(this.eval(e.args[0], frame));
          if (arr instanceof VArray) return arr.items[k] === undefined ? null : arr.items[k];
          if (typeof arr === 'string') return arr.charAt(k);
          throw new Error('cannot index this value');
        }
        case 'call': {
          var f = e.f, args = e.args.map(function (x) { return self.eval(x, frame); });
          if (f.t === 'id') {
            if (this.prog.subs[f.name]) return this.callSub(f.name, args, frame, e.args);
            var av = this.lookup(f.name, frame);
            if (av && av.get(f.name) instanceof VArray) { var it = av.get(f.name).items[num(args[0])]; return it === undefined ? null : it; }
            if (BUILTIN[f.name]) return BUILTIN[f.name](args);
            if (f.name === 'println' || f.name === 'print') { this.env.log(args.map(str).join(' ')); return null; }
            if (/^registerparameter/.test(f.name)) { this.params[lower(str(args[0]))] = args.length > 2 ? args[2] : null; return null; }
            if (/^getparameter/.test(f.name)) { return this.params[lower(str(args[0]))]; }
            if (/^(registerinfotext|registerpushbutton|registerparametercontainer|sendcommand|registerplugin)/.test(f.name)) return null;
            if (frame && frame.fn === f.name && !args.length) return frame.ret;
            throw new Error('unknown function ' + f.name + '()');
          }
          if (f.t === 'mem') {
            var target = this.evalObj(f.obj, frame);
            if (typeof target === 'string') return this.strCall(f, target, f.name, args, frame);
            if (target instanceof VArray && e.bare) return this.host.callMethod(target, f.name, args, this);
            if (target && target.kind === 'geometry' && f.name === 'text' && e.bare) return this.host.getMember(target, 'text');
            if (e.bare && target && (target.kind === 'container' || target.kind === 'geometry' || target.kind === 'alpha' || target instanceof Vec)) {
              try { return this.host.getMember(target, f.name); } catch (er) { /* a method call without parentheses */ }
            }
            return this.host.callMethod(target, f.name, args, this);
          }
          if (f.t === 'idx' || f.t === 'call') return this.eval(f, frame);
          throw new Error('cannot call this expression');
        }
        case 'with': return this.withObj;
      }
      throw new Error('unknown expression ' + e.t);
    };
    Script.prototype.strCall = function (memNode, s, name, args, frame) {
      if (STR[name]) return STR[name](s, args);
      var out = STRMUT[name](s, args);
      try { this.assign(memNode.obj, out, frame); } catch (er) { /* not assignable: result only */ }
      return out;
    };
    Script.prototype.callSub = function (name, args, frame, argNodes) {
      var sub = this.prog.subs[name], self = this;
      var nf = { vars: new Map(), fn: sub.isF ? name : null, ret: null };
      sub.params.forEach(function (p, i) { nf.vars.set(p.name, i < args.length ? args[i] : null); });
      if (this.depth > 60) throw new Error('script stopped: recursion too deep');
      this.depth = (this.depth || 0) + 1;
      try { this.run(sub.body, nf); } finally { this.depth--; }
      sub.params.forEach(function (p, i) {       // ByRef parameters written back
        if (p.byref && argNodes && argNodes[i] && (argNodes[i].t === 'id')) { try { self.assign(argNodes[i], nf.vars.get(p.name), frame); } catch (e) { /* ignore */ } }
      });
      return nf.ret;
    };
    Script.prototype.has = function (name) { return !!this.prog.subs[name]; };
    Script.prototype.callback = function (name, args) {
      if (!this.prog.subs[name] || this.dead) return;
      this.steps = 0;
      try { this.callSub(name, args || [], null); }
      catch (e) { this.env.log(this.o.name + ': ' + e.message, true); if (/too many steps|recursion/.test(e.message)) this.dead = true; }
    };
    Script.prototype.start = function () {
      this.steps = 0;
      try {
        if (this.has('oninitparameters')) this.callSub('oninitparameters', [], null);
        this.run(this.prog.main, null);
        if (this.has('oninit')) this.callSub('oninit', [], null);
      } catch (e) { this.env.log(this.o.name + ': ' + e.message, true); }
    };

    return { parse: parse, Script: Script, make: make, num: num, str: str };
  })();

  // ---------- the scene's own Viz scripts, run by the interpreter above ----------
  var scripts = [], scriptLog = [], watched = [], cbDepth = 0, renderPending = false;
  function renderSoon() { if (renderPending) return; renderPending = true; requestAnimationFrame(function () { renderPending = false; if (!playing) apply(cur); }); }
  var vsEnv = {
    all: all,
    textOf: function (o) { return textOf(o); },
    setText: function (o, v) { setText(o, v); renderSoon(); },
    changed: renderSoon,
    pluginChanged: function (o, type) { if (/^advanced_counter$/i.test(type)) reformatCounter(o); renderSoon(); },
    watchText: function (o, sc) {
      if (watched.some(function (w) { return w.o === o && w.sc === sc; })) return;
      var w = { o: o, sc: sc, fn: function () {
        if (cbDepth > 8) return;
        cbDepth++; try { sc.callback('ongeometrychanged', [{ kind: 'geometry', o: o }]); } finally { cbDepth--; }
      } };
      watched.push(w); onText(o.name, w.fn);
    },
    unwatchText: function (o, sc) {
      watched = watched.filter(function (w) {
        if (w.o !== o || w.sc !== sc) return true;
        textHooks[o.name] = (textHooks[o.name] || []).filter(function (f) { return f !== w.fn; }); return false;
      });
    },
    log: function (m, isErr) { scriptLog.push((isErr ? '⚠ ' : '') + m); if (isErr) console.warn('[Viz script] ' + m); }
  };
  var vsHost = VS.make(vsEnv), inPerField = false;
  function runPerField() {
    if (inPerField || !scripts.length) return;
    inPerField = true;
    try { scripts.forEach(function (sc) { if (sc.has('onexecperfield')) sc.callback('onexecperfield'); }); } finally { inPerField = false; }
  }
  function startScripts() {
    all.forEach(function (o) {
      if (!o.script || !o.script.trim()) return;
      try { scripts.push(new VS.Script(o, o.script, vsEnv, vsHost)); }
      catch (e) { vsEnv.log(o.name + ': cannot read the script (' + e.message + ')', true); }
    });
    scripts.forEach(function (sc) { sc.start(); });
    // apply the current data once, as if each watched text had just been typed
    watched.slice().forEach(function (w) { w.fn(); });
    // texts that scripts watch but that have no control field get their own box in the form
    var inputs = [];
    watched.forEach(function (w) {
      var o = w.o, t = findText(o);
      if (!t || inputs.indexOf(o) >= 0) return;
      var covered = fields.some(function (fd) { return fd.os.some(function (x) { return x === o || findText(x) === t; }); });
      if (!covered) inputs.push(o);
    });
    if (inputs.length) {
      var h = document.createElement('h3'); h.textContent = 'Script inputs'; form.appendChild(h);
      inputs.forEach(function (o) {
        var l = document.createElement('label'); l.className = 'f'; l.innerHTML = '<span>' + o.name + '</span>';
        var inp = document.createElement('input'); inp.type = 'text'; inp.value = textOf(o);
        inp.oninput = function () { setText(o, inp.value); apply(cur); };
        l.appendChild(inp); form.appendChild(l);
      });
    }
    if (scripts.length) {
      var d = document.createElement('details'); d.className = 'note';
      var errs = scriptLog.filter(function (m) { return m.charAt(0) === '⚠'; }).length;
      d.innerHTML = '<summary>Viz scripts: ' + scripts.length + ' running' + (errs ? ', ' + errs + ' message(s)' : '') + '</summary>';
      var pre = document.createElement('pre'); pre.style.whiteSpace = 'pre-wrap'; pre.style.fontSize = '11px';
      function refresh() { pre.textContent = scripts.map(function (s) { return '• ' + s.o.name + (s.dead ? ' (stopped)' : ''); }).join('\n') + (scriptLog.length ? '\n\n' + scriptLog.slice(-40).join('\n') : ''); }
      refresh(); d.addEventListener('toggle', refresh);
      d.appendChild(pre); form.appendChild(d);
    }
    window.ghScripts = scripts; window.ghScriptLog = scriptLog;
  }

  // ---------- images found in the Graphic Hub ----------
  var imgs = (S.images || []).map(function (x) { var im = new Image(); im.src = x.src; return { u: x.u, n: x.n, img: im }; });
  var texs = all.filter(function (o) { return o.texture || (o.geom && o.geom.type === 'Image'); });
  if (texs.length) {
    var h2 = document.createElement('h2'); h2.textContent = 'Textures'; form.appendChild(h2);
    if (!imgs.length) { var nt = document.createElement('p'); nt.className = 'note'; nt.textContent = 'No referenced image was found in the Graphic Hub: load your own with the file buttons.'; form.appendChild(nt); }
    texs.forEach(function (o) {
      var l = document.createElement('label'); l.className = 'f';
      l.innerHTML = '<span>' + o.name + '</span>';
      var sel = document.createElement('select');
      sel.innerHTML = '<option value="">(placeholder)</option>' + imgs.map(function (x, i) { return '<option value="' + i + '">' + x.n + '</option>'; }).join('');
      var guess = -1;
      imgs.forEach(function (x, i) { if (guess < 0 && x.n && (o.name.toLowerCase().indexOf(x.n.toLowerCase()) >= 0 || x.n.toLowerCase().indexOf(o.name.toLowerCase()) >= 0)) guess = i; });
      var main = texs.filter(function (x) { return !/flare|glow|shine|light|blur|shadow|reflex/i.test(x.name); });
      if (guess < 0 && imgs.length === main.length && main.indexOf(o) >= 0) guess = main.indexOf(o);
      if (guess >= 0) { sel.value = String(guess); o.img = imgs[guess].img; imgs[guess].img.onload = function () { apply(cur); }; }
      sel.onchange = function () { o.img = sel.value === '' ? null : imgs[+sel.value].img; apply(cur); };
      var up = document.createElement('input'); up.type = 'file'; up.accept = 'image/*'; up.style.marginTop = '4px';
      up.onchange = function () { var f = up.files[0]; if (!f) return; var im = new Image(); im.onload = function () { o.img = im; apply(cur); }; im.src = URL.createObjectURL(f); };
      l.appendChild(sel); l.appendChild(up); form.appendChild(l);
    });
  }
  if (S.fonts && S.fonts.length) {
    var fn = document.createElement('p'); fn.className = 'note';
    fn.textContent = 'Fonts referenced in the Graphic Hub: ' + S.fonts.map(function (x) { return x.n + ' [' + x.u.substr(0, 8) + ']'; }).join(', ') + '. Viz fonts cannot be used in a browser; text uses ' + FONT.split(',')[0] + '.';
    form.appendChild(fn);
  }
  var bl = document.createElement('label'); bl.className = 'note'; bl.innerHTML = '<input type="checkbox" id="bold"> Bold text';
  form.appendChild(bl); document.getElementById('bold').onchange = function () { window.ghBold = this.checked; apply(cur); };

  // ---------- layer tree ----------
  var treeEl = document.getElementById('tree');
  (function list(o, d) {
    o.kids.forEach(function (k) {
      var r = document.createElement('div');
      r.textContent = ' '.repeat(d * 2) + k.name + (k.geom ? '  · ' + k.geom.type : '') + (k.anims.length ? '  ◆' : '') + (k.script ? '  {script}' : '') + (k.maskSrc ? '  [mask]' : '');
      if (!k.active) r.className = 'off';
      treeEl.appendChild(r); list(k, d + 1);
    });
  })(root, 0);
  var sk = Object.keys(skipped);
  if (sk.length) document.getElementById('skipped').textContent = 'Not rendered (unsupported plugins): ' + sk.map(function (k) { return k + ' ×' + skipped[k]; }).join(', ');
  document.getElementById('summary').textContent = all.length + ' containers · ' + fields.length + ' fields · ' + (duration ? duration.toFixed(2) + ' s of animation' : 'no animation') + (stops.length ? ' · stop points ' + stops.map(function (x) { return x.toFixed(2); }).join(', ') : '');

  // ---------- playback (stops at the director's stop points, like Viz) ----------
  var cur = 0, playing = false, t0 = 0, target = 0, timeEl = document.getElementById('time'), clock = document.getElementById('clock');
  var end = Math.max(duration, 0.001);
  function show(t) { cur = t; apply(t); timeEl.value = Math.round(1000 * t / end); clock.textContent = t.toFixed(2) + ' / ' + duration.toFixed(2) + ' s'; }
  function nextStop(t) { for (var i = 0; i < stops.length; i++) if (stops[i] > t + 1e-6) return stops[i]; return end; }
  function tick(now) {
    if (!playing) return;
    var t = (now - t0) / 1000;
    if (t >= target) {
      if (target >= end && document.getElementById('loop').checked) { t0 = now; t = 0; target = nextStop(0); }
      else { playing = false; show(target); return; }
    }
    show(t); requestAnimationFrame(tick);
  }
  function run(from) { cur = from; target = nextStop(from); playing = true; t0 = performance.now() - from * 1000; requestAnimationFrame(tick); }
  document.getElementById('play').onclick = function () { run(0); };
  document.getElementById('cont').onclick = function () { run(cur >= end ? 0 : cur); };
  document.getElementById('stop').onclick = function () { playing = false; show(0); };
  timeEl.oninput = function () { playing = false; show(end * timeEl.value / 1000); };
  window.ghAll = all; window.ghSeek = show; window.ghDuration = duration; window.ghStops = stops;

  // ---------- view ----------
  var frame = document.getElementById('frame'), vp = document.getElementById('viewport');
  function fit() { var s = Math.min((vp.clientWidth - 24) / 1920, (vp.clientHeight - 24) / 1080); frame.style.transform = 'scale(' + s + ')'; frame.style.marginRight = (1920 * (s - 1)) + 'px'; frame.style.marginBottom = (1080 * (s - 1)) + 'px'; }
  window.addEventListener('resize', fit); fit();
  var mi = document.getElementById('minv'); mi.checked = maskInvert; mi.onchange = function () { maskInvert = mi.checked; apply(cur); };
  document.getElementById('bg').onchange = function () { frame.className = 'bg-' + this.value; };
  var ref = document.getElementById('ref');
  if (S.preview) ref.src = 'data:image/jpeg;base64,' + S.preview; else document.getElementById('refop').disabled = true;
  document.getElementById('refop').oninput = function () { ref.style.opacity = this.value / 100; };
  startScripts(); window.ghSetText = function (n, v) { setText(byName(n), v); apply(cur); };
  show(stops.length ? stops[0] : duration);   // first stop point = the state shown in the Viz preview
})();
</script>
</body>
</html>
'@

function Invoke-GhScripts($a) {
    $root = Get-GhRoot
    if ($a.Opt.all -or -not $a.Pos.Count) {
        # scan every scene of the Graphic Hub
        $scenes = @(Get-GhIndex | Where-Object { $_.Kind -eq 'Scene' })
        Write-GhTitle "Scenes containing Viz scripts ($($scenes.Count) scenes scanned)"
        $found = 0; $n = 0
        foreach ($s in $scenes) {
            $n++; Write-Progress -Activity 'Scanning scenes for scripts' -Status "$n / $($scenes.Count)" -PercentComplete ([int](100 * $n / [Math]::Max(1, $scenes.Count)))
            try { $list = [GhTool.Vdb]::SceneScripts([GhTool.Vdb]::Inspect($s.Path)) } catch { continue }
            if ($list.Count) {
                $found++
                $lines = 0; foreach ($x in $list) { $lines += ($x[1] -split "`n").Count }
                Write-Gh ("  {0}  [{1}]  {2} script(s), {3} lines: {4}" -f $s.Name, $s.Uuid.Substring(0, 8), $list.Count, $lines, (($list | ForEach-Object { $_[0] }) -join ', '))
            }
        }
        Write-Progress -Activity 'Scanning scenes for scripts' -Completed
        Write-Gh "  $found scene(s) with scripts. Extract one with: gh scripts <id> -Out <folder>" DarkGray
        return
    }
    $path = Resolve-GhObject ($a.Pos -join ' ')
    $i = [GhTool.Vdb]::Inspect($path)
    if ($i.Kind -ne 'Scene') { throw "Object $($i.Uuid) is not a scene ($($i.Kind))." }
    $list = [GhTool.Vdb]::SceneScripts($i)
    Write-GhTitle "Scripts in $($i.Name) [$($i.Uuid.Substring(0, 8))]"
    if (-not $list.Count) { Write-Gh '  This scene has no script.'; return }
    $out = if ($a.Opt.out) { Assert-GhOutside $a.Opt.out } else { Assert-GhOutside (Join-Path (Get-Location).ProviderPath ("{0}_{1}_scripts" -f (Get-SafeName $i.Name), $i.Uuid.Substring(0, 8))) }
    $k = 0
    foreach ($x in $list) {
        $k++
        $file = Join-Path $out ("{0:D2}_{1}.vs" -f $k, (Get-SafeName $x[0]))
        $header = "' Viz script from scene '$($i.Name)' [$($i.Uuid)], container '$($x[0])'`r`n"
        [IO.File]::WriteAllText($file, $header + ($x[1] -replace "`r?`n", "`r`n"), (New-Object Text.UTF8Encoding($true)))
        Write-Gh ("  {0,-28} {1,5} lines  -> {2}" -f $x[0], ($x[1] -split "`n").Count, (Split-Path $file -Leaf))
    }
    Write-GhOk "$($list.Count) script(s) saved in $out"
}

function Show-GhHelp {
    Write-Host ''
    Write-Host "  GHTool $script:GhVersion - Viz Graphic Hub data folder tool" -ForegroundColor Cyan
    Write-Host @'

  gh set [folder]             Choose the data folder (default: VizGHData). -Force if not recognised
  gh status                   Show the current Graphic Hub
  gh analyse [-Deep]          Analysis: breakdown, consistency, logs, RocksDB
                              -Deep: reads every object (types, formats, dates, Viz versions)
  gh scan [-Refresh]          Build the object index (cached automatically)
  gh browse                   Tree of objects by type (filters below)
      -Name <pattern> -Kind <type> -Year <yyyy> -Bucket <0-F> -Top <n> -All
      -Physical [-All]        Physical tree of folders/files
      -Grid                   Interactive table (Windows); the selection is exported
  gh find <text>              Search by name or start of a UUID
  gh show <id>                Object details (id = UUID, start of a UUID, name or path)
  gh export <id> [...]        Export one or more media (image -> PNG; others -> .bin)
      -Out <folder>  -Thumbs (JPEG thumbnails)  -Raw (raw data)  -NoFlip
  gh export -All [-Kind Image|*] [-Name ..] [-Year ..] [-Out ..] [-Force]
  gh gallery                  Web gallery of all images (opens in the browser)
      -Name -Kind -Year -Bucket  filters; -Kind * includes all objects (embedded thumbnails)
      -Size <px> (256)  -Fast (embedded 64 px thumbnails, instant)  -Full (+ full-resolution PNG)
      -Out <folder>  -Refresh  -NoOpen
  gh preview <id> [-Width n]  Preview the image in the terminal (ANSI colours)
  gh scene2html <id>          Turn a scene into an HTML page: layers, animation (with stop points),
                              a form for its control fields, textures from the GH when found
      -Out <file|folder>  -Font "<CSS font family>"  -NoRefs  -NoOpen
  gh scripts                  List the scenes that contain Viz scripts
  gh scripts <id> [-Out dir]  Save a scene's scripts as .vs text files
  gh logs                     List the log files
  gh logs -Tail [n] [-File name]        Last lines of a log (newest by default)
  gh logs -Grep <regex> [-All] [-Top n] Search the logs
  gh health [-Last n] [-File name]      [OK] TC/TCC/HQL/TS/TF status lines and alerts
  gh tables                   HQL tables and VizDbTables (sizes, segments)
  gh folders [file] [-All]    Readable strings in FolderCollection.dat (experimental)
  gh hex <id> [-Offset n] [-Length n]  Hex dump

  WRITING (bypasses the Graphic Hub - stop the server first, at your own risk):
  gh replace <id> <image> [-Mode fit|fill|stretch] [-Background RRGGBB]
                              Prepare an image replacement (same UUID, same dimensions/format,
                              regenerated thumbnails) and show a before/after preview. Nothing is written.
      -Apply                  Write it into the GH (automatic backup; file dates kept unless -Touch)
      -Force                  Ignore the detection of running Graphic Hub processes
  gh restore <uuid> [-File ..]  Restore the latest backup of an object
  gh backups [uuid]           List the backups
  help | cls | exit

  Examples:
    gh set D:\GH\VizGHData
    gh find meteo
    gh export 2EEBEAC8 -Thumbs -Out C:\Temp\Export
    gh export -All -Year 2017 -Out C:\Temp\Images2017
    gh replace 2EEBEAC8 C:\New\logo.png -Mode fit
'@
}

# ---------------------------------------------------------------------------
#  Argument parsing and command dispatch
# ---------------------------------------------------------------------------
$script:GhSwitches = @('deep', 'all', 'grid', 'physical', 'raw', 'refresh', 'force', 'noflip', 'thumbs', 'tail', 'fast', 'full', 'noopen', 'apply', 'touch', 'norefs')

function ConvertTo-GhArgs([string[]]$tokens) {
    $pos = New-Object System.Collections.Generic.List[string]
    $opt = @{}
    for ($i = 0; $i -lt $tokens.Count; $i++) {
        $t = $tokens[$i]
        if ($t -match '^--?([A-Za-z][\w-]*)(?::(.*))?$') {
            $k = $Matches[1].ToLower()
            if ($null -ne $Matches[2]) { $opt[$k] = $Matches[2]; continue }
            $next = if ($i + 1 -lt $tokens.Count) { $tokens[$i + 1] } else { $null }
            if ($k -eq 'tail' -and $next -match '^\d+$') { $opt[$k] = $next; $i++; continue }
            if ($script:GhSwitches -contains $k -or $null -eq $next -or $next -match '^--?[A-Za-z]') { $opt[$k] = $true }
            else { $opt[$k] = $next; $i++ }
        } else { $pos.Add($t) }
    }
    return @{ Pos = $pos.ToArray(); Opt = $opt }
}

function Invoke-GhCommand([string[]]$tokens) {
    $tokens = @($tokens | Where-Object { $_ -ne $null -and $_ -ne '' })
    if ($tokens.Count -and $tokens[0] -eq 'gh') { $tokens = @($tokens | Select-Object -Skip 1) }
    if (-not $tokens.Count) { Show-GhHelp; return }
    $cmd = $tokens[0].ToLower()
    $a = ConvertTo-GhArgs @($tokens | Select-Object -Skip 1)
    try {
        switch -Regex ($cmd) {
            '^(set|use)$' { Invoke-GhSet $a }
            '^(status|where|pwd)$' { Invoke-GhStatus }
            '^(analyse|analyze|analyse-deep)$' { Invoke-GhAnalyse $a }
            '^(scan|index)$' { $i = Get-GhIndex -Refresh:([bool]$a.Opt.refresh); Write-GhOk "$(@($i).Count) objects indexed" }
            '^(browse|tree|ls)$' { Invoke-GhBrowse $a }
            '^(find|search)$' { Invoke-GhFind $a }
            '^(show|info)$' { Invoke-GhShow $a }
            '^(export|extract)$' { Invoke-GhExport $a }
            '^(gallery|web)$' { Invoke-GhGallery $a }
            '^(preview|view)$' { Invoke-GhPreview $a }
            '^(scene2html|scene-html|html)$' { Invoke-GhScene2Html $a }
            '^scripts?$' { Invoke-GhScripts $a }
            '^(logs?|log)$' { Invoke-GhLogs $a }
            '^(health|status-lines)$' { Invoke-GhHealth $a }
            '^tables$' { Invoke-GhTables }
            '^replace$' { Invoke-GhReplace $a }
            '^restore$' { Invoke-GhRestore $a }
            '^backups?$' { Invoke-GhBackups $a }
            '^(folders|strings)$' { Invoke-GhFolders $a }
            '^hex$' { Invoke-GhHex $a }
            '^(help|\?)$' { Show-GhHelp }
            default { Write-GhErr "Unknown command: $cmd (type help)" }
        }
    } catch {
        Write-GhErr $_.Exception.Message
    }
}

function gh {
    # "-Option" tokens passed to a function without param() arrive as-is in $args.
    Invoke-GhCommand @($args | ForEach-Object { "$_" })
}

function Split-GhLine([string]$line) {
    $res = New-Object System.Collections.Generic.List[string]
    foreach ($m in [regex]::Matches($line, '"([^"]*)"|''([^'']*)''|(\S+)')) {
        if ($m.Groups[1].Success) { $res.Add($m.Groups[1].Value) }
        elseif ($m.Groups[2].Success) { $res.Add($m.Groups[2].Value) }
        else { $res.Add($m.Groups[3].Value) }
    }
    return , $res.ToArray()
}

function Start-GhShell {
    Import-GhConfig
    Write-Host ''
    Write-Host "  GHTool $script:GhVersion  -  Viz Graphic Hub. Type 'help'." -ForegroundColor Cyan
    try { $r = Get-GhRoot; Write-Host "  Graphic Hub : $r" -ForegroundColor DarkGray }
    catch { Write-Host "  No folder set: gh set <folder>" -ForegroundColor Yellow }
    while ($true) {
        Write-Host ''
        Write-Host 'GH> ' -ForegroundColor Cyan -NoNewline
        $line = [Console]::ReadLine()
        if ($null -eq $line) { break }
        $line = $line.Trim()
        if (-not $line) { continue }
        if ($line -match '^(exit|quit|q)$') { break }
        if ($line -match '^(cls|clear)$') { Clear-Host; continue }
        Invoke-GhCommand (Split-GhLine $line)
    }
}

# ---------------------------------------------------------------------------
#  Entry point
# ---------------------------------------------------------------------------
try {
    if ($MyInvocation.InvocationName -eq '.') {
        Import-GhConfig
        Set-Alias -Name vgh -Value gh -Scope Global -ErrorAction SilentlyContinue
        Write-Host "GHTool loaded: type 'gh help'." -ForegroundColor DarkGray
    } elseif ($Command -and $Command.Count) {
        Invoke-GhCommand $Command
    } else {
        Start-GhShell
    }
} catch {
    Stop-GhFatal 'Unexpected error.' $_
}
