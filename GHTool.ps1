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

$script:GhVersion = '1.3'

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
    public class Thumb  { public long Offset; public int Length; public int Width; public int Height; }
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

                    // XML version block (at the end of the file)
                    int tl = (int)Math.Min(fs.Length, 16384);
                    string tail = Encoding.GetEncoding(28591).GetString(ReadAt(fs, fs.Length - tl, tl));
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
                    else if (info.Chunks.Count == 0) info.Kind = "No data";
                }
            }
            catch (Exception ex) { info.Error = ex.Message; info.Kind = "Error"; }
            return info;
        }

        public static byte[] ReadPayload(VdbInfo info)
        {
            using (FileStream fs = OpenRead(info.Path))
            using (MemoryStream all = new MemoryStream((int)Math.Min(info.RawSize, int.MaxValue)))
            {
                foreach (Chunk c in info.Chunks)
                {
                    byte[] comp = ReadAt(fs, c.Offset, c.CompLen);
                    byte[] raw = Inflate(comp, 10, c.CompLen - 10, c.RawLen);
                    if (raw == null) throw new InvalidDataException("Unreadable chunk at offset " + c.Offset);
                    all.Write(raw, 0, raw.Length);
                }
                return all.ToArray();
            }
        }

        public static byte[] ReadThumb(VdbInfo info, int index)
        {
            Thumb t = info.Thumbs[index];
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

        // ---- thumbnail section: template [43-byte prefix][JPEG][17-byte suffix] ----
        public static byte[] RebuildIconSection(byte[] sec, byte[] jpeg, int w, int h)
        {
            int J = sec.Length - 60;
            if (J <= 0 || sec[43] != 0xFF || sec[44] != 0xD8) return null;
            if (U32(sec, 14) != J + 32 || U32(sec, 18) != J + 24 || U32(sec, 28) != J || U32(sec, 39) != J) return null;
            if (sec[22] != 4 || Encoding.ASCII.GetString(sec, 24, 4) != "JPEG") return null;
            int N = jpeg.Length;
            byte[] r = new byte[N + 60];
            Buffer.BlockCopy(sec, 0, r, 0, 43);
            P32(r, 14, (uint)(N + 32)); P32(r, 18, (uint)(N + 24)); P32(r, 28, (uint)N); P32(r, 39, (uint)N);
            r[32] = (byte)w; r[33] = (byte)(w >> 8); r[34] = (byte)h; r[35] = (byte)(h >> 8);
            Buffer.BlockCopy(jpeg, 0, r, 43, N);
            Buffer.BlockCopy(sec, 43 + J, r, 43 + N, 17);
            return r;
        }

        public static int IconWidth(byte[] sec) { return sec.Length > 36 ? sec[32] | (sec[33] << 8) : 0; }
        public static int IconHeight(byte[] sec) { return sec.Length > 36 ? sec[34] | (sec[35] << 8) : 0; }

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
    $dim = if ($r.Kind -eq 'Image') { "$($r.Width)×$($r.Height) $($r.PixelFormat)" } else { $r.Sections }
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
        'Thumbnails' = (($i.Thumbs | ForEach-Object { "$($_.Width)×$($_.Height) JPEG ($($_.Length) B @ $($_.Offset))" }) -join '; ')
        'zlib chunks' = $i.ChunkCount
        'Image' = $(if ($i.Kind -eq 'Image') { "$($i.Width)×$($i.Height), $($i.PixelFormat) (GL 0x$('{0:X4}' -f $i.GlFormat)), $($i.Channels) channels, $(Format-Size $i.PixelLength) of pixels" } else { '' })
        'Application' = $(if ($i.AppName) { "$($i.AppName) $($i.AppVersion)" } else { '' })
        'DB engine' = $i.DbVersion
        'System' = $(if ($i.SysName) { "$($i.SysName) $($i.SysVersion)" } else { '' })
        'Error' = $i.Error
    }
    foreach ($k in $rows.Keys) { if ("$($rows[$k])" -ne '') { Write-Gh ("  {0,-20} {1}" -f $k, $rows[$k]) } }
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
    if ($a.Opt.thumbs -or -not $payload) {
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
            if (-not $useFast) {
                if ($a.Opt.refresh -or -not (Test-Path -LiteralPath $png) -or $needFull) {
                    $i = [GhTool.Vdb]::Inspect($r.Path)
                    $payload = [GhTool.Vdb]::ReadPayload($i)
                    if ($a.Opt.refresh -or -not (Test-Path -LiteralPath $png)) { [GhTool.Vdb]::WriteThumbPng($i, $payload, $png, -not $a.Opt.noflip, $size); $made++ } else { $reused++ }
                    if ($needFull) { [GhTool.Vdb]::WriteImagePng($i, $payload, $full, -not $a.Opt.noflip) }
                    $payload = $null
                } else { $reused++ }
                $thumbRel = "thumbs/$($r.Uuid)_$size.png"
            } elseif ([int]$r.Thumbs -gt 0) {
                if ($a.Opt.refresh -or -not (Test-Path -LiteralPath $jpg)) {
                    $i = [GhTool.Vdb]::Inspect($r.Path)
                    $best = 0; for ($t = 1; $t -lt $i.ThumbCount; $t++) { if ($i.Thumbs[$t].Width -gt $i.Thumbs[$best].Width) { $best = $t } }
                    [IO.File]::WriteAllBytes($jpg, [GhTool.Vdb]::ReadThumb($i, $best)); $made++
                } else { $reused++ }
                $thumbRel = "thumbs/$($r.Uuid).jpg"
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
    if ($info.Sections -ne 'IconSmall,Icon,Data,Original,VERSION') { throw "Unrecognised section structure ($($info.Sections)): replacement refused." }
    if ($info.Channels -lt 1 -or $info.Channels -gt 4) { throw "Unsupported pixel format: $($info.PixelFormat)" }

    $orig = [IO.File]::ReadAllBytes($path)
    try { $layout = [GhTool.VdbWriter]::Parse($orig) } catch { throw "Unrecognised internal structure ($($_.Exception.Message)): replacement refused." }
    if (-not [GhTool.VdbWriter]::SameBytes($orig, [GhTool.VdbWriter]::Build($layout))) { throw "Identical rebuild failed: unknown format variant, replacement refused." }

    $names = $info.Sections -split ','
    $iData = [array]::IndexOf($names, 'Data'); $iS = [array]::IndexOf($names, 'IconSmall'); $iI = [array]::IndexOf($names, 'Icon')
    $chunkTotal = [long]0; foreach ($c in $info.Chunks) { $chunkTotal += $c.CompLen }
    if ($layout.Sections[$iData].Length -ne $chunkTotal) { throw "The Data section does not match the compressed chunks: replacement refused." }

    $payload = [GhTool.Vdb]::ReadPayload($info)
    $after = $payload.Length - ($info.PixelOffset + $info.PixelLength)
    if ($after -lt 0 -or $after -gt 2048) { throw "Extra data after the pixels ($after B): possible mipmap levels, replacement refused." }
    $w = $info.Width; $h = $info.Height; $ch = $info.Channels
    $stride = if ($info.PixelLength % $h -eq 0 -and $info.PixelLength / $h -ge $w * $ch) { $info.PixelLength / $h } else { $w * $ch }

    $mode = if ($a.Opt.mode) { "$($a.Opt.mode)".ToLower() } else { 'fit' }
    if ($mode -notin 'fit', 'fill', 'stretch') { throw "Unknown mode: $mode (fit, fill or stretch)" }
    $hasAlpha = $info.GlFormat -in 0x1908, 0x80E1, 0x190A, 0x1906
    $bg = ConvertFrom-GhColor $(if ($a.Opt.background) { $a.Opt.background } else { '000000' })
    $bgA = if ($hasAlpha -and -not $a.Opt.background) { [byte]0 } else { [byte]255 }

    $src = Read-GhImageFile $imagePath
    $rgba = [GhTool.VdbWriter]::Resize($src.Rgba, $src.W, $src.H, $w, $h, $mode, $bg[0], $bg[1], $bg[2], $bgA)

    $newPayload = [byte[]]$payload.Clone()
    [GhTool.VdbWriter]::WritePixels($rgba, $w, $h, $info.GlFormat, $ch, (-not $a.Opt.noflip), $newPayload, $info.PixelOffset, [int]$stride, $bg[0], $bg[1], $bg[2])
    $layout.Sections[$iData] = [GhTool.VdbWriter]::BuildDataSection($newPayload, $info.Chunks[0].RawLen)

    $thumbNote = 'thumbnails regenerated'
    foreach ($k in @($iS, $iI)) {
        if ($k -lt 0) { continue }
        $sec = $layout.Sections[$k]
        $tw = [GhTool.VdbWriter]::IconWidth($sec); $th = [GhTool.VdbWriter]::IconHeight($sec)
        if ($tw -lt 1 -or $th -lt 1 -or $tw -gt 1024 -or $th -gt 1024) { $thumbNote = 'original thumbnails kept (unknown template)'; continue }
        $t = [GhTool.VdbWriter]::Resize($rgba, $w, $h, $tw, $th, 'stretch', 0, 0, 0, 255)
        $jpg = [GhTool.VdbWriter]::EncodeJpeg($t, $tw, $th, 90)
        $ns = [GhTool.VdbWriter]::RebuildIconSection($sec, $jpg, $tw, $th)
        if ($ns) { $layout.Sections[$k] = $ns } else { $thumbNote = 'original thumbnails kept (unknown template)' }
    }
    $newBytes = [GhTool.VdbWriter]::Build($layout)

    # Verification: re-read the new file with the independent reader
    if (-not (Test-Path -LiteralPath $script:StagingDir)) { New-Item -ItemType Directory -Path $script:StagingDir -Force | Out-Null }
    $staged = Join-Path $script:StagingDir "$($info.Uuid).vdb"
    [IO.File]::WriteAllBytes($staged, $newBytes)
    $chk = [GhTool.Vdb]::Inspect($staged)
    if ($chk.Kind -ne 'Image' -or $chk.Width -ne $w -or $chk.Height -ne $h -or $chk.GlFormat -ne $info.GlFormat -or $chk.Name -ne $info.Name) { throw 'Verification failed: the rebuilt file does not read back correctly.' }
    if ($chk.ThumbCount -ne $info.ThumbCount) { throw 'Verification failed: unreadable thumbnails.' }
    if (-not [GhTool.VdbWriter]::SameBytes([GhTool.Vdb]::ReadPayload($chk), $newPayload)) { throw 'Verification failed: decompressed data differs.' }
    $re = [GhTool.VdbWriter]::Parse($newBytes)

    return [pscustomobject]@{ Info = $info; Path = $path; Bytes = $newBytes; Staged = $staged; Payload = $payload; NewPayload = $newPayload
        Mode = $mode; Source = "$($src.W)×$($src.H)"; Thumbs = $thumbNote; OldSize = $orig.Length }
}

function Invoke-GhReplace($a) {
    if ($a.Pos.Count -lt 2) { Write-GhErr 'Usage: gh replace <id> <new_image> [-Mode fit|fill|stretch] [-Background RRGGBB] [-Apply] [-Force]'; return }
    $path = Resolve-GhObject $a.Pos[0]
    $img = $a.Pos[1]
    Write-GhTitle "Replacing $(Split-Path $path -Leaf)"
    $r = New-GhReplacement $path $img $a
    $i = $r.Info
    Write-Gh ("  Object     : {0}  [{1}]  {2}×{3} {4}" -f $i.Name, $i.Uuid, $i.Width, $i.Height, $i.PixelFormat)
    Write-Gh ("  Source     : {0} ({1}) -> {2}×{3}, mode {4}" -f (Split-Path $img -Leaf), $r.Source, $i.Width, $i.Height, $r.Mode)
    Write-Gh ("  File       : {0} -> {1}  ({2})" -f (Format-Size $r.OldSize), (Format-Size $r.Bytes.Length), $r.Thumbs)
    Write-GhOk 'Structure rebuilt and read back successfully'

    $prev = Join-Path $script:StagingDir "$($i.Uuid)_before.png"; $next = Join-Path $script:StagingDir "$($i.Uuid)_after.png"
    [GhTool.Vdb]::WriteImagePng($i, $r.Payload, $prev, $true)
    $chk = [GhTool.Vdb]::Inspect($r.Staged)
    [GhTool.Vdb]::WriteImagePng($chk, $r.NewPayload, $next, $true)
    Write-Gh "  Previews   : $prev" DarkGray
    Write-Gh "               $next" DarkGray

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
$script:GhSwitches = @('deep', 'all', 'grid', 'physical', 'raw', 'refresh', 'force', 'noflip', 'thumbs', 'tail', 'fast', 'full', 'noopen', 'apply', 'touch')

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
