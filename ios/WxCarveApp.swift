//  WxCarveApp.swift —— iOS 微信聊天记录恢复（原生版）
//
//  单个 Swift 文件，包含：SQLite 空闲页/自由块/WAL 解析引擎 + SwiftUI 界面。
//  在 Xcode 里新建一个 iOS App（Interface: SwiftUI），把本文件拖进去替换掉
//  自动生成的 ContentView.swift / App.swift 即可运行。
//
//  作用范围（重要）：
//    本 App 读取"用户自己选择的"数据库文件（从 iTunes/Finder 备份里取出的
//    MM.sqlite 和 MM.sqlite-wal）。iOS 沙箱不允许任何 App 直接打开微信容器，
//    所以这是未越狱设备上唯一可行的形式——不是本 App 能力不足。
//
//  引擎算法与命令行版 wxrecover.py 一致，包含：
//    · SQLite varint（MSB-first，和 protobuf 的 LSB-first 相反）
//    · btree 遍历（内部页最右子页在页头 +8，指针数组从 +12 开始）
//    · 叶子 cell 解析 + 溢出页跟随
//    · 空闲块 / 未分配间隙 / freelist 页 / WAL 历史帧 全扫
//    · 记录精确解码（必须精确消费 payload 长度，压假阳性）
//    · 微信 Message blob 解码（zlib 信封、<msgsource> 元数据降权、中西文可读性判定）
//    · 记录头锚定 + 内容级兜底

import SwiftUI
import UniformTypeIdentifiers
import Compression
import CryptoKit

// MARK: - 常量

let kTimeMin = 946_684_800          // 2000-01-01
let kTimeMax = 4_102_444_800        // 2100-01-01

struct DbError: Error { let msg: String }

// MARK: - 字段值

enum Field {
    case null
    case int(Int)
    case real(Double)
    case text(String)
    case blob([UInt8])

    var intVal: Int? { if case .int(let v) = self { return v }; return nil }

    var textVal: String? {
        switch self {
        case .text(let s): return s
        case .blob(let b): return String(decoding: b, as: UTF8.self)
        default: return nil
        }
    }

    var bytesVal: [UInt8]? { if case .blob(let b) = self { return b }; return nil }

    var isEmptyText: Bool {
        switch self {
        case .null: return true
        case .text(let s): return s.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty
        case .blob(let b): return b.isEmpty
        default: return false
        }
    }
}

func serialSize(_ st: Int) -> Int {
    if st == 0 || st == 8 || st == 9 || st == 10 || st == 11 { return 0 }
    if st >= 1 && st <= 6 { return [1, 2, 3, 4, 6, 8][st - 1] }
    if st == 7 { return 8 }
    if st >= 12 { return st % 2 == 0 ? (st - 12) / 2 : (st - 13) / 2 }
    return 0
}

/// SQLite 的 varint 是 MSB-first；protobuf 的是 LSB-first。混用会把多字节
/// rowid / serial type 全读错——这是移植时最容易踩的坑。
func readVarint(_ b: [UInt8], _ pos: Int) throws -> (Int, Int) {
    var result = 0
    var p = pos
    for _ in 0..<8 {
        guard p < b.count else { throw DbError(msg: "varint eof") }
        let x = Int(b[p]); p += 1
        if x < 0x80 { return ((result << 7) | x, p) }
        result = (result << 7) | (x & 0x7f)
    }
    guard p < b.count else { throw DbError(msg: "varint eof") }
    let x = Int(b[p]); p += 1
    return ((result << 8) | x, p)
}

func pbVarint(_ b: [UInt8], _ pos: Int) throws -> (Int, Int) {
    var result = 0
    var shift = 1
    var p = pos
    while true {
        guard p < b.count else { throw DbError(msg: "pb varint eof") }
        let x = Int(b[p]); p += 1
        result += (x & 0x7f) * shift
        if x < 0x80 { return (result, p) }
        shift *= 128
        if shift > (1 << 56) { throw DbError(msg: "pb varint overflow") }
    }
}

func decodeRecord(_ payload: [UInt8]) -> ([Field], Int)? {
    if payload.isEmpty { return nil }
    guard let (hsize, p0) = try? readVarint(payload, 0) else { return nil }
    if hsize < 1 || hsize > payload.count || hsize > 4096 { return nil }
    var serials: [Int] = []
    var p = p0
    while p < hsize {
        guard let (st, np) = try? readVarint(payload, p) else { return nil }
        serials.append(st); p = np
        if serials.count > 128 { return nil }
    }
    if serials.isEmpty { return nil }
    var vals: [Field] = []
    var pos = hsize
    for st in serials {
        let n = serialSize(st)
        if pos + n > payload.count { return nil }
        switch st {
        case 0, 10, 11:
            vals.append(.null)
        case 8:
            vals.append(.int(0))
        case 9:
            vals.append(.int(1))
        case 7:
            var bits: UInt64 = 0
            for i in 0..<8 { bits = (bits << 8) | UInt64(payload[pos + i]) }
            vals.append(.real(Double(bitPattern: bits)))
        default:
            if st >= 12 {
                let seg = Array(payload[pos..<(pos + n)])
                vals.append(st % 2 == 0 ? .blob(seg) : .text(String(decoding: seg, as: UTF8.self)))
            } else {
                var v = 0
                for i in 0..<n { v = v * 256 + Int(payload[pos + i]) }
                if st <= 4 {
                    let bits = n * 8
                    if v >= (1 << (bits - 1)) { v -= (1 << bits) }
                }
                vals.append(.int(v))
            }
        }
        pos += n
    }
    return (vals, pos)
}

// MARK: - 数据库

struct Db {
    let data: [UInt8]
    let pageSize: Int
    let usable: Int
    let npages: Int
    let freelistHead: Int
    let nFreelist: Int

    static func u16(_ b: [UInt8], _ o: Int) -> Int { (Int(b[o]) << 8) | Int(b[o + 1]) }
    static func u32(_ b: [UInt8], _ o: Int) -> Int {
        (Int(b[o]) << 24) | (Int(b[o + 1]) << 16) | (Int(b[o + 2]) << 8) | Int(b[o + 3])
    }

    init(bytes: [UInt8]) throws {
        guard bytes.count > 100 else { throw DbError(msg: "文件太小，不是 SQLite 数据库") }
        let magic = String(decoding: bytes[0..<15], as: UTF8.self)
        guard magic == "SQLite format 3" else { throw DbError(msg: "不是 SQLite 数据库文件") }
        var ps = Db.u16(bytes, 16)
        if ps == 1 { ps = 65536 }
        data = bytes
        pageSize = ps
        usable = ps - Int(bytes[20])
        let hp = Db.u32(bytes, 28)
        npages = max(hp, (bytes.count + ps - 1) / ps)
        freelistHead = Db.u32(bytes, 32)
        nFreelist = Db.u32(bytes, 36)
    }

    /// 返回该页的独立副本（4KB，避免 ArraySlice 索引错位）
    func page(_ n: Int) -> [UInt8]? {
        guard n >= 1 else { return nil }
        let s = (n - 1) * pageSize
        guard s >= 0, s + pageSize <= data.count else { return nil }
        return Array(data[s..<(s + pageSize)])
    }

    func freelistPages() -> Set<Int> {
        var out = Set<Int>()
        var p = freelistHead
        var guardCount = 0
        while p != 0 && guardCount < 200_000 {
            guardCount += 1
            guard let trunk = page(p), trunk.count >= 8 else { break }
            let nLeaf = Db.u32(trunk, 4)
            out.insert(p)
            for i in 0..<min(nLeaf, (pageSize - 8) / 4) {
                let leaf = Db.u32(trunk, 8 + 4 * i)
                if leaf != 0 { out.insert(leaf) }
            }
            let nxt = Db.u32(trunk, 0)
            if nxt == p { break }
            p = nxt
        }
        return out
    }

    func pageFreeblocks(_ page: [UInt8], _ pgno: Int) -> [[UInt8]] {
        let off = pgno == 1 ? 100 : 0
        var out: [[UInt8]] = []
        guard page.count >= off + 8 else { return out }
        var fb = Db.u16(page, off + 1)
        var guardCount = 0
        while fb > 0 && guardCount < 10_000 {
            guardCount += 1
            guard fb + 4 <= page.count else { break }
            let nxt = Db.u16(page, fb)
            let size = Db.u16(page, fb + 2)
            guard size >= 4, fb + size <= page.count else { break }
            out.append(Array(page[(fb + 4)..<(fb + size)]))
            if nxt == 0 || nxt >= fb { break }
            fb = nxt
        }
        return out
    }

    func pageGap(_ page: [UInt8], _ pgno: Int) -> [UInt8]? {
        let off = pgno == 1 ? 100 : 0
        guard page.count >= off + 8 else { return nil }
        let ncell = Db.u16(page, off + 3)
        var cs = Db.u16(page, off + 5)
        if pgno == 1 && cs == 0 { cs = 65536 }
        let start = off + 8 + ncell * 2
        var end = cs == 0 ? page.count : cs
        if end > page.count { end = page.count }
        guard start >= off + 8, start < end else { return nil }
        return Array(page[start..<end])
    }

    func cellHeaderBefore(_ page: [UInt8], _ pos: Int) -> (Int, Int, Int)? {
        for r0 in max(0, pos - 6)..<pos {
            guard let (rowid, re) = try? readVarint(page, r0), re == pos else { continue }
            for p0 in max(0, r0 - 6)..<r0 {
                if let (plen, pe) = try? readVarint(page, p0),
                   pe == r0, plen > 0, plen < 50 * 1024 * 1024 {
                    return (plen, rowid, p0)
                }
            }
        }
        return nil
    }

    /// 解析一个 table-leaf cell，跟随溢出页
    func readCellBuf(_ buf: [UInt8], _ pos: Int) throws -> (Int, [UInt8], Int) {
        let U = usable
        let (plen, q0) = try readVarint(buf, pos)
        let (rowid, q) = try readVarint(buf, q0)
        if plen <= 0 || plen > 50 * 1024 * 1024 { throw DbError(msg: "bad payload len") }
        let X = U - 35
        var local = plen
        if plen > X {
            let M = ((U - 12) * 32) / 255 - 23
            let K = M + (plen - M) % (U - 4)
            local = K <= X ? K : M
        }
        guard q + local <= buf.count else { throw DbError(msg: "payload oob") }
        var payload = Array(buf[q..<(q + local)])
        var end = q + local
        if plen > local {
            guard end + 4 <= buf.count else { throw DbError(msg: "overflow ptr oob") }
            var nxt = Db.u32(buf, end)
            end += 4
            var guardCount = 0
            while nxt != 0 && payload.count < plen && guardCount < 100_000 {
                guardCount += 1
                guard let ov = page(nxt), ov.count >= 4 else { break }
                let take = min(U - 4, plen - payload.count)
                payload.append(contentsOf: ov[4..<(4 + take)])
                nxt = Db.u32(ov, 0)
            }
        }
        if payload.count > plen { payload = Array(payload[0..<plen]) }
        return (rowid, payload, end)
    }

    func parseLeafCells(_ page: [UInt8], _ pgno: Int) -> [(Int, [UInt8])] {
        var out: [(Int, [UInt8])] = []
        let off = pgno == 1 ? 100 : 0
        guard page.count >= off + 8, page[off] == 0x0d else { return out }
        let ncell = Db.u16(page, off + 3)
        if ncell == 0 || ncell > 20_000 { return out }
        let base = off + 8
        guard base + 2 * ncell <= page.count else { return out }
        for i in 0..<ncell {
            let p = Db.u16(page, base + 2 * i)
            if p < base || p >= page.count { continue }
            if let (rowid, payload, _) = try? readCellBuf(page, p) { out.append((rowid, payload)) }
        }
        return out
    }

    /// 内部页的 8..11 字节是最右子页指针，cell 指针数组从 +12 才开始
    func btreePages(_ root: Int) -> [Int] {
        var pages: [Int] = []
        var seen = Set<Int>()
        var stack = [root]
        while let p = stack.popLast() {
            if seen.contains(p) || p < 1 || p > npages { continue }
            seen.insert(p); pages.append(p)
            guard let page = self.page(p) else { continue }
            let off = p == 1 ? 100 : 0
            guard page.count >= off + 8, page[off] == 0x05 else { continue }
            let ncell = Db.u16(page, off + 3)
            guard off + 12 + 2 * ncell <= page.count else { continue }
            stack.append(Db.u32(page, off + 8))
            for i in 0..<ncell {
                let cp = Db.u16(page, off + 12 + 2 * i)
                if cp + 4 > page.count { continue }
                stack.append(Db.u32(page, cp))
            }
        }
        return pages
    }
}

// MARK: - WAL

struct WalFile {
    var frames: [Int: [[UInt8]]] = [:]
    var frameCount = 0

    init(bytes: [UInt8]?, pageSizeHint: Int) {
        guard let bytes = bytes, bytes.count >= 32 else { return }
        let magic = Db.u32(bytes, 0)
        guard magic == 0x377f0682 || magic == 0x377f0683 else { return }
        var ps = Db.u32(bytes, 8)
        if ps == 0 { ps = 65536 }
        guard ps >= 512, ps <= 65536 else { return }
        let s1 = Array(bytes[16..<20]), s2 = Array(bytes[20..<24])
        var off = 32
        while off + 24 + ps <= bytes.count {
            let pgno = Db.u32(bytes, off)
            let f1 = Array(bytes[(off + 8)..<(off + 12)])
            let f2 = Array(bytes[(off + 12)..<(off + 16)])
            let page = Array(bytes[(off + 24)..<(off + 24 + ps)])
            off += 24 + ps
            if pgno == 0 || f1 != s1 || f2 != s2 { continue }   // salt 不符 = 已作废的帧
            frames[pgno, default: []].append(page)
            frameCount += 1
        }
    }
}

// MARK: - 微信消息解码

let kMetaXml = try! NSRegularExpression(pattern: "<\\s*(msgsource|sysmsg|tips|oplog|appinfo|emoji)", options: [.caseInsensitive])
let kCjk = try! NSRegularExpression(pattern: "[\\u4e00-\\u9fff]")

func scoreText(_ s: String) -> Int {
    var t = s
    if let re = try? NSRegularExpression(pattern: "[\\u0000-\\u0008\\u000b-\\u001f]") {
        t = re.stringByReplacingMatches(in: t, range: NSRange(t.startIndex..., in: t), withTemplate: "")
    }
    t = t.trimmingCharacters(in: .whitespacesAndNewlines)
    if t.isEmpty { return -1 }
    var sc = min(t.count, 200)
    let ns = t as NSString
    if kMetaXml.firstMatch(in: t, range: NSRange(location: 0, length: ns.length)) != nil { sc -= 120 }
    else if t.hasPrefix("<") { sc -= 40 }
    if kCjk.firstMatch(in: t, range: NSRange(location: 0, length: ns.length)) != nil { sc += 40 }
    if t.count > 2000 { sc -= 200 }
    return sc
}

/// 按"解码后的字符"判可读性——不能按字节：一个汉字 3 字节，UTF-8 续字节会被
/// 误判成不可打印，结果中文正文全被丢掉、只剩 ascii 元数据。
func printableRatio(_ b: [UInt8]) -> Double {
    guard !b.isEmpty else { return 0 }
    guard let s = String(bytes: b, encoding: .utf8) else { return 0 }
    if s.isEmpty { return 0 }
    var good = 0
    var total = 0
    for ch in s.unicodeScalars {
        total += 1
        let v = ch.value
        if v == 9 || v == 10 || v == 13 || v >= 32 { good += 1 }
    }
    return total == 0 ? 0 : Double(good) / Double(total)
}

func zlibDecompress(_ bytes: [UInt8]) -> [UInt8]? {
    if bytes.count > 2 {
        let d = Data(bytes)
        if let out = try? (d as NSData).decompressed(using: .zlib) {
            return Array(out as Data)
        }
        // 退化方案：去掉 2 字节 zlib 头 + 4 字节 Adler32，按裸 deflate 解
        if bytes.count > 6 {
            let raw = Array(bytes[2..<(bytes.count - 4)])
            if let out = inflateRaw(raw) { return out }
        }
    }
    return nil
}

func inflateRaw(_ bytes: [UInt8]) -> [UInt8]? {
    guard !bytes.isEmpty else { return nil }
    var cap = max(4096, bytes.count * 8)
    for _ in 0..<3 {
        var out = [UInt8](repeating: 0, count: cap)
        var got = 0
        bytes.withUnsafeBufferPointer { src in
            out.withUnsafeMutableBufferPointer { dst in
                got = compression_decode_buffer(dst.baseAddress!, dst.count,
                                                src.baseAddress!, src.count,
                                                nil, COMPRESSION_ZLIB)
            }
        }
        if got > 0 { return Array(out[0..<got]) }
        cap *= 4
    }
    return nil
}

func pbStrings(_ buf: [UInt8]) -> [[UInt8]] {
    var out: [[UInt8]] = []
    var pos = 0
    while pos < buf.count {
        guard let (key, p1) = try? pbVarint(buf, pos) else { return out }
        let fn = key >> 3, wt = key & 7
        if fn == 0 || fn > 99999 { return out }
        var p = p1
        switch wt {
        case 0:
            guard let (_, np) = try? pbVarint(buf, p) else { return out }
            p = np
        case 1: p += 8
        case 5: p += 4
        case 2:
            guard let (ln, np) = try? pbVarint(buf, p) else { return out }
            if ln < 0 || np + ln > buf.count { return out }
            out.append(Array(buf[np..<(np + ln)]))
            p = np + ln
        default:
            return out
        }
        pos = p
    }
    return out
}

func decodeSegment(_ seg: [UInt8], _ depth: Int) -> String? {
    guard !seg.isEmpty else { return nil }
    if seg.count > 2, seg[0] == 0x78 {
        if let inf = zlibDecompress(seg), let r = decodeSegment(inf, depth + 1) { return r }
    }
    if depth < 5, !seg.isEmpty {
        let fn = Int(seg[0]) >> 3, wt = Int(seg[0]) & 7
        if (wt == 0 || wt == 2) && fn > 0 && fn < 16 {
            let subs = pbStrings(seg)
            let covered = subs.reduce(0) { $0 + $1.count }
            if !subs.isEmpty && covered >= seg.count - 2 {
                var best: String? = nil
                for sub in subs {
                    if let got = decodeSegment(sub, depth + 1),
                       best == nil || scoreText(got) > scoreText(best!) { best = got }
                }
                if let b = best { return b }
            }
        }
    }
    if printableRatio(seg) > 0.92, let s = String(bytes: seg, encoding: .utf8) { return s }
    if depth >= 4 { return nil }
    var best: String? = nil
    for sub in pbStrings(seg) {
        if let got = decodeSegment(sub, depth + 1),
           best == nil || got.count > best!.count { best = got }
    }
    return best
}

func decodeWechatMsg(_ blob: [UInt8]?) -> String {
    guard let blob = blob, !blob.isEmpty else { return "" }
    if printableRatio(blob) > 0.95, let s = String(bytes: blob, encoding: .utf8) {
        return s.trimmingCharacters(in: .whitespacesAndNewlines)
    }
    if blob[0] == 0x3c, let s = String(bytes: blob, encoding: .utf8) {   // '<' = XML
        return s.trimmingCharacters(in: .whitespacesAndNewlines)
    }
    if blob.count > 2, blob[0] == 0x78, let inf = zlibDecompress(blob) {
        let r = decodeWechatMsg(inf)
        if !r.isEmpty { return r }
    }
    var cands: [String] = []
    for seg in pbStrings(blob) {
        if seg.count > 3, seg[0] == 0x78, let inf = zlibDecompress(seg) {
            if let got = decodeSegment(inf, 1) { cands.append(got) }
        }
        if let got = decodeSegment(seg, 0) { cands.append(got) }
    }
    if !cands.isEmpty {
        return (cands.max { scoreText($0) < scoreText($1) } ?? "").trimmingCharacters(in: .whitespacesAndNewlines)
    }
    if let s = String(bytes: blob, encoding: .utf8) {
        return s.trimmingCharacters(in: .whitespacesAndNewlines)
    }
    return ""
}

func pbSpan(_ buf: [UInt8], _ start: Int, _ maxLen: Int = 8192) -> [UInt8] {
    var pos = start
    var fields = 0
    let lim = min(buf.count, start + maxLen)
    while pos < lim && fields < 8 {
        guard let (key, p1) = try? pbVarint(buf, pos) else { break }
        let fn = key >> 3, wt = key & 7
        if fn == 0 || fn > 16 || !(wt == 0 || wt == 1 || wt == 2 || wt == 5) { break }
        var p = p1
        var ok = true
        switch wt {
        case 0: if let (_, np) = try? pbVarint(buf, p) { p = np } else { ok = false }
        case 1: p += 8
        case 5: p += 4
        default:
            if let (ln, np) = try? pbVarint(buf, p), np + ln <= buf.count { p = np + ln } else { ok = false }
        }
        if !ok || p <= pos { break }
        pos = p; fields += 1
    }
    return Array(buf[start..<min(pos, buf.count)])
}

/// 把消息正文锚定回记录头：字段偏移、正文长度 serial 全对得上，
/// 说明 rowid 和时间是精确还原的，不是从 4 个随机字节猜的。
func anchorRecord(_ page: [UInt8], _ blobStart: Int, _ blobLen: Int, _ db: Db) -> (ts: Int, rowid: Int?)? {
    var hp = blobStart - 5
    while hp >= max(0, blobStart - 64) {
        defer { hp -= 1 }
        guard let (hsize, _) = try? readVarint(page, hp) else { continue }
        if hsize < 4 || hsize > 48 || hp + hsize > blobStart { continue }
        var serials: [Int] = []
        var q = hp + 1
        var ok = true
        while q < hp + hsize {
            guard let (st, nq) = try? readVarint(page, q) else { ok = false; break }
            serials.append(st); q = nq
            if serials.count > 24 { ok = false; break }
        }
        if !ok || serials.isEmpty || serials[0] != 0 { continue }
        var offs: [Int] = []
        var o = 0
        for st in serials { offs.append(o); o += serialSize(st) }
        let body = hp + hsize
        for i in 0..<serials.count where serials[i] == 4 && i + 1 < serials.count {
            if body + offs[i] + 4 != blobStart { continue }
            let nx = serials[i + 1]
            if nx < 12 || nx % 2 != 0 { continue }
            if (nx - 12) / 2 != blobLen { continue }
            let ts = Db.u32(page, body + offs[i])
            if ts < kTimeMin || ts > kTimeMax { continue }
            return (ts, db.cellHeaderBefore(page, hp)?.1)
        }
    }
    return nil
}

let kBlobRe = try! NSRegularExpression(pattern: "[\\u000a][\\u0001-\\u0040][\\x20-\\x7e]{2,40}[\\u0012]")

struct BlobHit {
    var blob: [UInt8]
    var ts: Int?
    var off: Int
    var rowid: Int?
}

func findWxBlobs(_ page: [UInt8], db: Db) -> [BlobHit] {
    var starts = Set<Int>()
    if let s = String(bytes: page, encoding: .isoLatin1) {
        let ns = s as NSString
        let ms = kBlobRe.matches(in: s, range: NSRange(location: 0, length: ns.length))
        for m in ms { starts.insert(m.range.location) }
    }
    for needle in ["<msg>", "<msgsource>", "<appmsg>", "<sysmsg>"] {
        let nb = Array(needle.utf8)
        if nb.isEmpty || page.count < nb.count { continue }
        var i = 0
        while i <= page.count - nb.count {
            if page[i] == nb[0] {
                var hit = true
                for k in 1..<nb.count where page[i + k] != nb[k] { hit = false; break }
                if hit { starts.insert(i) }
            }
            i += 1
        }
    }
    var out: [BlobHit] = []
    for p in starts.sorted() {
        var blob: [UInt8]
        let head = String(decoding: page[p..<min(p + 6, page.count)], as: UTF8.self)
        if head.hasPrefix("<msg") || head.hasPrefix("<appm") {
            let end = findBytes(page, Array("</msg>".utf8), from: p)
            blob = end > 0 ? Array(page[p..<min(end + 6, page.count)]) : Array(page[p...])
        } else {
            blob = pbSpan(page, p)
        }
        if blob.count < 4 { continue }
        var ts: Int? = nil
        var rowid: Int? = nil
        if let a = anchorRecord(page, p, blob.count, db) { ts = a.ts; rowid = a.rowid }
        if ts == nil {
            // 锚不上才退化成"往前 4 字节猜时间"
            for back in [4, 5, 6, 8] {
                let q = p - back
                if q < 0 || q + 4 > page.count { continue }
                let v = Db.u32(page, q)
                if v >= kTimeMin && v <= kTimeMax { ts = v; break }
            }
        }
        out.append(BlobHit(blob: blob, ts: ts, off: p, rowid: rowid))
    }
    return out
}

func findBytes(_ hay: [UInt8], _ needle: [UInt8], from: Int) -> Int {
    guard !needle.isEmpty, hay.count >= needle.count else { return -1 }
    var i = from
    while i <= hay.count - needle.count {
        if hay[i] == needle[0] {
            var hit = true
            for k in 1..<needle.count where hay[i + k] != needle[k] { hit = false; break }
            if hit { return i }
        }
        i += 1
    }
    return -1
}

// MARK: - 恢复引擎

struct RecoveredRow: Identifiable {
    let id = UUID()
    var tbl: String
    var rowid: Int?
    var ts: Int?
    var dir: Int?
    var text: String
    var source: String
}

struct SrcCount: Identifiable {
    var id: String { name }
    let name: String
    let count: Int
}

struct CarveStats {
    var live = 0
    var recRows = 0
    var contentRows = 0
    var total = 0
    var sources: [SrcCount] = []
}

final class Engine {
    private let db: Db
    private let wal: WalFile

    init(db: Db, wal: WalFile) {
        self.db = db
        self.wal = wal
    }

    static func loadDatabase(_ data: [UInt8]) throws -> Db { try Db(bytes: data) }

    /// 从 sqlite_master（root page = 1）读出所有表
    func readMasterTables() -> [(name: String, root: Int, sql: String)] {
        var out: [(String, Int, String)] = []
        for pg in db.btreePages(1) {
            guard let page = db.page(pg) else { continue }
            for (_, payload) in db.parseLeafCells(page, pg) {
                guard let (vals, _) = decodeRecord(payload), vals.count >= 5 else { continue }
                guard case .text(let type) = vals[0], type == "table" else { continue }
                let name = vals[1].textVal ?? ""
                let root = vals[3].intVal ?? 0
                let sql = vals[4].textVal ?? ""
                out.append((name, root, sql))
            }
        }
        return out
    }

    func parseColumns(_ sql: String) -> [String] {
        guard let i = sql.firstIndex(of: "("), let j = sql.lastIndex(of: ")") else { return [] }
        let body = String(sql[sql.index(after: i)..<j])
        var parts: [String] = []
        var depth = 0, cur = ""
        for ch in body {
            if ch == "(" { depth += 1 } else if ch == ")" { depth -= 1 }
            if ch == "," && depth == 0 { parts.append(cur); cur = "" } else { cur.append(ch) }
        }
        if !cur.isEmpty { parts.append(cur) }
        let kw: Set<String> = ["PRIMARY", "UNIQUE", "CHECK", "FOREIGN", "CONSTRAINT"]
        var names: [String] = []
        let re = try! NSRegularExpression(pattern: "^[\\[`\"']?([A-Za-z_][A-Za-z0-9_]*)")
        for p in parts {
            let t = p.trimmingCharacters(in: .whitespaces)
            let ns = t as NSString
            guard let m = re.firstMatch(in: t, range: NSRange(location: 0, length: ns.length)),
                  m.numberOfRanges > 1 else { continue }
            let nm = ns.substring(with: m.range(at: 1))
            if !kw.contains(nm.uppercased()) { names.append(nm) }
        }
        return names
    }

    static func pickColumns(_ cols: [String]) -> (rowid: Int, time: Int, text: Int, dir: Int) {
        let low = cols.map { $0.lowercased() }
        func find(_ cands: [String], _ dflt: Int) -> Int {
            for w in cands { if let i = low.firstIndex(of: w) { return i } }
            for w in cands { if let i = low.firstIndex(where: { $0.contains(w) }) { return i } }
            return dflt
        }
        return (find(["meslocalid", "localid", "rowid"], 0),
                find(["createtime", "create_time", "time"], 2),
                find(["message", "msgcontent", "content", "msg"], 3),
                find(["des", "issend", "direction"], 6))
    }

    private func decodeOne(_ payload: [UInt8], _ idx: (rowid: Int, time: Int, text: Int, dir: Int)) -> [Field]? {
        guard let (vals, used) = decodeRecord(payload), used == payload.count else { return nil }
        if idx.time < vals.count, let t = vals[idx.time].intVal, t < kTimeMin || t > kTimeMax { return nil }
        guard idx.text < vals.count else { return nil }
        if vals[idx.text].isEmptyText { return nil }
        return vals
    }

    private func allLivePairs(_ tables: [(name: String, root: Int, sql: String)]) -> Set<String> {
        var set = Set<String>()
        for t in tables where t.name == "Message" || t.name.hasPrefix("Chat_") {
            let cols = parseColumns(t.sql)
            guard !cols.isEmpty else { continue }
            let idx = Engine.pickColumns(cols)
            for pg in db.btreePages(t.root) {
                guard let page = db.page(pg) else { continue }
                for (_, payload) in db.parseLeafCells(page, pg) {
                    guard let (vals, _) = decodeRecord(payload),
                          idx.time < vals.count, idx.text < vals.count else { continue }
                    let text = decodeWechatMsg(vals[idx.text].bytesVal)
                    set.insert("\(vals[idx.time].intVal ?? -1)\u{0}\(text)")
                }
            }
        }
        return set
    }

    /// table == nil 表示"整库全扫"（左滑删掉整个会话、表已 DROP 时用）
    func carve(table: String?,
               progress: @escaping (String, Double) -> Void) -> (rows: [RecoveredRow], stats: CarveStats) {

        let tables = readMasterTables()
        let chatTables = tables.filter { $0.name == "Message" || $0.name.hasPrefix("Chat_") }

        let defaultCols = ["mesLocalID", "mesSvrID", "CreateTime", "Message",
                           "Status", "ImgStatus", "des", "msgSource"]
        var cols = defaultCols
        var target: (name: String, root: Int, sql: String)? = nil
        if let t = table, let found = chatTables.first(where: { $0.name == t }) {
            target = found
            let c = parseColumns(found.sql)
            if !c.isEmpty { cols = c }
        }
        let scanAll = (target == nil)
        let idx = Engine.pickColumns(cols)
        let free = db.freelistPages()

        progress("读取现存消息", 3)
        let myPages: [Int] = target != nil ? db.btreePages(target!.root)
                                           : Array(1...max(1, db.npages))
        var liveIds = Set<Int>()
        if let t = target {
            for pg in db.btreePages(t.root) {
                guard let page = db.page(pg) else { continue }
                for (rowid, _) in db.parseLeafCells(page, pg) { liveIds.insert(rowid) }
            }
        }
        let livePairs = allLivePairs(chatTables)

        progress("扫描空闲块与间隙", 12)
        var cand: [String: (payload: [UInt8], src: String, vals: [Field])] = [:]

        func add(_ rowid: Int, _ payload: [UInt8], _ src: String) {
            guard let vals = decodeOne(payload, idx) else { return }
            if scanAll {
                let key0 = "\(vals[idx.time].intVal ?? -1)\u{0}\(decodeWechatMsg(vals[idx.text].bytesVal))"
                if livePairs.contains(key0) { return }   // 还在库里，不是被删的
            }
            let key = scanAll ? "\(rowid):\(sha1Short(payload))" : "\(rowid)"
            if let old = cand[key], old.vals.count >= vals.count { return }
            cand[key] = (payload, src, vals)
        }

        var done = 0
        for pgno in myPages {
            var versions: [([UInt8], String)] = []
            if let mp = db.page(pgno) { versions.append((mp, "main")) }
            if let frames = wal.frames[pgno] { for f in frames { versions.append((f, "wal")) } }
            let onFree = free.contains(pgno)
            for (page, tag) in versions {
                for (rowid, payload) in db.parseLeafCells(page, pgno) {
                    if liveIds.contains(rowid) { continue }
                    add(rowid, payload, tag == "wal" ? "wal-frame"
                        : (onFree ? "freelist-page" : "live-page-cell"))
                }
                var regions: [(String, [UInt8])] = db.pageFreeblocks(page, pgno).map { ("freeblock", $0) }
                if let gap = db.pageGap(page, pgno), gap.count >= 6 { regions.append(("unallocated", gap)) }
                if tag == "main" && onFree { regions.append(("freelist-bytes", Array(page[8...]))) }
                for (rtag, reg) in regions {
                    if reg.count < 6 || reg.count > 262_144 { continue }
                    for (rowid, payload) in scanBlock(reg, idx) {
                        if liveIds.contains(rowid) { continue }
                        add(rowid, payload, tag == "wal" ? "wal-frame" : rtag)
                    }
                }
            }
            done += 1
            if done % 20 == 0 {
                progress("扫描空闲块与间隙（已捞 \(cand.count) 条）",
                         12 + 48 * Double(done) / Double(max(1, myPages.count)))
            }
        }

        progress("汇总全库现存消息", 60)
        var rows: [RecoveredRow] = []
        for (key, c) in cand.sorted(by: { $0.key < $1.key }) {
            let vals = c.vals
            let ts = vals[idx.time].intVal
            let dir = idx.dir < vals.count ? vals[idx.dir].intVal : nil
            let text = decodeWechatMsg(vals[idx.text].bytesVal)
            if scanAll && text.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty && ts == nil { continue }
            let rid = Int(key.split(separator: ":").first.map(String.init) ?? "") ?? nil
            var tbl = target?.name ?? "(全库)"
            if scanAll, let raw = vals[idx.text].bytesVal, let peer = inferPeer(raw, text) {
                tbl = "Chat_" + md5Hex(peer)
            }
            rows.append(RecoveredRow(tbl: tbl, rowid: rid, ts: ts, dir: dir, text: text, source: c.src))
        }

        var stats = CarveStats()
        stats.live = liveIds.count
        stats.recRows = rows.count

        progress("内容级兜底扫描", 62)
        var scanPages: [(Int, [UInt8])] = []
        for n in 1...max(1, db.npages) { if let p = db.page(n) { scanPages.append((n, p)) } }
        for (pgno, frames) in wal.frames { for f in frames { scanPages.append((pgno, f)) } }

        var seen = Set<String>()
        for r in rows { seen.insert("\(r.ts ?? -1)\u{0}\(r.text)") }
        var i = 0
        for (_, page) in scanPages {
            i += 1
            if i % 40 == 0 {
                progress("内容级兜底扫描（已捞 \(stats.contentRows) 条）",
                         62 + 36 * Double(i) / Double(max(1, scanPages.count)))
            }
            for hit in findWxBlobs(page, db: db) {
                let text = decodeWechatMsg(hit.blob)
                if text.isEmpty || scoreText(text) < 15 { continue }
                let key = "\(hit.ts ?? -1)\u{0}\(text)"
                if seen.contains(key) || livePairs.contains(key) { continue }
                seen.insert(key)
                var tbl = target?.name ?? "(全库)"
                if let peer = inferPeer(hit.blob, text) { tbl = "Chat_" + md5Hex(peer) }
                rows.append(RecoveredRow(tbl: tbl, rowid: hit.rowid, ts: hit.ts,
                                         dir: nil, text: text, source: "content-carve"))
                stats.contentRows += 1
            }
        }
        rows.sort { ($0.ts ?? 0) < ($1.ts ?? 0) }
        stats.total = rows.count
        var srcCount: [String: Int] = [:]
        for r in rows { srcCount[r.source, default: 0] += 1 }
        stats.sources = srcCount.sorted { $0.value > $1.value }
            .map { SrcCount(name: $0.key, count: $0.value) }
        progress("完成", 100)
        return (rows, stats)
    }

    private func scanBlock(_ block: [UInt8], _ idx: (rowid: Int, time: Int, text: Int, dir: Int)) -> [(Int, [UInt8])] {
        var out: [(Int, [UInt8])] = []
        for off in 0..<block.count {
            guard let (rowid, payload, _) = try? db.readCellBuf(block, off) else { continue }
            if payload.count > 2 * 1024 * 1024 { continue }
            guard decodeOne(payload, idx) != nil else { continue }
            out.append((rowid, payload))
            if out.count >= 500 { break }
        }
        return out
    }
}

func inferPeer(_ blob: [UInt8], _ text: String) -> String? {
    let re = try! NSRegularExpression(pattern: "wxid_[A-Za-z0-9_]{3,40}")
    if let s = String(bytes: blob, encoding: .utf8), let m = re.firstMatch(in: s, range: NSRange(s.startIndex..., in: s)) {
        return (s as NSString).substring(with: m.range)
    }
    let t = text
    if let m = re.firstMatch(in: t, range: NSRange(t.startIndex..., in: t)) {
        return (t as NSString).substring(with: m.range)
    }
    return nil
}

/// 微信每个联系人一张 Chat_<md5(wxid)> 表，所以必须用真 MD5 才能反推表名
func md5Hex(_ s: String) -> String {
    let digest = Insecure.MD5.hash(data: Data(s.utf8))
    return digest.map { String(format: "%02x", $0) }.joined()
}

func sha1Short(_ b: [UInt8], _ n: Int = 12) -> String {
    let digest = Insecure.SHA1.hash(data: Data(b))
    return digest.prefix(n).map { String(format: "%02x", $0) }.joined()
}

// MARK: - 界面

/// 读用户通过文件选择器给的文件（需要 security-scoped 访问）
func readPickableFile(_ url: URL) -> [UInt8]? {
    let scoped = url.startAccessingSecurityScopedResource()
    defer { if scoped { url.stopAccessingSecurityScopedResource() } }
    guard let data = try? Data(contentsOf: url) else { return nil }
    return [UInt8](data)
}

struct ContentView: View {
    @State private var dbURL: URL?
    @State private var walURL: URL?
    @State private var showPicker = false
    @State private var pickForWal = false
    @State private var busy = false
    @State private var progressText = ""
    @State private var progress = 0.0
    @State private var message = ""
    @State private var rows: [RecoveredRow] = []
    @State private var stats: CarveStats?
    @State private var chatTables: [String] = []
    @State private var chosen: String?
    @State private var showImporter = false
    @State private var autoStatus = ""
    @State private var autoRan = false

    var body: some View {
        NavigationView {
            ScrollView {
                VStack(alignment: .leading, spacing: 14) {
                    if !autoStatus.isEmpty {
                        Text(autoStatus).font(.footnote).foregroundColor(.green)
                    }

                    GroupBox("1 · 选择数据库文件") {
                        VStack(alignment: .leading, spacing: 8) {
                            Button {
                                pickForWal = false; showPicker = true
                            } label: {
                                Label(dbURL?.lastPathComponent ?? "选择 MM.sqlite（必选）",
                                      systemImage: "doc.badge.plus")
                            }
                            Button {
                                pickForWal = true; showPicker = true
                            } label: {
                                Label(walURL?.lastPathComponent ?? "选择 MM.sqlite-wal（强烈建议）",
                                      systemImage: "doc.badge.plus")
                            }
                            Text("提示：-wal 里有同一页的历史镜像，实测能把恢复率从 58% 提到 80%。")
                                .font(.caption).foregroundColor(.secondary)
                            Button("开始解析") { load() }
                                .buttonStyle(.borderedProminent)
                                .disabled(dbURL == nil || busy)
                        }
                    }

                    if !chatTables.isEmpty {
                        GroupBox("2 · 选择要恢复的聊天") {
                            VStack(alignment: .leading, spacing: 8) {
                                Picker("聊天表", selection: $chosen) {
                                    ForEach(chatTables, id: \.self) { Text($0).tag(Optional($0)) }
                                }
                                Button("恢复这张表") { carve(table: chosen) }
                                    .disabled(busy)
                                Button("整个会话被左滑删了？点这里（全库扫）") { carve(table: nil) }
                                    .disabled(busy)
                            }
                        }
                    }

                    if busy || progress > 0 {
                        GroupBox("进度") {
                            VStack(alignment: .leading, spacing: 6) {
                                ProgressView(value: progress, total: 100)
                                Text(progressText).font(.caption).foregroundColor(.secondary)
                            }
                        }
                    }

                    if let st = stats {
                        GroupBox("3 · 结果") {
                            VStack(alignment: .leading, spacing: 4) {
                                statLine("该表现存消息", "\(st.live)")
                                statLine("完整记录恢复", "\(st.recRows)")
                                statLine("内容级恢复", "\(st.contentRows)")
                                statLine("合计捞回", "\(st.total)")
                                ForEach(st.sources) { s in
                                    statLine("来源 \(s.name)", "\(s.count)")
                                }
                                if !rows.isEmpty {
                                    ShareLink(item: exportCSV()) { Text("导出 CSV") }
                                }
                            }
                        }
                    }

                    if !message.isEmpty {
                        Text(message).font(.caption).foregroundColor(.secondary)
                    }

                    if !rows.isEmpty {
                        GroupBox("捞回的消息（\(rows.count) 条）") {
                            VStack(alignment: .leading, spacing: 8) {
                                ForEach(Array(rows.prefix(300))) { r in
                                    VStack(alignment: .leading, spacing: 2) {
                                        HStack(spacing: 6) {
                                            Text(fmtTime(r.ts)).font(.caption2).foregroundColor(.secondary)
                                            if let d = r.dir {
                                                Text(d == 0 ? "我发出" : "对方")
                                                    .font(.caption2).foregroundColor(d == 0 ? .purple : .green)
                                            }
                                            Text(r.source).font(.caption2).foregroundColor(.blue)
                                            if let id = r.rowid { Text("rowid \(id)").font(.caption2).foregroundColor(.secondary) }
                                        }
                                        Text(r.text).font(.system(size: 14))
                                    }
                                    Divider()
                                }
                                if rows.count > 300 {
                                    Text("只显示前 300 条，完整内容请导出 CSV。")
                                        .font(.caption).foregroundColor(.secondary)
                                }
                            }
                        }
                    }
                }
                .padding()
            }
            .navigationTitle("微信聊天记录恢复")
            .toolbar {
                ToolbarItem(placement: .navigationBarTrailing) {
                    Button("重扫") { autoRan = false; autoLoadFromDocuments() }
                }
            }
            .onAppear { autoLoadFromDocuments() }
            .fileImporter(isPresented: $showPicker,
                          allowedContentTypes: [.data, .database],
                          allowsMultipleSelection: false) { result in
                if case .success(let urls) = result, let u = urls.first {
                    if pickForWal { walURL = u } else { dbURL = u }
                }
            }
        }
    }

    private func statLine(_ k: String, _ v: String) -> some View {
        HStack { Text(k); Spacer(); Text(v).bold() }
    }

    /// 打开 App 就自动在"本 App 的文件夹"里找数据库并直接开始恢复。
    /// （iOS 不允许任何 App 读微信自己的目录，所以数据得由你把备份里取出的
    ///   MM.sqlite 放到"文件"App → 微信恢复 这个文件夹里，之后全自动。）
    private func autoLoadFromDocuments() {
        guard !autoRan else { return }
        autoRan = true
        let docs = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask)[0]
        guard let en = FileManager.default.enumerator(at: docs,
                                                      includingPropertiesForKeys: [.fileSizeKey],
                                                      options: [.skipsHiddenFiles]) else { return }
        var dbs: [URL] = []
        var all: [URL] = []
        for case let u as URL in en {
            guard u.hasDirectoryPath == false else { continue }
            all.append(u)
            let n = u.lastPathComponent.lowercased()
            if n.hasSuffix(".sqlite") || n.hasSuffix(".db") || n == "mm.sqlite" {
                dbs.append(u)
            }
        }
        guard let db = dbs.max(by: { fileSize($0) < fileSize($1) }) else {
            autoStatus = "把 MM.sqlite（和 MM.sqlite-wal）拷进：文件 App → 微信恢复 文件夹，重开本 App 即自动开始。"
            return
        }
        let wal = all.first { $0.lastPathComponent == db.lastPathComponent + "-wal" }
        dbURL = db
        walURL = wal
        autoStatus = "已自动载入 \(db.lastPathComponent)"
            + (wal != nil ? " + wal" : "") + "，正在自动恢复…"
        load(autoCarve: true)
    }

    private func fileSize(_ u: URL) -> Int {
        (try? u.resourceValues(forKeys: [.fileSizeKey]).fileSize) ?? 0
    }

    private func load(autoCarve: Bool = false) {
        guard let dbURL = dbURL else { return }
        busy = true; message = ""; rows = []; stats = nil; chatTables = []
        progress = 0; progressText = "读取文件…"
        DispatchQueue.global(qos: .userInitiated).async {
            guard let dbBytes = readPickableFile(dbURL) else {
                DispatchQueue.main.async { busy = false; message = "读不到文件，请重新选择。" }
                return
            }
            let walBytes = walURL != nil ? readPickableFile(walURL!) : nil
            do {
                let db = try Db(bytes: dbBytes)
                let wal = WalFile(bytes: walBytes, pageSizeHint: db.pageSize)
                let eng = Engine(db: db, wal: wal)
                let tables = eng.readMasterTables()
                    .filter { $0.name == "Message" || $0.name.hasPrefix("Chat_") }
                    .map { $0.name }
                DispatchQueue.main.async {
                    busy = false
                    chatTables = tables
                    chosen = tables.first
                    message = "页大小 \(db.pageSize)B，共 \(db.npages) 页，freelist \(db.nFreelist) 页"
                        + (wal.frameCount > 0 ? "，WAL \(wal.frameCount) 帧 / 覆盖 \(wal.frames.count) 页" : "")
                    progressText = "解析完成"
                    if autoCarve {
                        autoStatus = "已自动载入并开始全库恢复…"
                        carve(table: nil)      // 全库扫：连被删掉的会话一起捞
                    }
                }
            } catch {
                DispatchQueue.main.async { busy = false; message = "解析失败：\((error as? DbError)?.msg ?? "\(error)")" }
            }
        }
    }

    private func carve(table: String?) {
        guard let dbURL = dbURL else { return }
        busy = true; rows = []; stats = nil; progress = 0
        DispatchQueue.global(qos: .userInitiated).async {
            guard let dbBytes = readPickableFile(dbURL) else {
                DispatchQueue.main.async { busy = false; message = "读不到文件。" }
                return
            }
            let walBytes = walURL != nil ? readPickableFile(walURL!) : nil
            do {
                let db = try Db(bytes: dbBytes)
                let eng = Engine(db: db, wal: WalFile(bytes: walBytes, pageSizeHint: db.pageSize))
                let result = eng.carve(table: table) { phase, pct in
                    DispatchQueue.main.async { progressText = phase; progress = pct }
                }
                DispatchQueue.main.async {
                    busy = false
                    rows = result.rows
                    stats = result.stats
                    progressText = "完成"
                }
            } catch {
                DispatchQueue.main.async { busy = false; message = "恢复失败：\((error as? DbError)?.msg ?? "\(error)")" }
            }
        }
    }

    private func fmtTime(_ ts: Int?) -> String {
        guard let ts = ts else { return "时间未知" }
        let f = DateFormatter()
        f.dateFormat = "yyyy-MM-dd HH:mm:ss"
        return f.string(from: Date(timeIntervalSince1970: TimeInterval(ts)))
    }

    private func exportCSV() -> URL {
        var csv = "\u{FEFF}时间,方向,rowid,来源,正文\n"
        for r in rows {
            let dir = r.dir == 0 ? "我发出" : (r.dir == 1 ? "对方" : "")
            let text = "\"" + r.text.replacingOccurrences(of: "\"", with: "\"\"") + "\""
            csv += "\(fmtTime(r.ts)),\(dir),\(r.rowid.map(String.init) ?? ""),\(r.source),\(text)\n"
        }
        let url = FileManager.default.temporaryDirectory.appendingPathComponent("微信恢复.csv")
        try? csv.data(using: .utf8)?.write(to: url)
        return url
    }
}

@main
struct WxCarveApp: App {
    var body: some Scene {
        WindowGroup { ContentView() }
    }
}
