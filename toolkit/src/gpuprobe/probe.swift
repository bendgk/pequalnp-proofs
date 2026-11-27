// GPU feasibility probe: "score every pair of wires" kernel (the inner loop of cktopt resubstitution / cktsls heat bath).
// For W wires of P bits: for every pair (a,b) compute popcount(((A|B)^T)&C) and popcount(((A&B)^T)&C) over all words.
import Metal
import Foundation

let W = Int(CommandLine.arguments.count > 1 ? CommandLine.arguments[1] : "1024")!
let P = Int(CommandLine.arguments.count > 2 ? CommandLine.arguments[2] : "16384")!
let words32 = P / 32
let src = """
#include <metal_stdlib>
using namespace metal;
kernel void score(device const uint *cols [[buffer(0)]], device const uint *T [[buffer(1)]], device const uint *C [[buffer(2)]],
                  device uint *out [[buffer(3)]], constant uint &W [[buffer(4)]], constant uint &NW [[buffer(5)]],
                  uint2 gid [[thread_position_in_grid]]) {
    if (gid.x >= W || gid.y >= W) return;
    uint a = gid.x * NW, b = gid.y * NW, co = 0, ca = 0;
    for (uint w = 0; w < NW; w++) {
        uint x = cols[a + w], y = cols[b + w], t = T[w], c = C[w];
        co += popcount(((x | y) ^ t) & c);
        ca += popcount(((x & y) ^ t) & c);
    }
    out[(gid.y * W + gid.x) * 2] = co; out[(gid.y * W + gid.x) * 2 + 1] = ca;
}
"""
guard let dev = MTLCreateSystemDefaultDevice() else { print("no Metal device"); exit(1) }
print("device:", dev.name, " maxBufferLength GB:", dev.maxBufferLength >> 30)
let lib = try! dev.makeLibrary(source: src, options: nil)
let pso = try! dev.makeComputePipelineState(function: lib.makeFunction(name: "score")!)
var rng = SystemRandomNumberGenerator()
var cols = [UInt32](repeating: 0, count: W * words32); for i in 0..<cols.count { cols[i] = UInt32.random(in: 0...UInt32.max, using: &rng) }
var T = [UInt32](repeating: 0, count: words32); for i in 0..<words32 { T[i] = UInt32.random(in: 0...UInt32.max, using: &rng) }
let C = [UInt32](repeating: 0xffffffff, count: words32)
let bc = dev.makeBuffer(bytes: cols, length: cols.count * 4, options: .storageModeShared)!
let bt = dev.makeBuffer(bytes: T, length: words32 * 4, options: .storageModeShared)!
let bC = dev.makeBuffer(bytes: C, length: words32 * 4, options: .storageModeShared)!
let bo = dev.makeBuffer(length: W * W * 8, options: .storageModeShared)!
var w32 = UInt32(W), nw = UInt32(words32)
let q = dev.makeCommandQueue()!
func run() -> Double {
    let t0 = Date()
    let cb = q.makeCommandBuffer()!, enc = cb.makeComputeCommandEncoder()!
    enc.setComputePipelineState(pso)
    enc.setBuffer(bc, offset: 0, index: 0); enc.setBuffer(bt, offset: 0, index: 1); enc.setBuffer(bC, offset: 0, index: 2); enc.setBuffer(bo, offset: 0, index: 3)
    enc.setBytes(&w32, length: 4, index: 4); enc.setBytes(&nw, length: 4, index: 5)
    enc.dispatchThreads(MTLSize(width: W, height: W, depth: 1), threadsPerThreadgroup: MTLSize(width: pso.threadExecutionWidth, height: pso.maxTotalThreadsPerThreadgroup / pso.threadExecutionWidth, depth: 1))
    enc.endEncoding(); cb.commit(); cb.waitUntilCompleted()
    return Date().timeIntervalSince(t0)
}
_ = run()
var best = 1e9; for _ in 0..<5 { best = min(best, run()) }
let pairs = Double(W) * Double(W)
print(String(format: "GPU: W=%d P=%d  %.4f s per all-pairs pass  = %.3e pair-scores/s = %.3e bit-ops/s (2 ops x P bits per pair)", W, P, best, pairs / best, pairs * Double(P) * 2 / best))
// CPU single-core reference (64-bit words)
let nw64 = P / 64
var c64 = [UInt64](repeating: 0, count: W * nw64); for i in 0..<c64.count { c64[i] = UInt64.random(in: 0...UInt64.max, using: &rng) }
var t64 = [UInt64](repeating: 0, count: nw64); for i in 0..<nw64 { t64[i] = UInt64.random(in: 0...UInt64.max, using: &rng) }
let sub = min(W, 192)
let t0 = Date(); var acc: UInt64 = 0
c64.withUnsafeBufferPointer { cp in t64.withUnsafeBufferPointer { tp in
    for a in 0..<sub { for b in 0..<sub {
        var co = 0, ca = 0
        for w in 0..<nw64 { let x = cp[a * nw64 + w], y = cp[b * nw64 + w], t = tp[w]
            co += ((x | y) ^ t).nonzeroBitCount; ca += ((x & y) ^ t).nonzeroBitCount }
        acc &+= UInt64(co) &+ UInt64(ca)
    } } } }
let dt = Date().timeIntervalSince(t0)
let cpuRate = Double(sub * sub) / dt
print(String(format: "CPU 1 core: %.3e pair-scores/s  (checksum %llu)  => GPU = %.1f CPU cores on this kernel", cpuRate, acc, (pairs / best) / cpuRate))
