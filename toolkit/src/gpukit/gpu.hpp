// gpukit — minimal Metal compute harness with a plain C++ API (no Objective-C types leak out).
//   Device::open()  ->  compile(MSL source string)  ->  alloc() shared buffers  ->  run1d / run2d  ->  read buffer.data
// Buffers are MTLStorageModeShared: on Apple silicon `data` IS the memory the GPU reads/writes (zero copy);
// after wait() returns, results are simply there. See docs/gpukit.md.
// Build: clang++ -std=c++20 -O3 -fobjc-arc -c gpu.mm ; link with -framework Metal -framework Foundation -framework CoreGraphics
#pragma once
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace gpukit {

struct Buffer {
  void* data = nullptr;   // CPU pointer to the shared memory (page aligned, zero-filled at alloc)
  size_t bytes = 0;
  void* h = nullptr;      // retained id<MTLBuffer>
  template <class T> T* as() const { return (T*)data; }
  explicit operator bool() const { return h != nullptr; }
};

struct Kernel {
  void* h = nullptr;             // retained id<MTLComputePipelineState>
  uint32_t simd = 32;            // threadExecutionWidth
  uint32_t maxGroup = 1024;      // maxTotalThreadsPerThreadgroup
  std::string name;
  explicit operator bool() const { return h != nullptr; }
};

// Bindings of one dispatch: buffers at [[buffer(i)]] indices and small by-value constants (`constant T &x [[buffer(i)]]`).
struct Args {
  struct B { int idx; void* h; size_t off; };
  struct C { int idx; std::vector<uint8_t> bytes; };
  std::vector<B> bufs;
  std::vector<C> consts;
  Args& buf(int idx, const Buffer& b, size_t byteOffset = 0) { bufs.push_back({idx, b.h, byteOffset}); return *this; }
  template <class T> Args& val(int idx, const T& v) {   // POD, <= 4 KB (Metal setBytes)
    C c; c.idx = idx; c.bytes.resize(sizeof(T)); std::memcpy(c.bytes.data(), &v, sizeof(T)); consts.push_back(std::move(c)); return *this;
  }
  Args& u32(int idx, uint32_t v) { return val<uint32_t>(idx, v); }
};

struct Dispatch { const Kernel* k = nullptr; Args args; size_t w = 1, h = 1; };   // grid w x h (h = 1: 1D)
struct Ticket { void* h = nullptr; };   // a committed command buffer

struct OpenOpts {
  bool lock = true;          // take the machine-wide one-job GPU lock (skipped when started under bin/gpurun)
  uint64_t maxBytes = 0;     // cap on the sum of alloc()ed buffers; 0 = $GPUKIT_MAX_BYTES or 2 GiB
  bool quiet = false;
};

class Device {
 public:
  // nullptr (and *err) if there is no Metal device. Blocks while another process holds the GPU lock.
  static Device* open(std::string* err = nullptr, const OpenOpts& o = OpenOpts());
  ~Device();
  std::string name() const;
  uint64_t max_buffer_bytes() const;     // device limit for ONE buffer
  uint64_t allocated_bytes() const;      // sum of live alloc()s
  // Compile `fn` (a `kernel void fn(...)`) from Metal Shading Language source. Returns a null Kernel and *err on failure.
  Kernel compile(const std::string& mslSource, const std::string& fn, std::string* err = nullptr);
  void release(Kernel& k);
  Buffer alloc(size_t bytes, std::string* err = nullptr);   // null Buffer if over the cap
  void free(Buffer& b);
  // Asynchronous: encode + commit, returns at once. Dispatches of one submit run in order in ONE command buffer.
  Ticket submit(const std::vector<Dispatch>& ds);
  Ticket submit1d(const Kernel& k, const Args& a, size_t n) { return submit({Dispatch{&k, a, n, 1}}); }
  Ticket submit2d(const Kernel& k, const Args& a, size_t w, size_t h) { return submit({Dispatch{&k, a, w, h}}); }
  // Blocks until done. Returns GPU seconds (GPUEndTime - GPUStartTime) or -1 with *err. Frees the ticket.
  double wait(Ticket& t, std::string* err = nullptr);
  double run1d(const Kernel& k, const Args& a, size_t n, std::string* err = nullptr) { Ticket t = submit1d(k, a, n); return wait(t, err); }
  double run2d(const Kernel& k, const Args& a, size_t w, size_t h, std::string* err = nullptr) { Ticket t = submit2d(k, a, w, h); return wait(t, err); }
  double gpu_seconds() const;            // total GPU time of all waited tickets
  uint64_t dispatches() const;           // number of waited command buffers
  struct Impl;
 private:
  Impl* p = nullptr;
};

// Keeps single dispatches short so WindowServer (same GPU) stays responsive: feed it the measured GPU time of the
// last chunk and it proposes the next chunk size aiming at `target` seconds (default 20 ms), within [lo, hi].
struct Pacer {
  double target = 0.020;
  size_t n, lo, hi;
  Pacer(size_t start, size_t lo_, size_t hi_, double targetSec = 0.020) : target(targetSec), n(start), lo(lo_), hi(hi_) {}
  size_t next(size_t done, double gpuSec) {
    if (gpuSec > 0 && done > 0) {
      double want = (double)done * target / gpuSec;
      double cur = (double)n;
      double nx = cur * 0.5 + want * 0.5;               // damped
      if (nx > cur * 2) nx = cur * 2;
      n = (size_t)nx;
    }
    if (n < lo) n = lo;
    if (n > hi) n = hi;
    return n;
  }
};

}  // namespace gpukit
