// gpukit implementation (Objective-C++, ARC). See gpu.hpp and docs/gpukit.md.
#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
#include "gpu.hpp"
#include <cstdio>
#include <cstdlib>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <mach-o/dyld.h>
#include <climits>
#include <string>
#include <unistd.h>

namespace gpukit {

struct Device::Impl {
  id<MTLDevice> dev = nil;
  id<MTLCommandQueue> q = nil;
  uint64_t allocated = 0, cap = 0;
  int lockfd = -1;
  double gpuSec = 0;
  uint64_t ndisp = 0;
};

// Lock file: $GPUKIT_LOCK, else $PNP_SLOTS/gpu.lock, else <dir of the executable>/../.slots/gpu.lock
// (= toolkit/.slots/gpu.lock for tools in toolkit/bin, the same file bin/gpurun uses).
static std::string lock_path() {
  const char* p = getenv("GPUKIT_LOCK");
  if (p && *p) return p;
  std::string dir;
  const char* s = getenv("PNP_SLOTS");
  if (s && *s) {
    dir = s;
  } else {
    char buf[4096];
    uint32_t n = sizeof buf;
    std::string exe = (_NSGetExecutablePath(buf, &n) == 0) ? std::string(buf) : std::string("./x");
    char* real = realpath(exe.c_str(), nullptr);
    if (real) { exe = real; free(real); }
    size_t k = exe.find_last_of('/');
    dir = (k == std::string::npos ? std::string(".") : exe.substr(0, k)) + "/../.slots";
  }
  ::mkdir(dir.c_str(), 0755);
  return dir + "/gpu.lock";
}

static int take_lock(bool quiet) {
  if (getenv("GPURUN_HELD")) return -1;                 // bin/gpurun already holds it for us
  const std::string lp = lock_path();
  const char* path = lp.c_str();
  int fd = ::open(path, O_RDWR | O_CREAT, 0644);
  if (fd < 0) { if (!quiet) fprintf(stderr, "gpukit: cannot open lock %s (continuing without)\n", path); return -1; }
  if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
    if (!quiet) fprintf(stderr, "gpukit: GPU is busy (lock %s), waiting...\n", path);
    while (flock(fd, LOCK_EX) != 0) usleep(100000);
  }
  char tag[128];
  int n = snprintf(tag, sizeof tag, "pid %d (gpukit in-process lock)\n", (int)getpid());
  if (ftruncate(fd, 0) == 0) (void)!pwrite(fd, tag, (size_t)n, 0);
  return fd;
}

Device* Device::open(std::string* err, const OpenOpts& o) {
  @autoreleasepool {
    id<MTLDevice> dev = MTLCreateSystemDefaultDevice();
    if (!dev) {
      NSArray<id<MTLDevice>>* all = MTLCopyAllDevices();
      if (all.count) dev = all[0];
    }
    if (!dev) { if (err) *err = "no Metal device"; return nullptr; }
    Device* d = new Device();
    d->p = new Impl();
    d->p->lockfd = o.lock ? take_lock(o.quiet) : -1;
    d->p->dev = dev;
    d->p->q = [dev newCommandQueue];
    uint64_t cap = o.maxBytes;
    if (!cap) { const char* e = getenv("GPUKIT_MAX_BYTES"); cap = e ? strtoull(e, nullptr, 10) : (uint64_t(2) << 30); }
    d->p->cap = cap;
    return d;
  }
}

Device::~Device() {
  if (!p) return;
  if (p->lockfd >= 0) { flock(p->lockfd, LOCK_UN); close(p->lockfd); }
  delete p;
}

std::string Device::name() const { return std::string([[p->dev name] UTF8String]); }
uint64_t Device::max_buffer_bytes() const { return (uint64_t)[p->dev maxBufferLength]; }
uint64_t Device::allocated_bytes() const { return p->allocated; }
double Device::gpu_seconds() const { return p->gpuSec; }
uint64_t Device::dispatches() const { return p->ndisp; }

Kernel Device::compile(const std::string& src, const std::string& fn, std::string* err) {
  Kernel k;
  @autoreleasepool {
    NSError* e = nil;
    MTLCompileOptions* opt = [MTLCompileOptions new];
    id<MTLLibrary> lib = [p->dev newLibraryWithSource:[NSString stringWithUTF8String:src.c_str()] options:opt error:&e];
    if (!lib) { if (err) *err = std::string("compile: ") + [[e localizedDescription] UTF8String]; return k; }
    id<MTLFunction> f = [lib newFunctionWithName:[NSString stringWithUTF8String:fn.c_str()]];
    if (!f) { if (err) *err = "no kernel function named " + fn; return k; }
    id<MTLComputePipelineState> pso = [p->dev newComputePipelineStateWithFunction:f error:&e];
    if (!pso) { if (err) *err = std::string("pipeline: ") + [[e localizedDescription] UTF8String]; return k; }
    k.simd = (uint32_t)pso.threadExecutionWidth;
    k.maxGroup = (uint32_t)pso.maxTotalThreadsPerThreadgroup;
    k.name = fn;
    k.h = (__bridge_retained void*)pso;
  }
  return k;
}

void Device::release(Kernel& k) {
  if (k.h) { (void)(__bridge_transfer id<MTLComputePipelineState>)k.h; k.h = nullptr; }
}

Buffer Device::alloc(size_t bytes, std::string* err) {
  Buffer b;
  if (bytes == 0) bytes = 16;
  if (p->allocated + bytes > p->cap) {
    if (err) *err = "gpukit: alloc of " + std::to_string(bytes) + " bytes would exceed the cap of " + std::to_string(p->cap) +
                    " (already " + std::to_string(p->allocated) + "); raise GPUKIT_MAX_BYTES deliberately if you must";
    return b;
  }
  @autoreleasepool {
    id<MTLBuffer> mb = [p->dev newBufferWithLength:bytes options:MTLResourceStorageModeShared];
    if (!mb) { if (err) *err = "gpukit: newBufferWithLength failed"; return b; }
    b.data = [mb contents];
    b.bytes = bytes;
    b.h = (__bridge_retained void*)mb;
    p->allocated += bytes;
  }
  return b;
}

void Device::free(Buffer& b) {
  if (!b.h) return;
  (void)(__bridge_transfer id<MTLBuffer>)b.h;
  p->allocated -= b.bytes;
  b = Buffer();
}

Ticket Device::submit(const std::vector<Dispatch>& ds) {
  Ticket t;
  @autoreleasepool {
    id<MTLCommandBuffer> cb = [p->q commandBuffer];
    id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
    for (const Dispatch& d : ds) {
      id<MTLComputePipelineState> pso = (__bridge id<MTLComputePipelineState>)d.k->h;
      [enc setComputePipelineState:pso];
      for (const auto& b : d.args.bufs) [enc setBuffer:(__bridge id<MTLBuffer>)b.h offset:b.off atIndex:(NSUInteger)b.idx];
      for (const auto& c : d.args.consts) [enc setBytes:c.bytes.data() length:c.bytes.size() atIndex:(NSUInteger)c.idx];
      NSUInteger sw = d.k->simd ? d.k->simd : 32, mg = d.k->maxGroup ? d.k->maxGroup : 1024;
      MTLSize tg;
      if (d.h <= 1) tg = MTLSizeMake(mg, 1, 1);
      else tg = MTLSizeMake(sw, mg / sw ? mg / sw : 1, 1);
      [enc dispatchThreads:MTLSizeMake(d.w, d.h ? d.h : 1, 1) threadsPerThreadgroup:tg];
    }
    [enc endEncoding];
    [cb commit];
    t.h = (__bridge_retained void*)cb;
  }
  return t;
}

double Device::wait(Ticket& t, std::string* err) {
  if (!t.h) { if (err) *err = "null ticket"; return -1; }
  double s = -1;
  @autoreleasepool {
    id<MTLCommandBuffer> cb = (__bridge_transfer id<MTLCommandBuffer>)t.h;
    t.h = nullptr;
    [cb waitUntilCompleted];
    if (cb.status == MTLCommandBufferStatusError || cb.error) {
      if (err) *err = std::string("gpu: ") + (cb.error ? [[cb.error localizedDescription] UTF8String] : "command buffer error");
      return -1;
    }
    s = cb.GPUEndTime - cb.GPUStartTime;
    if (s < 0) s = 0;
    p->gpuSec += s;
    p->ndisp++;
  }
  return s;
}

}  // namespace gpukit
