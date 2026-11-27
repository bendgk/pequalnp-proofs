# toolkit/Makefile — one build for every native tool. Output goes to bin/ (binaries are git-ignored).
#
#   make                 build everything that builds on this OS (Metal tools only on macOS)
#   make cpu             only the portable C++ tools
#   make gpu             only the Metal tools (macOS)
#   make check           tiny smoke test: cktcheck and the Python reference checker on a seed circuit
#   make clean
#   make PORTABLE=1      no -march/-mcpu=native (binaries that run on any CPU of the same arch)
#   make CXX=g++         pick the compiler (default: clang++ if found, else g++)
#
# Each src/<tool>/Makefile is a thin wrapper around this file, so `make -C src/<tool>` still works.

UNAME_S := $(shell uname -s)
UNAME_M := $(shell uname -m)

ifeq ($(origin CXX),default)
  CXX := $(shell command -v clang++ >/dev/null 2>&1 && echo clang++ || echo g++)
endif

ifeq ($(PORTABLE),1)
  ARCHFLAGS :=
else ifneq ($(filter arm64 aarch64,$(UNAME_M)),)
  ARCHFLAGS := -mcpu=native
else ifneq ($(filter x86_64 amd64,$(UNAME_M)),)
  ARCHFLAGS := -march=native
else
  ARCHFLAGS :=
endif

OPT      ?= -O3
WARN     ?= -Wall -Wextra -Wno-unused-parameter
CXXFLAGS ?= $(OPT) -std=c++20 $(ARCHFLAGS) $(WARN)
CXXFLAGS += -pthread
LDFLAGS  ?=

BIN   := bin
BUILD := build
INC   := include/ckt.hpp

CPU_TOOLS := cktcheck cktopt cktsat-core cktsls graphsynth ptrank startab startab-tricheck andtab
CPU_BINS  := $(addprefix $(BIN)/,$(CPU_TOOLS))

ifeq ($(UNAME_S),Darwin)
  GPU_BINS := $(BIN)/gputest $(BIN)/gpuopt $(BIN)/gpukit-example
  ifneq ($(shell command -v swiftc 2>/dev/null),)
    GPU_BINS += $(BIN)/gpuprobe
  endif
else
  GPU_BINS :=
endif

METAL_FW := -framework Metal -framework Foundation -framework CoreGraphics

.PHONY: all cpu gpu check clean
# Builds and runs belong in the sandbox (sandbox/run; SECURITY.md). Building on the bare host is refused
# unless PNP_IN_SANDBOX=1 (set inside the images and by sandbox/run's macOS Metal sandbox) or the owner of the
# machine opts in with PNP_HOST_BUILD=1 after reading the diff. This guards honest agents against an
# accidental host build; it is not the security boundary (a hostile Makefile could delete it). The boundary
# is that the host only ever runs sandbox/run, which is short and reviewed.
ifneq ($(PNP_IN_SANDBOX)$(PNP_HOST_BUILD),)
else ifneq ($(filter-out clean,$(or $(MAKECMDGOALS),all)),)
  $(error Refusing to build on the host. Use toolkit/sandbox/run build (or set PNP_HOST_BUILD=1 if you reviewed the source))
endif

all: cpu gpu
cpu: $(CPU_BINS)

# CUDA backends: every src/<tool>/cuda/*.cu becomes bin/<tool>-cuda (see PORTING.md). None exist yet.
NVCC    ?= nvcc
CU_SRCS := $(wildcard src/*/cuda/*.cu)
.PHONY: cuda
cuda:
ifeq ($(strip $(CU_SRCS)),)
	@echo "cuda: no CUDA backend in src/*/cuda/ yet. See PORTING.md to add one."
else
	@command -v $(NVCC) >/dev/null || { echo "cuda: nvcc not found"; exit 1; }
	@mkdir -p $(BIN)
	@for f in $(CU_SRCS); do t=$$(echo $$f | cut -d/ -f2); echo "nvcc $$f -> $(BIN)/$$t-cuda"; \
	  $(NVCC) -O3 -std=c++20 -Iinclude -o $(BIN)/$$t-cuda $$f || exit 1; done
endif
gpu: $(GPU_BINS)
ifneq ($(UNAME_S),Darwin)
	@echo "gpu: skipped — the only GPU backend today is Apple Metal (macOS). See PORTING.md to add one."
endif

$(BIN) $(BUILD):
	@mkdir -p $@

# Build to a temporary name and rename, so a running job keeps its old binary.
define LINK
	$(CXX) $(CXXFLAGS) -o $@.new $(1) $(LDFLAGS) && mv -f $@.new $@
endef

$(BIN)/cktcheck: src/cktcheck/cktcheck.cpp $(INC) | $(BIN)
	$(call LINK,src/cktcheck/cktcheck.cpp)
$(BIN)/cktopt: src/cktopt/cktopt.cpp $(INC) | $(BIN)
	$(call LINK,src/cktopt/cktopt.cpp)
$(BIN)/cktsat-core: src/cktsat/core.cpp $(INC) | $(BIN)
	$(call LINK,src/cktsat/core.cpp)
$(BIN)/cktsls: src/cktsls/cktsls.cpp $(INC) | $(BIN)
	$(call LINK,src/cktsls/cktsls.cpp)
$(BIN)/graphsynth: src/graphsynth/main.cpp $(wildcard src/graphsynth/*.hpp) $(INC) | $(BIN)
	$(call LINK,src/graphsynth/main.cpp)
$(BIN)/ptrank: src/ptrank/ptrank.cpp $(wildcard src/ptrank/*.hpp) | $(BIN)
	$(call LINK,src/ptrank/ptrank.cpp)
$(BIN)/startab: src/startab/startab.cpp $(INC) | $(BIN)
	$(call LINK,src/startab/startab.cpp)
$(BIN)/startab-tricheck: src/startab/tricheck.cpp | $(BIN)
	$(call LINK,src/startab/tricheck.cpp)
$(BIN)/andtab: src/andtab/andtab.cpp | $(BIN)
	$(call LINK,src/andtab/andtab.cpp)

# ---- Apple Metal (macOS only) -------------------------------------------------------------------------------
$(BUILD)/gpu.o: src/gpukit/gpu.mm src/gpukit/gpu.hpp | $(BUILD)
	$(CXX) $(CXXFLAGS) -fobjc-arc -c src/gpukit/gpu.mm -o $@
$(BIN)/gputest: src/gpukit/gputest.cpp $(BUILD)/gpu.o src/gpukit/gpu.hpp | $(BIN)
	$(call LINK,src/gpukit/gputest.cpp $(BUILD)/gpu.o $(METAL_FW))
$(BIN)/gpukit-example: src/gpukit/example.cpp $(BUILD)/gpu.o src/gpukit/gpu.hpp | $(BIN)
	$(call LINK,src/gpukit/example.cpp $(BUILD)/gpu.o $(METAL_FW))
$(BIN)/gpuopt: src/gpuopt/gpuopt.cpp $(BUILD)/gpu.o src/gpukit/gpu.hpp $(INC) | $(BIN)
	$(call LINK,src/gpuopt/gpuopt.cpp $(BUILD)/gpu.o $(METAL_FW))
$(BIN)/gpuprobe: src/gpuprobe/probe.swift | $(BIN)
	swiftc -O -o $@.new src/gpuprobe/probe.swift && mv -f $@.new $@

# ---- smoke test (single thread, well under a second) -------------------------------------------------------
check: $(BIN)/cktcheck | $(BUILD)
	$(BIN)/cktcheck specs/cand32.spec seeds/cand32_207.ckt --basis aon
	$(BIN)/pyrun py/pnpfast.py check specs/cand32.spec seeds/cand32_207.ckt
	@# a wrong circuit (first OR gate turned into AND) must be rejected by both checkers
	@awk '/^or /&&!d{sub(/^or/,"and");d=1}{print}' seeds/cand32_207.ckt > $(BUILD)/bad.ckt
	@if $(BIN)/cktcheck specs/cand32.spec $(BUILD)/bad.ckt --basis aon -q; then echo "check: FAILED, cktcheck accepted a wrong circuit"; exit 1; fi
	@if $(BIN)/pyrun py/pnpfast.py check specs/cand32.spec $(BUILD)/bad.ckt >/dev/null; then echo "check: FAILED, pnpfast accepted a wrong circuit"; exit 1; fi
	@echo "check: both checkers accept the seed and reject the mutated circuit: ok"

clean:
	rm -rf $(BUILD) $(addprefix $(BIN)/,$(CPU_TOOLS) gputest gpuopt gpukit-example gpuprobe) $(BIN)/*.new
