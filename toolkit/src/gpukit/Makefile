# Thin wrapper: the build lives in toolkit/Makefile (one portable build for every tool).
all:
	$(MAKE) -C ../.. build/gpu.o bin/gputest bin/gpukit-example
clean:
	rm -f ../../build/gpu.o ../../bin/gputest ../../bin/gpukit-example 
.PHONY: all clean
