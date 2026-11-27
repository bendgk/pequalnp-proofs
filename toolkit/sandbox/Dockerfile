# syntax=docker/dockerfile:1
# pnp toolkit, CPU image. Build context: toolkit/ (see sandbox/run). About 150 MB, most of it Python.
#
# Security properties (see ../SECURITY.md):
#   - base image pinned by digest; Python wheels pinned by sha256, binary wheels only (no setup.py runs)
#   - compilers exist only in the build stage; the runtime stage has no compiler, no package manager cache,
#     no shell tools beyond the base, and runs as an unprivileged numeric user
#   - sandbox/run starts it with no network, a read-only root, no capabilities, no-new-privileges,
#     pid/memory/cpu limits, and only the input and output folders mounted
ARG BASE=debian:trixie-slim@sha256:8aa5a7bf5a1955bddbe7d74fcdd0b91ab30e74362a8b73af672b0481b35b44a0

FROM ${BASE} AS build
RUN apt-get update \
 && apt-get install -y --no-install-recommends clang make python3 python3-pip ca-certificates \
 && rm -rf /var/lib/apt/lists/*
COPY sandbox/requirements.txt /tmp/requirements.txt
RUN python3 -m pip install --no-cache-dir --break-system-packages --require-hashes --only-binary=:all: \
      --target /opt/pysite -r /tmp/requirements.txt
COPY . /opt/toolkit
# NATIVE=1 (default) tunes for the CPU of the machine that builds the image, which is the machine that runs it.
ARG NATIVE=1
ENV PNP_IN_SANDBOX=1
RUN set -eu; cd /opt/toolkit; \
    if [ "$NATIVE" = 1 ]; then make -j"$(nproc)" cpu; else make -j"$(nproc)" cpu PORTABLE=1; fi; \
    rm -rf build; find . -name '__pycache__' -prune -exec rm -rf {} +

FROM ${BASE}
RUN apt-get update \
 && apt-get install -y --no-install-recommends python3 \
 && rm -rf /var/lib/apt/lists/* /var/cache/apt /usr/share/doc /usr/share/man
COPY --from=build --chown=0:0 /opt/pysite /opt/pysite
COPY --from=build --chown=0:0 /opt/toolkit /opt/toolkit
# Everything the image ships is owned by root and not writable by the user that runs it.
RUN chmod -R go-w /opt/toolkit /opt/pysite
ENV PATH=/opt/toolkit/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
    PYTHONPATH=/opt/pysite:/opt/toolkit/py \
    PYTHONDONTWRITEBYTECODE=1 \
    PNP_TOOLKIT=/opt/toolkit \
    PNP_SLOTS=/slots \
    PNP_IN_SANDBOX=1 \
    PNP_RUNS=/out/runs \
    PNP_FOUND=/out/found \
    HOME=/tmp
USER 65532:65532
WORKDIR /work
