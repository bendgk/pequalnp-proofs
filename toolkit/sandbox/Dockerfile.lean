# syntax=docker/dockerfile:1
# Lean image: the repository's pinned toolchain, for building proof files (bin/leancheck) in a sandbox.
# A Lean file can run arbitrary code while it compiles (#eval, initialize, macros), so a proof is compiled
# only here: no network, read-only repository, unprivileged user, Mathlib cache in a named volume.
# elan is the same pinned release as .github/workflows/authoritative.yml, checked by sha256 before it runs.
ARG BASE=debian:trixie-slim@sha256:8aa5a7bf5a1955bddbe7d74fcdd0b91ab30e74362a8b73af672b0481b35b44a0
FROM ${BASE}
ARG ELAN_VERSION=v4.4.0
ARG ELAN_SHA256_X86_64=0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2
ARG ELAN_SHA256_AARCH64=45cde3006f82f98804c94cf2ca4949d117060a5f3cc8afa62f523759947ee21f
ARG LEAN_TOOLCHAIN
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git python3 \
 && rm -rf /var/lib/apt/lists/* /usr/share/doc /usr/share/man
ENV ELAN_HOME=/opt/elan
WORKDIR /opt/elan-download
RUN set -eu; \
    test -n "$LEAN_TOOLCHAIN" || { echo "LEAN_TOOLCHAIN build arg missing (sandbox/run passes lean/lean-toolchain)"; exit 1; }; \
    arch=$(uname -m); case "$arch" in x86_64) want=$ELAN_SHA256_X86_64;; aarch64) want=$ELAN_SHA256_AARCH64;; *) exit 1;; esac; \
    curl -sSfL --proto '=https' --proto-redir '=https' -o elan.tgz \
      "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$arch-unknown-linux-gnu.tar.gz"; \
    echo "$want  elan.tgz" | sha256sum -c -; \
    tar -xzf elan.tgz elan-init; ./elan-init -y --no-modify-path --default-toolchain none; \
    /opt/elan/bin/elan toolchain install "$LEAN_TOOLCHAIN"; /opt/elan/bin/elan default "$LEAN_TOOLCHAIN"; \
    rm -f elan.tgz elan-init; chmod -R go-w /opt/elan
COPY --chown=0:0 . /opt/toolkit
ENV PATH=/opt/elan/bin:/opt/toolkit/bin:/usr/local/bin:/usr/bin:/bin \
    PYTHONPATH=/opt/toolkit/py PYTHONDONTWRITEBYTECODE=1 \
    PNP_TOOLKIT=/opt/toolkit PNP_IN_SANDBOX=1 PNP_RUNS=/out/runs HOME=/tmp
USER 65532:65532
WORKDIR /work
