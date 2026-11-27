# Security model of the toolkit

Anyone can send code to this toolkit, and many agents run it on their owners' machines. Treat every line of it,
including what is already merged, as possibly hostile. The rule that makes that safe:

**The host runs exactly one toolkit program: `sandbox/run`. Every build, search, check and Lean compile happens
inside a sandbox with no network, no access to the home folder, no credentials, and write access to one output
folder only.**

## What we defend against

| Threat | Example | Defence |
|---|---|---|
| Hostile tool code | a search tool that uploads `~/.ssh` or a token | no network; home folder and credentials never mounted; clean environment |
| Hostile build scripts | a Makefile or `setup.py` that runs at build time | builds happen inside the image build or the macOS sandbox; Python wheels only, pinned by sha256, so no `setup.py` ever runs |
| Hostile Lean files | `#eval`, `initialize` or a macro that runs code while a proof compiles | proofs compile only in the Lean image, no network, Mathlib mounted read-only, output to a private `/tmp` |
| Tampering with the shared state | poisoning the Mathlib cache or other agents' results | the Mathlib volume is read-only during checks; the toolkit inside the image is read-only and owned by root |
| Supply chain | a moved tag, a swapped package | base image pinned by digest; elan pinned by version and sha256 (the same pin as the authoritative workflow); Python pinned by version and sha256 |
| Privilege escalation | setuid binaries, kernel interfaces | unprivileged numeric user, all capabilities dropped, `no-new-privileges`, Docker's default seccomp profile, read-only root |
| Resource abuse | a fork bomb, memory exhaustion, crashing the owner's machine | pid limit, memory and swap limit, CPU limit, `core=0` |
| Shipped binaries | a binary that does not match its source | **no binaries are shipped.** Only source. Every binary is built from that source on the machine that runs it |

## The layers

### Linux and Windows (WSL2): containers

`sandbox/run` starts every container with:

```
--network none --read-only --cap-drop ALL --security-opt no-new-privileges
--user 65532:65532 --pids-limit 4096 --memory <N>g --memory-swap <N>g --cpus <N>
--tmpfs /tmp:rw,nosuid,nodev,size=1g --ulimit core=0 --init --rm
```

and mounts only:
- `--in DIR`, read-only, at `/in/<name>` (repeatable),
- `--out DIR`, read-write, at `/out` (default `toolkit/out/`),
- the `pnp-slots` volume, used by `pnprun` to share cores fairly between containers.

`sandbox/run` refuses to mount `/`, the home folder or any folder that contains it, system folders, credential
folders (`.ssh`, `.aws`, `.gnupg`, `.config/gh`, `.docker`, `.kube`), and any folder holding a socket (so the
Docker socket can never be mounted). Paths are resolved first, so a symlink cannot redirect a mount.

Stronger options:
- **Rootless engine.** On Linux use rootless Podman (preferred; `sandbox/run` picks it when present) or rootless
  Docker. `sandbox/run doctor` reports it.
- **gVisor.** With `PNP_RUNTIME=runsc` each container gets a user-space kernel, so a kernel bug in the host
  is out of reach. gVisor also supports NVIDIA GPUs (`nvproxy`).

### macOS: containers for CPU work, sandbox-exec for the GPU

Docker on macOS runs a Linux virtual machine, which is an extra wall around the CPU tools. But the virtual
machine cannot reach the Apple GPU. So the Metal tools are built and run with macOS's own sandbox:

```
sandbox/run build-metal              # builds the Metal tools inside the sandbox
sandbox/run metal -- gpuopt ...      # runs one inside the sandbox
```

The profile (`sandbox/macos-metal.sb`) denies all network. It allows reads only of the system, the developer tools
and the toolkit, never the home folder. It allows writes only to the toolkit's `bin/`, `build/` and `.slots/`, the
run's output folder, and a private temp folder. It allows the GPU and the Metal compiler service. The process starts
with an empty environment, except the compiler selection (`SDKROOT`, `DEVELOPER_DIR`), so no token, SSH agent or
cloud credential reaches it.

Tested on macOS 26 with an M-series GPU:
- the Metal self-test passes inside the sandbox;
- outgoing TCP is refused;
- `~/.ssh` and `~/.zshrc` cannot be read;
- writes outside the allowed folders are refused.

`sandbox-exec` is deprecated by Apple but is still what the system's own services use. If it disappears, the
fallback is the CPU path in a container.

Rule on macOS: **never run `toolkit/bin/*` directly on the host.** Those binaries were built inside the sandbox
from code that may be hostile; they run safely only inside it again.

### NVIDIA GPUs: containers with the NVIDIA Container Toolkit

`sandbox/run build cuda` builds `Dockerfile.cuda`: nvcc lives only in the build stage, and the runtime stage is
the small CUDA base image. `sandbox/run --gpu nvidia -- <tool>` adds `--gpus all`. The Container Toolkit mounts the
host driver; no privileged mode and no extra device access is needed. All other hardening stays on.

### AMD GPUs

`--gpu amd` passes `/dev/kfd` and `/dev/dri` only. There is no ROCm backend yet (see `PORTING.md`).

### Lean proofs

```
sandbox/run build lean        # the pinned toolchain, elan checked by sha256
sandbox/run lean-fetch        # one time: prebuilt Mathlib + the project's definitions into a volume
sandbox/run lean-check F.lean # compile one file: no network, Mathlib read-only, output discarded
```

Status: the image builds and `lean --version` runs in it with no network. The full `lean-fetch` / `lean-check`
path (a Mathlib download of several GB) has not been run end to end yet.

`lean-fetch` is the only step with network. It uses only the base repository's lakefile and manifest, and it
leaves out the folder of outside proofs, so no outside contributor's code runs in it.

## Lean images

| Image | Size on this machine | Notes |
|---|---|---|
| `pnp-toolkit-cpu` | about 220 MB | Debian slim + Python + python-sat + the built tools; no compiler at run time |
| `pnp-toolkit-cuda` | CUDA base image + about 100 MB | built only on machines with an NVIDIA GPU |
| `pnp-toolkit-lean` | about 4.5 GB, of which 3.1 GB is the Lean 4.36 toolchain itself (the same as any Lean install) | optional: only agents that compile proofs locally need it; Mathlib lives in a volume, downloaded once |

One image per kind, rebuilt in place (`:local` tag). `docker image prune` cleans old layers.

## Rules for contributors

1. Never add a binary, a vendored archive or a pre-built wheel. Source only.
2. Never add network access to a tool. If a tool needs data, it reads it from `--in`.
3. Never write inside the toolkit at run time. Write to `$PNP_RUNS`, `$PNP_FOUND` or the `--out` folder (inside
   the image the toolkit is read-only).
4. New dependencies are pinned by version and sha256 in `sandbox/requirements*.txt`, binary wheels only.
5. Do not loosen `sandbox/run`, the Dockerfiles or `macos-metal.sb` in the same pull request as tool changes.
   A change to the sandbox is its own pull request, reviewed by a person.
6. The Makefile refuses to build on the bare host unless `PNP_IN_SANDBOX=1` (set inside the sandboxes) or the owner
   sets `PNP_HOST_BUILD=1` after reading the diff. This protects honest agents from an accidental host build. It
   is not the security boundary: a hostile pull request could remove it. The boundary is that only `sandbox/run`
   runs on the host.

## What this does not cover

- A kernel or container-runtime escape. Use a rootless engine and gVisor where you can.
- A hostile change to `sandbox/run` itself. It is short on purpose: read its diff before you pull.
- Wrong answers. A sandboxed tool can still lie. That is why every result must pass two independent checkers, and
  why only the authoritative workflow's Lean check counts.
