# REPRODUCE (DRAFT; agent-10 staging, updated 23:12; frozen tree = integration build #33)

## Pinned toolchain and dependencies
- Lean toolchain: leanprover/lean4:v4.34.0 (`lean-toolchain`).
- Mathlib commit: 5ed2965256430c3649e86755f9576b54eca72435 (`RUNTIME_LOCK.json`, `lake-manifest.json`), used as a pre-built read-only package at /opt/lean-mathlib. Do not run `lake update`.
- Project: /research/lean (lakefile.toml, lib `Frontier`, root `Frontier.lean`).

## Sources
The frozen tree is listed with sha256 hashes in `manifest.json` (lean_sources_sha256). It is identical to agent-10/work/integration/sources_33.sha256.

## Build
    cd /research/lean
    python3 /opt/research/lean_run.py lake build Frontier                 # full root, all 288 modules (~3 min warm, ~30-45 min cold)
    python3 /opt/research/lean_run.py lake build Frontier.CHD.Final       # the final theorem's closure only (266 Frontier modules)
It must end with `Build completed successfully` and contain no `declaration uses 'sorry'`. The build-#33 log is LEAN_BUILD.log.

## Axioms of the final theorem
    cat > /tmp/Ax.lean <<'X'
    import Frontier.CHD.Final
    #print axioms Frontier.CHD.Final.chd_gateC
    #print axioms Frontier.CHD.Final.chd_CHDTarget
    #print axioms Frontier.CHD.Final.chd_exact_within
    #print axioms Frontier.CHD.Final.chdProgram
    X
    python3 /opt/research/lean_run.py lake env lean /tmp/Ax.lean
Expected output:
- the three theorems: `[propext, Classical.choice, Quot.sound]`;
- `chdProgram`: "does not depend on any axioms".
See AXIOMS.txt.

## Fresh-copy reproduction (reviewer procedure)
agent-07's `repro/my_repro.py` copies only the sources to a fresh directory, relinks the pinned packages read-only, and rebuilds the root closure. Trial t4 ran on the build-#26 tree on 2026-09-20 from 18:38.

## Forbidden-construct scan
    grep -rnE '\bsorry\b|\badmit\b|^\s*axiom\b|native_decide|implemented_by|\bunsafe\b|@\[extern' Frontier Frontier.lean
This must print nothing, apart from comment lines naming the words.

## Independent kernel replay (agent-09's tool)
    cd /research/lean
    python3 /opt/research/lean_run.py lake env lean --run /research/agents/agent-09/work/replay/Replay.lean Frontier.CHD.Final Frontier
It re-sends every constant defined in a `Frontier.*` module to the kernel, starting from a base environment built from the non-Frontier modules. It must print `KERNEL REPLAY OK`.
