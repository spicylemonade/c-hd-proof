# Reproduce the checked C-HD result

## Requirements

Install Lean's `elan` toolchain manager, Git, Python 3, and the ordinary native build tools for your platform. Internet access is needed for the pinned Lean toolchain and public Mathlib dependencies. The package does not include compiled dependencies or credentials.

Pins:
- Lean: `leanprover/lean4:v4.34.0`
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`
- Full dependency revisions: `formal/lean/lake-manifest.json`

## One command

From this package directory:

```sh
bash formal/check.sh
```

This verifies the frozen hashes and unchanged portable proof sources, fetches the matching Mathlib cache, builds the complete `Frontier` project, checks the final theorem types and axiom dependencies, and replays the final theorem's project constants through Lean's kernel.

A fresh source rebuild took about 54 minutes on the shared cloud machine; local times and memory needs will differ. Do not run `lake update`, since that would change the dependency resolution.

## Individual steps

```sh
python3 formal/verify_sources.py
cd formal/lean
lake exe cache get
lake build Frontier
lake env lean ../CheckAxioms.lean
lake env lean --run ../Replay.lean Frontier.CHD.Final Frontier
```

For the final theorem's dependency closure alone, use `lake build Frontier.CHD.Final` instead of `lake build Frontier`.

Expected axiom lists for `chd_gateC`, `chd_CHDTarget`, and `chd_exact_within`:

```text
[propext, Classical.choice, Quot.sound]
```

`chdProgram` should report that it does not depend on any axioms. The closed examples in `CheckAxioms.lean` should typecheck. The replay should finish with `KERNEL REPLAY OK` and 18,994 project constants for this frozen snapshot.

The replay rechecks C-HD's project constants against the pinned Lean/core/Mathlib environment. It does not independently re-prove the entire Mathlib library.

## Original evidence

- `verification/build_33.log`: full original build, exit 0.
- `verification/agent-07/fresh_build.log` and `fresh_build_summary.json`: independent source rebuild.
- `verification/agent-07/replay.txt`: replay of that fresh build.
- `verification/agent-07/closed_probe.txt`: final theorem types have no outstanding hypotheses.
- `verification/agent-09/final_audit.json`: separate axiom, source and kernel-replay audit.
- `verification/OPERATOR_AXIOM_CHECK.json`: an additional direct Lean check before export.

The reviewer-1 hash comparison lists four added supplemental files. None of the frozen build-33 files changed; the supplemental files are isolated under `formal/supplementary/` here.

The original cloud scripts and reproduction notes are included for provenance under `verification/original-tools/` and `info/`. They reference the cloud filesystem. Use the portable instructions above on another computer.
