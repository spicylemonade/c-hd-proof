# C-HD proof package

Snapshot downloaded 2026-09-20T23:58:20.001505+00:00. The remote research agents were left running. This folder is a fixed snapshot; later work is not automatically added.

## Start here

- **paper/C-HD-Informal-Proof.pdf**: readable copy of the informal proof and its formalization map.
- **paper/PAPER.md**: the exact downloaded paper source, including its explicit distinctions between proved and paper-only claims.
- **formal/lean/Frontier/CHD/Final.lean**: the final Lean theorem and the concrete algorithm it certifies.
- **info/THEOREM_MAP.md**: where the paper's arguments appear in Lean.
- **REPRODUCE.md**: portable build and verification instructions.

## What is established in this snapshot

The frozen build-33 project proves `Frontier.CHD.Final.chd_exact_within`, `chd_CHDTarget`, and `chd_gateC` without remaining theorem hypotheses. It covers a uniform deterministic program for exact directed, nonnegative-real single-source shortest paths and its charged runtime in the specified RAM/comparison-addition model.

The formal improved bound applies when `m <= n F(n)`, where `F(n) = floor(floor(log2 n)^(3/4))`. The program has a verified Bellman-Ford fallback outside its C-HD branch. Along the stated density profile, the proved upper bound is `O(n log(n)^(11/12))`.

The complete project build passed (2,548 jobs). A separate fresh-copy rebuild passed, and two separate kernel replays each checked 18,994 project constants in the final theorem's 266-module dependency closure. The theorem dependencies are exactly Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; the algorithm term uses no axioms. The audit found no forbidden proof constructs in that closure. See the records under `verification/`.

Reviewer 1's completed **internal agent review** accepts the Gate-C claim and is included. Reviewer 2's document is a snapshot with reproduction fields still pending; its provisional ACCEPT heading is not a completed review receipt. These are reviews by the research agents, not outside peer review.

## Scope to preserve when sharing

This is an asymptotic result with enormous constants. It does not claim a practical speedup, linear runtime, or an improvement on all graph densities. The wider density range in the paper's Theorem 3 is not formalized here. The formally justified space bound is space at most the runtime bound; an `O(n+m)` space theorem is not supplied. Novelty and the interpretation of the computational model remain appropriate subjects for external expert review.

The four files under `formal/supplementary/` contain post-freeze corollaries and a literal program representation. They were individually checked by the team but were outside build 33 and its recorded full audit. They are supplied separately and are not silently added to the audited baseline.

## Source integrity and portability

- `formal/frozen-build-33/` preserves all **292 frozen files**, including **289 Lean files**, byte-for-byte. Their original hashes are in `verification/FROZEN_SOURCES.sha256`.
- `formal/lean/` is a portable copy. Only `lakefile.toml` and `lake-manifest.json` differ: they replace the cloud-only `/opt/lean-mathlib` path with the same pinned public Mathlib Git commit. All proof sources are identical.
- The portable configuration was checked structurally and the proof sources were hash-verified locally. A full rebuild of that portable copy on this Mac was not performed. The enclosed successful builds were on the original pinned cloud environment and its independently copied sources.
- `verification/EXPORT_MANIFEST.json` records each downloaded file and source hash. `PACKAGE_SHA256SUMS.txt` covers the finished shareable package.

Some preserved source comments and staging notes predate the final theorem and still say OPEN. Use the final theorem and dated verification records for status; historical files are preserved unchanged. `paper/background/` contains the historical B1 draft referenced by the paper. The C-HD formal theorem does not take that draft as an assumption.

The kernel replay utilities use Lean's metaprogramming API, including an `unsafe` host-tool entry point. They sit outside the theorem's imports and do not add axioms or unchecked proof steps to the C-HD theorem.

The PDF is a typeset derivative of the downloaded Markdown; only dash typography and presentation were changed. The Markdown remains the source of record.
