# Final audit record: agent-09 (theory, scope, axiom, cost and novelty audit lane). NON-GATE.

Target: `Frontier.CHD.Final.chd_gateC : Frontier.GateC` on the FROZEN tree #33 (agent-10, sources_33.sha256, 292 files).

Author note: agent-09 is the author of the C-HD candidate and is RECUSED as its reviewer. This file records the mechanical audit only. It is not a review verdict.

## 1. Tree identity
- On 2026-09-20 at 23:33 UTC, `sha256sum -c sources_33.sha256` gave 292/292 OK against /research/lean. This was re-checked after the FinalRaw install: still 292/292.
- The import closure of `Frontier.CHD.Final` has 266 modules. All of them are in sources_33, and each audited hash equals the frozen hash (audit_runs/final_final_33_skipbuild.json).

## 2. Mechanical acceptance checks (audit_tools/final_audit.py, root Frontier.CHD.Final)
- Forbidden-token scan over the 266 modules, with comments and strings stripped: **0 hits**. Patterns: sorry, admit, native_decide, `axiom` declarations, unsafe, implemented_by, @[extern], opaque, ofReduceBool, @[csimp], skipKernelTC, `set_option debug`, run_cmd, #eval, postulate, Lean.Elab.Command.
- `#print axioms`:
  - `Final.chd_gateC`, `Final.chd_CHDTarget`, `Final.chd_exact_within` and `GateCTarget.chdTarget_F_imp_gateC`: [propext, Classical.choice, Quot.sound];
  - the program constants `Final.chdProgram`, `DPro.dProC`, `BL2Inst.fpAtRaw` and `BL2.fpAlloc`: **no axioms**. The algorithm term uses no choice.
- Independent kernel replay (replay/Replay.lean, `Environment.replay` of every Frontier constant in the closure): **KERNEL REPLAY OK, 18,994 constants, 267 s.**
- Build: the #33 oleans were built by agent-10 (rc 0, 2548 jobs). This run used `--skip-build`, because peers' from-scratch fresh-copy rebuilds held the exclusive full-build lock. Those two independent rebuilds (agent-07, agent-02) are the reproducibility evidence.

## 3. Statement files (the meaning of the claim)
- CostModel, Spec, GateC, GateCCalc, Audit, AuditGateC, AuditBridge, RAMLogic and RAMWitness are byte-identical between my 20:02 dry run and the frozen tree. agent-10 reports them unchanged since build #26 at 18:31.
- CostModel provenance: frozen `808c8f9d` = the 10:46 base (`ba77c486`) + agent-08's `machine_procs.diff`, which I APPROVED in audit_procs_ext.md, + exactly my two requested revisions:
  - R1: the P10 simulation sentence in the header doc;
  - R2: `enter` charges 1 cost and 1 space cell per call, so `space ≤ cost` covers the return stack.
  - I checked this by applying the approved diff to the base and diffing against the frozen file. No other change.
- Independent gate formalization: my `Frontier.Audit.GateC ramModel` (Audit.lean / AuditBridge / AuditGateC, written independently of CostModel's `GateC`) also holds for the same witness. The proof is `AuditGateC.chdTarget_imp_auditGateC Final.chd_CHDTarget`: FinalExtras.chd_auditGateC, and my scratch L09/AuditFinal.lean, std axioms.

## 4. Literal program text
- `Frontier/CHD/FinalRaw.lean` (2d53cb7d, new file, outside the frozen closure; #34 extra):
  - `chdProgramRaw` is the `repr` normal form of `chdProgram` (1,939,652 chars, 19,351 lines);
  - `chdProgramRaw_eq : chdProgram = chdProgramRaw := rfl`.
  - Both are axiom-free, with 0 forbidden hits.

## 5. Scope and cost (re-derived; consistent with the staged CLAIM and LIMITATIONS)
- The Gate-C window is d = m/n ≥ √L, L = lg n. There Dijkstra is the best known bound: DMM+25 beats it iff d < L^{1/3}, and DMSY26 iff d < √L.
- C-HD is o(nL) iff d·lg d = o(L), and it beats DMSY26 iff d = ω(L^{1/4}).
- Formally covered: m ≤ n·F(n), F(n) = ⌊⌊log₂ n⌋^{3/4}⌋. The window √L ≤ d ≤ F(n) sits inside the Gate-C window, along μ(n) = n·⌊ln(n+2)^{3/4}⌋. The certified bound there is Θ(n·L^{11/12}).
- Outside that range the program falls back to verified Bellman-Ford, O((n+1)(m+1)). No claim is made there.
- Word size is (n+m+2)^{161}, i.e. 161·log₂(n+m+2) bits. Constants are astronomically large:
  - kmN ≈ 1.02·10^{10};
  - the D pool is ≈ 1.2·10^{11}·Tnat cells;
  - the dPro constant is 23·12·kmN + 300.
  All of this is honest, and asymptotically irrelevant.
- Space ≤ cost. It is Θ(T), not O(n+m).

## 6. Novelty (independent confirmation of the newest source)
- arXiv 2607.19346 (Hair, Li, Li, Zhang, 21 Jul 2026), read in full HTML:
  - Las Vegas RANDOMIZED, m^{1+o(1)} w.h.p.;
  - √log n recursion levels with O(log n)^i instances at level i, so the overhead is exp(O(√log n·lglg n)), which is super-polylogarithmic;
  - uses potentials w + φ(u) − φ(v), i.e. subtraction, outside comparison-addition.
- It does NOT pre-empt C-HD.
- The staged NOVELTY.md verdict is correct. I sent 3 precision fixes (23:39), and agent-03 applied them in paper 2e9ac65d.

## 7. Cross-checks of the consolidated THEOREM_MAP.md (agent-07)
- 51 of 53 file-hash citations equal the frozen hashes. The 2 others are dated history (SpineFirst and SpineLoopA at 21:25), now annotated.
- Part 4 (B-L2 / dPro) is my THEOREM_MAP_BL2.md verbatim: 20/20 hashes OK.

## 8. What this record does NOT establish
- It is not a peer review. REVIEW_1 (agent-07) and REVIEW_2 (agent-02) are separate and required.
- It is not an exhaustive literature search. Novelty rests on the supplied primary papers plus the dated web re-checks.
- It does not certify the paper-level window beyond m ≤ n·F(n).

## 9. Gate-C conformance and non-vacuity (GOAL formal acceptance, item 1: agent-09 and agent-10 audit)
- `chd_gateC : Frontier.GateC` has **no hypotheses**, so it is a closed theorem. `Frontier.GateC` (CostModel.lean:394, unchanged) says: ∃ P, P.Exact ∧ ∃ T, (∀ G s, P.RunsWithin G s (T G.n G.m)) ∧ ∃ μ with, eventually, n·√ln(n+2) ≤ μ n ≤ n·ln(n+2), and T(n, μ n)/(n·ln(n+2)) → 0.
- Non-vacuity, clause by clause:
  - (a) `P.Exact` is exact SSSP on EVERY directed graph with nonnegative real weights and EVERY source: the distance array plus the reachability flag, from the explicit edge-list input (Spec/CostModel, audited earlier).
  - (b) `RunsWithin` requires a terminating run with total CostModel cost ≤ T on EVERY input. T = C·Tdisp is a real bound everywhere; outside the covered range it is the Bellman-Ford bound C(n+1)(m+1).
  - (c) For every n there exist graphs with μ(n) edges (the model allows multigraphs), so the o(n log n) statement is about actual inputs.
  - (d) The window [n√log n, n log n] is exactly where Dijkstra's O(m + n log n) is Θ(n log n) and beats the DMM+25 and DMSY26 bound expressions. FinalCompare.chd_beats_known formalizes the comparison with those three expressions along μ.
  - (e) T is the program's own cost bound in the unit-cost model with honest allocation charges. No oracle, and the algorithm term is axiom-free.
- An independent formalization of the gate, `Frontier.Audit.GateC ramModel` (the strong form), also holds for the same witness (FinalExtras.chd_auditGateC).
- **Verdict (agent-09, audit lane):** the final theorem states Gate C faithfully and non-vacuously. Novelty (item 5) is a review judgement, supported by §6 and the NOVELTY.md record.
