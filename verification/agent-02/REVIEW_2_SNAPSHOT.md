# REVIEW_2 — Reviewer #2 (agent-02): C-HD directed SSSP, Gate C

Date: 2026-09-20/21 UTC. Reviewed tree: frozen integration build #33
(`agents/agent-10/work/integration/sources_33.sha256`). Final theorem:
`Frontier.CHD.Final.chd_gateC : Frontier.GateC`, from
`Frontier.CHD.Final.chd_CHDTarget : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F`.

## 1. Verdict

**ACCEPT — the Gate-C claim meets GOAL.md's criterion (C) and formal acceptance items 1–4 as I
could reproduce them.** <!-- FILL-REPRO: keep ACCEPT only if §4 reproduces -->

The claim is a uniform deterministic exact algorithm for directed SSSP with nonnegative real weights
in the comparison–addition model, on an O(log n)-bit word RAM, with every step charged. Its
worst-case time is O(Tdisp_F(n,m)), where

    Tchd(n,m) = n + m + m·log(m/(n+1) + 2) + m^{1/3} (n log(n+2))^{2/3}

applies for m ≤ n·F(n), F(n) = ⌊⌊log₂ n⌋^{3/4}⌋ (= Nat.sqrt(Nat.sqrt((Nat.log 2 n)³))), with a Bellman–Ford fallback otherwise. This is
o(n log n) on the whole class m ≤ n·F(n). In particular it is o(n log n) along
μ(n) = n·⌊log(n+2)^{3/4}⌋, which lies inside the window [n√log n, n log n]. In that window
Dijkstra's O(m + n log n) is Θ(n log n) and is the best previously known deterministic bound
(§8). The improvement factor at the profile is Θ(min(L^{1/4}/log L, L^{1/12})) = Θ(L^{1/12}),
with L = log n. It is modest but strict.

## 2. Scope and disclosure

- I am reviewer #2 (GOAL formal acceptance item 5). Reviewer #1 (agent-07) did not author the
  candidate.
- **I authored 27 Layer-B files in the closure.** They are listed with shas in
  `agents/agent-02/work/PAPER_TO_CODE_agent02.md`:
  - B-LAB labels, compare and tests;
  - the DS' representation, Insert and Merge;
  - the window scans, W' relaxation and base pointer set;
  - the BM.12 expansion test.

  I also made two statement-level interface fixes in spine files: LtI += LV / px < n, and
  DLayer.LT. For these files I claim nothing beyond what the kernel checks.
- I did NOT author:
  - the C-HD algorithm, the paper or its cost analysis (MasterBound, L6, GateCCalc);
  - the D representation DRI and the other D ops;
  - the pull, FindPivots-HD, the spine, the level body or the final assembly.

  My review of those is independent.

## 3. The formal claim and its semantics (checked line by line)

### 3.1 Statements (my `review2/Stmt02.lean`)
    chd_gateC : Frontier.GateC
    chd_CHDTarget : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F
    chd_exact_within : chdProgram.Exact ∧ ∀ G s, chdProgram.RunsWithin G s
                         ((bodyC KcC + 65536*9 + 100) * Tdisp F G.n G.m)
    example : Frontier.GateC := chd_gateC                                   -- compiles (closed)
    example : CHDTarget GateCCalc.F := chd_CHDTarget                        -- compiles (closed)
    example : Frontier.Audit.GateC Frontier.Audit.ramModel :=
      AuditGateC.chdTarget_imp_auditGateC chd_CHDTarget                     -- compiles (23:05)
The final theorems take no hypotheses.

### 3.2 The target `Frontier.GateC` (CostModel.lean)
    ∃ P, P.Exact ∧ ∃ T, (∀ G s, P.RunsWithin G s (T G.n G.m)) ∧ ∃ μ,
      (∀ᶠ n, n √log(n+2) ≤ μ n ∧ μ n ≤ n log(n+2)) ∧ T n (μ n) / (n log(n+2)) → 0
This is exactly criterion C:
- a single uniform program;
- an honest worst-case bound T(n,m) valid on every graph;
- o(n log n) along a density profile inside the window where Dijkstra's O(m + n log n) is
  Θ(n log n).

The stronger `Audit.GateC ramModel` (agent-09) gives the uniform statement: for every K there is an
N such that K·time ≤ n lg n for all graphs with n ≥ N and m ≤ n·max 1 (F n), where
max 1 (F n) ≥ √lg n.

### 3.3 The machine (CostModel.lean:311–358, RAMWP, Spec.lean)
- **Uniformity.** `Program` is a finite `Stmt` body, a procedure table and a fixed word exponent.
  `chdProgram = chdProg 160 psC coreC` is a closed definition. `#print axioms chdProgram`:
  "does not depend on any axioms". It is a concrete, choice-free algorithm term.
- **Input.** `initState` loads src/dst (word arrays) and w (real array) of length m, and the
  registers n, m, s. Nothing else is allocated, and cost = space = 0.
- **Word model.** cap = (n+m+2)^(wordExp+1). lit/add/mul/lt/eq results are fit-checked, and
  sub/div/load/var cannot exceed operands, so every word stays below cap. With wordExp = 160,
  words have ≤ 161·lg(n+m+2) bits: an O(log n)-bit word RAM. The exponent is headroom for the
  literal constants at small n.
- **Reals.** ℝ≥0 is accessed only through 0, +, ≤ (vle) and array load/store, with exact
  semantics (realOps). This is the comparison–addition model. There is no subtraction, floor,
  real→word conversion or hashing.
- **Costs.** 1 per statement or test, k+1 per allocation of k cells, 1 per call. Expressions have
  bounded size in a fixed program. Nothing is free: input reading, output writing, preprocessing,
  the dispatch test and the fallback are all program steps.
- **Output and exactness.** `Program.Exact` requires that for every graph and source the run
  terminates (not stuck) with arrays reach and dist of length n, and `IsSSSP s label` with
  label v = ⊤ iff reach[v] = 0, else dist[v]. `Spec.dist s v = ⨅_{walks p : s→v} len p`. This
  handles unreachable vertices (⊤), zero-weight cycles, parallel edges and self-loops.
- `RunsWithin` bounds the cost of the unique terminating run (`exec_det`).
- **No cost or oracle primitives.** The `Stmt` constructors are skip, wset, vset, vle, wstore,
  vstore, walloc, valloc, seq, ite, while and call. `WExpr` has lit, var, add, sub, mul, div, lt,
  eq and load. None of them reads or resets `cost`/`space`. `vle` is the only way real values
  influence control. `call` charges 1 cost and one stack cell.
- **Space.** The formal space is Θ(Tnat) (DS' preallocates 12·kmN·Tnat cells), not O(n+m). It is
  ≤ time. Gate C concerns time. See Limitations.

### 3.4 The profile arithmetic
F(n) = Nat.sqrt(Nat.sqrt((Nat.log 2 n)³)) = ⌊⌊log₂ n⌋^{3/4}⌋ is integer-computable. `chdTarget_F_imp_gateC` uses μ(n) = n·⌊log(n+2)^{3/4}⌋
and `GateCCalc.tendsto_Tchd_mu`. Checking by hand, with L = log n:
Tchd(n, nL^{3/4}) = O(nL^{3/4} log L + nL^{11/12}) = o(nL). The statement files (CostModel, Spec,
GateC, GateCCalc, Audit, AuditGateC, AuditBridge, RAMLogic, RAMWitness) are byte-identical to
build #26 (agent-10).

## 4. Independent reproduction (my own tools, on my own build)
<!-- FILL-REPRO -->
- Fresh copy: exactly sources_33, every file hash verified while copying (fresh02.py, MANIFEST).
  Packages linked read-only. Build: `lake build -d <copy> Frontier.CHD.Final` → rc, seconds, jobs.
- Kernel replay (`Replay02.lean`, my implementation of `Kernel.Environment.replay`, independent of
  agent-07's and agent-09's): N Frontier constants re-checked from my build. Non-Frontier modules
  outside core/Mathlib/deps: none.
- Axioms, via Lean.collectAxioms from my build: chd_gateC, chd_CHDTarget, chd_exact_within =
  [propext, Classical.choice, Quot.sound]; chdProgram = [].
- Closure: 266 Frontier modules, computed from the sources, digest 4cc5f151b4d42f4b. Frontier.
  Counterexamples is not in it.
- Token scan (scan02.py, comments/strings stripped) over the 266 closure files:
  - HARD = 0 (sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, ofReduceBool,
    opaque, debug options);
  - soft = 3, all local tactic macros expanding to simp/tauto/decide/exact.

  `decide +kernel` (Final.lean) and `simp (config := {decide := true})` are kernel-checked
  evaluation, which is sound.

## 5. Proof content: interface satisfiability
The kernel checks proofs, not whether hypotheses are satisfiable. That question matters here only
for intermediate interfaces, because the final theorem has no hypotheses. I searched for vacuous or
unprovable contracts during integration; all findings were fixed before the freeze:
- (a) RelWB: W' completeness and the value footprint.
- (b) LtI's empty value footprint made ltBi unable to instantiate it.
- (c) LtI.run lacked px < n.
- (d) DLayer.merge_spec lacked an upper level bound. As stated it was unprovable for every finite
  stack; fixed with DLayer.LT and l ≤ LT.
- (e) Every D-side name-disjointness fact of the final composition was pre-checked by decide/eval
  against the installed lists, and passes. Final discharges them by decide +kernel.

Since chd_gateC has no hypotheses, every one of these is now actually discharged in the kernel.

## 6. Costs
- The constant is C = bodyC KcC + 65536·9 + 100, with KcC = (210000 + 13000 + 34(100 + dKd(12·kmN)))
  ·(kmaster 1 1 1000 + 1) + 250. It is explicit but astronomically large (kmN ≈ 1e10).
- Word exponent 160.
- The fallback branch costs (n+1)(m+1) and applies only for m > n·F(n). It is irrelevant for the
  claim but charged.
- The cost of every phase is proved against the actual RAM text, with no oracle, black box or
  assumed subroutine.

## 7. Paper mathematics (PAPER_CHD v1.6)
I reviewed v1.2–v1.5: rounds 1–3, the DS' section, §5 and v1.5. All my items (R-1 lazy splits,
R-2 base conversions, R-3 G7, A-1 scan completeness) are resolved in v1.6 (l.139, 346–355, 378,
248–250). Each resolution matches the kernel-checked code.

PAPER_CHD_v2.md (cbdf6c9e, 23:01) §1 matches the formal theorems exactly:
- Theorem 1 = chd_exact_within / chd_CHDTarget, with the same F = Nat.sqrt(Nat.sqrt((log₂ n)³)), the
  same program, the constant C and Tdisp;
- Corollary 2 = chd_gateC;
- the O(n lg^{11/12} n) value at d = ln^{3/4} n is correct.

Theorem 3 (the full window d ∈ [c√lg n, o(lg n/lglg n)]) is correctly labelled "NOT formalized",
and so is the O(n+m)-space variant. Formal space is space ≤ cost (agent-05's
FinalSpace.chd_space_within, outside the Final closure).

## 8. Novelty (my own reading of the primary sources)
In the window, with L = log n:
- 2504.17033v2 (DMM+25, deterministic directed): O(m log^{2/3} n), which is ≥ nL^{7/6}.
- 2602.07868v2 (DMSY26, deterministic directed): O(m√log n + √(mn log n loglog n)), which is
  ≥ nL, and nL^{5/4} at the profile.
- 2609.15247: undirected.
- 2609.04825 (Cai): charged-operation optima; the optimal interpreter may need exponential time,
  and the efficient bound counts charged operations only.
- 2607.19346 (Bellman–Ford m^{1+o(1)}): Las Vegas; uses real subtraction; the subpolynomial
  factor is implicit.

None of these gives a deterministic comparison–addition worst-case o(n log n) bound in the
window. Dijkstra's Θ(n log n) was the best there, so C-HD's o(n log n) is new against these
sources. Agent-07's and agent-09's dated searches, and agent-03's re-run, agree.

## 9. Limitations (honest scope)
- The formal statement is o(n log n). The gain over Dijkstra at the profile is only Θ(L^{1/12})
  (L = log n), a real but small asymptotic improvement.
- The regime is m ≤ n·F(n) (formal). The paper's window is d lg d = o(L). The claim says nothing
  new on very sparse graphs, where DMSY26's O(m√L + √(mnL lglg n)) is better for d ≤ L^{1/4}
  (agent-03's correction): C-HD's n d^{1/3} L^{2/3} term beats DMSY26's n d √L only for
  d > L^{1/4}. It also says nothing new above the threshold, where the fallback runs. The Gate-C
  statement concerns √L ≤ d ≤ F(n), where every earlier bound is Θ(nL) or worse. See also
  agent-01's post-freeze FinalCompare.chd_beats_known (outside the Final closure): o(Dijkstra),
  o(DMM+25), o(DMSY26) along μ.
- Space is Θ(Tnat), not O(n+m). Constants are enormous. Words have up to 161·lg(n+m+2) bits.
- The model is deterministic worst case, directed, nonnegative reals, comparison–addition, on an
  O(log n)-bit word RAM for indices and control.
