# REVIEW 1: independent non-author review of the C-HD Gate-C claim (agent-07, reviewer #1). FINAL, 2026-09-20 23:59 UTC.

## Verdict: ACCEPTED, for Gate (C) only, with the limitations of §9.

This is my verdict as reviewer #1. It applies to the frozen tree integration build #33, recorded in
/research/agents/agent-10/work/integration/sources_33.sha256 (292 files). REVIEW_2 (agent-02) is a separate, independent review.

### Decision rule (FINAL_REVIEWER_STATEMENT_TEMPLATE.md, items 1-6), all checked on the frozen tree
1. PASS: a theorem with EXACTLY the frozen type is proved.
   - `Frontier.CHD.Final.chd_gateC : Frontier.GateC` and `Frontier.CHD.Final.chd_CHDTarget : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F`.
   - Closedness: `example : Frontier.GateC := Frontier.CHD.Final.chd_gateC` typechecks, and so does the CHDTarget analogue (rc 0), so no hypotheses remain.
   - Axioms: [propext, Classical.choice, Quot.sound].
   - My independent kernel replay of the closure (Lean.Kernel.Environment.replay) on MY fresh build: REPLAY OK, 18,994 Frontier constants,
     266 Frontier modules, and no modules outside Frontier/Mathlib/core. agent-09's independent replay gives the same count.
2. PASS: the frozen statement prints (GateC, CHDTarget, Tchd with real exponents (1/3 : ℝ) and (2/3 : ℝ), F, chdTarget_F_imp_gateC,
   chdTarget_of_body) are UNCHANGED from my 12:30 snapshot.
3. PASS: the fresh-copy rebuild of the whole root in a new directory builds OK: 2548 jobs, 3204 s, the same job count as build #33.
   - The token scan of all 288 Frontier sources finds 0 HARD tokens (sorry, admit, native_decide, axiom, unsafe, implemented_by, extern,
     ofReduceBool, csimp, sorryAx, #eval, run_cmd, Lean.Elab, debug.skipKernelTC, partial def).
   - INFO: 36 × `decide +kernel` (kernel-evaluated) and 11 × `simp` with `decide := true`. Both are sound.
4. PASS: every obligation in CHD_INTERFACE_OBLIGATIONS.md (v40) is discharged by a theorem in the final closure, and Layer B covers
   every operation of the algorithm.
   - The algorithm term `Frontier.CHD.Final.chdProgram` "does not depend on any axioms" and is computable: `#eval` of its Repr gives
     149,020 characters, `wordExp` = 160 and `procs.length` = 2.
5. PASS: THEOREM_MAP.md passes my mechanical check. Every cited Frontier theorem exists in the frozen tree, and every file:line
   citation is within 3 lines.
   - Six cited names are installed, compiled alternatives that are not on the final route; §10.2 of the map names what the route uses instead.
   - The paper (PAPER_CHD v2.0) matches the code: §1 = the Lean statements, with F, Tchd, Tdisp and μ checked symbol by symbol.
   - The paper-to-code discrepancies D1-D9 are all resolved.
6. PASS: the staged NOVELTY covers DMM+25, DMSY26 (Thm 1.1, fn. 1, Lemma 3.2), KR26, Cai 2026, the B1 draft, the undirected
   analogue and arXiv 2607.19346.
   - The staged LIMITATIONS states the space bound actually proved (space ≤ cost; Θ(Tnat) preallocation; no O(n+m) theorem) and the
     lg^{1/12} n size of the gain at the Lean profile.

Reviewer independence: I authored NO module of the C-HD chain. My only file in /research/lean is Frontier/Counterexamples.lean,
a lane deliverable, and my audit confirms it is NOT in the closure of Frontier.CHD.Final. My tools (ramsim, Replay07, the scanners,
the C++ simulator) live in my work directory.

## 1. What is proved (statements)
- `Frontier.GateC` (frozen, CostModel.lean): ∃ P, P.Exact ∧ ∃ T, (∀ G s, P.RunsWithin G s (T G.n G.m)) ∧ ∃ μ,
  (eventually n·√log(n+2) ≤ μ n ≤ n·log(n+2)) ∧ T(n, μ n)/(n·log(n+2)) → 0.
- `CHDTarget F`: ∃ P, P.Exact ∧ ∃ C, ∀ G s, P.RunsWithin G s (C · Tdisp F G.n G.m). The definitions are:
  - Tdisp F n m = if m ≤ n·F n then Tchd n m else (n+1)(m+1) (GateC.lean:27-28);
  - Tchd n m = n + m + m·ln(m/(n+1)+2) + m^{1/3}·(n·ln(n+2))^{2/3};
  - F n = Nat.sqrt (Nat.sqrt ((Nat.log 2 n)^3)) = ⌊⌊log₂ n⌋^{3/4}⌋.
- The profile of the Gate-C proof is μ n = n·⌊ln(n+2)^{3/4}⌋ (GateCCalc.μ), which satisfies μ ≤ n·F(n) (GateC.lean:46).
- Semantics:
  - `Program.Exact`: every run outputs, for every vertex, the infimum over walks (⊤ if unreachable), i.e. exact labeled distances.
  - `RunsWithin G s T`: the unique terminating run costs ≤ T.
- Model (CostModel v2):
  - a deep-embedded RAM with words < (n+m+2)^{e+1}, e = 160;
  - real values touched only by 0, + and ≤ (comparison-addition), with no operation from reals to words;
  - the input is read from arrays and the output (reach, dist) is materialized;
  - every statement, test and allocated cell is charged (allocation of k cells costs k+1);
  - procedures are part of the finite program syntax, cost 1 per call, and have no frames.

## 2. Proof audit
- Fresh copy repro/final1/proj, taken at 22:54. It is byte-identical to sources_33.sha256: 292/292 files, 0 differences.
  - Afterwards the shared tree differs from it only by 4 NEW post-freeze files outside the closure
    (FinalCompare, FinalExtras, FinalRaw, FinalSpace); no frozen file changed.
- Every Lean check below ran against MY fresh build (`lake env -d <copy>`), not the shared oleans.
  - Rebuild: OK, 2548 jobs.
  - Kernel replay of the closure: 18,994 constants OK.
  - #print axioms of chd_gateC, chd_CHDTarget and chd_exact_within: [propext, Classical.choice, Quot.sound].
  - Closedness probe: rc 0.
  - Program probe: no axioms.
  - Statement diff: unchanged.
- Earlier replays today:
  - build #28 root: 16,910 constants;
  - L6.LevelRoute: 14,071 (20:53);
  - SpinePostProof: 7,592 (20:59);
  - L6.Assembly: 14,969 (21:24);
  - build #32b root: 19,366 (21:59), matching agent-09 exactly.
- The chain (every link in the replayed closure):
  - GateC ⇐ `GateCTarget.chdTarget_F_imp_gateC` ⇐ `Final.chd_CHDTarget` ⇐ `Final.chd_exact_within`
    ⇐ `L6.chdProg_of_DLayer` (FinalGen) ⇐ `L6.chdTarget_of_step` (Assembly) ⇐ `L6.chdTarget_of_levels` (LevelRoute).
  - Level induction `L6.callSpec_of_levels`:
    - base: `L6.callSpec_base` (agent-03's `RamSpine.callSpec_zero`);
    - step: `L6.hs_of_parts` ⇐ `RamBody.callSpec_succ` ⇐ `RamBody.body_spec`.
    - Step inputs: `L6.hFP_of` (B-L2 FindPivots-HD), `L6.hLoop_of_parts` (`loop2_spec` + `postSpec`),
      `finB_uniform` + `fin_spec_stmt` (finalization), `L6.hSbA_chd` (expansion size).
  - D layer: `DLI.DLf` = `mkDL` over dsNew/dsIns/dsDelB/dsEmpty, `dsMerge_ok` and `pullD_ok`; allocation `DPro.dProSpecC`.
  - Exactness: `L6.complete_of_topRun` (`BM.bmsspDL_top`) and `L6.coreOut_of_labAt`.
  - Cost (Layer A): `L6.masterSpec_of_good`, `TraceFits.chdDL_tele_top` (lazy ≤ literal amortized), `CostFinal.total_le_Tchd`.
  - Dispatcher / L6 / output: `Dispatch.dispatch_runs`, `Dispatch.bf_bodySpec`, `L6.l6_runs`, `L6.body_spec`, `L6.outLoop_runs`.

## 3. Interface-satisfiability audit (the part the kernel cannot do)
A kernel-checked implication with an unsatisfiable hypothesis proves nothing, so throughout the day I checked every interface
structure for instantiability. The final theorem is CLOSED, so every such hypothesis was eventually discharged by a concrete object.
The findings along the way, all fixed before the freeze:
- 17:48: inverted DLayer.frame / PhiI.frame. I MISSED this in my pass; agents 06 and 03 found it.
- 18:30: RelWB needed W'-completeness. Found by agent-02.
- 20:18: the use/ucap threading must not reuse the polynomial slack.
  - Cu = 2 is satisfiable without new lemmas, since insertL costs ≥ 2.
  - The post-half's no-slack bound holds via lres.length ≤ card markedGroups. (me)
- 20:40: the final procedure table lacked the RECURSIVE select procedure that the pull calls (`call pSel`). Fixed with the
  2-entry ps (me).
- 20:42: LtI.run needed px < n (agent-02).
- 20:45: merge_spec lifted DR from level l-1 to l with no upper bound, which is unprovable for a finite stack. Fixed with DLayer.LT (agent-02).
  - The same bug in MergeOK was fixed at 21:37 (me).
- 20:47: use after dPro is 1, not 0, so the post became use ≤ 2 (me). The pull needs sel.w, so dPro now allocates it (me).
- 21:05: body_spec's LoopSpecB was factor 1, which the factor-2 CallSpec IH cannot supply. It was restated (agents 08 and 07).
- 21:55: the pull wrote spine registers; pullD saves/restores them (agent-04).

## 4. Cost audit
- The cost is the machine's own counter, charged by `exec`, and nothing is uncharged. Lean-level computation occurs only in proofs,
  and the algorithm is a closed Stmt term.
- The constants are fixed literals computed by `#eval` in the kernel:
  - one level constant K = 210,000 for all levels (≥ 208,989 required), K_D = 23,037, Ko = 92,469, Kfin = 69,411;
  - kmN = 10,219,910,400;
  - e = 160 (hbig needs e ≥ 139).
- Capacity: the D arrays have 12·kmN·Tnat + 4 cells each, sized from the Layer-A master bound (not from the RAM clock, so there is no
  circularity). They are allocated at O(Tnat) = O(Tchd) cost, because Tnat ≤ 33·Tchd (L6/Tnat.Tnat_le_Tchd) and Tchd ≤ 6·Tnat.
- Total: `chd_exact_within` gives RunsWithin (bodyC KcC + 65536·9 + 100)·Tdisp F on EVERY graph and source.

## 5. The algorithm (O30)
- `Final.chdProgram := chdProg 160 psC coreC`. By rfl, coreC = coreTop (spineOf (spinePro BL2.fpAlloc (DPro.dPro (12·kmN)))).
  - psC = [bmsspProc (baseProgC dsNew dsIns) recC, selBody entLess 1].
  - recC = recText fpAtRaw dsNew dsIns dsEmpty (iterText pullD dsMerge dsDelB dsIns) (finProg dsEmpty tstT6 dsIns tstWp (relW dsIns) dsDelW).
- My serialization of the program has 24,936 tokens. agent-09's literal twin `chdProgramRaw` (rfl bridge, no axioms) is an extra outside the closure.

## 6. Independent evidence (not proof)
- ramsim, my independent interpreter of `exec` with identical charges, run on the EXACT final text except ONE token: dPro's capacity
  literal is 12 instead of 12·kmN, since 1.2e11·Tnat cells cannot be allocated in a simulator. The token diff was checked mechanically.
  - body mode (real parameters): 300 random graphs, 0 mismatches vs Dijkstra, 0 stuck;
  - deep mode (t = k = 2, L forced): 200 graphs, 0 mismatches, 0 stuck;
  - instrumented run: 4 recursion levels (calls by level {0: 855, 1: 257, 2: 60, 3: 15}), 970 calls of the recursive select procedure;
  - full mode: the dispatcher at n = 2^16 (the C-HD branch, real parameters, weights up to 1e6) was exact.
- C++ simulator (lab/, sha 579bfbf5), all with 0 violations:
  - CallPost: 459M distinct checks;
  - the spine pointer invariant: 1.5e9 observations (exhaustive n = 4 over weights {0,1} + absent, and n = 5 over weight {0} + absent);
  - DS' lazy = literal;
  - mutation tests show the checkers have teeth.

## 7. Paper-to-code
- PAPER_CHD v2.0 (agent-03):
  - §1 Theorem 1 = `chd_exact_within`/`chd_CHDTarget`, and Corollary 2 = `chd_gateC`;
  - Theorem 3 (the full window up to lg n / lglg n) is explicitly NOT formalized;
  - §9 names the actual route, and its limitations match §9 below;
  - all 166 plain-text Lean-like names in the paper resolve, except math symbols and the build-#34 extras, which are labelled as such.
- THEOREM_MAP.md was consolidated by me from the owners' 9 parts. It is mechanically checked (626 identifiers) and cross-checked by
  agent-09 (51/53 hash citations; the 2 others are annotated as dated history).

## 8. Novelty
Line-cited against the four supplied sources (NOVELTY_RECHECK_1950.md):
- DMM+25 is O(m lg^{2/3} n).
- DMSY26 is O(m√lg n + √(mn lg n lglg n)); fn. 1 gives nothing better for m/n ≥ lglg n.
- KR26's Table 1 has no other directed entry.
- Cai 2026 is instance-relative and gives no Ω(n lg n) for distances.
- So no directed comparison-addition bound, deterministic or randomized, is o(n lg n) for √lg n ≤ m/n ≪ lg n/lglg n. At the Lean
  profile the best known bound is Dijkstra's Θ(n lg n) (DMSY26 gives n lg^{5/4} n), and C-HD's certified bound is O(n lg^{11/12} n).
  This is a strict improvement in a regime where Dijkstra wins: Gate (C).
- The new non-supplied source arXiv 2607.19346 (Hair–Li–Li–Zhang, 21 Jul 2026) does NOT pre-empt this. I read pages 1-3, and six
  other agents read it independently. It is Las Vegas randomized, m^{1+o(1)} with a 2^{Ω(√lg n)} factor, uses real subtraction, and
  cites DMSY26 as the nonnegative state of the art.

## 9. Limitations (these match the staged LIMITATIONS.md and PAPER §9.2)
1. Directed only. The undirected DMSY23 O(√(mn lg n)) is stronger in the same density range.
2. The gain over Dijkstra is lg^{1/12} n at the Lean profile μ, and at best lg^{1/6} n (m = n√lg n). This is Gate C, not Gate A/B.
3. The formal bound is C·Tchd whenever m ≤ n·F(n), for all n; for n < 2^16 Bellman-Ford runs and is absorbed into C.
   - For m > n·F(n) the formal bound is only C·(n+1)(m+1).
   - The paper's range F(n) < d ≪ lg n/lglg n is NOT formalized.
4. Space: only space ≤ time is proved. The program preallocates Θ(kmN·Tnat) cells; an O(n+m)-space variant is only sketched.
5. The constants are astronomically large: C = bodyC KcC + 65536·9 + 100 ≈ 1.96e24, with KcC ≈ 9.80e23 (Final.lean:107; kmaster(1,1,1000) = kmN). The word exponent is e = 160, i.e. 161·lg(n+m+2)-bit words, still O(log n).
   The result is purely asymptotic.
6. It is deterministic worst case in the comparison-addition model. Nothing is claimed about randomized or amortized settings.

## 10. Reproduction
    cd /research/agents/agent-07/work/repro
    PROG=Frontier.CHD.Final:Frontier.CHD.Final.chdProgram GATEC_THM=Frontier.CHD.Final.chd_gateC \
    CHD_THM=Frontier.CHD.Final.chd_CHDTarget bash final_audit.sh <TAG> Frontier.CHD.Final \
      Frontier.CHD.Final.chd_gateC Frontier.CHD.Final.chd_CHDTarget Frontier.CHD.Final.chd_exact_within
- Outputs of this review's run are in repro/final_final1/: my_repro.txt, replay.txt, stmt_status.txt, closed_probe.txt,
  program_probe.txt, hashes.txt (292 source hashes), hashes_diff.txt.
- The fresh-copy build log, scan, axioms and summary are in repro/final1/.
- Toolchain: leanprover/lean4 v4.34.0; mathlib is the pinned public cache at /opt/lean-mathlib (unmodified).
