# REVIEW 1: independent non-author review of the C-HD Gate-C claim (agent-07). DRAFT v3, 2026-09-20 22:58 UTC.

Status of this draft: every <...> field must be filled from the FINAL tree by repro/final_audit.sh. The verdict is decided only
by FINAL_REVIEWER_STATEMENT_TEMPLATE.md items 1-6. If the final theorem is not proved, REVIEW_1_FALLBACK.md is used instead.

Reviewer: agent-07. Lane: counterexamples and proof testing. I authored NO module of the C-HD chain. My only file in
/research/lean is Frontier/Counterexamples.lean, a lane deliverable; the audit checks that it is NOT in the final closure.
Verdict: <ACCEPTED | NOT ACCEPTED>.

## 1. Claim
- Final theorems (module Frontier.CHD.Final): `chd_gateC : Frontier.GateC`, `chd_CHDTarget : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F`,
  and `chd_exact_within` (the named program is Exact and RunsWithin C·Tdisp F).
  Closedness is checked by `example : Frontier.GateC := <GATEC_THM>`, which is exactly the frozen type with no hypotheses.
  Result: <closed_probe>.
- The frozen statements are identical to the 12:30 snapshot. This was re-verified 20:22 (stmt_2022.txt); final result: <stmt_status>.
  - GateC: there exist P Exact and T with RunsWithin T, and a profile μ with n·sqrt(log(n+2)) ≤ μ(n) ≤ n·log(n+2) eventually and
    T(n, μ n)/(n log(n+2)) → 0.
  - CHDTarget F: there exist P Exact and C with RunsWithin G s (C·Tdisp F n m) for every graph.
  - Tchd n m = n + m + m·log(m/(n+1)+2) + m^(1/3)·(n·log(n+2))^(2/3), with real exponents (1/3 : ℝ) and (2/3 : ℝ).
  - F n = sqrt(sqrt(Nat.log 2 n ^ 3)).
- Model (CostModel v2): a word RAM with words < (n+m+2)^(e+1).
  - Real values are touched only by 0, + and ≤ (the comparison-addition model).
  - Allocation of k cells costs k+1.
  - The procedure table is part of the finite Program syntax. It is never modified, and `call` costs 1.
  - There are no oracle primitives, and no operation converts values to words.
- The witness program is `Final.chdProgram := chdProg 160 psC coreC` (O30), a closed def:
  - coreC = coreTop (spineOf (spinePro BL2.fpAlloc DPro.dProC)), with dProC = dPro (12·kmN) and kmN = 10,219,910,400 (verified by rfl and #eval);
  - psC = chdPs dsNew dsIns recC [selBody entLess 1];
  - recC = recText fpAtRaw dsNew dsIns dsEmpty (iterText pullD dsMerge dsDelB dsIns) (finProg dsEmpty tstT6 dsIns tstWp (relW dsIns) dsDelW).
  The serialized text has 24,936 tokens.
  - Probe: #print axioms = <none>; #eval repr length <n>; wordExp <e>; procs.length <2>.
  - ps = [bmsspProc (baseProgC newS insS) recC, selBody entLess 1] (O32).

## 2. Proof audit
- Kernel replay (repro/Replay07.lean, Lean.Kernel.Environment.replay) of every Frontier constant in the final closure: <N> constants, <result>.
  Axioms of the final theorems: <list>. Expected: propext, Classical.choice, Quot.sound.
- Fresh-copy rebuild + token scan (repro/my_repro.py): <result>. HARD tokens: <0>. INFO: <decide := true / decide +kernel list>.
- The import closure contains only Frontier, Mathlib and core modules: <result>. Frontier.Counterexamples is absent: <result>.
- Chain (final names; every link replayed):
  - GateC ⇐ GateCTarget.chdTarget_F_imp_gateC ⇐ CHDTarget F
    ⇐ L6/Final <CHD_THM> (instantiation: DLf, dPro, ps, e, decide checks, hbig)
    ⇐ L6/Assembly.chdTarget_of_step
    ⇐ L6/LevelRoute.chdTarget_of_levels
    ⇐ callSpec_of_levels (base callSpec_base = agent-03 callSpec_zero; step = body_spec composition)
    ⇐ TopGlue / ProFinal / SpineIface / Body / Dispatch
    ⇐ exactness (complete_of_topRun: BM.bmsspDL_top, fpC_sound, tau_top_gt) and cost (MasterSpec: chdDL_tele_top, CostFinal.total_le_Tchd).
  - Layer B:
    - B-L2: fpCall_spec, fpAtRaw;
    - B-L3: DLayerInst DRI and the ops new/ins/delB/empty (04), merge (02 DMergeI), pull (05 pullS + 04 wrapper), dPro (09);
    - B-L4: loop2_spec (08), pro_spec (01), postSpec (06), fin_spec (03), body_spec (01);
    - base: RamBaseCase + BaseConvDL + callSpec_zero.
- Tracker CHD_INTERFACE_OBLIGATIONS.md, O1-O32 + B-L2/3/4 + PT: <all DONE / open list>.

## 3. Interface-satisfiability audit (my main non-kernel contribution)
The kernel accepts theorems whose hypotheses are unsatisfiable, so every interface was checked for instantiability:
- 17:48 SpineLoop pass MISSED the inverted DLayer.frame/PhiI.frame (found by 06/03). Fixed, 6666f2ae.
- 18:30 RelWB needed W'-completeness (found by 02).
- 20:18 use/ucap (O31) is satisfiable:
  - each op has use ≤ use + (c+1), or equality;
  - insertL costs ≥ 2;
  - merge reuses block records (groupAux);
  - the post-half's no-slack bound holds via lres.length ≤ card markedGroups.
  Adopted: Cu = 2.
- 20:40 the procedure table lacked the recursive select procedure needed by the pull (O32). Fixed by the 2-entry ps (agent-10, 20:42).
- 20:42 agent-02 found LtI.run unsatisfiable without px < n. Fixed.
- 20:45 (02) merge_spec lacked a level bound; 21:37 MergeOK gets l ≤ P.top and DLayer gets LT. 20:47 (07) use after dPro is 1, not 0 (the post says use ≤ 2);
  pullS needs sel.w, which dPro now allocates. 21:05 (07/08) LoopSpecB factor 1 vs factor 2 was restated. 21:55 (04) the pull wrote spine registers; pullD saves/restores them.
- Final instance check: every interface structure is instantiated by a concrete object in the final theorem (DLf, PIf, heapI, labI, treeImpl).
  So no hypothesis survives: <result of closedness>.

## 4. Cost audit
- The RAM cost is the model's `cost`, charged by `exec` itself. No work is uncharged, and Lean-level computation appears only in proofs.
- Level constant K is uniform in the level (the single-K induction). The use capacity is ucap = 12·kmN·Tnat + 2, and dPro allocates arrays of ucap + 2 = 12·kmN·Tnat + 4 cells each, at O(Tnat) cost
  (Tnat ≤ 33·Tchd, L6/Tnat.Tnat_le_Tchd). The constants are huge but fixed.
- e ≥ Dp + 40 is chosen last (hbig).

## 5. Independent evidence (not proof)
- C++ simulator (lab/, sha 579bfbf5). All runs had 0 violations:
  - CallPost: 459M distinct checks;
  - pointer invariant: 1.5e9 observations (exhaustive n=4 over weights {0,1} + absent, and n=5 over weight {0} + absent);
  - DS' lazy = literal;
  - #blocks bound;
  - mutation tests have teeth.
- ramsim (independent exec interpreter, identical charges):
  - BF: cost 206 = Lean;
  - body skeleton: 550 graphs;
  - dispatcher at n = 2^16: exact;
  - params: 300 cases;
  - stub assembly (L6 + prologue + fpAlloc + coreTop + fpAtRaw): 460 runs, 0 stuck, sound labels;
  - FINAL program text: my serialization of `Final.chdProgram` differs in exactly ONE token (dPro's capacity literal 12·kmN -> 12,
    since 1.2e11·Tnat cells cannot be allocated in a simulator) from the program I ran. Results with e = 160 and psC exactly:
    - body mode (real parameters), 300 graphs: 0 mismatches vs Dijkstra, 0 stuck;
    - deep mode (t = k = 2, L forced), 200 graphs: 0 mismatches, 0 stuck;
    - instrumented, 120 graphs: calls by level {0: 855, 1: 257, 2: 60, 3: 15}, 970 calls of the recursive select procedure, 0 bad;
    - full mode (dispatcher at n = 2^16, C-HD branch, Cw = 1): <result>.
- Numeric parameter checks: params/param_check.py (508 cases) and tnat_check.py (1,115 cases, Tnat/Tchd ∈ [2.16, 5.45]).

## 6. Novelty (NOVELTY_RECHECK_1950.md, line-cited against the 4 supplied sources)
- No directed comparison-addition bound, deterministic or randomized, is o(n lg n) for sqrt(lg n) ≤ m/n ≪ lg n/lglg n.
  - DMM+25: O(m lg^{2/3} n).
  - DMSY26: O(m sqrt(lg n) + sqrt(mn lg n lglg n)); footnote 1 gives nothing better for m/n ≥ lglg n.
  - KR26 Table 1 lists no other directed entry.
  - Cai 2026 is instance-relative and has no Ω(n lg n) for DIST.
- C-HD, Tchd = O(n + m + m lg(m/n) + m^{1/3}(n lg n)^{2/3}), is o(n lg n) there and beats every known directed bound for
  lg^{1/4} n ≪ m/n ≪ lg n/lglg n. This satisfies Gate (C).

## 7. Limitations (must match the package's LIMITATIONS.md)
1. Space: only space ≤ time, the model invariant (chdProg_space).
2. The gain over Dijkstra is lg^{1/12} n at the Lean profile μ = n·F(n), and at best lg^{1/6} n (m = n sqrt(lg n)).
   It is a Gate-C (density-regime) result, not Gate A/B.
3. The undirected DMSY23 bound O(sqrt(mn lg n)) is stronger in the same density range.
4. The formal bound is C·Tchd(n, m) whenever m ≤ n·F(n), for ALL n. For n < 2^16 the program runs Bellman-Ford there, and its cost is absorbed by the 65536·9 term of C. For m > n·F(n) the formal bound is only C·(n+1)(m+1), the Bellman-Ford fallback in Tdisp.
5. The constants are huge. kmN ≈ 1.02e10, the level constant is K = 210,000 (K_D = 23,037), and the D arrays hold 12·kmN·Tnat + 4 cells each. This is an asymptotic result only.
   SPACE: the program preallocates Θ(kmN·Tnat) cells, so the formal space is Θ(T), not O(n+m) (agents 05/04). Space ≤ time is the only formal space statement; an O(n+m)-space variant is only sketched.
6. Deterministic worst case, in the comparison-addition model with a word RAM of (e+1)·lg(n+m+2)-bit words, e = 160 (hbig needs e ≥ 139). Words are O(log n) bits with a large constant.
7. F = Nat.sqrt (Nat.sqrt ((Nat.log 2 n)^3)) = ⌊⌊lg n⌋^{3/4}⌋. The C-HD code runs only for n ≥ 2^16 and m ≤ n·F(n). The paper's Theorem 3 (o(n lg n) up to d = o(lg n/lglg n)) is NOT formalized beyond d ≤ F(n).

## 8. Reproduction
- repro/final_audit.sh <TAG> <ROOT> <THMS> with PROG=<Module:Const>, GATEC_THM=<..> and CHD_THM=<..>.
  Outputs go to repro/final_<TAG>/: my_repro.txt, replay.txt, stmt_status.txt, closed_probe.txt, program_probe.txt, hashes.txt.
- The pinned toolchain is leanprover/lean4 v4.34.0 with the public mathlib cache (lean-toolchain, lake-manifest.json sha256 in hashes.txt).
