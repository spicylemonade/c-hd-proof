# CLAIM (DRAFT, not a claim yet; agent-10 staging, updated 2026-09-20 23:05 UTC)

STATUS: CANDIDATE, NOT YET ACCEPTED.
- The theorem below is PROVED in Lean on the frozen tree (integration build #33, 2548 jobs, 0 sorry, standard axioms).
- Acceptance still needs the independent kernel replay (agent-09), the fresh-copy rebuild (agent-07), REVIEW_1 (agent-07) and REVIEW_2 (agent-02).
- Nothing in this file may be copied to /research/final/ until the whole GOAL.md checklist passes.

## Gate
C: a strict new worst-case upper bound, for DIRECTED graphs, in a density regime where Dijkstra's O(m + n lg n) is the best known bound.

## Lean theorems (Frontier/CHD/Final.lean)
- `theorem Frontier.CHD.Final.chd_gateC : Frontier.GateC`: the gate statement of CostModel.lean:394.
- `theorem Frontier.CHD.Final.chd_CHDTarget : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F`: the frozen target of GateC.lean.
- `theorem Frontier.CHD.Final.chd_exact_within`: `chdProgram.Exact ∧ ∀ G s, chdProgram.RunsWithin G s ((bodyC KcC + 65536·9 + 100) · Tdisp F n m)`.
- Axioms: [propext, Classical.choice, Quot.sound] for all three.
- `#print axioms Frontier.CHD.Final.chdProgram`: "does not depend on any axioms". So the algorithm term uses no choice.

Witness program: `Final.chdProgram := L6.chdProg 160 psC coreC`, which is
  `⟨Dispatch.dispatchProg (chdBody coreC) BF.prog, 160, psC⟩`.
- coreC = coreTop (spineOf (spinePro BL2.fpAlloc DPro.dProC)).
- psC = [bmsspProc (baseProgC dsNew dsIns) recC, selBody entLess 1].
- recC = recText fpAtRaw dsNew dsIns dsEmpty (iterText pullD dsMerge dsDelB dsIns) (finProg dsEmpty tstT6 dsIns tstWp (relW dsIns) dsDelW).
It is ONE closed RAM program, uniform over all inputs, with word exponent e = 160.

## Model
CostModel v2 RAM (Frontier/CostModel.lean):
- words < (n + m + 2)^(e+1);
- real weights enter only via `+` and `≤` (comparison-addition);
- every statement and test costs 1, and allocating k cells costs k + 1;
- procedures have no frames (global registers/arrays);
- input is an explicit edge list, output is the distance array plus a reachability flag.

## Bound
Worst-case time C · Tdisp F n m, where:
- Tdisp_F(n, m) = Tchd(n, m) if m ≤ n·F(n), and (n+1)(m+1) otherwise (GateC.lean:27). There is NO condition on n: the bound holds for every n.
  - Tchd(n, m) = n + m + m·ln(m/(n+1) + 2) + m^{1/3}·(n·ln(n+2))^{2/3}, with natural logs (GateCCalc.lean:22).
  - F(n) = Nat.sqrt(Nat.sqrt((Nat.log 2 n)^3)) = ⌊⌊log₂ n⌋^{3/4}⌋, with an inner floor.
- The program runs the C-HD code when log₂ n ≥ 16 and m ≤ n·F(n), and verified Bellman-Ford otherwise.
  - For log₂ n < 16, Bellman-Ford costs ≤ 9(n+1)(m+1) ≤ 9·2^16·Tchd. That is the 65536·9 term of C.

Space ≤ time (`NamedWitness.chdProg_space`).

## Regime of improvement (d = m/n, L = lg n)
- Gate C (the regime where Dijkstra is the best known bound) is d ≥ sqrt(L).
- C-HD is o(nL) there iff d lg d = o(L).
- The formal profile is μ(n) = n · ⌊ln(n+2)^{3/4}⌋ (GateCCalc.s, natural log):
  - it lies inside the Dijkstra-wins window (`mu_window`);
  - Tchd = o(n lg n) along it (`tendsto_Tchd_mu`).
- The Lean bound covers m ≤ n F(n), i.e. d ≤ L^{3/4}. So the formally covered Gate-C regime is sqrt(L) ≤ d ≤ F(n).
- The wider paper regime, up to d ≪ L/lglg n, is NOT formally proved.
- For comparison only (paper level): for L^{1/4} ≪ d < sqrt(L) the Tchd bound also beats DMSY26's O(m sqrt(L)). The DMSY26 bound is not formalized.
