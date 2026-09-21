# LIMITATIONS (DRAFT; agent-10 staging; NOT a final file; updated 2026-09-20 23:05 UTC)

This draft becomes /research/final/LIMITATIONS.md only if CHDTarget F is proved unconditionally and reviewed.
Until then there is NO result.

## Scope of the claim
- **Directed only.** For undirected graphs, DMSY23's O(sqrt(m n lg n)) (KR26 fn. 2) is stronger in the same density range. C-HD claims nothing for undirected graphs beyond what it inherits (agent-07, 19:48/19:59).
- **Gate C only.** No claim for gates A, B, E or F.
- **Deterministic worst case** in the CostModel v2 RAM + comparison-addition machine. There are no randomized or amortized claims.
- **The formally covered regime is narrower than the paper's window.**
  - The Lean theorem certifies the Tchd bound only for m ≤ n·F(n), with F(n) = ⌊⌊log₂ n⌋^{3/4}⌋ (inner floor; Nat.sqrt(Nat.sqrt((Nat.log 2 n)^3))).
  - So the formally covered improvement regime is sqrt(L) ≤ d ≤ F(n), with d = m/n and L = lg n.
  - The paper-level window sqrt(L) ≤ d ≪ L/lglg n is NOT formally covered.
  - The condition d lg d = o(L) (agent-07's correction) applies at paper level only.
- **Outside the window the program is worse than Dijkstra.** The dispatcher runs Bellman-Ford when n < 2^16 or m > n·F(n). This costs O((n+1)(m+1)), and no improvement is claimed for that range. Gate C only needs one density profile μ.
- **Size of the improvement.**
  - At the Lean profile μ(n) = n·⌊ln(n+2)^{3/4}⌋, the gain over O(m + n lg n) is about lg^{1/12} n (C-HD: n·L^{11/12} vs Dijkstra n·L).
  - At m ≈ n·sqrt(lg n) the gain is about lg^{1/6} n.

## Model and constants
- **Word size.** Words are polynomial: the capacity is (n + m + 2)^(e+1), with the fixed word exponent e = 160, i.e. 161·log2(n+m+2)-bit words.
  - e is chosen AFTER the constants (hbig160 : … ≤ 4^(160+1-8)).
  - The budget slack has degree 8: SlfC ≤ (10^9 + 64(K+28)^4·10^56)·(cn+cm+2)^8.
- **Constants are astronomically large.** They include:
  - 5100·c·a in total_le_Tchd;
  - kmaster(1, 1, 1000);
  - 13000 + 34(Kf + Kd) in the prologue;
  - the step constant K.
  There is no practical relevance. The practical-result option was removed by the user.
- **Space is Θ(T), not O(n + m)** (agent-05/agent-04, 22:54).
  - The D layer preallocates its entry pool, block records and stack with ucap + 2 = 12·kmN·Tnat + 4 cells each, plus sel.w of 6·ecap + 60 cells, and never reclaims entries.
  - Formally, space ≤ cost (AuditBridge / NamedWitness.chdProg_space), and the allocation is O(Tnat) = O(Tchd) time.
  - There is no O(n + m) space theorem.

## Verification scope
- The proofs use the standard axioms propext, Classical.choice and Quot.sound, and these are disclosed.
- The program is one closed term. `#print axioms Frontier.CHD.Final.chdProgram` prints "does not depend on any axioms". Choice is used only in the proofs and in the specification (distances as walk infima), never in the algorithm.
- The name-disjointness side conditions are decided by the kernel (`decide +kernel`) at a closed dummy instance, then transferred by definitional unfolding.
- Novelty rests on the four supplied primary sources plus web searches (agent-07's and agent-09's records). This is not an exhaustive literature review.
