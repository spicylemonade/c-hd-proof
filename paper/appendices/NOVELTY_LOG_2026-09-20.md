# C-HD novelty log (agent-03), re-run 2026-09-20 ~17:45 UTC

Claim checked: a deterministic comparison–addition algorithm for exact directed nonnegative-real SSSP (labeled distances,
explicit input, all costs charged) in worst-case time O(n + m + m·lg(2 + m/n) + m^{1/3}(n lg n)^{2/3}), which is
o(n lg n) for average degree d = m/n in [c·√lg n, o(lg n / lg lg n)] — a regime where Dijkstra (O(m + n lg n) = Θ(n lg n))
is currently the best known worst-case upper bound.

## Primary sources re-read (local copies in /research/references, hashes in source-hashes.json)
- 2504.17033v2 (Duan, Mao, Mao, Shu, Yin 2025): deterministic directed O(m lg^{2/3} n). At d = lg^α n this is n lg^{α+2/3} n,
  ≥ n lg n for α ≥ 1/3.
- 2602.07868v2 (Duan, Mao, Shu, Yin 2026, ICALP 2026): deterministic directed O(m√lg n + √(mn lg n lglg n)).
  At d ≥ √lg n the first term is ≥ n lg n. Footnote 1 ("also works when δ > log k") does not change the analysis:
  FindPivots is charged k(δ + log k) per local search (see PAPER §8).
- 2609.15247 (undirected, 2026): undirected graphs only; not comparable.
- 2609.04825v1 (Cai, resource complexity, Sept 2026): Theorem 9.2/K.2 uses DMSY26 as a black box on an active core, bound
  O(OPT_DIST·√log OPT_DIST·lglog OPT_DIST). OPT_DIST is Θ(m) on topologies whose addition law ρ_fwd is Θ(m), so the
  worst case over graphs with (n, m) is Ω(m√lg m) ≥ n lg n at d ≥ √lg n. Its other results are exact resource laws and
  lower bounds, not worst-case improvements in this regime.
- Universally optimal Dijkstra (Haeupler, Hladík, Rozhoň, Tarjan, Tětek; arXiv 2311.11793): optimal for the ORDER-producing
  task per topology; its worst case over (n, m) is Θ(m + n lg n).

## Web searches (US index, WebSearch tool), all on 2026-09-20
1. "directed single-source shortest paths 2026 deterministic comparison-addition faster than Dijkstra moderate density"
   — hits: 2602.07868, 2504.17033 (STOC'25), 2609.15247. No new directed bound.
2. "arXiv 2026 directed SSSP \"sorting barrier\" new bound m log^(1/3) n OR \"sqrt(log n)\" improvement"
   — hits: the same, plus 1808.10658 (bottleneck paths), 2111.13240 (hopsets). Nothing in this regime.
3. "\"single-source shortest paths\" directed graphs \"average degree\" improvement over Dijkstra 2026 arXiv"
   — hits: 2602.07868, 2511.03007 (implementation study of DMM+25), parallel SSSP papers. Nothing new.
4. "Duan Mao Shu Yin directed shortest path follow-up 2026 \"o(m + n log n)\" dense regime lower order"
   — hits: 2602.07868 (+ ICALP 2026 version), 2602.16638 (negative weights, n^{2+o(1)}), popular articles. Nothing new.
5. "arXiv September 2026 shortest paths directed real weights deterministic new algorithm"
   — hits: 2609.05590 (Duong, integer negative weights, O((m + n lglg n) lg² n lg(nW)): integer model, not comparable),
     2511.07859 / 2511.12714 (negative-weight, integer), 2602.07868.
6. "\"bundle\" Dijkstra directed graphs shortest paths comparison addition 2026 m sqrt(n log n) directed extension"
   — hits: DMSY23 (undirected, randomized), 2510.12598 (undirected derandomization), 2311.11793. The directed extension of
     bundle Dijkstra is still listed as open (KR26 Sec. 4).
7. "directed SSSP real weights \"n log n\" barrier graphs with m = n log^{c} n new upper bound 2026"
   — hits: 2602.07868, 2504.17033, blog posts, implementations. Nothing new.

## Conclusion (unchanged from PAPER §8, now with a dated log)
No located primary source gives a deterministic (or randomized) directed comparison–addition SSSP bound that is o(n lg n)
for average degree d ≥ c·√lg n. The C-HD bound would be a new worst-case improvement over Dijkstra in the regime
d ∈ [c√lg n, o(lg n / lglg n)], by a different mechanism (counted unexplored leaves in FindPivots, permanent L_X deletions,
disjoint handled ranges with home charging, block-linking D). This is a novelty check, not a proof: the claim stays
NON-GATE until the Lean chain of GOAL.md closes and two reviews reproduce it. Caveat: the web index is US-only and may
lag arXiv by days; the search should be repeated immediately before any final claim.

## Dated re-run 2026-09-20 ~22:55 UTC, before the final assembly (web searches with the WebSearch tool, US index)
Queries:
1. "directed single-source shortest paths deterministic faster than Dijkstra 2026 arXiv new bound"
2. "\"shortest paths\" directed \"real weights\" o(n log n) \"average degree\" arXiv September 2026"
3. "Duan Mao Shu Yin directed shortest path 2026 improvement \"m log\" deterministic sorting barrier new"
4. "arXiv 2609 single-source shortest paths directed graphs nonnegative weights comparison-addition model"
5. "\"directed\" \"bundle\" Dijkstra shortest path m sqrt(n log n) directed graphs 2026 extension"
6. "new shortest path algorithm September 2026 directed graphs beats Duan et al \"log^{1/3}\" OR \"o(m sqrt(log n))\""

Hits already known: 2504.17033, 2602.07868 (ICALP 2026), 2609.15247 (undirected), 2511.03007 (implementation study),
2609.05590 (deterministic negative weights, integer), 2511.07859 / 2511.12714 / 2602.16638 (negative weights).

NEW primary sources checked:
- **arXiv 2607.19346**: Hair, G. Z. Li, J. Li, Zhang, "Bellman-Ford in Almost-Linear Time", 21 Jul 2026.
  - Thm 1.1: a Las Vegas RANDOMIZED algorithm for directed SSSP with real, possibly negative, weights in m^{1+o(1)} time w.h.p.,
    in the comparison-addition model. This covers nonnegative weights as a special case.
  - The o(1) term is not stated in closed form. The recursion structure (depth O(√log n), O(log n)^i branching,
    polylogarithmic work per level) indicates an m^{o(1)} factor of order 2^{O(√log n · loglog n)}.
  - It does not pre-empt C-HD. In our regime d = m/n ≥ √lg n, any bound m·f(n) with f(n) ≥ lg n is ≥ n·lg^{3/2} n, which is not
    o(n lg n). To be o(n lg n) at d = √lg n, an almost-linear bound would need an m^{o(1)} factor that is o(√lg n). Nothing in
    2607.19346 claims or suggests that. Its bound is also randomized, while C-HD is deterministic.
- arXiv 2602.16153: G. Z. Li, J. Li, Zhang, "Bellman-Ford in Almost-Linear Time for Dense Graphs", Feb 2026. n^{2+o(1)} time,
  so it is not comparable at m = n·polylog n.

Conclusion unchanged: no located primary source gives a deterministic (or randomized) directed comparison–addition SSSP bound that
is o(n lg n) at d ∈ [c·√lg n, o(lg n / lglg n)].
@novelty auditors (agent-09, agent-07): please independently confirm the reading of 2607.19346's o(1) term from its full text.
- Correction (23:05), per reviewer #2 (agent-02, board 23:00): 2607.19346 uses real subtraction (potentials), so it lies OUTSIDE
  the comparison–addition model. My "comparison-addition model" above came from an automated page summary and was wrong on this
  point. The conclusion is unchanged: it does not pre-empt C-HD, because it is randomized, uses subtraction, and has no
  o(n lg n) guarantee in the window.
- Addendum (23:45), the independent confirmations of the 2607.19346 reading (board, 22:59-23:40):
  - agent-10 (22:59): read the abstract and HTML Theorem 1.1. Las Vegas, m^{1+o(1)} w.h.p.; the machinery is ≥ m lg n.
  - agent-07 (22:59): its own introduction cites O(m√(log n loglog n)) [DMM+25, DMSY26] as the nonnegative state of the art.
  - agent-05 (22:59): the factors are exp(O(√(lg n lglg n))).
  - agent-04 (22:59, from the PDF text): base case Õ(m·k) with k ≤ 2^{√log n}, so the o(1) factor is ≥ 2^{√lg n}.
  - agent-02 (23:00): it uses real subtraction (potentials).
  - agent-09 (23:20 and 23:40, from the full HTML): at most √log n recursion levels ("the number of negative vertices drops by
    2^{√log n} in each recursive call") and O(log n)^i recursive instances at level i. Total exp(O(√lg n·lglg n)).
  - Precise statement, which is used in PAPER_CHD_v2 §8. The published analysis carries a factor 2^{Ω(√lg n)}, and at most
    exp(O(√lg n·lglg n)). So the best bound known from 2607.19346 is ω(n lg n) throughout the window.
  - Note: "m^{1+o(1)} ≥ m·2^{√lg n}" is not a valid inequality, since m^{1+o(1)} is a class of functions; agent-09 flagged this.
