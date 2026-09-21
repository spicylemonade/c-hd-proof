# NOVELTY (DRAFT; agent-10 staging, updated 23:52. Sources: agent-07's NOVELTY_CHECK_agent07.md and NOVELTY_RECHECK_1950.md, agent-09's NOVELTY_CHD_FINAL.md, agent-10's NOVELTY_LOG.md)

## Claim being assessed
C-HD computes exact directed SSSP with nonnegative real weights, deterministically in the comparison-addition model, in time O(n + m + m lg(m/n) + m^{1/3}(n lg n)^{2/3}). The Lean theorem (natural-log Tchd = n + m + m·ln(m/(n+1)+2) + m^{1/3}(n ln(n+2))^{2/3}) certifies the regime m ≤ n F(n) with F(n) = ⌊⌊log₂ n⌋^{3/4}⌋. Write d = m/n.

## Known bounds (primary sources in /research/references, hashes in source-hashes.json)
| work | graphs | bound |
|---|---|---|
| Dijkstra with a Fibonacci heap | directed | O(m + n lg n) |
| DMM+25 (2504.17033v2) | directed | O(m lg^{2/3} n) |
| DMSY26 (2602.07868v2), Thm 1.1 and fn. 1 | directed | O(m √lg n + √(m n lg n lglg n)). Degree capped at δ = O(lg k). Their Lemma 3.2 FindPivots costs k(δ + lg k) per vertex. |
| DMSY23 (quoted in 2609.15247) | undirected, randomized | O(√(m n lg n)) for n lglg n ≤ m ≤ n lg n |
| Kadria–Roditty 2026 (2609.15247) | undirected, randomized | O(m √lg n (lglg n)^{1/4} …). Its §4 states that the directed extension is open. |
| Cai 2026 (2609.04825v1) | directed, per fixed topology | Resource tradeoffs. It gives no Ω(n lg n) bound for distances, so there is no conflict. |
| Hair–Li–Li–Zhang 2026 (arXiv 2607.19346, 21 Jul 2026), Thm 1.1 | directed, real (negative allowed), Las Vegas RANDOMIZED, w.h.p. | m^{1+o(1)}. The published analysis has ≤ √lg n recursion levels, with O(log n)^i instances at level i, and a base case Õ(m·k) with k up to 2^{√lg n}. The subpolynomial factor is 2^{Ω(√lg n)}, with a total of exp(O(√lg n·lglg n)). |
| B1 draft (background, unverified) | directed | a smaller improvement; not this team's result |

## Where C-HD is new (directed, deterministic, comparison-addition)
- vs Dijkstra: C-HD = o(n lg n) iff d lg d = o(lg n), i.e. d = o(lg n / lglg n). The m lg(m/n) term gives n d lg d (agent-07's correction, 19:59).
- vs DMSY26: C-HD is smaller iff d = ω(lg^{1/4} n). The term ratio is lg^{1/6} n / d^{2/3}.
- So C-HD strictly improves the best known directed bound for lg^{1/4} n ≪ d ≪ lg n / lglg n.
- For d ≥ √lg n, Dijkstra is the best known directed bound, so the sub-window √lg n ≤ d ≪ lg n / lglg n is a Gate-C (Dijkstra-wins) regime.
- At the Lean profile d = ⌊ln(n+2)^{3/4}⌋, C-HD's certified bound Tchd(n, μ(n)) is Θ(n lg^{11/12} n). Only the upper bound on the running time is proved. The comparison is with n lg n for Dijkstra and n lg^{5/4} n for DMSY26.

## The technical delta vs DMSY26
DMSY26 caps the degree at O(lg k). C-HD keeps degree Θ(d) using:
- FindPivots-HD with counted unexplored leaves, stopping at |K| = k;
- FH.9 L_X edge deletions, with Lemma L;
- foreign-leaf accounting via handled ranges;
- F3 home charging;
- DS' lazy blocks with splice Merge;
- k = ⌈√t⌉, forced by Θ(k²) intra-K edges per search.

## Caveats
- The result is DIRECTED only. The undirected DMSY23 bound O(√(m n lg n)) (KR26 fn. 2) is stronger in the same density range.
- The undirected analogue is stronger and known.
- The gain is small: lg^{1/12} n at the Lean profile.
- The formally covered regime is only m ≤ n F(n).

## Search log
- 2026-09-20 ~11:15 UTC: four web queries (agent-10). No directed comparison-addition o(n lg n) result was found for m/n ∈ [√lg n, lg n).
- 2026-09-20 agent-07 re-check against the four reference texts: consistent.
- 2026-09-20 19:50 UTC agent-07 dated re-check with line citations: DMSY26 Thm 1.1 (l. 39-41) and fn. 1 (l. 331-333); DMM+25 Thm 1.1 (l. 41); KR26 Table 1 (l. 88-96); Cai l. 164-168. No directed bound is o(n lg n) for sqrt(lg n) ≤ d ≪ lg n / lglg n.
- 2026-09-20 19:58 UTC agent-09 NOVELTY_CHD_FINAL.md, reviewed by agent-07. Fixes applied here: the d lg d condition, and 2504.17033v2 = DMM+25.
- 2026-09-20 22:55 UTC agent-03 re-run (6 queries). One NEW primary source: arXiv 2607.19346 (Hair–Li–Li–Zhang, "Bellman-Ford in Almost-Linear Time").
  - agent-10 independently fetched the abstract and HTML Theorem 1.1 at 23:02 UTC: "There is a (Las Vegas) randomized algorithm for single-source shortest paths on real-weighted directed graphs which runs in m^{1+o(1)} time, with high probability."
  - It does NOT pre-empt C-HD:
    (i) it is randomized, and C-HD's claim is deterministic worst case;
    (i') it uses real SUBTRACTION (potentials), which lies outside the comparison-addition model (reviewer #2, agent-02, 23:00);
    (ii) its STATED upper bound m^{1+o(1)} = n·d·m^{o(1)} is o(n lg n) at d ≥ sqrt(lg n) only if the subpolynomial factor is o(sqrt(lg n)). The paper does not state the factor in closed form, and its analysis multiplies polylog factors over O(log n) shortcutting rounds. So as published, the bound does not give o(n lg n) anywhere in the Gate-C window, and Dijkstra remains the best known bound there even counting randomized algorithms. Confirmations of this reading:
      - agent-07 (22:59);
      - agent-05 (22:59): the factors are exp(O(sqrt(lg n lglg n)));
      - agent-04 (22:59, from the PDF text): the o(1) factor is at least 2^{sqrt(lg n)}, because its base case costs Õ(m·k) with k up to 2^{sqrt(log n)};
      - agent-09 (23:20, full HTML): exp(O(sqrt(log n)·lglg n)), which is super-polylog.
      So the published analysis carries a factor 2^{Ω(√lg n)}: its base case is Õ(m·k) with k up to 2^{√lg n}, and √lg n recursion levels with O(log n)^i instances at level i give exp(O(√lg n·lglg n)) in total. The best bound known from it is therefore ω(n lg n) throughout the window.
- A dated final re-check is to be run before completion.
