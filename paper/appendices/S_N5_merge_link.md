# PAPER_CHD — section N5 (author agent-03): Merge at degree delta. Status: paper proof sketch, NOT reviewed.

## N5.0 The issue
B1 S4.5 T3 charges Merge (BM.14) at O(|D_i|). Since |D_Y| ≤ |S_Y| + δ|U_Y| (B1 (B4)), this is O(δ|U_X|) per call, i.e. O(δN)
per layer and O(δ N L) = O(m L) overall.
 - DMSY26/B1 absorb it because δ ≤ lg t.
 - In C-HD, m L = n d lg n / t, which exceeds the whole budget.
Whether Θ(δ N L) Merge volume is attainable is OPEN. My hop-ordered zero-weight tree family gives only O(m): only the left chain is
partial. A family needs many partial calls per layer whose returned frontiers are ~δ|U|. Neither a construction nor a proof of O(m)
for the linear Merge exists.
Correction: my 11:1x "last-child chain" argument was wrong. Leftovers of NON-last partial children survive. After Merge(D_i), the next
Pull takes only M_l keys, and later D_{i+1}, ... land in front of D_i's remainder (their values are ≺ B_{i+1}, and B_{i+1} is ⪯ every
surviving value).
So C-HD adopts M-LINK below, whose total cost is O(m) unconditionally.

## N5.1 M-LINK (change to S5 Lemma DS, Merge only)
Setting: a level-l block structure D (parameter M = M_l, l ≥ 2) and the returned D' = D_i of a level-(l−1) child (parameter
M' = M_{l−1} = M/2^t). Precondition (S5, unchanged): every stored value of D' is ≺ B_i ⪯ every stored value of D.
 (1) CONSOLIDATE D' left to right: walk D''s blocks in separator order and concatenate consecutive blocks (unordered doubly linked
     lists: O(1) per concatenation; separator = the first block's separator; sizes add). Close a chunk as soon as it holds
     ≥ ⌈M'/3⌉ entries. Closing only at D'-block boundaries keeps (SEP), as in S5 v1.2.
 (2) If the last chunk has < ⌈M'/3⌉ entries, move its entries one by one into the chunk before it. If there is no chunk before it
     (|D'| < M'/3), insert its entries into D's first block, splitting if needed: O(|D'| + M) with O(M) charged as in S5(b).
 (3) Re-separate D's old first block f: set sep_f := B_i. This is legal: every entry of f is ⪰ B_i by PP (D unchanged since BM.10),
     and every D' value is ≺ B_i. No scan is needed. The chunks c_1 < … < c_r get separators −INF, min-free; c_j's separator is the
     separator of its first D'-block for j ≥ 2.
 (4) Insert the r chunks into D's red-black tree: O(r · lg #blocks(D)).
     (A join of the two trees in O(r + lg) also works: all chunk separators precede f's.)
 Membership stacks (S5 §4) are unchanged: entries keep their list nodes. Duplicate keys (a key in both D and D') are handled as in
 S5: the D-entry is unlinked, O(1), found via the membership stack, when the D'-entry is linked.
 Duplicate keys: handled EAGERLY at insertion time, so that M-LINK never meets them (no per-entry pass):
 (5) RULE EA (eager ancestor deletion). When a call Y performs D_Y.Insert(v, lambda) and v has entries in structures of ANCESTOR calls
     (the lower records of v's membership stack, S5 §4), those ancestor entries are deleted (O(1) each; each entry is deleted at most
     once, so this is charged to its creation).
 LEMMA N5.0 (EA is invisible). Let X's i-th child Y_i return. After BM.15, D_X has the same keys and stored values with and without EA.
 Proof. (i) Ancestor structures are not read during Y_i (R9, FP6), so EA changes nothing that Y_i observes.
  (ii) PERSISTENCE: every key v inserted into any D inside Y_i's subtree ends, at Y_i's return, in U_i or in keys(D_i). Track v's entry.
       Its removals are: Pull, after which v ∈ S of a child W', and then v ∈ U_{W'} ⊆ U_i or v ∈ D_{W'} by (R7), merged back up;
       Delete at BM.15, which needs v ∈ U_i; BC.6 extraction, which needs v ∈ U_i; and return of a structure, which is merged into its
       parent. Induction over the subtree gives the claim.
  (iii) So EA deletes, from D_X, only entries of keys that the unmodified algorithm also removes after the return: keys in U_i (BM.15)
       and keys in D_i. For the latter, S5's Merge keeps the D_i value, which is ≺ the old value by the Merge precondition. ∎
 Consequence: when D_i is linked into D_X, keys(D_i) ∩ keys(D_X) = ∅. Keys of D_i are either inserted inside Y_i's subtree (EA removed
 their D_X entry) or S_i-leftovers (BM.25 of Y_i), whose D_X entries were removed by the Pull at BM.10. So M-LINK is O(#blocks),
 not O(|D_i|).

## N5.2 Lemma N5 (cost)
With M-LINK at levels l ≥ 2 and S5's entry-wise Merge at l = 1 (children are base-case BSTs):
 (a) each Merge(D_i) into a level-l call costs O(#blocks(D_i) + (1 + 3|D_i|/M_{l−1}) · lg #blocks(D)) amortized, where #blocks(D_i)
     is charged to block destruction or chunk creation;
 (b) the block count stays bounded, which keeps Insert O(t) and Pull O(M_l):
     #blocks(D) ≤ 1 + O(N_X/M_l) + 3N_X/M_{l−1}, so lg #blocks(D) ≤ lg(N_X/M_l) + t + O(1) = O(t + lg(tδ)), and (A_M) holds for
     l ≥ 2;
 (c) total Merge work over the run is O(m + N).
Proof sketch.
 (a) Consolidation touches each D'-block once; each concatenation destroys a block. Blocks are charged once at creation (S5(a,g)).
     Chunks number ≤ 3|D'|/M' + 1, each inserted in O(lg #blocks).
 (b) Blocks of D are D's own blocks plus linked chunks. Own blocks: S5(a) gives 1 + O(N/M). Linked chunks: Σ_i 3|D_i|/M_{l−1}
     ≤ 3N_X/M_{l−1}, with N_X ≤ |S_X| + δ|U_X| = O(δ t^3 2^{lt}).
     Pull may remove up to 3·2^t + O(1) front chunks to collect > M_l entries. Each removal is charged to its creation. The removals
     cost O(2^t · t) = O(M_l) for l ≥ 2, and selection costs O(M_l). So PP and O(|S'|) amortized are unchanged.
 (c) l = 1 merges: Σ_{partial base calls} |D_Y| ≤ Σ δ|U_Y| ≤ δN = O(m), since base-call U's are disjoint.
     l ≥ 2 merges: Σ_{partial Y at level l−1} (1 + 3|D_Y|/M_{l−1}) · O(t). This is at most
       (#partial calls) · O(t) + O(t/M_{l−1}) · δN
         = O(N/t^2) + O(δN / 2^{(l−2)t}),
     using that a partial call has |U| ≥ Λ_{l−1} ≥ t^3 and the U's of a layer are disjoint. Summing over l ≥ 2 gives
     O(δN) = O(m). ∎
Obligation for S5 (agent-04): rewrite Lemma DS rows "Merge" and (e) with (a)–(b), and add rule EA to Insert (one membership-stack
walk). Everything else in S5 is unchanged, and correctness (PP, SEP, Merge precondition) is unchanged.
Formalization note: if the team prefers to avoid M-LINK, it must PROVE Σ_{partial Y} |D_Y| = o(n lg n) for the linear Merge. I do not
have such a proof.
