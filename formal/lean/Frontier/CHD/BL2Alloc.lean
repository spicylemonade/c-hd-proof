import Frontier.CHD.BL2Call
import Frontier.CHD.TreeRAM10
import Frontier.CHD.AllocList

/-!
# Frontier.CHD.BL2Alloc — B-L2: the one-time allocation of FindPivots-HD and the initial live out-lists
(owner agent-09, NON-GATE)

* `outRep_init`: L6's CSR live lists (`gHd` / `gNxt` over the ranges `[gSt x, gSt (x+1))`, CoreIn's
  `hd` / `nxt`) represent the out-lists `outL` with NO deleted edge: `OutRep st c ∅`;
* `fpAlloc` = agent-03's `allocFP` (tree + tail arrays), the FindPivots arrays (heap, members,
  marks, `W`, `Q`), and the registers `fp.hsz = fp.kl = 0`, `fp.k := cp.k`, `fp.ob := 0`;
  `fpAlloc_spec`: afterwards `FPClean c d ∅` holds for every context with cap `k`.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.PartitionRAM Frontier.CHD.AllocList

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-! ## The initial live out-lists -/

theorem csr_list {m a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) (q : Fin m → Prop) [DecidablePred q]
    (hq : ∀ e : Fin m, q e ↔ a ≤ (e : ℕ) ∧ (e : ℕ) < b) :
    ((List.finRange m).filter (fun e => decide (q e))).map Fin.val = List.range' a (b - a) := by
  have hp1 : List.Pairwise (· ≤ ·)
      (((List.finRange m).filter (fun e => decide (q e))).map Fin.val) :=
    List.Pairwise.map _ (fun _ _ h => le_of_lt h) ((List.pairwise_lt_finRange m).filter _)
  have hp2 : List.Pairwise (· ≤ ·) (List.range' a (b - a)) :=
    (List.pairwise_lt_range' (s := a) (n := b - a)).imp le_of_lt
  refine List.Perm.eq_of_pairwise' hp1 hp2 ?_
  rw [List.perm_ext_iff_of_nodup]
  · intro x
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_range'_1]
    constructor
    · rintro ⟨e, he, rfl⟩; have := (hq e).mp he; omega
    · intro hx; exact ⟨⟨x, by omega⟩, (hq _).mpr (by simp; omega), rfl⟩
  · exact ((List.nodup_finRange m).filter _).map Fin.val_injective
  · exact List.nodup_range'

theorem seg_range {st : State V} {m b : ℕ} (hbm : b ≤ m) (hL : m ≤ st.wlen "gNxt")
    (hnxt : ∀ p, p < b → a ≤ p → st.wa "gNxt" p = if p + 1 = b then m else p + 1) :
    ∀ j p, p + j = b → a ≤ p → Seg st "gNxt" m (if p = b then m else p) (List.range' p j) m := by
  intro j
  induction j with
  | zero => intro p hp _; subst hp; simp only [Nat.add_zero, if_true, List.range'_zero]; exact .nil m
  | succ j ih =>
    intro p hp hap
    have hpb : p ≠ b := by omega
    rw [if_neg hpb, List.range'_succ]
    refine .cons p _ m (by omega) (by omega) ?_
    rw [hnxt p (by omega) hap]
    have := ih (p + 1) (by omega) (by omega)
    by_cases h1 : p + 1 = b
    · rw [if_pos h1]; rw [if_pos h1] at this; exact this
    · rw [if_neg h1]; rw [if_neg h1] at this; exact this

/-- **The initial live out-lists**: L6's CSR layout represents `outL` with no deleted edge. -/
theorem outRep_init {st : State V} {c : FPCtx G s}
    (hHdL : G.n ≤ st.wlen "gHd") (hNxL : G.m ≤ st.wlen "gNxt")
    (hle : ∀ u : Fin G.n, st.wa "gSt" u ≤ st.wa "gSt" (u + 1))
    (hlem : ∀ u : Fin G.n, st.wa "gSt" (u + 1) ≤ G.m)
    (hsrc : ∀ (e : Fin G.m) (u : Fin G.n),
      G.src e = u ↔ st.wa "gSt" u ≤ e ∧ (e : ℕ) < st.wa "gSt" (u + 1))
    (hd : ∀ x : Fin G.n,
      st.wa "gHd" x = if st.wa "gSt" x = st.wa "gSt" (x + 1) then G.m else st.wa "gSt" x)
    (hnxt : ∀ (x : Fin G.n) (p : ℕ), st.wa "gSt" x ≤ p → p < st.wa "gSt" (x + 1) →
      st.wa "gNxt" p = if p + 1 = st.wa "gSt" (x + 1) then G.m else p + 1)
    (hout : ∀ u, c.out u = (List.finRange G.m).filter (fun e => decide (G.src e = u))) :
    OutRep st c ∅ := by
  refine ⟨hHdL, fun w => ?_⟩
  have hL : live c ∅ w = List.range' (st.wa "gSt" w) (st.wa "gSt" (w + 1) - st.wa "gSt" w) := by
    unfold live sl
    rw [hout w]
    have : ((List.finRange G.m).filter (fun e => decide (G.src e = w))).filter
        (fun e => decide (e ∉ (∅ : Finset (Fin G.m)))) =
        (List.finRange G.m).filter (fun e => decide (G.src e = w)) := by
      rw [List.filter_eq_self]; intro e _; simp
    rw [this]
    exact csr_list (hle w) (hlem w) (fun e => G.src e = w) (fun e => hsrc e w)
  rw [hL, hd w]
  have := seg_range (st := st) (a := st.wa "gSt" w) (hlem w) hNxL
    (fun p hp hap => hnxt w p hap hp) (st.wa "gSt" (w + 1) - st.wa "gSt" w) (st.wa "gSt" w)
    (by have := hle w; omega) le_rfl
  by_cases h : st.wa "gSt" w = st.wa "gSt" (w + 1)
  · rw [if_pos h] at this ⊢; exact this
  · rw [if_neg h] at this ⊢; exact this

/-! ## The one-time allocation -/

/-- The FindPivots arrays (name, size register). -/
def fpArrsA : List (String × String) :=
  [("fp.H", "cp.k"), ("fp.hp", "gN"), ("fp.inH", "gN"), ("fp.K", "cp.k"), ("fp.inK", "gN"),
   ("fp.val", "gN"), ("fp.fm", "gN"), ("fp.kp", "gN"), ("fp.inW", "gN"), ("fp.W", "gN"),
   ("fp.Q", "gN")]

/-- **The one-time allocation of FindPivots-HD** (spine prologue, once `gN` and `cp.k` hold `n` and
the cap `k`): agent-03's tree / tail arrays, the FindPivots arrays, and the empty registers. -/
def fpAlloc : Stmt :=
  seq allocFP (seq (allocWs fpArrsA) (seq (wset "fp.hsz" (lit 0)) (seq (wset "fp.kl" (lit 0))
    (seq (wset "fp.k" (var "cp.k")) (wset "fp.ob" (lit 0))))))

/-- Arrays / registers written by `fpAlloc`. -/
def fpAllocWA : List String := (("pt.GV" :: fpArrsN) ++ fpArrsA.map Prod.fst) ++ []
def fpAllocWR : List String := ([] ++ []) ++ ["fp.hsz", "fp.kl", "fp.k", "fp.ob"]

/-- **After `fpAlloc`, the FindPivots state is clean** (`FPClean c d ∅` for every context with cap
`k` whose out-lists are represented), for the first call of the spine. -/
theorem fpAlloc_spec {st : State V} {k : ℕ} (hN : st.w "gN" = G.n) (hk : st.w "cp.k" = k)
    (hgM : st.w "gM" = G.m) (hHL : G.m ≤ st.wlen "gHead")
    (hH : ∀ q : Fin G.m, st.wa "gHead" q = G.dst q) (hcap : 2 * G.n + 2 < st.cap) :
    Runs ops fpAlloc st (fun st' =>
      (∀ (c : FPCtx G s) (d : Labels G s), c.k = k → OutRep st c ∅ → FPClean c d ∅ st') ∧
      Unchanged st st' fpAllocWA [] fpAllocWR [] ∧
      st'.cost = st.cost + 34 * G.n + 2 * k + 41) := by
  unfold fpAlloc
  refine runs_seq ((allocFP_spec (ops := ops) hN (by omega)).mono ?_)
  rintro s1 ⟨hTA1, hPTA1, hA1, hw1, hv1, hva1, hvl1, hcap1, hp1, hc1⟩
  have hu1 : Unchanged st s1 ("pt.GV" :: fpArrsN) [] [] [] :=
    ⟨fun a ha => ⟨(hA1 a ha).2, (hA1 a ha).1⟩, fun a _ => ⟨by rw [hva1], by rw [hvl1]⟩,
      fun x _ => by rw [hw1], fun x _ => by rw [hv1], hcap1, hp1⟩
  refine runs_seq ((allocWs_runs (ops := ops) fpArrsA (by decide) s1).mono ?_)
  rintro s2 ⟨hA2, hu2, hc2⟩
  have hcap2 : s2.cap = st.cap := by rw [hu2.cap, hcap1]
  have hw2 : ∀ x, s2.w x = st.w x := fun x => by rw [hu2.wreg x (by simp), hw1]
  have hL : ∀ p ∈ fpArrsA, s2.wlen p.1 = st.w p.2 ∧ ∀ i, s2.wa p.1 i = 0 := fun p hp => by
    rw [← hw1]; exact hA2 p hp
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
  refine runs_seq (runs_wset (a := k) (by simp [hw2, hk]) ?_)
  refine runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_
  generalize hs3 : ((((((((s2.setW "fp.hsz" 0).charge 1).setW "fp.kl" 0).charge 1).setW "fp.k"
    k).charge 1).setW "fp.ob" 0).charge 1) = s3
  have hu3 : Unchanged s2 s3 [] [] ["fp.hsz", "fp.kl", "fp.k", "fp.ob"] [] := by
    rw [← hs3]
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
    simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]
  have hwa3 : s3.wa = s2.wa := by rw [← hs3]; rfl
  have hwl3 : s3.wlen = s2.wlen := by rw [← hs3]; rfl
  have hhsz : s3.w "fp.hsz" = 0 := by rw [← hs3]; simp
  have hkl : s3.w "fp.kl" = 0 := by rw [← hs3]; simp
  have hkk : s3.w "fp.k" = k := by rw [← hs3]; simp
  have hob : s3.w "fp.ob" = 0 := by rw [← hs3]; simp
  have hgM3 : s3.w "gM" = G.m := by rw [hu3.wreg _ (by decide), hw2]; exact hgM
  -- the allocated arrays
  have zlen : ∀ a r, (a, r) ∈ fpArrsA → s3.wlen a = st.w r ∧ ∀ i, s3.wa a i = 0 :=
    fun a r h => by rw [hwl3, hwa3]; exact hL (a, r) h
  have hZ : ∀ a, (a, "gN") ∈ fpArrsA → Bits (G := G) s3 a ∅ := fun a h => by
    obtain ⟨h1, h2⟩ := zlen a "gN" h
    exact ⟨by rw [h1, hN], fun v => by rw [h2]; simp⟩
  -- arrays not allocated here
  have hkeep : ∀ a, a ∉ "pt.GV" :: fpArrsN → a ∉ fpArrsA.map Prod.fst →
      s3.wa a = st.wa a ∧ s3.wlen a = st.wlen a := fun a h1 h2 => by
    rw [hwa3, hwl3, (hu2.warr a h2).1, (hu2.warr a h2).2]; exact ⟨(hA1 a h1).2, (hA1 a h1).1⟩
  have hHead := hkeep "gHead" (by decide) (by decide)
  refine ⟨fun c d hck hO => ?_, (hu1.cat hu2).cat hu3, ?_⟩
  · have hHd := hkeep "gHd" (by decide) (by decide)
    have hNx := hkeep "gNxt" (by decide) (by decide)
    have hfr : ∀ a ∈ frWA0, s3.wa a = s1.wa a ∧ s3.wlen a = s1.wlen a := fun a ha => by
      rw [hwa3, hwl3]
      exact hu2.warr a (fun h => by revert h; revert ha; revert a; decide)
    have hpt : ∀ a ∈ ptaArrs, s3.wa a = s1.wa a ∧ s3.wlen a = s1.wlen a := fun a ha => by
      rw [hwa3, hwl3]
      exact hu2.warr a (fun h => by revert h; revert ha; revert a; decide)
    refine ⟨⟨hgM3, by rw [hHead.2]; exact hHL, fun q => by rw [hHead.1]; exact hH q,
      ⟨[], List.nodup_nil, rfl, by rw [hhsz]; rfl, by rw [(zlen "fp.H" "cp.k" (by decide)).1, hk, hck],
        fun i h => absurd h (by simp), by rw [(zlen "fp.hp" "gN" (by decide)).1, hN],
        fun i h => absurd h (by simp), hZ "fp.inH" (by decide)⟩,
      by rw [hkl]; rfl, by rw [(zlen "fp.K" "cp.k" (by decide)).1, hk, hck],
      fun i h => absurd h (by simp [emptySt]),
      by have := hZ "fp.inK" (by decide); simpa [emptySt] using this,
      hZ "fp.val" (by decide), hZ "fp.fm" (by decide), by rw [(zlen "fp.kp" "gN" (by decide)).1, hN],
      fun v hv => absurd hv (by simp [emptySt]), by rw [hkk, hck], List.nodup_nil,
      by simp [emptySt]⟩,
      ⟨by rw [hHd.2]; exact hO.1, fun w => by rw [hHd.1]; exact (hO.2 w).of_eq hNx.1 hNx.2⟩,
      TA0.frame hTA1 hfr, hPTA1.frame hpt, hZ "fp.inW" (by decide),
      by rw [hob, (zlen "fp.W" "gN" (by decide)).1, hN]; omega,
      by rw [hob, (zlen "fp.Q" "gN" (by decide)).1, hN]; omega, hob⟩
  · have : allocCost s1 fpArrsA = 2 * k + 9 * G.n + 12 := by
      simp [allocCost, fpArrsA, hw1, hN, hk]; ring
    rw [← hs3]; simp only [State.charge_cost, State.setW_cost]
    rw [hc2, hc1, this]; ring

end Frontier.CHD.BL2
