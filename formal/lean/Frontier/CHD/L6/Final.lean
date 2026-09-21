import Frontier.CHD.L6.Sort
import Frontier.CHD.L6.SortedRelKey
import Frontier.CHD.Preprocess
import Frontier.CHD.RamBaseCase

/-!
# L6 structural theorem (agent-10, scratch): the reduced graph `H` read from the final state

After pass B (state `t0`, `BPost`) and the sort pass (state `t`, `SPInv` at `N`):
* every slot `e < M` lies in exactly one range `[gSt x, gSt (x+1))`, `x < N`, and `gSrc[e] = x`;
* the pair `(gW[e], gHead[e])` of a post-sort slot is a pre-sort pair of the same range, and
  conversely; pre-sort pairs are chain edges `(0, x+1)` or kept edges `(w e_i, off (dst e_i))`.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Finset
open Frontier.CHD.MergeSort (srcFn segL keyLe)

section Ranges

variable {I : L6In} {st t0 t : State ℝ≥0} (hB : BPost I st t0) (hS : SPInv I t0 (I.off I.n) t)
  (hδ : 3 ≤ I.δ)

include hB hδ in
theorem st0_zero : t0.wa "gSt" 0 = 0 := by
  have := st_off hB.F hB.stN 0 (Nat.zero_le _); simpa [L6In.off, L6In.sl] using this

include hB hδ in
/-- Every slot lies in some range. -/
theorem slot_cover {e : ℕ} (he : e < I.sl I.n) :
    ∃ x < I.off I.n, t0.wa "gSt" x ≤ e ∧ e < t0.wa "gSt" (x + 1) := by
  have hN := hB.stN
  have h0 := st0_zero hB hδ
  -- the least index whose start exceeds `e`
  have hex : ∃ y, e < t0.wa "gSt" y ∧ y ≤ I.off I.n := ⟨I.off I.n, by rw [hN]; exact he, le_rfl⟩
  classical
  let y := Nat.find hex
  have hy : e < t0.wa "gSt" y ∧ y ≤ I.off I.n := Nat.find_spec hex
  have hy0 : y ≠ 0 := by
    intro h0'; have := hy.1; rw [h0', h0] at this; omega
  refine ⟨y - 1, by omega, ?_, by rw [Nat.sub_add_cancel (by omega)]; exact hy.1⟩
  by_contra hlt
  push_neg at hlt
  have := Nat.find_min hex (show y - 1 < y by omega)
  exact this ⟨hlt, by omega⟩

include hB hδ in
theorem range_unique {e x x' : ℕ} (hx : x < I.off I.n) (hx' : x' < I.off I.n)
    (h : t0.wa "gSt" x ≤ e ∧ e < t0.wa "gSt" (x + 1))
    (h' : t0.wa "gSt" x' ≤ e ∧ e < t0.wa "gSt" (x' + 1)) : x = x' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := st_mono hB.F hB.stN hδ (show x + 1 ≤ x' by omega) (by omega); omega
  · have := st_mono hB.F hB.stN hδ (show x' + 1 ≤ x by omega) (by omega); omega

theorem mem_rangeL {t0 t : State ℝ≥0} {x : ℕ} {a : ℝ≥0 × ℕ} :
    a ∈ rangeL t0 t x ↔ ∃ o < t0.wa "gSt" (x + 1) - t0.wa "gSt" x,
      a = (t.va "gW" (t0.wa "gSt" x + o), t.wa "gHead" (t0.wa "gSt" x + o)) := by
  unfold rangeL segL
  simp only [List.mem_map, List.mem_range, srcFn]
  constructor
  · rintro ⟨o, ho, rfl⟩; exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩; exact ⟨o, ho, rfl⟩

include hB hS hδ in
/-- A post-sort pair is a pre-sort pair of the same range. -/
theorem post_pre {x e : ℕ} (hx : x < I.off I.n) (he : t0.wa "gSt" x ≤ e ∧ e < t0.wa "gSt" (x + 1)) :
    ∃ o < t0.wa "gSt" (x + 1) - t0.wa "gSt" x,
      (t.va "gW" e, t.wa "gHead" e) = (t0.va "gW" (t0.wa "gSt" x + o), t0.wa "gHead" (t0.wa "gSt" x + o)) := by
  have hm : (t.va "gW" e, t.wa "gHead" e) ∈ rangeL t0 t x :=
    mem_rangeL.mpr ⟨e - t0.wa "gSt" x, by omega, by rw [Nat.add_sub_cancel' he.1]⟩
  exact mem_rangeL.mp ((hS.sorted x hx).2.subset hm)

include hB hS hδ in
/-- A pre-sort pair appears at some post-sort slot of the same range. -/
theorem pre_post {x o : ℕ} (hx : x < I.off I.n) (ho : o < t0.wa "gSt" (x + 1) - t0.wa "gSt" x) :
    ∃ e, (t0.wa "gSt" x ≤ e ∧ e < t0.wa "gSt" (x + 1)) ∧
      (t.va "gW" e, t.wa "gHead" e) = (t0.va "gW" (t0.wa "gSt" x + o), t0.wa "gHead" (t0.wa "gSt" x + o)) := by
  have hm : (t0.va "gW" (t0.wa "gSt" x + o), t0.wa "gHead" (t0.wa "gSt" x + o)) ∈ rangeL t0 t0 x :=
    mem_rangeL.mpr ⟨o, ho, rfl⟩
  obtain ⟨o', ho', h⟩ := mem_rangeL.mp ((hS.sorted x hx).2.symm.subset hm)
  exact ⟨t0.wa "gSt" x + o', ⟨by omega, by omega⟩, h.symm⟩

end Ranges

/-! ## Pre-sort slot contents (from `VFacts`) -/

theorem slotR_eq {I : L6In} {v q o : ℕ} (hδ : 3 ≤ I.δ) (ho : o < I.δ - 1) :
    slotR I v (q * (I.δ - 1) + o) = I.sl v + q * I.δ + o := by
  unfold slotR
  have hd : 0 < I.δ - 1 := by omega
  have h1 : (q * (I.δ - 1) + o) / (I.δ - 1) = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt ho, zero_add]
  have h2 : (q * (I.δ - 1) + o) % (I.δ - 1) = o := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
  rw [h1, h2]

/-- Each pre-sort slot of chunk `q` of kept `v` holds a chain edge or a kept edge. -/
theorem pre_content {I : L6In} {r : State ℝ≥0} (hδ : 3 ≤ I.δ) {v q o : ℕ} (hF : VFacts I v r)
    (hk : I.keep v ≠ 0) (hq : q < I.cc v) (ho : o < I.lenF v q) :
    (q + 1 < I.cc v ∧ o = I.δ - 1 ∧ r.wa "gHead" (I.sl v + q * I.δ + o) = I.off v + q + 1 ∧
      r.va "gW" (I.sl v + q * I.δ + o) = 0) ∨
    (∃ i < I.deg v, slotR I v i = I.sl v + q * I.δ + o ∧
      r.wa "gHead" (I.sl v + q * I.δ + o) = I.off (I.dst ((I.KL v).getD i 0)) ∧
      r.va "gW" (I.sl v + q * I.δ + o) = I.wt ((I.KL v).getD i 0)) := by
  by_cases hc : q + 1 < I.cc v ∧ o = I.δ - 1
  · left
    obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨h1, h2⟩ := hF.chain q hc1
    subst hc2
    exact ⟨hc1, rfl, h1, h2⟩
  · right
    have hle := L6In.deg_le_cc hk hδ
    have hp := L6In.cc_pred_le hk hδ
    have ho' : o < I.δ - 1 := by
      by_cases hmid : q + 1 < I.cc v
      · rw [L6In.lenF_mid hmid] at ho
        have : o ≠ I.δ - 1 := fun h => hc ⟨hmid, h⟩
        omega
      · rw [L6In.lenF_last hmid] at ho
        have hq' : q = I.cc v - 1 := by omega
        subst hq'
        have h2 := mul_pred_add (I.cc v - 1) (I.δ - 1 + 1) (by omega)
        have h3 : I.cc v * (I.δ - 1) = (I.cc v - 1) * (I.δ - 1) + (I.δ - 1) := by
          have : I.cc v = (I.cc v - 1) + 1 := by have := L6In.cc_pos hk; omega
          conv_lhs => rw [this]
          ring
        omega
    have hi : q * (I.δ - 1) + o < I.deg v := by
      by_cases hmid : q + 1 < I.cc v
      · have h1 : (q + 1) * (I.δ - 1) ≤ (I.cc v - 1) * (I.δ - 1) := Nat.mul_le_mul_right _ (by omega)
        have h2 : (q + 1) * (I.δ - 1) = q * (I.δ - 1) + (I.δ - 1) := by ring
        omega
      · rw [L6In.lenF_last hmid] at ho; omega
    refine ⟨q * (I.δ - 1) + o, hi, slotR_eq hδ ho', ?_⟩
    have := hF.real _ hi
    rw [slotR_eq hδ ho'] at this
    exact this

/-! ## Kept edges -/

namespace L6In

variable {I : L6In}

theorem KL_mem {v i : ℕ} (hk : I.keep v ≠ 0) (hi : i < I.deg v) : (I.KL v).getD i 0 ∈ I.KL v := by
  rw [List.getD_eq_getElem _ _ (by rw [I.KL_length hk]; exact hi)]; exact List.getElem_mem _

theorem KL_grp {v e : ℕ} (he : e ∈ I.KL v) : e ∈ I.grp v ∧ I.kept v e := by
  simp only [KL, List.mem_filter, decide_eq_true_eq] at he; exact he

/-- A kept edge of `v` leaves `v`, is not a loop, and its head is kept. -/
theorem kept_edge {v e : ℕ} (he : e ∈ I.KL v) :
    e < I.m ∧ I.src e = v ∧ I.dst e ≠ v ∧ I.keep (I.dst e) ≠ 0 := by
  obtain ⟨hg, hkp⟩ := KL_grp he
  obtain ⟨hem, hs⟩ := I.mem_grp.mp hg
  refine ⟨hem, hs, hkp.1, ?_⟩
  have : I.keep (I.dst e) = 1 :=
    (keepF_eq_one I.src I.dst I.m I.s (I.dst e)).mpr (Or.inr ⟨e, hem, rfl, by rw [hs]; exact Ne.symm hkp.1⟩)
  omega

theorem off_lt_of_keep {v : ℕ} (hv : v < I.n) (hk : I.keep v ≠ 0) : I.off v < I.off I.n := by
  have h1 := off_mono I (show v + 1 ≤ I.n by omega)
  have h2 := cc_pos hk
  rw [I.off_succ] at h1; omega

end L6In

section Bounds

variable {I : L6In} {st t0 t : State ℝ≥0} (hB : BPost I st t0) (hS : SPInv I t0 (I.off I.n) t)
  (hδ : 3 ≤ I.δ)

include hB hδ in
/-- Pre-sort source of every slot of range `x`. -/
theorem src_pre {x e : ℕ} (hx : x < I.off I.n) (he : t0.wa "gSt" x ≤ e ∧ e < t0.wa "gSt" (x + 1)) :
    t0.wa "gSrc" e = x := by
  obtain ⟨v, hv, hk, q, hq, hxq, ha, hb⟩ := st_range_any hB.F hB.stN hδ hx
  have := (hB.F v hv hk).src q hq (e - t0.wa "gSt" x) (by omega)
  rw [show I.sl v + q * I.δ + (e - t0.wa "gSt" x) = e by omega] at this
  rw [this, hxq]

include hS in
theorem sort_frame_wa {a : String} (ha : a ∉ ["gHead", "ms_H"]) : t.wa a = t0.wa a :=
  (hS.U.warr a ha).1

include hB hS hδ in
theorem src_post_lt {e : ℕ} (he : e < I.sl I.n) : t.wa "gSrc" e < I.off I.n := by
  obtain ⟨x, hx, hr⟩ := slot_cover hB hδ he
  rw [sort_frame_wa hS (by simp), src_pre hB hδ hx hr]; exact hx

include hB hS hδ in
theorem head_post_lt {e : ℕ} (he : e < I.sl I.n) : t.wa "gHead" e < I.off I.n := by
  obtain ⟨x, hx, hr⟩ := slot_cover hB hδ he
  obtain ⟨o, ho, hpair⟩ := post_pre hB hS hδ hx hr
  have hh : t.wa "gHead" e = t0.wa "gHead" (t0.wa "gSt" x + o) := (Prod.mk.inj hpair).2
  obtain ⟨v, hv, hk, q, hq, hxq, ha, hb⟩ := st_range_any hB.F hB.stN hδ hx
  have ho' : o < I.lenF v q := by omega
  rw [hh, ha]
  rcases pre_content hδ (hB.F v hv hk) hk hq ho' with ⟨hc, -, h1, -⟩ | ⟨i, hi, -, h1, -⟩
  · rw [h1]
    have := off_mono I (show v + 1 ≤ I.n by omega)
    rw [I.off_succ] at this; omega
  · rw [h1]
    obtain ⟨hem, -, -, hkd⟩ := L6In.kept_edge (L6In.KL_mem hk hi)
    exact L6In.off_lt_of_keep (hB.E.A.hdst _ hem) hkd

end Bounds

/-! ## Post-sort facts in ℕ-terms -/

section Post

variable {I : L6In} {st t0 t : State ℝ≥0} (hB : BPost I st t0) (hS : SPInv I t0 (I.off I.n) t)
  (hδ : 3 ≤ I.δ)

include hB hS in
theorem own_post {v q : ℕ} (hv : v < I.n) (hk : I.keep v ≠ 0) (hq : q < I.cc v) :
    t.wa "gOwn" (I.off v + q) = v := by
  rw [sort_frame_wa hS (by simp)]; exact (hB.F v hv hk).own q hq

include hB hS hδ in
theorem src_post {x e : ℕ} (hx : x < I.off I.n) (he : t0.wa "gSt" x ≤ e ∧ e < t0.wa "gSt" (x + 1)) :
    t.wa "gSrc" e = x := by
  rw [sort_frame_wa hS (by simp)]; exact src_pre hB hδ hx he

include hB hS hδ in
/-- Classification of a post-sort slot of chunk `q` of kept `v`. -/
theorem edge_post {v q e : ℕ} (hv : v < I.n) (hk : I.keep v ≠ 0) (hq : q < I.cc v)
    (he : t0.wa "gSt" (I.off v + q) ≤ e ∧ e < t0.wa "gSt" (I.off v + q + 1)) :
    (q + 1 < I.cc v ∧ t.wa "gHead" e = I.off v + q + 1 ∧ t.va "gW" e = 0) ∨
    (∃ i < I.deg v, t.wa "gHead" e = I.off (I.dst ((I.KL v).getD i 0)) ∧
      t.va "gW" e = I.wt ((I.KL v).getD i 0)) := by
  have hx : I.off v + q < I.off I.n := by
    have := off_mono I (show v + 1 ≤ I.n by omega); rw [I.off_succ] at this; omega
  obtain ⟨o, ho, hpair⟩ := post_pre hB hS hδ hx he
  obtain ⟨ha, hb⟩ := st_range hB.F hB.stN hδ hv hk hq
  have ho' : o < I.lenF v q := by omega
  have h1 : t.wa "gHead" e = t0.wa "gHead" (t0.wa "gSt" (I.off v + q) + o) := (Prod.mk.inj hpair).2
  have h2 : t.va "gW" e = t0.va "gW" (t0.wa "gSt" (I.off v + q) + o) := (Prod.mk.inj hpair).1
  rw [ha] at h1 h2
  rcases pre_content hδ (hB.F v hv hk) hk hq ho' with ⟨hc, -, g1, g2⟩ | ⟨i, hi, -, g1, g2⟩
  · exact Or.inl ⟨hc, h1.trans g1, h2.trans g2⟩
  · exact Or.inr ⟨i, hi, h1.trans g1, h2.trans g2⟩

include hB hS hδ in
/-- Every kept edge has a post-sort copy in its chunk. -/
theorem copy_post {u i : ℕ} (hu : u < I.n) (hk : I.keep u ≠ 0) (hi : i < I.deg u) :
    ∃ e, e < I.sl I.n ∧ t.wa "gSrc" e = I.off u + i / (I.δ - 1) ∧
      t.wa "gHead" e = I.off (I.dst ((I.KL u).getD i 0)) ∧ t.va "gW" e = I.wt ((I.KL u).getD i 0) := by
  set q := i / (I.δ - 1) with hqdef
  set o := i % (I.δ - 1) with hodef
  have hd : 0 < I.δ - 1 := by omega
  have hle := L6In.deg_le_cc hk hδ
  have hio : q * (I.δ - 1) + o = i := by rw [hqdef, hodef, Nat.mul_comm]; exact Nat.div_add_mod i _
  have hoδ : o < I.δ - 1 := Nat.mod_lt _ hd
  have hq : q < I.cc u := by rw [hqdef, Nat.div_lt_iff_lt_mul hd]; omega
  have ho : o < I.lenF u q := by
    by_cases hmid : q + 1 < I.cc u
    · rw [L6In.lenF_mid hmid]; omega
    · rw [L6In.lenF_last hmid]; omega
  have hx : I.off u + q < I.off I.n := by
    have := off_mono I (show u + 1 ≤ I.n by omega); rw [I.off_succ] at this; omega
  obtain ⟨ha, hb⟩ := st_range hB.F hB.stN hδ hu hk hq
  obtain ⟨e, he, hpair⟩ := pre_post hB hS hδ hx (show o < t0.wa "gSt" (I.off u + q + 1) - t0.wa "gSt" (I.off u + q) by omega)
  have hreal := (hB.F u hu hk).real i hi
  have hslot : slotR I u i = t0.wa "gSt" (I.off u + q) + o := by
    rw [ha]; unfold slotR; rw [← hqdef, ← hodef]
  rw [hslot] at hreal
  have hM : t0.wa "gSt" (I.off u + q + 1) ≤ I.sl I.n := st_le_M hB.F hB.stN hδ (by omega)
  refine ⟨e, by omega, src_post hB hS hδ hx he, ?_, ?_⟩
  · rw [(Prod.mk.inj hpair).2]; exact hreal.1
  · rw [(Prod.mk.inj hpair).1]; exact hreal.2

include hB hS hδ in
/-- Every chain edge has a post-sort copy in its chunk. -/
theorem chain_post {v q : ℕ} (hv : v < I.n) (hk : I.keep v ≠ 0) (hq : q + 1 < I.cc v) :
    ∃ e, e < I.sl I.n ∧ t.wa "gSrc" e = I.off v + q ∧ t.wa "gHead" e = I.off v + q + 1 ∧
      t.va "gW" e = 0 := by
  have hx : I.off v + q < I.off I.n := by
    have := off_mono I (show v + 1 ≤ I.n by omega); rw [I.off_succ] at this; omega
  obtain ⟨ha, hb⟩ := st_range hB.F hB.stN hδ hv hk (show q < I.cc v by omega)
  have hlen := L6In.lenF_mid hq
  obtain ⟨e, he, hpair⟩ := pre_post hB hS hδ hx
    (show I.δ - 1 < t0.wa "gSt" (I.off v + q + 1) - t0.wa "gSt" (I.off v + q) by omega)
  have hch := (hB.F v hv hk).chain q hq
  rw [← ha] at hch
  have hM : t0.wa "gSt" (I.off v + q + 1) ≤ I.sl I.n := st_le_M hB.F hB.stN hδ (by omega)
  refine ⟨e, by omega, src_post hB hS hδ hx he, ?_, ?_⟩
  · rw [(Prod.mk.inj hpair).2]; exact hch.1
  · rw [(Prod.mk.inj hpair).1]; exact hch.2

end Post

/-- The graph `H` given by total functions with bound proofs. -/
def mkH (N M : ℕ) (src dst : ℕ → ℕ) (w : ℕ → ℝ≥0) (hs : ∀ e < M, src e < N)
    (hd : ∀ e < M, dst e < N) : Graph where
  n := N
  m := M
  src e := ⟨src e, hs e e.2⟩
  dst e := ⟨dst e, hd e e.2⟩
  w e := w e

/-! ## Sortedness and distinct heads per range -/

namespace L6In

variable {I : L6In}

theorem off_inj_keep {w1 w2 : ℕ} (hk1 : I.keep w1 ≠ 0) (hk2 : I.keep w2 ≠ 0)
    (h : I.off w1 = I.off w2) : w1 = w2 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := off_mono I (show w1 + 1 ≤ w2 by omega)
    rw [I.off_succ] at h1; have := cc_pos hk1; omega
  · have h1 := off_mono I (show w2 + 1 ≤ w1 by omega)
    rw [I.off_succ] at h1; have := cc_pos hk2; omega

theorem grp_nodup (u : ℕ) : (I.grp u).Nodup := List.Nodup.filter _ (List.nodup_range)

theorem KL_nodup (v : ℕ) : (I.KL v).Nodup := List.Nodup.filter _ (grp_nodup v)

/-- Kept edges of `v` have distinct heads. -/
theorem KL_dst_inj {v e1 e2 : ℕ} (h1 : e1 ∈ I.KL v) (h2 : e2 ∈ I.KL v) (hd : I.dst e1 = I.dst e2) :
    e1 = e2 := by
  obtain ⟨-, hk1⟩ := KL_grp h1
  obtain ⟨-, hk2⟩ := KL_grp h2
  have a := hk1.2
  have b := hk2.2
  rw [hd] at a
  rw [a] at b
  exact Option.some_injective _ b

/-- Distinct indices of the kept list give distinct heads. -/
theorem KL_head_ne {v i1 i2 : ℕ} (hk : I.keep v ≠ 0) (hi1 : i1 < I.deg v) (hi2 : i2 < I.deg v)
    (hne : i1 ≠ i2) : I.off (I.dst ((I.KL v).getD i1 0)) ≠ I.off (I.dst ((I.KL v).getD i2 0)) := by
  intro h
  obtain ⟨-, -, -, hk1⟩ := kept_edge (KL_mem hk hi1)
  obtain ⟨-, -, -, hk2⟩ := kept_edge (KL_mem hk hi2)
  have hd := off_inj_keep hk1 hk2 h
  have he := KL_dst_inj (KL_mem hk hi1) (KL_mem hk hi2) hd
  have hl : i1 < (I.KL v).length := by rw [I.KL_length hk]; exact hi1
  have hl2 : i2 < (I.KL v).length := by rw [I.KL_length hk]; exact hi2
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl2] at he
  exact hne ((List.Nodup.getElem_inj_iff (KL_nodup v)).mp he)

/-- A kept head is never the chain head `off v + q + 1` of another vertex's inner chunk. -/
theorem kept_head_ne_chain {v w q : ℕ} (hkw : I.keep w ≠ 0) (hwv : w ≠ v)
    (hq : q + 1 < I.cc v) : I.off w ≠ I.off v + q + 1 := by
  intro h
  rcases Nat.lt_or_gt_of_ne hwv with hlt | hlt
  · have h1 := off_mono I (show w + 1 ≤ v by omega)
    rw [I.off_succ] at h1; have := cc_pos hkw; omega
  · have h1 := off_mono I (show v + 1 ≤ w by omega)
    rw [I.off_succ] at h1; omega

end L6In

section Heads

variable {I : L6In} {st t0 t : State ℝ≥0} (hB : BPost I st t0) (hS : SPInv I t0 (I.off I.n) t)
  (hδ : 3 ≤ I.δ)

include hB hδ in
/-- Pre-sort heads within one range are pairwise distinct. -/
theorem pre_heads_ne {x o1 o2 : ℕ} (hx : x < I.off I.n)
    (ho1 : o1 < t0.wa "gSt" (x + 1) - t0.wa "gSt" x) (ho2 : o2 < t0.wa "gSt" (x + 1) - t0.wa "gSt" x)
    (hne : o1 ≠ o2) :
    t0.wa "gHead" (t0.wa "gSt" x + o1) ≠ t0.wa "gHead" (t0.wa "gSt" x + o2) := by
  obtain ⟨v, hv, hk, q, hq, hxq, ha, hb⟩ := st_range_any hB.F hB.stN hδ hx
  have ho1' : o1 < I.lenF v q := by omega
  have ho2' : o2 < I.lenF v q := by omega
  rw [ha]
  rcases pre_content hδ (hB.F v hv hk) hk hq ho1' with ⟨hc1, he1, h1, -⟩ | ⟨i1, hi1, hs1, h1, -⟩ <;>
  rcases pre_content hδ (hB.F v hv hk) hk hq ho2' with ⟨hc2, he2, h2, -⟩ | ⟨i2, hi2, hs2, h2, -⟩
  · exact absurd (he1.trans he2.symm) hne
  · rw [h1, h2]
    obtain ⟨hem, hes, hed, hkd⟩ := L6In.kept_edge (L6In.KL_mem hk hi2)
    exact (L6In.kept_head_ne_chain hkd hed hc1).symm
  · rw [h1, h2]
    obtain ⟨hem, hes, hed, hkd⟩ := L6In.kept_edge (L6In.KL_mem hk hi1)
    exact L6In.kept_head_ne_chain hkd hed hc2
  · rw [h1, h2]
    apply L6In.KL_head_ne hk hi1 hi2
    intro h; subst h
    rw [hs1] at hs2; exact hne (by omega)

include hB hS hδ in
/-- Post-sort heads within one range are pairwise distinct. -/
theorem post_heads_ne {x e1 e2 : ℕ} (hx : x < I.off I.n)
    (h1 : t0.wa "gSt" x ≤ e1 ∧ e1 < t0.wa "gSt" (x + 1))
    (h2 : t0.wa "gSt" x ≤ e2 ∧ e2 < t0.wa "gSt" (x + 1)) (hne : e1 ≠ e2) :
    t.wa "gHead" e1 ≠ t.wa "gHead" e2 := by
  set a := t0.wa "gSt" x
  set len := t0.wa "gSt" (x + 1) - t0.wa "gSt" x
  have hpre : ((rangeL t0 t0 x).map Prod.snd).Nodup := by
    unfold rangeL segL
    rw [List.map_map, List.nodup_map_iff_inj_on (List.nodup_range)]
    intro o1 ho1 o2 ho2 heq
    simp only [List.mem_range] at ho1 ho2
    by_contra hne'
    exact pre_heads_ne hB hδ hx ho1 ho2 hne' heq
  have hpost : ((rangeL t0 t x).map Prod.snd).Nodup :=
    ((hS.sorted x hx).2.map Prod.snd).nodup_iff.mpr hpre
  unfold rangeL segL at hpost
  rw [List.map_map, List.nodup_map_iff_inj_on (List.nodup_range)] at hpost
  intro heq
  have := hpost (e1 - a) (by simp; omega) (e2 - a) (by simp; omega)
    (by simp only [Function.comp, srcFn]; rw [Nat.add_sub_cancel' h1.1, Nat.add_sub_cancel' h2.1]; exact heq)
  omega

include hS in
/-- Post-sort slots of one range are in `keyLe` order. -/
theorem post_keyLe {x e1 e2 : ℕ} (hx : x < I.off I.n)
    (h1 : t0.wa "gSt" x ≤ e1) (h12 : e1 < e2) (h2 : e2 < t0.wa "gSt" (x + 1)) :
    keyLe realOps.le (t.va "gW" e1, t.wa "gHead" e1) (t.va "gW" e2, t.wa "gHead" e2) = true := by
  have hs := (hS.sorted x hx).1
  unfold rangeL segL at hs
  rw [List.pairwise_map] at hs
  have := List.pairwise_iff_getElem.mp hs (e1 - t0.wa "gSt" x) (e2 - t0.wa "gSt" x)
    (by simp; omega) (by simp; omega) (by omega)
  simp only [List.getElem_range, srcFn] at this
  rwa [Nat.add_sub_cancel' h1, Nat.add_sub_cancel' (by omega : t0.wa "gSt" x ≤ e2)] at this

end Heads

/-! ## The reduced graph and its keep-set reduction -/

section Red

variable {G : Graph} {s : Fin G.n} {I : L6In} {st t0 t : State ℝ≥0}
  (hB : BPost I st t0) (hS : SPInv I t0 (I.off I.n) t) (hδ : 3 ≤ I.δ)
  (hn : I.n = G.n) (hm : I.m = G.m) (hs : I.s = s)
  (hsrc : ∀ e : Fin G.m, I.src e = G.src e) (hdst : ∀ e : Fin G.m, I.dst e = G.dst e)
  (hw : ∀ e : Fin G.m, I.wt e = G.w e)

/-- The reduced graph read from the final state. -/
noncomputable def Hgr : Graph :=
  mkH (I.off I.n) (I.sl I.n) (t.wa "gSrc") (t.wa "gHead") (t.va "gW")
    (fun _ he => src_post_lt hB hS hδ he) (fun _ he => head_post_lt hB hS hδ he)

theorem N_pos (hsn : I.s < I.n) : 0 < I.off I.n :=
  lt_of_le_of_lt (Nat.zero_le _) (L6In.off_lt_of_keep hsn (keep_s I))

include hB hS hδ in
/-- Owner of every virtual vertex (`gOwn`), with its chunk. -/
theorem owner {x : ℕ} (hx : x < I.off I.n) :
    ∃ v < I.n, I.keep v ≠ 0 ∧ ∃ q < I.cc v, x = I.off v + q ∧ t.wa "gOwn" x = v := by
  obtain ⟨v, hv, hk, h1, h2⟩ := L6In.cover I.n x hx
  refine ⟨v, hv, hk, x - I.off v, by omega, by omega, ?_⟩
  have := own_post hB hS hv hk (show x - I.off v < I.cc v by omega)
  rwa [show I.off v + (x - I.off v) = x by omega] at this

include hB hS hδ in
theorem own_lt {x : ℕ} (hx : x < I.off I.n) : t.wa "gOwn" x < I.n := by
  obtain ⟨v, hv, -, q, -, -, h⟩ := owner hB hS hδ hx
  rw [h]; exact hv

/-- The keep-set reduction of `G` realized by the final state. -/
noncomputable def kred (hsn : I.s < I.n) : KReduction G (Hgr hB hS hδ) s where
  keep v := I.keep v ≠ 0
  keep_s := by rw [← hs]; exact keep_s I
  keep_dst e hne := by
    have h1 : I.keep (G.dst e) = 1 := by
      apply (keepF_eq_one I.src I.dst I.m I.s (G.dst e)).mpr
      right
      refine ⟨e, by rw [hm]; exact e.2, by rw [hdst], ?_⟩
      rw [hsrc]; intro h; exact hne (Fin.ext h)
    show I.keep (G.dst e) ≠ 0
    omega
  proj x := ⟨t.wa "gOwn" x, by rw [← hn]; exact own_lt hB hS hδ x.2⟩
  rep v := ⟨if I.off v < I.off I.n then I.off v else 0, by
    split_ifs with h
    · exact h
    · exact N_pos hsn⟩
  proj_rep v hv := by
    have hvn : (v : ℕ) < I.n := by rw [hn]; exact v.2
    apply Fin.ext
    simp only [L6In.off_lt_of_keep hvn hv, if_true]
    have := own_post hB hS hvn hv (L6In.cc_pos hv)
    simpa using this
  proj_keep x := by
    obtain ⟨v, -, hk, q, -, -, h⟩ := owner hB hS hδ x.2
    show I.keep (t.wa "gOwn" x) ≠ 0
    rw [h]; exact hk
  copy_of e hne hk := by
    have hun : (G.src e : ℕ) < I.n := by rw [hn]; exact (G.src e).2
    have hk' : I.keep (G.src e) ≠ 0 := hk
    have heg : (e : ℕ) ∈ I.grp (G.src e) := I.mem_grp.mpr ⟨by rw [hm]; exact e.2, by rw [hsrc]⟩
    have hdu : I.dst e ≠ (G.src e : ℕ) := by
      rw [hdst]; intro h; exact hne (Fin.ext h.symm)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
      (bst_isSome (dst := I.dst) (wt := I.wt) (u := (G.src e : ℕ)) heg hdu)
    have hbs := bst_some hb
    have hbKL : b ∈ I.KL (G.src e) := by
      simp only [L6In.KL, List.mem_filter, decide_eq_true_eq]
      refine ⟨hbs.1, ?_, ?_⟩
      · rw [hbs.2.1]; exact hdu
      · rw [hbs.2.1]; exact hb
    obtain ⟨i, hi, hib⟩ := List.getElem_of_mem hbKL
    have hideg : i < I.deg (G.src e) := by rw [← I.KL_length hk']; exact hi
    have hgetD : (I.KL (G.src e)).getD i 0 = b := by rw [List.getD_eq_getElem _ _ hi]; exact hib
    have hq : i / (I.δ - 1) < I.cc (G.src e) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := L6In.deg_le_cc hk' hδ; omega
    obtain ⟨f, hfM, hfs, hfh, hfw⟩ := copy_post hB hS hδ hun hk' hideg
    rw [hgetD] at hfh hfw
    obtain ⟨hbm, -, -, hkd⟩ := L6In.kept_edge hbKL
    have hdn : I.dst b < I.n := hB.E.A.hdst b hbm
    refine ⟨⟨f, hfM⟩, ?_, ?_, ?_⟩
    · apply Fin.ext
      show t.wa "gOwn" (t.wa "gSrc" f) = (G.src e : ℕ)
      rw [hfs]; exact own_post hB hS hun hk' hq
    · apply Fin.ext
      show t.wa "gHead" f = (if I.off (G.dst e) < I.off I.n then I.off (G.dst e) else 0)
      rw [hfh, hbs.2.1, hdst]
      rw [hbs.2.1, hdst] at hkd hdn
      rw [if_pos (L6In.off_lt_of_keep hdn hkd)]
    · show t.va "gW" f ≤ G.w e
      rw [hfw, ← hw]; exact bst_min hb e heg rfl
  classify f := by
    have hfM : (f : ℕ) < I.sl I.n := f.2
    obtain ⟨x, hx, hr⟩ := slot_cover hB hδ hfM
    obtain ⟨v, hv, hk, q, hq, hxq, hown⟩ := owner hB hS hδ hx
    have hsrcf : t.wa "gSrc" f = x := src_post hB hS hδ hx hr
    rw [hxq] at hr
    rcases edge_post hB hS hδ hv hk hq hr with ⟨hc, hh, -⟩ | ⟨i, hi, hh, hwf⟩
    · right
      apply Fin.ext
      show t.wa "gOwn" (t.wa "gSrc" f) = t.wa "gOwn" (t.wa "gHead" f)
      rw [hsrcf, hh, hown, show I.off v + q + 1 = I.off v + (q + 1) by ring,
        own_post hB hS hv hk hc]
    · left
      obtain ⟨hem, hes, hed, hkd⟩ := L6In.kept_edge (L6In.KL_mem hk hi)
      have hemG : (I.KL v).getD i 0 < G.m := by rw [← hm]; exact hem
      have hdn : I.dst ((I.KL v).getD i 0) < I.n := hB.E.A.hdst _ hem
      refine ⟨⟨(I.KL v).getD i 0, hemG⟩, ?_, ?_, ?_, ?_⟩
      · intro h
        apply hed
        have h1 := congrArg Fin.val h
        rw [← hsrc ⟨_, hemG⟩, ← hdst ⟨_, hemG⟩] at h1
        exact h1.symm.trans hes
      · apply Fin.ext
        show t.wa "gOwn" (t.wa "gSrc" f) = (G.src ⟨_, hemG⟩ : ℕ)
        rw [hsrcf, hown, ← hsrc ⟨_, hemG⟩]; exact hes.symm
      · apply Fin.ext
        show t.wa "gHead" f = (if I.off (G.dst ⟨_, hemG⟩) < I.off I.n then I.off (G.dst ⟨_, hemG⟩) else 0)
        rw [hh, ← hdst ⟨_, hemG⟩, if_pos (L6In.off_lt_of_keep hdn hkd)]
      · show G.w ⟨_, hemG⟩ ≤ t.va "gW" f
        rw [hwf, ← hw ⟨_, hemG⟩]
  head_conn x := by
    obtain ⟨v, hv, hk, q, hq, hxq, hown⟩ := owner hB hS hδ x.2
    have hoffv : I.off v < I.off I.n := L6In.off_lt_of_keep hv hk
    have hblk : I.off v + I.cc v ≤ I.off I.n := by
      have := off_mono I (show v + 1 ≤ I.n by omega); rw [I.off_succ] at this; exact this
    have key : ∀ j, ∀ _hj : j ≤ q, ∃ p : List (Fin (Hgr hB hS hδ).m),
        (Hgr hB hS hδ).IsWalk ⟨I.off v, hoffv⟩ ⟨I.off v + j, by show I.off v + j < I.off I.n; omega⟩ p ∧
        (Hgr hB hS hδ).len p = 0 := by
      intro j
      induction j with
      | zero => intro _; exact ⟨[], by simpa using Graph.IsWalk.nil _, by simp⟩
      | succ j ih =>
        intro hj
        obtain ⟨p, hp, hl⟩ := ih (by omega)
        obtain ⟨f, hfM, hfs, hfh, hfw⟩ := chain_post hB hS hδ hv hk (show j + 1 < I.cc v by omega)
        have hsf : (Hgr hB hS hδ).src ⟨f, hfM⟩ = ⟨I.off v + j, by show I.off v + j < I.off I.n; omega⟩ :=
          Fin.ext hfs
        have hdf : (Hgr hB hS hδ).dst ⟨f, hfM⟩ =
            ⟨I.off v + (j + 1), by show I.off v + (j + 1) < I.off I.n; omega⟩ := by
          apply Fin.ext; show t.wa "gHead" f = I.off v + (j + 1); rw [hfh]; ring
        refine ⟨p ++ [⟨f, hfM⟩], ?_, ?_⟩
        · have h1 := Graph.IsWalk.single (G := Hgr hB hS hδ) ⟨f, hfM⟩
          rw [hsf, hdf] at h1
          exact hp.append h1
        · rw [Graph.len_append, hl, Graph.len_cons]
          show (0 : ℝ≥0) + (t.va "gW" f + (Hgr hB hS hδ).len []) = 0
          rw [hfw]; simp
    obtain ⟨p, hp, hl⟩ := key q le_rfl
    refine ⟨p, ?_, hl⟩
    have e1 : (⟨if I.off (t.wa "gOwn" x) < I.off I.n then I.off (t.wa "gOwn" x) else 0, by
        split_ifs with h
        · exact h
        · exact N_pos hsn⟩ : Fin (Hgr hB hS hδ).n) = ⟨I.off v, hoffv⟩ := by
      apply Fin.ext; simp [hown, hoffv]
    have e2 : (⟨I.off v + q, by show I.off v + q < I.off I.n; omega⟩ : Fin (Hgr hB hS hδ).n) = x :=
      Fin.ext hxq.symm
    rw [e2] at hp
    convert hp using 2

include hB hS hδ in
theorem st_post (x : ℕ) : t.wa "gSt" x = t0.wa "gSt" x := by
  rw [sort_frame_wa hS (by simp)]

/-- `gSt` ranges are exactly the out-edges (the predicate consumed by agent-08's base case). -/
theorem csrAt : Frontier.CHD.RamBaseCase.CSRAt t (Hgr hB hS hδ) where
  len := by
    show I.off I.n + 1 ≤ t.wlen "gSt"
    rw [(hS.U.warr "gSt" (by simp)).2, hB.lSt]
  le u := by
    show t.wa "gSt" u ≤ t.wa "gSt" (u + 1)
    rw [st_post hB hS hδ, st_post hB hS hδ]; exact st_le_succ hB.F hB.stN hδ u.2
  le_m u := by
    show t.wa "gSt" (u + 1) ≤ I.sl I.n
    have hu : (u : ℕ) < I.off I.n := u.2
    rw [st_post hB hS hδ]; exact st_le_M hB.F hB.stN hδ (by omega)
  src e u := by
    show (⟨t.wa "gSrc" e, _⟩ : Fin (I.off I.n)) = u ↔ t.wa "gSt" u ≤ e ∧ (e : ℕ) < t.wa "gSt" (u + 1)
    rw [st_post hB hS hδ, st_post hB hS hδ]
    obtain ⟨x, hx, hr⟩ := slot_cover hB hδ e.2
    have hsx := src_post hB hS hδ hx hr
    constructor
    · intro h
      have : (u : ℕ) = x := by rw [← hsx]; exact (congrArg Fin.val h).symm
      rw [this]; exact hr
    · intro h
      apply Fin.ext
      show t.wa "gSrc" e = u
      rw [hsx]; exact range_unique hB hδ hx u.2 hr h

/-- Heads and weights per slot (the predicate consumed by agent-02's label layer). -/
theorem graphAt : Frontier.RAM.LabRAM.GraphAt t (Hgr hB hS hδ) where
  head := by
    refine ⟨?_, fun i hi => ?_⟩
    · show 0 + I.sl I.n ≤ t.wlen "gHead"
      rw [hS.hL, hB.lHead]; omega
    · simp only [Nat.zero_add, finExt, dif_pos hi]; rfl
  w := by
    refine ⟨?_, fun i hi => ?_⟩
    · show 0 + I.sl I.n ≤ t.vlen "gW"
      rw [hS.wL, hB.lW]; omega
    · simp only [Nat.zero_add, finExt, dif_pos hi]; rfl

/-- The out-list of virtual vertex `x`: its slots in increasing order. -/
def outL (H : Graph) (x : Fin H.n) : List (Fin H.m) :=
  (List.finRange H.m).filter (fun e => decide (H.src e = x))

theorem outL_mem {H : Graph} {x : Fin H.n} {e : Fin H.m} : e ∈ outL H x ↔ H.src e = x := by
  simp [outL]

theorem outL_nodup {H : Graph} (x : Fin H.n) : (outL H x).Nodup :=
  (List.nodup_finRange _).filter _

include hB hS hδ in
theorem outL_range {x : Fin (Hgr hB hS hδ).n} {e : Fin (Hgr hB hS hδ).m}
    (he : e ∈ outL (Hgr hB hS hδ) x) : t0.wa "gSt" x ≤ e ∧ (e : ℕ) < t0.wa "gSt" (x + 1) := by
  have h := ((csrAt hB hS hδ).src e x).mp (outL_mem.mp he)
  rwa [st_post hB hS hδ, st_post hB hS hδ] at h

include hB hS hδ in
/-- **P4**: out-lists are sorted in the walk order (`SortedRel`), for any source. -/
theorem outL_sorted (s' : Fin (Hgr hB hS hδ).n) (x : Fin (Hgr hB hS hδ).n) :
    (outL (Hgr hB hS hδ) x).Pairwise (SortedRel (Hgr hB hS hδ) s') := by
  have h1 : (outL (Hgr hB hS hδ) x).Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  refine h1.imp_of_mem (fun {e e'} he he' hlt => ?_)
  obtain ⟨ha, hb⟩ := outL_range hB hS hδ he
  obtain ⟨ha', hb'⟩ := outL_range hB hS hδ he'
  have hx : (x : ℕ) < I.off I.n := x.2
  have hlt' : (e : ℕ) < e' := hlt
  have hkey := post_keyLe hS hx ha hlt' hb'
  have hne := post_heads_ne hB hS hδ hx ⟨ha, hb⟩ ⟨ha', hb'⟩ (by omega)
  apply sortedRel_of_key
  simp only [keyLe, realOps_le, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hkey
  obtain ⟨hw1, hw2⟩ := hkey
  show t.va "gW" e < t.va "gW" e' ∨ (t.va "gW" e = t.va "gW" e' ∧
    (⟨t.wa "gHead" e, _⟩ : Fin (I.off I.n)) < ⟨t.wa "gHead" e', _⟩)
  rcases hw2 with hw2 | hw2
  · left; exact lt_of_le_of_ne hw1 (fun h => hw2 (h ▸ le_rfl))
  · by_cases hwe : t.va "gW" e' ≤ t.va "gW" e
    · right
      refine ⟨le_antisymm hw1 hwe, ?_⟩
      show t.wa "gHead" e < t.wa "gHead" e'
      omega
    · left; exact lt_of_le_of_ne hw1 (fun h => hwe (h ▸ le_rfl))

include hB hS hδ in
/-- Out-lists have pairwise distinct heads (`Simple`). -/
theorem outL_simple (x : Fin (Hgr hB hS hδ).n) :
    ((outL (Hgr hB hS hδ) x).map (Hgr hB hS hδ).dst).Nodup := by
  refine (outL_nodup x).map_on ?_
  intro e he e' he' heq
  by_contra hne
  obtain ⟨ha, hb⟩ := outL_range hB hS hδ he
  obtain ⟨ha', hb'⟩ := outL_range hB hS hδ he'
  have hne' : (e : ℕ) ≠ e' := fun h => hne (Fin.ext h)
  exact post_heads_ne hB hS hδ x.2 ⟨ha, hb⟩ ⟨ha', hb'⟩ hne' (congrArg Fin.val heq)

end Red

end Frontier.CHD.L6
