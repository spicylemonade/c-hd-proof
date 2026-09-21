import Frontier.CHD.DLazy

/-!
# Frontier.CHD.DLazySharp — the SHARPENED amortized pull (agent-06; Layer A, NON-GATE, tracker O6c)

`DLazy.pullL_amortized` charges `735 M + 950` per pull, independent of the number of keys returned; the
per-call inequality `Valid.cost_le` needs `735 |S'| + O(1)` (reviewer #1, O6c).  In the selection branch
`|S'| = M`; in the exhausted branch the cost is `3 |S'| + O(1)` after the potential pays for the walked blocks
and stale entries.  Proofs follow agent-04's `pull_lazy_amortized` / `pullL_amortized` / `pullM_amortized`
verbatim, with the bound sharpened.
-/

namespace Frontier.CHD.DL

open Frontier.CHD Frontier.CHD.DB

section Ops

variable {κ α : Type*} [DecidableEq κ] [LinearOrder α] [Inhabited α]

/-- `pull` on a prepared structure, sharpened: the additive term is `735 · #pulled keys + 950`. -/
theorem pull_lazy_amortized_sharp {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) (hP : PrepOK L D.M 0 D.blocks) :
    (pull 1 L D).2.2.2.2 + potL (pull 1 L D).2.2.1 (pull 1 L D).2.2.2.1 ≤
      potL L D + (735 * (pull 1 L D).1.length + 950) := by
  have hpost := pull_post 1 hwf hK hid hM
  obtain ⟨hne, hint⟩ := hwf
  unfold pull at hpost ⊢
  obtain ⟨pre, hbs, hacc, hk, hsc, hrem, hpre⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  set acc := (collect L D.M [] D.blocks).1 with hacc_def
  set rem := (collect L D.M [] D.blocks).2.1 with hrem_def
  have hacc_le : acc.length ≤ 3 * D.M + 1 :=
    collect_acc_le L D.M D.blocks [] (by simpa using hP) (by simp)
  have hsc' : (collect L D.M [] D.blocks).2.2.2 = acc.length + staleCnt L pre := by
    rw [hsc, sum_length_allEnts, length_allEnts L pre, ← hacc]
  have hpotD : potL L D = 2 * (staleCnt L pre + staleCnt L rem) + spot D.M pre + spot D.M rem := by
    unfold potL; rw [hbs, staleCnt_append, spot_append]; ring
  have hpre3 := three_mul_length_le_spot D.M pre
  by_cases hsmall : acc.length ≤ D.M
  · rw [ite_eq_left hsmall] at hpost ⊢
    dsimp only at hpost ⊢
    have hpot' : potL (clearKeys L (acc.map (·.key))) ⟨D.M, D.Bd, [⟨⊥, []⟩]⟩ = 3 := by
      simp [potL, staleCnt, allEnts, spot, bw, Ssum]
    rw [hpot', hsc', hk, List.length_map]
    omega
  · rw [ite_eq_right hsmall] at hpost ⊢
    dsimp only at hpost ⊢
    obtain ⟨hlen, hxB, -, -, -⟩ := hpost
    set x := (selectC (acc.map (·.val)) D.M).1 with hx
    set S := acc.filter (fun e => decide (e.val < x)) with hS
    set R := acc.filter (fun e => decide (x ≤ e.val)) with hR
    set ks := S.map (·.key) with hks
    have hM' : D.M < acc.length := by omega
    have hsel := selectC_cost (acc.map (·.val)) (k := D.M) (by simpa using hM')
    simp only [List.length_map] at hsel
    have hSR : S.length + R.length = acc.length := by
      rw [hS, hR, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      have := List.length_eq_countP_add_countP (l := acc) (fun e : Entry κ α => e.val < x)
      rw [this]; congr 1; apply List.countP_congr; intro e _; simp
    have hxneq : x ≠ D.Bd := by
      have hkth : IsKth (acc.map (·.val)) D.M x := selectC_isKth _ (by simpa using hM')
      obtain ⟨e0, he0, hex⟩ := List.mem_map.mp hkth.1
      rw [hacc] at he0
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he0
      have := (hint.bounds b (by rw [hbs]; exact List.mem_append_left _ hb) e0 heb hl).2
      intro h; rw [hex, h] at this
      exact absurd this (lt_irrefl _)
    have hSlen : S.length = D.M := by
      rcases hxB with h | h
      · exact absurd h hxneq
      · simpa [hks] using h
    have hRlive : ∀ e ∈ R, e.IsLive (clearKeys L ks) := by
      intro e he
      have he' := (List.mem_filter.mp he)
      rw [hacc] at he'
      have hl := (mem_liveVals.mp he'.1).2
      rw [isLive_clearKeys]
      refine ⟨hl, fun hk' => ?_⟩
      obtain ⟨e', he's, hkk⟩ := List.mem_map.mp hk'
      have h1 := List.mem_filter.mp he's
      rw [hacc] at h1
      have hl' := (mem_liveVals.mp h1.1).2
      have := (live_key_unique hl hl' hkk.symm).2
      have hxe : x ≤ e.val := by simpa using he'.2
      have hex : e'.val < x := by simpa using h1.2
      rw [this] at hxe
      exact absurd hex (not_lt.mpr hxe)
    have hstaleR : staleCnt (clearKeys L ks) [⟨⊥, R⟩] = 0 := by
      simp only [staleCnt, allEnts, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      rw [List.countP_eq_zero]
      intro e he; simp [hRlive e he]
    have hstaleRem : staleCnt (clearKeys L ks) rem ≤ staleCnt L rem := by
      unfold staleCnt
      apply List.countP_mono_left
      intro e he h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h ⊢
      intro hl
      apply h
      rw [isLive_clearKeys]
      refine ⟨hl, fun hk' => ?_⟩
      obtain ⟨e', he's, hkk⟩ := List.mem_map.mp hk'
      have h1 := List.mem_filter.mp he's
      rw [hacc] at h1
      obtain ⟨⟨b', hb', heb'⟩, hl'⟩ := mem_liveVals.mp h1.1
      have hide := (live_key_unique hl hl' hkk.symm).1
      have hnd := hid
      unfold IdsNodup at hnd
      rw [hbs] at hnd
      simp only [allEnts, List.map_append, List.flatten_append] at hnd
      have hnd' := List.nodup_append.mp hnd
      exact hnd'.2.2 _ (List.mem_map.mpr ⟨e', (show e' ∈ allEnts pre from
        mem_allEnts.mpr ⟨b', hb', heb'⟩), rfl⟩) _ (List.mem_map.mpr ⟨e, he, rfl⟩) hide.symm
    have hRS : Ssum D.M R.length ≤ 2 :=
      le_trans (Ssum_mono (by omega)) (Ssum_two_mul_add_one hM)
    have hpot' : potL (clearKeys L ks) ⟨D.M, D.Bd, ⟨⊥, R⟩ :: rem⟩ ≤
        2 * staleCnt L rem + (3 + 420 * (R.length - D.M) + 210 * 2) + spot D.M rem := by
      unfold potL
      simp only
      rw [show (⟨⊥, R⟩ :: rem : List (Block κ α)) = [⟨⊥, R⟩] ++ rem from rfl, staleCnt_append,
        spot_append, hstaleR]
      simp only [spot, bw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega
    have hSk : (S.map (·.key)).length = D.M := by rw [List.length_map]; exact hSlen
    rw [hsc', hk, hSk]
    omega


/-- **Sharpened amortized cost of `pullL`**: `cost + Φ' ≤ Φ + 735 |S'| + 950`, `S'` the pulled keys. -/
theorem pullL_amortized_sharp {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    (pullL 1 L D).2.2.2.2 + potL (pullL 1 L D).2.2.1 (pullL 1 L D).2.2.2.1 ≤
      potL L D + (735 * (pullL 1 L D).1.length + 950) := by
  have hnd := lvnd_of_inv hK hid
  have h1 := prepList_amortized hM 0 D.blocks hnd
  have hP := prepList_prepOK L D.M 0 D.blocks hnd
  have h2 := pull_lazy_amortized_sharp (D := prepD L D) (wf_prepD hwf) hK (idsNodup_prepD hid) hM hP
  have e1 : potL L (prepD L D) = 2 * staleCnt L (prepList L D.M 0 D.blocks).1 +
      spot D.M (prepList L D.M 0 D.blocks).1 := rfl
  have e2 : potL L D = 2 * staleCnt L D.blocks + spot D.M D.blocks := rfl
  rw [e1] at h2
  rw [pullL_eq, e2]
  dsimp only
  omega

/-- **Sharpened amortized cost with the entry potential**. -/
theorem pullM_amortized_sharp {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    (pullL 1 L D).2.2.2.2 + potM (pullL 1 L D).2.2.1 (pullL 1 L D).2.2.2.1 ≤
      potM L D + (735 * (pullL 1 L D).1.length + 950) := by
  have := pullL_amortized_sharp hwf hK hid hM
  have := epot_pullL (L := L) (D := D)
  unfold potM; omega

end Ops

end Frontier.CHD.DL
