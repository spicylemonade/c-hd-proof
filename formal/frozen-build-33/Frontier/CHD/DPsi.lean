import Frontier.CHD.DLazy

/-!
# Frontier.CHD.DPsi — a block-count potential for the lazy structure (owner: agent-01; NON-GATE)

The insertion charge of `DLazy` (`insertM_amortized`) contains the binary-search cost
`bsCost D.blocks.length`, so the number of blocks must be bounded.  Blocks with few entries
accumulate (the leftover block of a full `pull`, the last group of a `merge`), so the bound needs a
potential:

* `thr M = max 1 ⌊M/3⌋`, and `nsm M bs` = the number of SMALL blocks (fewer than `thr M` entries);
* `psi D = M · nsm + 2 · #entries`.

Facts:
* `length_le_nsm_add`: `#blocks ≤ nsm + #entries / thr M` (big blocks hold `≥ thr M` entries);
* `psi_new`: `psi = M` for a new structure;
* `psi_insertL`: `psi' ≤ psi + 2` (an insertion only grows one block);
* `psi_pullL`: `psi' + M ≤ psi` or `psi' = M` (median splits only create big blocks; a full pull
  removes its `M` pulled entries and adds at most one block; a short pull resets the structure);
* `psi_merge`: `psi' ≤ psi + M + 2 · #entries(D')` for `M ≥ 3` (grouping leaves at most one small
  group, the last).
-/

namespace Frontier.CHD.DL

open Frontier.CHD Frontier.CHD.DB

section Psi

set_option linter.unusedSectionVars false

variable {κ α : Type*} [DecidableEq κ] [LinearOrder α] [Inhabited α]

/-- the small-block threshold: `max 1 ⌊M/3⌋` entries -/
def thr (M : ℕ) : ℕ := max 1 (M / 3)

theorem one_le_thr (M : ℕ) : 1 ≤ thr M := le_max_left _ _

theorem thr_le (M : ℕ) : thr M ≤ M + 1 := max_le (by omega) (by omega)

/-- the number of SMALL blocks (fewer than `thr M` entries) -/
def nsm (M : ℕ) (bs : List (Block κ α)) : ℕ :=
  bs.countP (fun b => decide (b.ents.length < thr M))

theorem nsm_nil (M : ℕ) : nsm M ([] : List (Block κ α)) = 0 := rfl

theorem nsm_cons (M : ℕ) (b : Block κ α) (bs : List (Block κ α)) :
    nsm M (b :: bs) = nsm M bs + if b.ents.length < thr M then 1 else 0 := by
  unfold nsm
  rw [List.countP_cons]
  simp

theorem nsm_append (M : ℕ) (bs₁ bs₂ : List (Block κ α)) :
    nsm M (bs₁ ++ bs₂) = nsm M bs₁ + nsm M bs₂ := by
  unfold nsm
  rw [List.countP_append]

theorem allEnts_cons_length (b : Block κ α) (bs : List (Block κ α)) :
    (allEnts (b :: bs)).length = b.ents.length + (allEnts bs).length := by
  simp [allEnts]

theorem allEnts_append_length (bs₁ bs₂ : List (Block κ α)) :
    (allEnts (bs₁ ++ bs₂)).length = (allEnts bs₁).length + (allEnts bs₂).length := by
  simp [allEnts]

/-- the big blocks hold at least `thr M` entries each -/
theorem thr_mul_big_le (M : ℕ) : ∀ bs : List (Block κ α),
    thr M * (bs.length - nsm M bs) ≤ (allEnts bs).length
  | [] => by simp
  | b :: bs => by
    have ih := thr_mul_big_le M bs
    have hle : nsm M bs ≤ bs.length := List.countP_le_length
    rw [nsm_cons, List.length_cons, allEnts_cons_length]
    split_ifs with h
    · have e : bs.length + 1 - (nsm M bs + 1) = bs.length - nsm M bs := by omega
      rw [e]
      omega
    · have e : bs.length + 1 - (nsm M bs + 0) = (bs.length - nsm M bs) + 1 := by omega
      rw [e, Nat.mul_add, Nat.mul_one]
      omega

/-- **blocks versus entries**: `#blocks ≤ #small + #entries / thr M` -/
theorem length_le_nsm_add (M : ℕ) (bs : List (Block κ α)) :
    bs.length ≤ nsm M bs + (allEnts bs).length / thr M := by
  have h1 := thr_mul_big_le M bs
  have h2 : bs.length - nsm M bs ≤ (allEnts bs).length / thr M :=
    (Nat.le_div_iff_mul_le (one_le_thr M)).mpr (by rw [Nat.mul_comm]; exact h1)
  omega

/-- **The block-count potential** `psi = M · #small + 2 · #entries`. -/
def psi (D : DStr κ α) : ℕ := D.M * nsm D.M D.blocks + 2 * (allEnts D.blocks).length

theorem psi_new (M : ℕ) (Bd : α) : psi (⟨M, Bd, [⟨⊥, []⟩]⟩ : DStr κ α) = M := by
  have h : 0 < thr M := one_le_thr M
  unfold psi
  rw [nsm_cons, nsm_nil]
  simp [h, allEnts]

/-- the number of blocks under a `psi` budget -/
theorem blocks_le_of_psi {D : DStr κ α} {P : ℕ} (h : psi D ≤ P) (hM : 1 ≤ D.M) :
    D.blocks.length ≤ P / D.M + (P / 2) / thr D.M := by
  have h1 := length_le_nsm_add D.M D.blocks
  unfold psi at h
  have hn : nsm D.M D.blocks ≤ P / D.M :=
    (Nat.le_div_iff_mul_le hM).mpr (by rw [Nat.mul_comm]; omega)
  have he : (allEnts D.blocks).length ≤ P / 2 := by omega
  have he' : (allEnts D.blocks).length / thr D.M ≤ (P / 2) / thr D.M := Nat.div_le_div_right he
  omega

/-- the number of entries under a `psi` budget -/
theorem ents_le_of_psi {D : DStr κ α} {P : ℕ} (h : psi D ≤ P) : (allEnts D.blocks).length ≤ P / 2 := by
  unfold psi at h
  omega

/-! ### Insert -/

theorem psi_insertL {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    (hne : D.blocks ≠ []) : psi (insertL L fresh D v lam).2.2.1 ≤ psi D + 2 := by
  by_cases hskip : skipIns L v lam = true
  · have e : (insertL L fresh D v lam).2.2.1 = D := by
      unfold insertL DB.insert
      simp [hskip]
    rw [e]
    omega
  · obtain ⟨pre, c, post, hbs, hres⟩ := addTo_noSplit 0
      (L := Function.update L v (some (fresh, lam))) (M := bigM D) (lam := lam)
      (e := (⟨fresh, v, lam⟩ : Entry κ α)) D.blocks hne
      (fun c hc => by have := length_le_allEnts hc; unfold bigM; omega)
    have e : (insertL L fresh D v lam).2.2.1 =
        ⟨D.M, D.Bd, pre ++ ⟨c.sep, (⟨fresh, v, lam⟩ : Entry κ α) :: c.ents⟩ :: post⟩ := by
      unfold insertL DB.insert
      simp only [hskip, Bool.false_eq_true, ite_false]
      rw [hres]
    rw [e]
    unfold psi
    dsimp only
    rw [hbs, nsm_append, nsm_append, nsm_cons, nsm_cons, allEnts_append_length,
      allEnts_append_length, allEnts_cons_length, allEnts_cons_length]
    dsimp only
    have hn : (if (c.ents.length + 1) < thr D.M then 1 else 0) ≤
        (if c.ents.length < thr D.M then 1 else 0) := by
      split_ifs <;> omega
    rw [List.length_cons]
    have := Nat.mul_le_mul_left D.M (Nat.add_le_add_left (Nat.add_le_add_left hn (nsm D.M post))
      (nsm D.M pre))
    omega

/-! ### Pull -/

variable (T : ℕ)

/-- **`psi` over `DB.pull`**: a full pull saves `M`, a short one resets to `psi = M`. -/
theorem psi_pull {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    psi (pull T L D).2.2.2.1 + D.M ≤ psi D ∨ psi (pull T L D).2.2.2.1 = D.M := by
  obtain ⟨-, hor, -, -, -⟩ := pull_post T hwf hK hid hM
  obtain ⟨hne, hint⟩ := hwf
  obtain ⟨pre, hbs, hacc, -, -, hrem, hpre⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  unfold pull at hor ⊢
  set acc := (collect L D.M [] D.blocks).1 with hacc_def
  set rem := (collect L D.M [] D.blocks).2.1 with hrem_def
  by_cases hsmall : acc.length ≤ D.M
  · rw [if_pos hsmall]
    right
    exact psi_new D.M D.Bd
  · rw [if_neg hsmall] at hor ⊢
    left
    dsimp only at hor ⊢
    set x := (selectC (acc.map (·.val)) D.M).1 with hx
    have hkth : IsKth (acc.map (·.val)) D.M x := selectC_isKth _ (by simp; omega)
    -- the selected value is a live value, hence below `Bd`
    have hxB : x ≠ D.Bd := by
      obtain ⟨e0, he0, hex⟩ := List.mem_map.mp hkth.1
      rw [hacc] at he0
      have he0' : e0 ∈ liveVals L D.blocks := by
        rw [hbs, liveVals_append, List.mem_append]; exact Or.inl he0
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he0'
      have hlt := (IntervalOK.bounds hint b hb e0 heb hl).2
      rw [← hex]
      exact ne_of_lt (WithBot.coe_lt_coe.mp hlt)
    have hcnt : (acc.filter (fun e => decide (e.val < x))).length = D.M := by
      rcases hor with h | h
      · exact absurd h hxB
      · simpa using h
    have hsplit : (acc.filter (fun e => decide (e.val < x))).length +
        (acc.filter (fun e => decide (x ≤ e.val))).length = acc.length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      have := List.length_eq_countP_add_countP (l := acc) (fun e : Entry κ α => e.val < x)
      rw [this]
      congr 1
      apply List.countP_congr
      intro e _
      simp
    have hacc_le : acc.length ≤ (allEnts pre).length := by
      rw [hacc]; exact (liveVals_sublist_allEnts L pre).length_le
    unfold psi
    dsimp only
    rw [nsm_cons, allEnts_cons_length, hbs, nsm_append, allEnts_append_length]
    dsimp only
    have hif : (if (acc.filter (fun e => decide (x ≤ e.val))).length < thr D.M then 1 else 0) ≤ 1 := by
      split_ifs <;> omega
    have k1 : D.M * (nsm D.M rem + (if (acc.filter (fun e => decide (x ≤ e.val))).length < thr D.M
        then 1 else 0)) ≤ D.M * nsm D.M rem + D.M := by
      rw [Nat.mul_add]
      have := Nat.mul_le_mul_left D.M hif
      omega
    have k2 : D.M * nsm D.M rem ≤ D.M * (nsm D.M pre + nsm D.M rem) :=
      Nat.mul_le_mul_left D.M (Nat.le_add_left _ _)
    omega

theorem nsm_prep (L : Live κ α) (M : ℕ) :
    ∀ bs, (∀ c ∈ bs, LVnd L c) → nsm M (prep L M bs).1 ≤ nsm M bs := by
  intro bs
  induction bs using prep.induct (L := L) (M := M) with
  | case1 => intro _; simp [prep]
  | case2 b bs h ih =>
    intro hnd
    rw [prep, dif_pos h]
    have hlo := lvnd_lo (hnd b List.mem_cons_self)
    have hhi := lvnd_hi (hnd b List.mem_cons_self)
    have k := ih (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hlo
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hhi
      · exact hnd c (List.mem_cons_of_mem _ hc))
    refine k.trans ?_
    have hd : ((liveOf L b.ents).map (·.val)).Nodup := hnd b List.mem_cons_self
    obtain ⟨hbig, -⟩ := h
    have hpos : 0 < (liveOf L b.ents).length := by omega
    have hlo_len : (loOf L b).length = (liveOf L b.ents).length / 2 := split_sizes hd hpos
    have hsum := lo_hi_length L b
    have hb_len := length_liveOf_le L b.ents
    have hthr := thr_le M
    rw [nsm_cons, nsm_cons, nsm_cons]
    dsimp only
    split_ifs <;> omega
  | case3 b bs h => intro _; rw [prep, dif_neg h]

theorem nsm_prepList (L : Live κ α) (M : ℕ) :
    ∀ cnt bs, (∀ c ∈ bs, LVnd L c) → nsm M (prepList L M cnt bs).1 ≤ nsm M bs := by
  intro cnt bs
  induction cnt, bs using prepList.induct (L := L) (M := M) with
  | case1 cnt => intro _; simp [prepList]
  | case2 cnt b rest h => intro _; rw [prepList, if_pos h]
  | case3 cnt b rest h hp => exact absurd hp (prep_ne_nil L M _ (List.cons_ne_nil _ _))
  | case4 cnt b rest h b' bs' hp ih =>
    intro hnd
    rw [prepList, if_neg h]
    split
    · next hp' => exact absurd hp' (prep_ne_nil L M _ (List.cons_ne_nil _ _))
    · next b'' bs'' hp' =>
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
      have hP := prep_lvnd L M (b :: rest) hnd
      rw [hp] at hP
      have k1 := nsm_prep L M (b :: rest) hnd
      rw [hp, nsm_cons] at k1
      have k2 := ih (fun c' hc' => hP c' (List.mem_cons_of_mem _ hc'))
      simp only
      rw [nsm_cons]
      omega

/-- **`psi` over `pullL`** -/
theorem psi_pullL {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    psi (pullL T L D).2.2.2.1 + D.M ≤ psi D ∨ psi (pullL T L D).2.2.2.1 = D.M := by
  have hnd := lvnd_of_inv hK hid
  have h1 := nsm_prepList L D.M 0 D.blocks hnd
  have h2 := (prepList_subperm L D.M 0 D.blocks).length_le
  have hP : psi (prepD L D) ≤ psi D := by
    unfold psi prepD
    dsimp only
    have := Nat.mul_le_mul_left D.M h1
    omega
  have h3 := psi_pull T (wf_prepD hwf) hK (idsNodup_prepD hid) hM
  have e3 : (prepD L D).M = D.M := rfl
  rw [e3] at h3
  rw [pullL_eq]
  dsimp only
  omega

/-! ### Merge -/

theorem nsm_groupAux {g : ℕ} (M : ℕ) (hg : thr M = g) :
    ∀ (cur : Option (Block κ α)) (bs : List (Block κ α)), nsm M (groupAux g cur bs) ≤ 1
  | none, [] => by simp [groupAux, nsm]
  | some c, [] => by
      simp only [groupAux]
      rw [nsm_cons, nsm_nil]
      split_ifs <;> omega
  | none, b :: bs => by
      simp only [groupAux]
      split_ifs with h
      · rw [nsm_cons, if_neg (by omega)]
        exact nsm_groupAux M hg none bs
      · exact nsm_groupAux M hg (some b) bs
  | some c, b :: bs => by
      simp only [groupAux]
      split_ifs with h
      · rw [nsm_cons]
        dsimp only
        rw [if_neg (by omega)]
        exact nsm_groupAux M hg none bs
      · exact nsm_groupAux M hg _ bs

/-- **`psi` over `merge`** (parent parameter `M ≥ 3`) -/
theorem psi_merge {D D' : DStr κ α} (hM3 : 3 ≤ D.M) :
    psi (merge T D D').1 ≤ psi D + D.M + 2 * (allEnts D'.blocks).length := by
  unfold psi
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · have e : (merge T D D').1 = D := by unfold merge; rw [hD]
    rw [e, hD]
    omega
  · have hne : D.blocks ≠ [] := by rw [hD]; exact List.cons_ne_nil _ _
    have hlen := (merge_entries_length T (D' := D') hne).1
    have hmM := (merge_entries_length T (D' := D') hne).2
    have hmD : (merge T D D').1 = { D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) } := by
      unfold merge; rw [hD]
    have hg : thr D.M = D.M / 3 := by unfold thr; exact max_eq_right (by omega)
    have hn1 := nsm_groupAux D.M hg none D'.blocks
    have hn2 : nsm D.M (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) ≤ nsm D.M (f :: rest) := by
      split_ifs
      · rw [nsm_cons, nsm_cons]
      · rw [nsm_cons]; omega
    rw [hmM, hmD]
    rw [hD] at hlen
    rw [hmD] at hlen
    dsimp only at hlen ⊢
    rw [nsm_append, Nat.mul_add]
    have := Nat.mul_le_mul_left D.M (Nat.add_le_add hn1 hn2)
    rw [Nat.mul_add] at this
    have e1 : D.M * (1 + nsm D.M (f :: rest)) = D.M + D.M * nsm D.M (f :: rest) := by ring
    omega

end Psi

end Frontier.CHD.DL
