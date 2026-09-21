import Frontier.CHD.RamT6

/-!
# Frontier.CHD.RamWp — BM.26 of the RAM spine: the completed part `W'` of `W` (agent-01)

**NON-GATE** (B-L4, Layer B).  `wpProg tst`: for every `x` of the level-`l` `W` row, if `x` is not
yet in `U` (`sp.inU[l·n + x] = 0`) and `tst` decides `P x` (instantiated by B-LAB with
`P x := d x < B'f`), then `x` is appended to the `W'` row (`Wp`/`Wp.len`) and to the `U` row, and
marked in `sp.inU`.  Layer A: `W' = {x ∈ W | x ∉ U ∧ d x < B'f}` with `lW' = lW.filter …`, and the
returned set `U ∪ W'`.
-/

namespace Frontier.CHD.RamInit

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel Frontier.CHD.BM

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- The arrays written by `wpProg` itself. -/
def wpArrs : List String := ["Wp", "Wp.len", "U", "U.len", "sp.inU"]

/-- The vertex indices of a list of vertices. -/
def vals (L : List (Fin G.n)) : List ℕ := L.map Fin.val

@[simp] theorem vals_length (L : List (Fin G.n)) : (vals L).length = L.length := by simp [vals]
@[simp] theorem vals_append (L1 L2 : List (Fin G.n)) : vals (L1 ++ L2) = vals L1 ++ vals L2 := by
  simp [vals]
@[simp] theorem vals_nil : vals ([] : List (Fin G.n)) = [] := rfl
@[simp] theorem vals_singleton (x : Fin G.n) : vals [x] = [(x : ℕ)] := rfl
theorem vals_getElem (L : List (Fin G.n)) (i : ℕ) (h : i < (vals L).length) :
    (vals L)[i] = (L[i]'(by simpa using h) : ℕ) := by simp [vals]
theorem mem_vals {L : List (Fin G.n)} {x : ℕ} : x ∈ vals L ↔ ∃ y ∈ L, (y : ℕ) = x := by
  simp [vals]
theorem val_mem_vals {L : List (Fin G.n)} {x : Fin G.n} : (x : ℕ) ∈ vals L ↔ x ∈ L := by
  rw [mem_vals]; exact ⟨fun ⟨y, hy, he⟩ => (Fin.ext he) ▸ hy, fun h => ⟨x, h, rfl⟩⟩

/-- **BM.26**. -/
def wpProg (tst : Stmt) : Stmt :=
  seq (rowReset "Wp.len")
  (seq (wset "t6.i" (lit 0))
  (.while (lt (var "t6.i") (load "W.len" (var "lvl")))
    (seq (wset "px" (load "W" (rb (var "t6.i"))))
    (seq (ite (load "sp.inU" (rb (var "px"))) skip
            (seq tst
              (ite (var "t6.b")
                 (seq (rowAppend "Wp" "Wp.len" (var "px"))
                 (seq (rowAppend "U" "U.len" (var "px"))
                      (wstore "sp.inU" (rb (var "px")) (lit 1))))
                 skip)))
         (incr "t6.i")))))


/-- The loop state of BM.26 after `k` members of `W`. -/
structure WpInv (st r : State V) (l n : ℕ) (lW lU : List (Fin G.n)) (Q : Fin G.n → Prop)
    [DecidablePred Q] (k : ℕ) : Prop where
  wp : RowRep r "Wp" "Wp.len" n l (vals ((lW.take k).filter (fun x => decide (Q x))))
  u : RowRep r "U" "U.len" n l (vals (lU ++ (lW.take k).filter (fun x => decide (Q x))))
  inU : ∀ x < n, r.wa "sp.inU" (l * n + x) =
    if x ∈ vals (lU ++ (lW.take k).filter (fun x => decide (Q x))) then 1 else 0
  rows : ∀ a ∈ ["Wp", "U", "sp.inU"], ∀ i, (i < l * n ∨ (l + 1) * n ≤ i) → r.wa a i = st.wa a i
  lens : ∀ a ∈ ["Wp.len", "U.len"], ∀ l', l' ≠ l → r.wa a l' = st.wa a l'
  inUl : (l + 1) * n ≤ r.wlen "sp.inU"

theorem WpInv.congr {st r : State V} {l n : ℕ} {lW lU : List (Fin G.n)} {Q : Fin G.n → Prop}
    [DecidablePred Q] {k k' : ℕ} (h : WpInv st r l n lW lU Q k)
    (he : (lW.take k').filter (fun x => decide (Q x)) = (lW.take k).filter (fun x => decide (Q x))) :
    WpInv st r l n lW lU Q k' :=
  ⟨by rw [he]; exact h.wp, by rw [he]; exact h.u, fun x hx => by rw [he]; exact h.inU x hx,
    h.rows, h.lens, h.inUl⟩


theorem getElem_not_mem_take {α : Type*} {L : List α} (hnd : L.Nodup) {k : ℕ} (hk : k < L.length) :
    L[k] ∉ L.take k := by
  intro hm
  have hsplit := List.take_append_drop k L
  have hnd' : (L.take k ++ L.drop k).Nodup := by rw [hsplit]; exact hnd
  have hd := (List.nodup_append.mp hnd').2.2
  have hmem : L[k] ∈ L.drop k := by
    rw [List.drop_eq_getElem_cons hk]; exact List.mem_cons_self
  exact hd _ hm _ hmem rfl

theorem filter_take_succ {α : Type*} (L : List α) (q : α → Bool) {k : ℕ} (hk : k < L.length) :
    (L.take (k + 1)).filter q = (L.take k).filter q ++ (if q L[k] then [L[k]] else []) := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.filter_append]
  simp only [Option.toList_some, List.filter_cons, List.filter_nil]

/-- The members selected so far form a list without repetition, disjoint from `U`. -/
theorem wp_nodup {lW lU : List (Fin G.n)} (hW : lW.Nodup) (hU : lU.Nodup) (P : ℕ → Prop)
    [DecidablePred P] (k : ℕ) :
    (lU ++ (lW.take k).filter (fun x => decide (x ∉ lU ∧ P (x : ℕ)))).Nodup := by
  rw [List.nodup_append]
  refine ⟨hU, (((List.take_sublist k lW).filter _).trans (List.filter_sublist)).nodup hW, ?_⟩
  intro a ha b hb hab
  subst hab
  have := (List.mem_filter.mp hb).2
  simp only [decide_eq_true_eq] at this
  exact this.1 ha

theorem wp_len_le {lW lU : List (Fin G.n)} (hW : lW.Nodup) (hU : lU.Nodup) (P : ℕ → Prop)
    [DecidablePred P] (k : ℕ) :
    (lU ++ (lW.take k).filter (fun x => decide (x ∉ lU ∧ P (x : ℕ)))).length ≤ G.n := by
  have := (wp_nodup hW hU P k).length_le_card
  simpa using this


/-- **BM.26 is correct.** -/
theorem wpProg_spec {tst : Stmt} {DR : State V → DGl G s → DStrM G s → Prop} {P : ℕ → Prop}
    [DecidablePred P] {Ct : ℕ} {TW TV : List String} (hT : TestI ops tst DR P Ct TW TV)
    {g : DGl G s} {D : DStrM G s}
    (hDRf : ∀ st r, DR st g D → Unchanged st r wpArrs [] t6Regs [] → st.cost ≤ r.cost → DR r g D)
    (st : State V) (hDR : DR st g D) {l n : ℕ} {lW lU : List (Fin G.n)} (hW : lW.Nodup)
    (hU : lU.Nodup) (hWr : RowRep st "W" "W.len" n l (vals lW))
    (hUr : RowRep st "U" "U.len" n l (vals lU))
    (hinU : ∀ x < n, st.wa "sp.inU" (l * n + x) = if x ∈ vals lU then 1 else 0)
    (hWpl : (l + 1) * n ≤ st.wlen "Wp") (hWpll : l < st.wlen "Wp.len")
    (hinUl : (l + 1) * n ≤ st.wlen "sp.inU") (hl : st.w "lvl" = l) (hn : st.w "n" = n)
    (hGn : G.n ≤ n) (hcap : (l + 1) * n + n + 2 < st.cap) :
    Runs ops (wpProg tst) st (fun r =>
      WpInv st r l n lW lU (fun x => x ∉ lU ∧ P (x : ℕ)) lW.length ∧ DR r g D ∧
      Unchanged st r wpArrs [] (t6Regs ++ TW) TV ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 3 + lW.length * (Ct + 16)) := by
  classical
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hln : (l + 1) * n = l * n + n := Nat.succ_mul l n
  have hWl : lW.length ≤ n := by have := hWr.1; simpa using this
  have hWlen : l < st.wlen "W.len" := hWr.2.2.1
  have hWll : st.wa "W.len" l = lW.length := by have := hWr.2.2.2.1; simpa using this
  set Q : Fin G.n → Prop := fun x => x ∉ lU ∧ P (x : ℕ) with hQ
  have mi : "t6.i" ∈ t6Regs ++ TW := by simp [t6Regs]
  have mpx : "px" ∈ t6Regs ++ TW := by simp [t6Regs]
  have hregs : ∀ a, a = "lvl" ∨ a = "n" → a ∉ t6Regs ++ TW := by
    intro a ha hm
    simp only [List.mem_append] at hm
    rcases hm with h1 | h1
    · simp [t6Regs] at h1; rcases ha with rfl | rfl <;> simp at h1
    · rcases ha with rfl | rfl
      · exact (hT.regs _ h1).2.2.1 rfl
      · exact (hT.regs _ h1).2.2.2 rfl
  -- `Wp.len[lvl] := 0`
  refine runs_seq ((rowReset_spec st (arr := "Wp") (n := n) hl hWpll hWpl (by omega)).mono ?_)
  rintro r0 ⟨hWp0, hU0, hlen0, hwa0, hc0⟩
  have hcap0 : r0.cap = st.cap := hU0.cap
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap0]; omega)) ?_)
  set r1 := (r0.setW "t6.i" 0).charge 1 with hr1
  have hU1 : Unchanged st r1 wpArrs [] (t6Regs ++ TW) TV := by
    rw [hr1, unch_charge, unch_setW mi]
    exact hU0.mono (by simp [wpArrs]) (by simp) (by simp) (by simp)
  have hwa1 : ∀ a, a ≠ "Wp.len" → r1.wa a = st.wa a := fun a ha => by simp [hr1, hwa0 a ha]
  have hwl1 : ∀ a, a ≠ "Wp.len" → r1.wlen a = st.wlen a := fun a ha => by
    simp [hr1]; exact (hU0.warr a (by simpa using ha)).2
  have hI1 : WpInv st r1 l n lW lU Q 0 := by
    refine ⟨?_, ?_, fun x hx => ?_, fun a ha i hi => ?_, fun a ha l' hl' => ?_, ?_⟩
    · simp only [List.take_zero, List.filter_nil, vals_nil]
      exact hWp0.of_eq (by simp [hr1]) (by simp [hr1]) (by simp [hr1]) (fun i _ => by simp [hr1])
    · simp only [List.take_zero, List.filter_nil, List.append_nil]
      exact hUr.of_eq (hwl1 _ (by decide)) (hwl1 _ (by decide)) (by rw [hwa1 _ (by decide)])
        (fun i _ => by rw [hwa1 _ (by decide)])
    · simp only [List.take_zero, List.filter_nil, List.append_nil]
      rw [hwa1 _ (by decide)]; exact hinU x hx
    · simp at ha; rcases ha with rfl | rfl | rfl <;> rw [hwa1 _ (by decide)]
    · simp at ha; rcases ha with rfl | rfl
      · simp [hr1]; exact hlen0 l' hl'
      · rw [hwa1 _ (by decide)]
    · rw [hwl1 _ (by decide)]; exact hinUl
  have hbound : ∀ k, (lU ++ (lW.take k).filter (fun x => decide (Q x))).length ≤ n :=
    fun k => (wp_len_le hW hU P k).trans hGn
  refine runs_while_nat (fun m r => ∃ k, m = lW.length - k ∧ k ≤ lW.length ∧ r.w "t6.i" = k ∧
      WpInv st r l n lW lU Q k ∧ DR r g D ∧ Unchanged st r wpArrs [] (t6Regs ++ TW) TV ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 2 + k * (Ct + 16)) _ ?_ lW.length r1 ?_
  swap
  · have hU1' : Unchanged st r1 wpArrs [] t6Regs [] := by
      rw [hr1, unch_charge, unch_setW (by simp [t6Regs])]
      exact hU0.mono (by simp [wpArrs]) (by simp) (by simp) (by simp)
    exact ⟨0, by simp, by omega, by simp [hr1], hI1, hDRf st r1 hDR hU1' (by simp [hr1] <;> omega), hU1, by simp [hr1]; omega,
      by simp [hr1]; omega⟩
  rintro m r ⟨k, rfl, hkl, hkr, hIr, hDRr, hUr, hc1, hc2⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have hlr : r.w "lvl" = l := by rw [hUr.wreg "lvl" (hregs _ (Or.inl rfl))]; exact hl
  have hnr : r.w "n" = n := by rw [hUr.wreg "n" (hregs _ (Or.inr rfl))]; exact hn
  have hWa := hUr.warr "W" (by simp [wpArrs])
  have hWla := hUr.warr "W.len" (by simp [wpArrs])
  have eT : evalW r (lt (var "t6.i") (load "W.len" (var "lvl"))) =
      some (if k < lW.length then 1 else 0) := by
    rw [evalW_lt_of (by rw [evalW_var, hkr]) (x := k) (y := lW.length)
      (by simp [hlr, hWla.1, hWla.2, hWlen, hWll]) (by rw [hcapr]; omega)]
  refine ⟨if k < lW.length then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hk : k < lW.length := by by_contra hc; rw [if_neg hc] at hx; exact hx rfl
    set x := lW[k] with hxdef
    have hkn : k < n := by omega
    have hxn : (x : ℕ) < n := lt_of_lt_of_le x.2 hGn
    have hxnt : x ∉ lW.take k := getElem_not_mem_take hW hk
    set F := (lW.take k).filter (fun y => decide (Q y)) with hF
    have hxF : x ∉ F := fun h => hxnt (List.mem_of_mem_filter h)
    have hfs : (lW.take (k + 1)).filter (fun y => decide (Q y)) =
        F ++ (if decide (Q x) then [x] else []) := filter_take_succ lW (fun y => decide (Q y)) hk
    -- `px := W[lvl n + t6.i]`
    have eP : evalW (r.charge 1) (load "W" (rb (var "t6.i"))) = some (x : ℕ) := by
      have hlt : l * n + k < st.wlen "W" := by
        have := hWr.2.1; have := row_index_lt (l := l) (show k < n by omega); omega
      rw [eval_row_load (r.charge 1) "W" (e := var "t6.i") (l := l) (n := n) (i := k) (by simpa using hlr)
        (by simpa using hnr) (by simp [hkr]) (by simp [hWa.2]; exact hlt)
        (by simp [hcapr]; have := row_index_lt (l := l) (show k < n by omega); omega)]
      have := hWr.2.2.2.2 k (by simpa using hk)
      rw [vals_getElem] at this
      simp [hWa.1, this, hxdef]
    refine runs_seq (runs_wset eP ?_)
    set r2 := ((r.charge 1).setW "px" (x : ℕ)).charge 1 with hr2
    have hc2r : r2.cost = r.cost + 2 := by simp [hr2]
    have hU12 : Unchanged r r2 wpArrs [] t6Regs [] := by
      rw [hr2, unch_charge, unch_setW (by simp [t6Regs]), unch_charge]; exact Unchanged.refl _ _ _ _ _
    have hDR2 : DR r2 g D := hDRf r r2 hDRr hU12 (by omega)
    have hUr2 : Unchanged st r2 wpArrs [] (t6Regs ++ TW) TV :=
      hUr.trans (hU12.mono (by simp) (by simp) (by intro a ha; simp [ha]) (by simp))
    have hinUx : r2.wa "sp.inU" (l * n + x) = if x ∈ lU then 1 else 0 := by
      have := hIr.inU x hxn
      simp only [hr2, State.charge_wa, State.setW_wa]
      rw [this]
      congr 1
      apply propext
      rw [val_mem_vals, List.mem_append]
      exact ⟨fun h => h.resolve_right hxF, Or.inl⟩
    have eI : evalW r2 (load "sp.inU" (rb (var "px"))) = some (if x ∈ lU then 1 else 0) := by
      rw [eval_row_load r2 "sp.inU" (e := var "px") (l := l) (n := n) (i := x) (by simp [hr2, hlr]) (by simp [hr2, hnr])
        (by simp [hr2]) (by simp [hr2]; have := hIr.inUl; have := row_index_lt (l := l) hxn; omega)
        (by simp [hr2, hcapr]; have := row_index_lt (l := l) hxn; omega), hinUx]
    refine runs_seq ?_
    by_cases hxU : x ∈ lU
    · -- already in `U`: skip
      refine runs_ite_true eI (by simp [hxU]) (runs_skip ?_)
      set r3 := (r2.charge 1).charge 1 with hr3
      have e5 : evalW r3 (add (var "t6.i") (lit 1)) = some (k + 1) := by
        simp [hr3, hr2, hkr, hcapr, fit_of_lt (show k + 1 < st.cap by omega),
          fit_of_lt (show 1 < st.cap by omega)]
      refine runs_wset e5 ?_
      set r4 := (r3.setW "t6.i" (k + 1)).charge 1 with hr4
      have hQx : ¬ Q x := fun h => h.1 hxU
      have hF1 : (lW.take (k + 1)).filter (fun y => decide (Q y)) = F := by
        rw [hfs]; simp [hQx]
      have hU34 : Unchanged r2 r4 wpArrs [] t6Regs [] := by
        rw [hr4, unch_charge, unch_setW (by simp [t6Regs]), hr3, unch_charge, unch_charge]
        exact Unchanged.refl _ _ _ _ _
      refine ⟨lW.length - (k + 1), by omega, k + 1, rfl, by omega, by simp [hr4], ?_,
        hDRf r2 r4 hDR2 hU34 (by simp [hr4, hr3] <;> omega), hUr2.trans (hU34.mono (by simp) (by simp) (by intro a ha; simp [ha]) (by simp)),
        by simp [hr4, hr3]; omega, by simp [hr4, hr3]; rw [Nat.add_mul]; omega⟩
      have hwa4 : r4.wa = r.wa := by simp [hr4, hr3, hr2]
      have hwl4 : r4.wlen = r.wlen := by simp [hr4, hr3, hr2]
      refine WpInv.congr ?_ hF1
      exact ⟨hIr.wp.of_eq (by rw [hwl4]) (by rw [hwl4]) (by rw [hwa4]) (fun i _ => by rw [hwa4]),
        hIr.u.of_eq (by rw [hwl4]) (by rw [hwl4]) (by rw [hwa4]) (fun i _ => by rw [hwa4]),
        fun y hy => by rw [hwa4]; exact hIr.inU y hy, fun a ha i hi => by rw [hwa4]; exact hIr.rows a ha i hi,
        fun a ha l' hl' => by rw [hwa4]; exact hIr.lens a ha l' hl', by rw [hwl4]; exact hIr.inUl⟩
    · -- not in `U`: test `P x`
      refine runs_ite_false (by rw [eI]; simp [hxU]) ?_
      refine runs_seq ((hT.run (r2.charge 1) g D (hDRf r2 _ hDR2 (by
        rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp)) (by simp [hr2])).mono ?_)
      rintro r3 ⟨hb3, hU3, hc3a, hc3b, hDR3⟩
      have hpx3 : r3.w "px" = (x : ℕ) := by
        rw [hU3.wreg "px" (fun h => (hT.regs _ h).2.1 rfl)]; simp [hr2]
      have hk3 : r3.w "t6.i" = k := by
        rw [hU3.wreg "t6.i" (fun h => (hT.regs _ h).1 rfl)]; simp [hr2, hkr]
      have hl3 : r3.w "lvl" = l := by
        rw [hU3.wreg "lvl" (fun h => (hT.regs _ h).2.2.1 rfl)]; simp [hr2, hlr]
      have hn3 : r3.w "n" = n := by
        rw [hU3.wreg "n" (fun h => (hT.regs _ h).2.2.2 rfl)]; simp [hr2, hnr]
      have hcap3 : r3.cap = st.cap := by rw [hU3.cap]; simp [hr2, hcapr]
      have hwa3 : r3.wa = r2.wa := funext fun a => (hU3.warr a (by simp)).1
      have hwl3 : r3.wlen = r2.wlen := funext fun a => (hU3.warr a (by simp)).2
      have hpx2 : (r2.charge 1).w "px" = (x : ℕ) := by simp [hr2]
      rw [hpx2] at hb3
      have hUr3 : Unchanged st r3 wpArrs [] (t6Regs ++ TW) TV :=
        hUr2.trans ((Unchanged.charge r2 1 _ _ _ _).trans
          (hU3.mono (by simp) (by simp) (by intro a ha; simp [ha]) (by simp)))
      by_cases hPx : P (x : ℕ)
      · -- append to `W'` and `U`, mark
        have h1 : r3.w "t6.b" = 1 := by rw [hb3, if_pos hPx]
        refine runs_ite_true (by simp [h1]) one_ne_zero ?_
        have hQx : Q x := ⟨hxU, hPx⟩
        have hF1 : (lW.take (k + 1)).filter (fun y => decide (Q y)) = F ++ [x] := by
          rw [hfs]; simp [hQx]
        have hbk1 := hbound (k + 1)
        rw [hF1] at hbk1
        simp only [List.length_append, List.length_singleton] at hbk1
        -- `Wp` row
        have hWp3 : RowRep (r3.charge 1) "Wp" "Wp.len" n l (vals F) :=
          hIr.wp.of_eq (by simp [hwl3, hr2]) (by simp [hwl3, hr2]) (by simp [hwa3, hr2])
            (fun i _ => by simp [hwa3, hr2])
        refine runs_seq ((rowAppend_spec (r3.charge 1) (arr := "Wp") (len := "Wp.len") (v := (x : ℕ))
          (by decide) hWp3 (by simpa using hl3) (by simpa using hn3) (by rw [vals_length]; omega)
          (by simp [hpx3]) (by simp [hcap3]; omega)).mono ?_)
        rintro r4 ⟨hWp4, hU4, hfr4a, hfr4l, hfr4o, hc4⟩
        have hl4 : r4.w "lvl" = l := by rw [hU4.wreg "lvl" (by simp)]; simpa using hl3
        have hn4 : r4.w "n" = n := by rw [hU4.wreg "n" (by simp)]; simpa using hn3
        have hpx4 : r4.w "px" = (x : ℕ) := by rw [hU4.wreg "px" (by simp)]; simpa using hpx3
        have hcap4 : r4.cap = st.cap := by rw [hU4.cap]; simpa using hcap3
        have hUrow4 : RowRep r4 "U" "U.len" n l (vals (lU ++ F)) :=
          hIr.u.of_eq (by rw [(hU4.warr "U" (by simp)).2]; simp [hwl3, hr2])
            (by rw [(hU4.warr "U.len" (by simp)).2]; simp [hwl3, hr2])
            (by rw [(hU4.warr "U.len" (by simp)).1]; simp [hwa3, hr2])
            (fun i _ => by rw [(hU4.warr "U" (by simp)).1]; simp [hwa3, hr2])
        refine runs_seq ((rowAppend_spec r4 (arr := "U") (len := "U.len") (v := (x : ℕ)) (by decide)
          hUrow4 hl4 hn4 (by rw [vals_length, List.length_append]; omega) (by simp [hpx4])
          (by rw [hcap4]; omega)).mono ?_)
        rintro r5 ⟨hUrow5, hU5, hfr5a, hfr5l, hfr5o, hc5⟩
        have hl5 : r5.w "lvl" = l := by rw [hU5.wreg "lvl" (by simp)]; exact hl4
        have hn5 : r5.w "n" = n := by rw [hU5.wreg "n" (by simp)]; exact hn4
        have hpx5 : r5.w "px" = (x : ℕ) := by rw [hU5.wreg "px" (by simp)]; exact hpx4
        have hcap5 : r5.cap = st.cap := by rw [hU5.cap]; exact hcap4
        have hinUl5 : (l + 1) * n ≤ r5.wlen "sp.inU" := by
          rw [(hU5.warr "sp.inU" (by simp)).2, (hU4.warr "sp.inU" (by simp)).2]; simp [hwl3, hr2]
          exact hIr.inUl
        have eI5 : evalW r5 (rb (var "px")) = some (l * n + x) := by
          simp [rb, hl5, hn5, hpx5, hcap5, fit_of_lt (show l * n < st.cap by omega),
            fit_of_lt (show l * n + (x : ℕ) < st.cap by have := row_index_lt (l := l) hxn; omega)]
        refine runs_wstore (arr := "sp.inU") eI5 (evalW_lit_of (a := 1) (by rw [hcap5]; omega))
          (by have := row_index_lt (l := l) hxn; omega) ?_
        set r6 := (r5.storeW "sp.inU" (l * n + x) 1).charge 1 with hr6
        have hk6 : r6.w "t6.i" = k := by
          simp [hr6]; rw [hU5.wreg "t6.i" (by simp), hU4.wreg "t6.i" (by simp)]; simpa using hk3
        have hcap6 : r6.cap = st.cap := by simp [hr6, hcap5]
        have e7 : evalW r6 (add (var "t6.i") (lit 1)) = some (k + 1) := by
          simp only [evalW_add', evalW_var, hk6, evalW_lit', hcap6, fit_of_lt (show k + 1 < st.cap by omega),
            fit_of_lt (show 1 < st.cap by omega), Option.bind_some]
        refine runs_wset e7 ?_
        set r7 := (r6.setW "t6.i" (k + 1)).charge 1 with hr7
        have hU37 : Unchanged r3 r7 wpArrs [] t6Regs [] := by
          rw [hr7, unch_charge, unch_setW (by simp [t6Regs]), hr6, unch_charge,
            unch_storeW (by simp [wpArrs])]
          exact (Unchanged.charge r3 1 _ _ _ _).trans ((hU4.mono (by simp [wpArrs]) (by simp) (by simp) (by simp)).trans
            (hU5.mono (by simp [wpArrs]) (by simp) (by simp) (by simp)))
        have hwa7 : ∀ a i, r7.wa a i = if a = "sp.inU" ∧ i = l * n + x then 1 else r5.wa a i := by
          intro a i; simp [hr7, hr6]
        have hc7 : r7.cost = r5.cost + 2 := by simp [hr7, hr6]
        have hc4' : r4.cost = r3.cost + 3 := by have := hc4.1; simp at this; omega
        have hc3a' : r2.cost + 1 ≤ r3.cost := by simpa using hc3a
        have hc3b' : r3.cost ≤ r2.cost + 1 + Ct := by simpa using hc3b
        have hkm : (k + 1) * (Ct + 16) = k * (Ct + 16) + (Ct + 16) := by ring
        refine ⟨lW.length - (k + 1), by omega, k + 1, rfl, by omega, by simp [hr7], ?_,
          hDRf r3 r7 hDR3 hU37 (by omega), hUr3.trans (hU37.mono (by simp) (by simp) (by intro a ha; simp [ha]) (by simp)),
          by omega, by omega⟩
        · refine ⟨?_, ?_, fun y hy => ?_, fun a ha i hi => ?_, fun a ha l' hl' => ?_, ?_⟩
          · rw [hF1, vals_append, vals_singleton]
            refine hWp4.of_eq ?_ ?_ ?_ ?_
            · rw [show r7.wlen "Wp" = r5.wlen "Wp" by simp [hr7, hr6], (hU5.warr "Wp" (by simp)).2]
            · rw [show r7.wlen "Wp.len" = r5.wlen "Wp.len" by simp [hr7, hr6], (hU5.warr "Wp.len" (by simp)).2]
            · rw [hwa7]; simp; rw [(hU5.warr "Wp.len" (by simp)).1]
            · intro i _; rw [hwa7]; simp; rw [(hU5.warr "Wp" (by simp)).1]
          · rw [hF1, ← List.append_assoc, vals_append, vals_singleton]
            refine hUrow5.of_eq (by simp [hr7, hr6]) (by simp [hr7, hr6]) ?_ ?_
            · rw [hwa7]; simp
            · intro i _; rw [hwa7]; simp
          · rw [hF1, hwa7]
            by_cases hyx : y = x
            · subst hyx; simp
            · have hne : l * n + y ≠ l * n + x := by omega
              simp only [hne, and_false, if_false]
              rw [hfr5o "sp.inU" (by decide) (by decide), hfr4o "sp.inU" (by decide) (by decide)]
              simp only [State.charge_wa, hwa3, hr2, State.setW_wa]
              rw [hIr.inU y hy]
              congr 1
              apply propext
              simp only [hF, vals_append, vals_singleton, List.mem_append, List.mem_singleton]
              constructor
              · rintro (h | h)
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
              · rintro (h | h | h)
                · exact Or.inl h
                · exact Or.inr h
                · exact absurd h hyx
          · rw [hwa7]
            have hne : ¬ (a = "sp.inU" ∧ i = l * n + x) := by
              rintro ⟨rfl, rfl⟩; have := row_index_lt (l := l) hxn; omega
            rw [if_neg hne]
            simp at ha
            rcases ha with rfl | rfl | rfl
            · rw [(hU5.warr "Wp" (by simp)).1, hfr4a i (by
                intro he; rw [vals_length] at he; have := row_index_lt (l := l) (show F.length < n by omega); omega)]
              simp [hwa3, hr2]; exact hIr.rows "Wp" (by simp) i hi
            · rw [hfr5a i (by
                intro he; rw [vals_length, List.length_append] at he
                have := row_index_lt (l := l) (show lU.length + F.length < n by omega); omega),
                (hU4.warr "U" (by simp)).1]
              simp [hwa3, hr2]; exact hIr.rows "U" (by simp) i hi
            · rw [hfr5o "sp.inU" (by decide) (by decide), hfr4o "sp.inU" (by decide) (by decide)]
              simp [hwa3, hr2]; exact hIr.rows "sp.inU" (by simp) i hi
          · rw [hwa7]; simp only [show ¬ (a = "sp.inU" ∧ l' = l * n + x) by
              rintro ⟨rfl, -⟩; simp at ha, if_false]
            simp at ha
            rcases ha with rfl | rfl
            · rw [(hU5.warr "Wp.len" (by simp)).1, hfr4l l' hl']; simp [hwa3, hr2]
              exact hIr.lens "Wp.len" (by simp) l' hl'
            · rw [hfr5l l' hl', (hU4.warr "U.len" (by simp)).1]; simp [hwa3, hr2]
              exact hIr.lens "U.len" (by simp) l' hl'
          · simp [hr7, hr6]; exact hinUl5
      · -- test fails: skip
        have h0 : r3.w "t6.b" = 0 := by rw [hb3, if_neg hPx]
        refine runs_ite_false (by simp [h0]) (runs_skip ?_)
        set r4 := (r3.charge 1).charge 1 with hr4
        have e5 : evalW r4 (add (var "t6.i") (lit 1)) = some (k + 1) := by
          simp [hr4, hk3, hcap3, fit_of_lt (show k + 1 < st.cap by omega),
            fit_of_lt (show 1 < st.cap by omega)]
        refine runs_wset e5 ?_
        set r5 := (r4.setW "t6.i" (k + 1)).charge 1 with hr5
        have hQx : ¬ Q x := fun h => hPx h.2
        have hF1 : (lW.take (k + 1)).filter (fun y => decide (Q y)) = F := by
          rw [hfs]; simp [hQx]
        have hU35 : Unchanged r3 r5 wpArrs [] t6Regs [] := by
          rw [hr5, unch_charge, unch_setW (by simp [t6Regs]), hr4, unch_charge, unch_charge]
          exact Unchanged.refl _ _ _ _ _
        have hwa5 : r5.wa = r.wa := by simp [hr5, hr4, hwa3, hr2]
        have hwl5 : r5.wlen = r.wlen := by simp [hr5, hr4, hwl3, hr2]
        have hc5 : r5.cost = r3.cost + 3 := by simp [hr5, hr4]
        have hc3b' : r3.cost ≤ r2.cost + 1 + Ct := by simpa using hc3b
        have hc3a' : r2.cost + 1 ≤ r3.cost := by simpa using hc3a
        have hkm : (k + 1) * (Ct + 16) = k * (Ct + 16) + (Ct + 16) := by ring
        refine ⟨lW.length - (k + 1), by omega, k + 1, rfl, by omega, by simp [hr5], ?_,
          hDRf r3 r5 hDR3 hU35 (by omega), hUr3.trans (hU35.mono (by simp) (by simp) (by intro a ha; simp [ha]) (by simp)),
          by omega, by omega⟩
        refine WpInv.congr ?_ hF1
        exact ⟨hIr.wp.of_eq (by rw [hwl5]) (by rw [hwl5]) (by rw [hwa5]) (fun i _ => by rw [hwa5]),
          hIr.u.of_eq (by rw [hwl5]) (by rw [hwl5]) (by rw [hwa5]) (fun i _ => by rw [hwa5]),
          fun y hy => by rw [hwa5]; exact hIr.inU y hy, fun a ha i hi => by rw [hwa5]; exact hIr.rows a ha i hi,
          fun a ha l' hl' => by rw [hwa5]; exact hIr.lens a ha l' hl', by rw [hwl5]; exact hIr.inUl⟩
  · have hk : k = lW.length := by by_contra hc; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hk
    have hwa' : (r.charge 1).wa = r.wa := rfl
    refine ⟨⟨hIr.wp, hIr.u, hIr.inU, hIr.rows, hIr.lens, hIr.inUl⟩,
      hDRf r _ hDRr (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp),
      by rw [unch_charge]; exact hUr, by simp; omega, by simp; omega⟩

end Frontier.CHD.RamInit
