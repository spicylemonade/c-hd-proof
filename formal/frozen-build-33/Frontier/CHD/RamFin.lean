import Frontier.CHD.RamInit

/-!
# Frontier.CHD.RamFin — BM.24a–31 of the RAM spine: the finalization (owner: agent-01)

**NON-GATE** (B-L4, Layer B).  This part: the word-level clears at the end of a call (BM.30–31),
so that the next call at the same level starts with clean rows:
* `rowZero arr rw len`: for every element `x` of row `lvl` of the row list `rw` (length `len[lvl]`),
  `arr[lvl·n + x] := 0`.  With `rw = S` it clears the group-membership row `sp.g` (every remaining
  group member lies in `S`; removed members were cleared by agent-08's `gDel`), with `rw = U` it
  clears the `sp.inU` row.
-/

namespace Frontier.CHD.RamInit

open Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel

variable {V : Type} {ops : VOps V}

/-- `arr[lvl·n + rw[lvl·n + i]] := 0` for `i < len[lvl]` (index register `rz.i`). -/
def rowZero (arr rw len : String) : Stmt :=
  seq (wset "rz.i" (lit 0))
  (.while (lt (var "rz.i") (load len (var "lvl")))
     (seq (wstore arr (rb (load rw (rb (var "rz.i")))) (lit 0))
          (incr "rz.i")))

/-- **`rowZero` clears row `l` of `arr` on the elements of the row list.** -/
theorem rowZero_spec (st : State V) {arr rw len : String} {n l : ℕ} {xs : List ℕ}
    (harr : arr ≠ rw) (harr2 : arr ≠ len) (hR : RowRep st rw len n l xs)
    (hl : st.w "lvl" = l) (hn : st.w "n" = n)
    (hxs : ∀ x ∈ xs, x < n) (hlen : (l + 1) * n ≤ st.wlen arr) (hcap : (l + 1) * n + 1 < st.cap) :
    Runs ops (rowZero arr rw len) st (fun r =>
      (∀ i, r.wa arr i = if ∃ x ∈ xs, i = l * n + x then 0 else st.wa arr i) ∧
      Unchanged st r [arr] [] ["rz.i"] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 3 * xs.length + 2) := by
  classical
  have hxl : xs.length ≤ n := hR.1
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hln : (l + 1) * n = l * n + n := Nat.succ_mul l n
  have hlenl : st.wa len l = xs.length := hR.2.2.2.1
  have hlenlt : l < st.wlen len := hR.2.2.1
  have hrwl : (l + 1) * n ≤ st.wlen rw := hR.2.1
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  set st1 := (st.setW "rz.i" 0).charge 1 with hst1
  refine runs_while_nat (fun m r => ∃ i, m = xs.length - i ∧ i ≤ xs.length ∧ r.w "rz.i" = i ∧
      (∀ j, r.wa arr j = if ∃ x ∈ xs.take i, j = l * n + x then 0 else st.wa arr j) ∧
      Unchanged st r [arr] [] ["rz.i"] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 1 + 3 * i) _ ?_
    xs.length st1 ⟨0, by simp, by omega, by simp [hst1], fun j => by simp [hst1],
      by rw [hst1, unch_charge, unch_setW (by simp)]; exact Unchanged.refl _ _ _ _ _,
      by simp [hst1], by simp [hst1]⟩
  rintro m r ⟨i, rfl, hil, hir, hwa, hU, hwl, hc⟩
  have hcapr : r.cap = st.cap := hU.cap
  have hlr : r.w "lvl" = l := by rw [hU.wreg "lvl" (by simp)]; exact hl
  have hnr : r.w "n" = n := by rw [hU.wreg "n" (by simp)]; exact hn
  have hlenr : r.wa len = st.wa len := (hU.warr len (by simpa using Ne.symm harr2)).1
  have hrwr : r.wa rw = st.wa rw := (hU.warr rw (by simpa using Ne.symm harr)).1
  have eT : evalW r (lt (var "rz.i") (load len (var "lvl"))) = some (if i < xs.length then 1 else 0) := by
    rw [evalW_lt_of (by rw [evalW_var, hir]) (x := i) (y := xs.length)
      (by simp [hlr, hwl, hlenlt, hlenr, hlenl]) (by rw [hcapr]; omega)]
  refine ⟨if i < xs.length then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hi : i < xs.length := by by_contra h; rw [if_neg h] at hx; exact hx rfl
    set x := xs[i] with hxdef
    have hxn : x < n := hxs x (List.getElem_mem hi)
    have hidx : l * n + i < (l + 1) * n := row_index_lt (by omega)
    have hidx2 : l * n + x < (l + 1) * n := row_index_lt hxn
    -- the target index `lvl·n + rw[lvl·n + rz.i]`
    have eI : evalW (r.charge 1) (rb (load rw (rb (var "rz.i")))) = some (l * n + x) := by
      have h1 : evalW (r.charge 1) (load rw (rb (var "rz.i"))) = some x := by
        rw [eval_row_load (r.charge 1) rw (e := var "rz.i") (i := i) (by simpa using hlr)
          (by simpa using hnr) (by simp [hir]) (by simp [hwl]; omega) (by simp [hcapr]; omega)]
        simp only [State.charge_wa, hrwr]
        exact congrArg some (hR.2.2.2.2 i hi)
      show evalW (r.charge 1) (add (mul (var "lvl") (var "n")) (load rw (rb (var "rz.i")))) = _
      rw [evalW_add', evalW_mul', h1]
      simp [hlr, hnr, hcapr, fit_of_lt (show l * n < st.cap by omega),
        fit_of_lt (show l * n + x < st.cap by omega)]
    refine runs_seq (runs_wstore eI (evalW_lit_of (by simp [hcapr]; omega))
      (by simp [hwl]; omega) ?_)
    set r2 := ((r.charge 1).storeW arr (l * n + x) 0).charge 1 with hr2
    have e5 : evalW r2 (add (var "rz.i") (lit 1)) = some (i + 1) := by
      simp [hr2, hir, hcapr, fit_of_lt (show i + 1 < st.cap by omega),
        fit_of_lt (show 1 < st.cap by omega)]
    refine runs_wset e5 ?_
    refine ⟨xs.length - (i + 1), by omega, i + 1, rfl, by omega, by simp, fun j => ?_, ?_,
      by simp [hr2, hwl], by simp [hr2, hc]; ring⟩
    · have htake : xs.take (i + 1) = xs.take i ++ [x] := by
        rw [List.take_succ, List.getElem?_eq_getElem hi]; rfl
      simp only [State.charge_wa, State.setW_wa, hr2, State.storeW_wa, htake, List.mem_append,
        List.mem_singleton]
      by_cases hj : j = l * n + x
      · simp [hj]
      · simp only [hj, and_false, if_false]
        rw [hwa j]
        congr 1
        apply propext
        constructor
        · rintro ⟨y, hy, rfl⟩; exact ⟨y, Or.inl hy, rfl⟩
        · rintro ⟨y, hy | rfl, rfl⟩
          · exact ⟨y, hy, rfl⟩
          · exact absurd rfl hj
    · rw [unch_charge, unch_setW (by simp), hr2, unch_charge, unch_storeW (by simp), unch_charge]
      exact hU
  · have hi : i = xs.length := by by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hi
    refine ⟨fun j => by simp [hwa j, List.take_length], by rw [unch_charge]; exact hU,
      by simp [hwl], by simp [hc]; ring⟩

end Frontier.CHD.RamInit
