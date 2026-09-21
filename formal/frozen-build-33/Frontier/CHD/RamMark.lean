import Frontier.CHD.RamLevel
import Frontier.RAMWP

/-!
# RamMark — setting a bitmap on the elements of a row prefix (spine helper, agent-08)

`markRow arr len rw k val`: for `i < k` (`k` in register `rk`), `arr[row[l*n + i]] := val`, where
the row is `rw` at level `l` (register `lvl`, `n`).  Used by BM.11–12 (mark / clear the child's
frontier) and BM.24 (`inU` bits).
-/

namespace Frontier.CHD.RamMark

open Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel

variable {V : Type} {ops : VOps V}

/-- `i := 0; while i < rk do (arr[rw[lvl*n + i]] := val; i := i + 1)` (index register `mk.i`). -/
def markRow (arr rw rk : String) (val : ℕ) : Stmt :=
  seq (wset "mk.i" (lit 0))
  (.while (lt (var "mk.i") (var rk))
     (seq (wstore arr (load rw (add (mul (var "lvl") (var "n")) (var "mk.i"))) (lit val))
          (wset "mk.i" (add (var "mk.i") (lit 1)))))

/-- The first `k` elements of the row list are marked with `val`, nothing else changes. -/
theorem markRow_spec (st : State V) {arr rw len rk : String} {n l k val : ℕ} {xs : List ℕ}
    (harr : arr ≠ rw) (harr2 : arr ≠ len) (hR : RowRep st rw len n l xs) (hk : k ≤ xs.length)
    (hrk : st.w rk = k) (hrk' : rk ≠ "mk.i") (hl : st.w "lvl" = l) (hn : st.w "n" = n)
    (hl2 : "lvl" ≠ "mk.i") (hn2 : "n" ≠ "mk.i")
    (hxs : ∀ x ∈ xs, x < st.wlen arr) (hcap : (l + 1) * n < st.cap) (hval : val < st.cap)
    (hc1 : 1 < st.cap) :
    Runs ops (markRow arr rw rk val) st (fun r =>
      (∀ x, r.wa arr x = if x ∈ xs.take k then val else st.wa arr x) ∧
      Unchanged st r [arr] [] ["mk.i"] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 3 * k + 2) := by
  have hxl : xs.length ≤ n := hR.1
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  set st1 := (st.setW "mk.i" 0).charge 1 with hst1
  refine runs_while_nat (fun j r => ∃ i, j = k - i ∧ i ≤ k ∧ r.w "mk.i" = i ∧
      (∀ x, r.wa arr x = if x ∈ xs.take i then val else st.wa arr x) ∧
      Unchanged st r [arr] [] ["mk.i"] [] ∧ r.wlen = st.wlen ∧ r.cost = st.cost + 1 + 3 * i) _ ?_ k st1
    ⟨0, by simp, Nat.zero_le _, by simp [hst1, State.setW, State.charge],
      fun x => by simp [hst1, State.charge, State.setW],
      ⟨fun a _ => ⟨rfl, rfl⟩, fun a _ => ⟨rfl, rfl⟩, fun z hz => by
        simp only [List.mem_singleton] at hz; simp [hst1, State.setW, State.charge, hz],
        fun _ _ => rfl, rfl, rfl⟩, rfl, by simp [hst1, State.charge]⟩
  rintro j r ⟨i, rfl, hik, hi, hw, hU, hwl, hc⟩
  have hcapr : r.cap = st.cap := hU.cap
  have hrkr : r.w rk = k := by rw [hU.wreg rk (by simpa using hrk'), hrk]
  refine ⟨if i < k then 1 else 0, by
    rw [evalW_lt_of (by rw [evalW_var, hi]) (by rw [evalW_var, hrkr]) (by omega)],
    fun hx => ?_, fun hx => ?_⟩
  · have hik' : i < k := by by_contra h; rw [if_neg h] at hx; exact hx rfl
    have hixs : i < xs.length := by omega
    have e1 := hU.warr rw (by simpa using Ne.symm harr)
    have e2 := hU.warr len (by simpa using Ne.symm harr2)
    have hRr : RowRep r rw len n l xs := hR.of_eq e1.2 e2.2 (by rw [e2.1]) (fun q _ => by rw [e1.1])
    have hl' : r.w "lvl" = l := by rw [hU.wreg "lvl" (by simpa using hl2)]; exact hl
    have hn' : r.w "n" = n := by rw [hU.wreg "n" (by simpa using hn2)]; exact hn
    have hidx : l * n + i < (l + 1) * n := row_index_lt (by omega)
    have hrowlen : l * n + i < r.wlen rw := by have := hRr.2.1; omega
    have f1 : l * n < r.cap := by rw [hcapr]; omega
    have f2 : l * n + i < r.cap := by rw [hcapr]; omega
    have hload : evalW (r.charge 1) (load rw (add (mul (var "lvl") (var "n")) (var "mk.i"))) =
        some xs[i] := by
      simp only [evalW_load', evalW_add', evalW_mul', evalW_var, State.charge_w, State.charge_cap,
        State.charge_wlen, hl', hn', hi, Option.bind_some, fit_of_lt f1, fit_of_lt f2, hrowlen,
        ite_true, State.charge_wa]
      rw [hRr.2.2.2.2 i hixs]
    have hxi : xs[i] < (r.charge 1).wlen arr := by
      simp only [State.charge_wlen, hwl]; exact hxs _ (List.getElem_mem hixs)
    refine runs_seq (runs_wstore hload (evalW_lit_of (by simp only [State.charge_cap, hcapr]; exact hval))
      hxi ?_)
    set r2 := ((r.charge 1).storeW arr xs[i] val).charge 1 with hr2
    have hi2 : r2.w "mk.i" = i := by simp [hr2, State.storeW, State.charge, hi]
    refine runs_wset (a := i + 1) (evalW_add_of (by rw [evalW_var, hi2])
      (evalW_lit_of (by simp [hr2, State.charge, State.storeW, hcapr]; omega))
      (by simp [hr2, State.charge, State.storeW, hcapr]; omega)) ?_
    refine ⟨k - (i + 1), by omega, i + 1, rfl, by omega, by simp [State.setW, State.charge], ?_, ?_,
      ?_, ?_⟩
    · intro x
      simp only [State.charge_wa, State.setW_wa, hr2, State.storeW_wa, List.take_succ,
        List.getElem?_eq_getElem hixs, Option.toList_some, List.mem_append, List.mem_singleton]
      by_cases hx : x = xs[i]
      · simp [hx]
      · simp only [hx, and_false, if_false, false_or, hw x]
        simp
    · refine ⟨fun a ha => ⟨?_, (hU.warr a ha).2⟩, fun a ha => hU.varr a ha, fun z hz => ?_,
        fun z hz => hU.vreg z hz, hU.cap, hU.procs⟩
      · simp only [List.mem_singleton] at ha
        funext q
        simp only [State.charge_wa, State.setW_wa, hr2, State.storeW_wa, ha, false_and, if_false]
        exact congrFun (hU.warr a (by simpa using ha)).1 q
      · simp only [List.mem_singleton] at hz
        simp only [State.charge_w, State.setW_w, hz, if_false, hr2, State.storeW_w]
        exact hU.wreg z (by simpa using hz)
    · simp [State.setW, State.charge, hr2, State.storeW, hwl]
    · simp [State.setW, State.charge, hr2, State.storeW, hc]; ring
  · have hik' : i = k := by by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hik'
    refine ⟨fun x => by simp [State.charge, hw x], Unchanged.trans hU (Unchanged.charge _ 1 _ _ _ _),
      by simp [State.charge, hwl], by simp [State.charge, hc]; ring⟩


end Frontier.CHD.RamMark
