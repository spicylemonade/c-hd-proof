import Frontier.RAMWP
import Frontier.RAMRep

/-!
# Frontier.CHD.RamLevel — per-level RAM data of the BMSSP spine (B-L4)

Owner: agent-08.  NON-GATE (Layer B data structures with kernel-checked specifications).

At most one BMSSP call per level is active, so every per-call object lives in a *row* of a
level-indexed array: row `l` of an array `arr` is the index range `[l * n, (l + 1) * n)`
(`n` = register `"n"`, the number of vertices; level in register `"lvl"`).

* **row lists** (`RowRep`): the list `xs` (`|xs| ≤ n`) is stored in `arr[l * n + i]`, its length
  in `len[l]`; operations `rowReset`, `rowAppend`; used for `S`, `U`, `W`, `Q`, marked groups;
* **the group table** (`GTab`): `pm.g[l * n + x]` = group index + 1 of `x` in the level-`l`
  call, `0` = none; operations `gSet`, `gClr`, `gGet`.  It replaces B1's nested membership
  stacks (one membership per vertex per active call; during level-`l` code all child records
  are cleared, so the table agrees with the stack semantics).

Every specification states its exact write set (`RAMRep.Unchanged`) and a pointwise frame for the
written array, so the representations of the other levels are preserved (`RowRep.other`).
-/

namespace Frontier.CHD.RamLevel

open Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V}

/-! ## Row lists -/

/-- `arr[lvl * n + len[lvl]]`, the next free slot of the current row. -/
def rowNext (arr len : String) : WExpr :=
  add (mul (var "lvl") (var "n")) (load len (var "lvl"))

/-- `len[lvl] := 0` -/
def rowReset (len : String) : Stmt := wstore len (var "lvl") (lit 0)

/-- `arr[lvl * n + len[lvl]] := e; len[lvl] := len[lvl] + 1` -/
def rowAppend (arr len : String) (e : WExpr) : Stmt :=
  seq (wstore arr (rowNext arr len) e)
      (wstore len (var "lvl") (add (load len (var "lvl")) (lit 1)))

/-- `x := arr[lvl * n + i]` for a word expression `i` -/
def rowGet (x arr : String) (i : WExpr) : Stmt :=
  wset x (load arr (add (mul (var "lvl") (var "n")) i))

/-- Row `l` of `arr` (length in `len[l]`) spells the list `xs`. -/
def RowRep (st : State V) (arr len : String) (n l : ℕ) (xs : List ℕ) : Prop :=
  xs.length ≤ n ∧ (l + 1) * n ≤ st.wlen arr ∧ l < st.wlen len ∧ st.wa len l = xs.length ∧
  ∀ i (h : i < xs.length), st.wa arr (l * n + i) = xs[i]

theorem RowRep.length_le {st : State V} {arr len : String} {n l : ℕ} {xs : List ℕ}
    (h : RowRep st arr len n l xs) : xs.length ≤ n := h.1

/-- A row representation only depends on the two arrays and their lengths, and on the part of
`arr` inside row `l` and the cell `len[l]`. -/
theorem RowRep.of_eq {st st' : State V} {arr len : String} {n l : ℕ} {xs : List ℕ}
    (h : RowRep st arr len n l xs) (hwl : st'.wlen arr = st.wlen arr)
    (hwl' : st'.wlen len = st.wlen len) (hlen : st'.wa len l = st.wa len l)
    (harr : ∀ i < n, st'.wa arr (l * n + i) = st.wa arr (l * n + i)) :
    RowRep st' arr len n l xs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, hwl ▸ h2, hwl' ▸ h3, hlen ▸ h4, fun i hi => ?_⟩
  rw [harr i (by omega)]
  exact h5 i hi

theorem row_index_lt {n l i : ℕ} (hi : i < n) : l * n + i < (l + 1) * n := by
  rw [Nat.succ_mul]; omega

theorem row_disjoint {n l l' i i' : ℕ} (hi : i < n) (hi' : i' < n) (hl : l ≠ l') :
    l * n + i ≠ l' * n + i' := by
  intro h
  have h1 : (l * n + i) / n = l := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, zero_add]
  have h2 : (l' * n + i') / n = l' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi', zero_add]
  rw [h] at h1
  exact hl (h1.symm.trans h2)

theorem row_inj {n l i i' : ℕ} (h : l * n + i = l * n + i') : i = i' := by omega

/-- Resetting row `l` gives the empty list; only `len[l]` is written. -/
theorem rowReset_spec (st : State V) {arr len : String} {n l : ℕ} (hl : st.w "lvl" = l)
    (hlen : l < st.wlen len) (hn : (l + 1) * n ≤ st.wlen arr) (hcap : 0 < st.cap) :
    Runs ops (rowReset len) st (fun st' => RowRep st' arr len n l [] ∧
      Unchanged st st' [len] [] [] [] ∧ (∀ j, j ≠ l → st'.wa len j = st.wa len j) ∧
      (∀ b, b ≠ len → st'.wa b = st.wa b) ∧ st'.cost = st.cost + 1) := by
  apply wp_sound
  simp only [wp, rowReset, evalW_var, evalW_lit', fit_of_lt hcap, hl]
  refine ⟨hlen, ?_⟩
  refine ⟨⟨by simp, by simpa using hn, by simpa using hlen, by simp, fun i h => by simp at h⟩,
    ⟨fun a ha => ?_, fun a _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩,
    fun j hj => by simp [hj], fun b hb => ?_, by simp⟩
  · have : a ≠ len := by simpa using ha
    refine ⟨funext fun j => by simp [this], rfl⟩
  · funext j; simp [hb]

/-- Appending `v` (the value of `e`) to row `l`; writes `arr[l*n + |xs|]` and `len[l]` only. -/
theorem rowAppend_spec (st : State V) {arr len : String} (hne : arr ≠ len) {n l : ℕ}
    {xs : List ℕ} {e : WExpr} {v : ℕ} (h : RowRep st arr len n l xs) (hl : st.w "lvl" = l)
    (hn : st.w "n" = n) (hlt : xs.length < n) (he : evalW st e = some v)
    (hcap : (l + 1) * n < st.cap) :
    Runs ops (rowAppend arr len e) st (fun st' => RowRep st' arr len n l (xs ++ [v]) ∧
      Unchanged st st' [arr, len] [] [] [] ∧
      (∀ j, j ≠ l * n + xs.length → st'.wa arr j = st.wa arr j) ∧
      (∀ j, j ≠ l → st'.wa len j = st.wa len j) ∧
      (∀ b, b ≠ arr → b ≠ len → st'.wa b = st.wa b) ∧ st'.cost = st.cost + 2 ∧
      st'.wlen = st.wlen) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hi : l * n + xs.length < (l + 1) * n := row_index_lt hlt
  have c1 : l * n < st.cap := by omega
  have c2 : l * n + xs.length < st.cap := by omega
  have c3 : xs.length + 1 < st.cap := by
    have : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  have c4 : 1 < st.cap := by omega
  have hia : l * n + xs.length < st.wlen arr := by omega
  have hne' : len ≠ arr := fun h => hne h.symm
  apply wp_sound
  simp only [wp, rowAppend, rowNext, evalW_var, evalW_add', evalW_mul', evalW_load',
    evalW_lit', hl, hn, he, fit_of_lt c1, Option.bind_some, h3, if_true, h4, fit_of_lt c2,
    State.charge_wa, State.charge_wlen, State.storeW_wa, State.storeW_wlen, State.charge_cap,
    State.storeW_cap, hne', false_and, if_false, fit_of_lt c4, fit_of_lt c3, hia,
    State.charge_w, State.storeW_w, h4]
  simp only [true_and]
  refine ⟨⟨by simp; omega, by simpa using h2, by simpa using h3, by simp, fun i hi' => ?_⟩,
    ⟨fun a ha => ?_, fun a _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩,
    fun j hj => ?_, fun j hj => ?_, fun b hb hb' => ?_, by simp⟩
  · simp only [List.length_append, List.length_singleton] at hi'
    simp only [State.charge_wa, State.storeW_wa, hne, false_and, if_false]
    by_cases hix : i = xs.length
    · subst hix; simp
    · have hlt' : i < xs.length := by omega
      have : l * n + i ≠ l * n + xs.length := by omega
      simp [this, hix, List.getElem_append_left hlt', h5 i hlt']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    refine ⟨funext fun j => by simp [ha.1, ha.2], rfl⟩
  · simp [hne, hj]
  · simp [hne', hj]
  · funext j; simp [hb, hb']

/-- Reading entry `i < |xs|` of row `l` into register `x`. -/
theorem rowGet_spec (st : State V) {x arr len : String} {n l : ℕ} {xs : List ℕ} {ie : WExpr}
    {i : ℕ} (h : RowRep st arr len n l xs) (hl : st.w "lvl" = l) (hn : st.w "n" = n)
    (hie : evalW st ie = some i) (hi : i < xs.length) (hcap : (l + 1) * n < st.cap) :
    Runs ops (rowGet x arr ie) st (fun st' => st' = (st.setW x xs[i]).charge 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hin : l * n + i < (l + 1) * n := row_index_lt (by omega)
  have c1 : l * n < st.cap := by omega
  have c2 : l * n + i < st.cap := by omega
  apply wp_sound
  simp only [wp, rowGet, evalW_var, evalW_add', evalW_mul', evalW_load', hl, hn, hie,
    fit_of_lt c1, Option.bind_some, fit_of_lt c2, show l * n + i < st.wlen arr by omega, ite_true]
  rw [h5 i hi]

/-- Rows of other levels, and other arrays, are untouched by an append at level `l`. -/
theorem RowRep.other {st st' : State V} {arr len : String} {n l l' : ℕ} {xs ys : List ℕ}
    (h : RowRep st arr len n l' ys) (hl : l ≠ l') (hxs : xs.length < n)
    (hwl : st'.wlen arr = st.wlen arr) (hwl' : st'.wlen len = st.wlen len)
    (harr : ∀ j, j ≠ l * n + xs.length → st'.wa arr j = st.wa arr j)
    (hlen : ∀ j, j ≠ l → st'.wa len j = st.wa len j) : RowRep st' arr len n l' ys :=
  h.of_eq hwl hwl' (hlen l' (Ne.symm hl)) (fun i hi => harr _ (row_disjoint hi hxs (Ne.symm hl)))

/-! ## Compact pivot groups (BM.5–8, BM.11–18, BM.23, BM.30)

Row `l` of the arrays below describes the groups `P 0, …, P (p-1)` of the level-`l` call:
`sp.gs[l n + j]` / `sp.gl[l n + j]` = start offset / current length of the segment of group `j`
in row `l` of `sp.gm` (the members), `sp.gp[l n + j]` = its pivot, `sp.gpos[l n + x]` = offset
of member `x`, `sp.g[l n + x]` = `j + 1` if `x ∈ P j`, `0` if `x` is in no group.  Removing a
member is an O(1) swap with the last member of its segment, so scans of a group cost its
*current* size (as charged by `BMCost.iterCost`). -/

/-- `lvl * n + e` -/
def rb (e : WExpr) : WExpr := add (mul (var "lvl") (var "n")) e

section groups

variable (st : State V) (l n : ℕ)

/-- start offset of group `j` -/
def gs (j : ℕ) : ℕ := st.wa "sp.gs" (l * n + j)
/-- current length of group `j` -/
def gl (j : ℕ) : ℕ := st.wa "sp.gl" (l * n + j)
/-- member at offset `q` -/
def gmem (q : ℕ) : ℕ := st.wa "sp.gm" (l * n + q)

end groups

/-- Row `l` represents `p` groups `P` with pivots `piv`. -/
structure GrpRep (st : State V) (l n p : ℕ) (P : ℕ → Finset ℕ) (piv : ℕ → ℕ) : Prop where
  len_gm : (l + 1) * n ≤ st.wlen "sp.gm"
  len_gs : (l + 1) * n ≤ st.wlen "sp.gs"
  len_gl : (l + 1) * n ≤ st.wlen "sp.gl"
  len_gp : (l + 1) * n ≤ st.wlen "sp.gp"
  len_gpos : (l + 1) * n ≤ st.wlen "sp.gpos"
  len_g : (l + 1) * n ≤ st.wlen "sp.g"
  p_le : p ≤ n
  seg : ∀ j < p, gs st l n j + gl st l n j ≤ n
  mem_lt : ∀ j < p, ∀ q < gl st l n j, gmem st l n (gs st l n j + q) < n
  pos : ∀ j < p, ∀ q < gl st l n j,
    st.wa "sp.gpos" (l * n + gmem st l n (gs st l n j + q)) = gs st l n j + q
  memb : ∀ j < p, ∀ q < gl st l n j, st.wa "sp.g" (l * n + gmem st l n (gs st l n j + q)) = j + 1
  img : ∀ j < p, P j = (Finset.range (gl st l n j)).image fun q => gmem st l n (gs st l n j + q)
  nomemb : ∀ x < n, st.wa "sp.g" (l * n + x) = 0 ∨ ∃ j < p, st.wa "sp.g" (l * n + x) = j + 1 ∧ x ∈ P j
  pivs : ∀ j < p, st.wa "sp.gp" (l * n + j) = piv j
  disj : ∀ j < p, ∀ j' < p, j ≠ j' →
    gs st l n j + gl st l n j ≤ gs st l n j' ∨ gs st l n j' + gl st l n j' ≤ gs st l n j

/-- Membership in a group is read off the table. -/
theorem GrpRep.mem_iff {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) {x : ℕ} :
    x ∈ P j ↔ x < n ∧ st.wa "sp.g" (l * n + x) = j + 1 := by
  constructor
  · intro hx
    rw [h.img j hj, Finset.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [Finset.mem_range] at hq
    exact ⟨h.mem_lt j hj q hq, h.memb j hj q hq⟩
  · rintro ⟨hx, hg⟩
    rcases h.nomemb x hx with h0 | ⟨j', hj', hg', hx'⟩
    · omega
    · have : j' = j := by omega
      exact this ▸ hx'

/-- Array-level effect of removing member `x` of group `j` by a swap with the last member. -/
theorem GrpRep.del {st st' : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) {x j : ℕ} (hj : j < p) (hxj : x ∈ P j)
    (hwl : st'.wlen = st.wlen)
    (hgs : st'.wa "sp.gs" = st.wa "sp.gs") (hgp : st'.wa "sp.gp" = st.wa "sp.gp")
    (hgm : ∀ i, st'.wa "sp.gm" i = if i = l * n + st.wa "sp.gpos" (l * n + x)
      then gmem st l n (gs st l n j + gl st l n j - 1) else st.wa "sp.gm" i)
    (hgpos : ∀ i, st'.wa "sp.gpos" i =
      if i = l * n + gmem st l n (gs st l n j + gl st l n j - 1)
      then st.wa "sp.gpos" (l * n + x) else st.wa "sp.gpos" i)
    (hgl : ∀ i, st'.wa "sp.gl" i = if i = l * n + j then gl st l n j - 1 else st.wa "sp.gl" i)
    (hg : ∀ i, st'.wa "sp.g" i = if i = l * n + x then 0 else st.wa "sp.g" i) :
    GrpRep st' l n p (Function.update P j ((P j).erase x)) piv := by
  -- the position of `x`
  have hxj' := hxj
  rw [h.img j hj, Finset.mem_image] at hxj'
  obtain ⟨qx, hqx, hxq⟩ := hxj'
  rw [Finset.mem_range] at hqx
  set G0 := gs st l n j with hG0
  set L0 := gl st l n j with hL0
  set y := gmem st l n (G0 + L0 - 1) with hy
  have hq0 : st.wa "sp.gpos" (l * n + x) = G0 + qx := by rw [← hxq]; exact h.pos j hj qx hqx
  -- injectivity of the members of a segment
  have inj : ∀ j1 < p, ∀ q1 < gl st l n j1, ∀ j2 < p, ∀ q2 < gl st l n j2,
      gmem st l n (gs st l n j1 + q1) = gmem st l n (gs st l n j2 + q2) → j1 = j2 ∧ q1 = q2 := by
    intro j1 hj1 q1 hq1 j2 hj2 q2 hq2 he
    have m1 := h.memb j1 hj1 q1 hq1
    have m2 := h.memb j2 hj2 q2 hq2
    rw [he] at m1
    have hjj : j1 = j2 := by omega
    subst hjj
    have p1 := h.pos j1 hj1 q1 hq1
    have p2 := h.pos j1 hj1 q2 hq2
    rw [he] at p1
    exact ⟨rfl, by omega⟩
  have hyL : L0 - 1 < L0 := by omega
  have hyeq : y = gmem st l n (G0 + (L0 - 1)) := by rw [hy]; congr 1; omega
  -- new rows
  have gs' : ∀ j', gs st' l n j' = gs st l n j' := fun j' => by simp only [gs, hgs]
  have gl' : ∀ j', gl st' l n j' = if j' = j then L0 - 1 else gl st l n j' := by
    intro j'; simp only [gl, hgl]; by_cases hjj : j' = j <;> simp [hjj]
  have gm' : ∀ q, gmem st' l n q = if q = G0 + qx then y else gmem st l n q := by
    intro q; simp only [gmem, hgm, hq0]; by_cases hq : q = G0 + qx <;> simp [hq, hy, gmem]
  -- segments of other groups avoid the positions of group `j`
  have avoid : ∀ j' < p, j' ≠ j → ∀ q < gl st l n j', gs st l n j' + q ≠ G0 + qx ∧
      gs st l n j' + q ≠ G0 + (L0 - 1) := by
    intro j' hj' hjj q hq
    rcases h.disj j' hj' j hj hjj with h1 | h1 <;> constructor <;> omega
  have hmem_lt : ∀ j' < p, ∀ q < gl st' l n j', gmem st' l n (gs st' l n j' + q) < n := by
    intro j' hj' q hq
    rw [gs', gm']
    rw [gl'] at hq
    split_ifs with h1
    · rw [hyeq]; exact h.mem_lt j hj _ hyL
    · by_cases hjj : j' = j
      · rw [if_pos hjj] at hq; subst hjj; exact h.mem_lt j' hj q (by omega)
      · rw [if_neg hjj] at hq; exact h.mem_lt j' hj' q hq
  refine ⟨by rw [hwl]; exact h.len_gm, by rw [hwl]; exact h.len_gs, by rw [hwl]; exact h.len_gl,
    by rw [hwl]; exact h.len_gp, by rw [hwl]; exact h.len_gpos, by rw [hwl]; exact h.len_g,
    h.p_le, ?_, hmem_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- seg
    intro j' hj'
    rw [gs', gl']
    have := h.seg j' hj'
    split_ifs with hjj
    · subst hjj; omega
    · exact this
  · -- pos
    intro j' hj' q hq
    rw [gs', gm']
    rw [gl'] at hq
    by_cases hjj : j' = j
    · rw [if_pos hjj] at hq
      rw [hjj]
      by_cases hqq : G0 + q = G0 + qx
      · rw [if_pos hqq, hgpos, if_pos rfl, hq0]; exact hqq.symm
      · rw [if_neg hqq, hgpos]
        have hne : l * n + gmem st l n (G0 + q) ≠ l * n + y := by
          intro he
          have := inj j hj q (by omega) j hj (L0 - 1) hyL
            (by have h1 := Nat.add_left_cancel he; rw [hyeq] at h1; exact h1)
          omega
        rw [if_neg hne]
        exact h.pos j hj q (by omega)
    · rw [if_neg hjj] at hq
      have ⟨a1, _⟩ := avoid j' hj' hjj q hq
      rw [if_neg a1, hgpos]
      have hne : l * n + gmem st l n (gs st l n j' + q) ≠ l * n + y := by
        intro he
        have := inj j' hj' q hq j hj (L0 - 1) hyL
          (by have h1 := Nat.add_left_cancel he; rw [hyeq] at h1; exact h1)
        exact hjj this.1
      rw [if_neg hne]
      exact h.pos j' hj' q hq
  · -- memb
    intro j' hj' q hq
    rw [gs', gm']
    rw [gl'] at hq
    by_cases hjj : j' = j
    · rw [if_pos hjj] at hq
      rw [hjj]
      by_cases hqq : G0 + q = G0 + qx
      · rw [if_pos hqq, hg]
        have hne : l * n + y ≠ l * n + x := by
          intro he
          have := inj j hj (L0 - 1) hyL j hj qx hqx
            (by have h1 := Nat.add_left_cancel he; rw [hyeq, ← hxq] at h1; exact h1)
          omega
        rw [if_neg hne, hyeq]; exact h.memb j hj _ hyL
      · rw [if_neg hqq, hg]
        have hne : l * n + gmem st l n (G0 + q) ≠ l * n + x := by
          intro he
          have := inj j hj q (by omega) j hj qx hqx
            (by have h1 := Nat.add_left_cancel he; rw [← hxq] at h1; exact h1)
          omega
        rw [if_neg hne]; exact h.memb j hj q (by omega)
    · rw [if_neg hjj] at hq
      have ⟨a1, _⟩ := avoid j' hj' hjj q hq
      rw [if_neg a1, hg]
      have hne : l * n + gmem st l n (gs st l n j' + q) ≠ l * n + x := by
        intro he
        have := inj j' hj' q hq j hj qx hqx
          (by have h1 := Nat.add_left_cancel he; rw [← hxq] at h1; exact h1)
        exact hjj this.1
      rw [if_neg hne]; exact h.memb j' hj' q hq
  · -- img
    intro j' hj'
    by_cases hjj : j' = j
    · rw [hjj]
      rw [Function.update_self, gl', if_pos rfl, gs']
      ext z
      simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_range, gm']
      constructor
      · rintro ⟨hzx, hz⟩
        rw [h.img j hj, Finset.mem_image] at hz
        obtain ⟨qz, hqz, rfl⟩ := hz
        rw [Finset.mem_range] at hqz
        by_cases hlast : qz = L0 - 1
        · -- the last member moves to the hole of `x`
          refine ⟨qx, ?_, by rw [if_pos rfl, hyeq, hlast]⟩
          rcases Nat.lt_or_ge qx (L0 - 1) with h1 | h1
          · exact h1
          · exfalso; apply hzx
            have : qx = L0 - 1 := by omega
            rw [hlast, ← this, hxq]
        · refine ⟨qz, by omega, ?_⟩
          have : G0 + qz ≠ G0 + qx := by
            intro he; apply hzx; rw [← hxq]; congr 1
          rw [if_neg this]
      · rintro ⟨q, hq, hz⟩
        split_ifs at hz with hqq
        · subst hz
          refine ⟨?_, ?_⟩
          · intro he
            have := inj j hj (L0 - 1) hyL j hj qx hqx (by rw [← hyeq, he, hxq])
            omega
          · rw [h.img j hj, Finset.mem_image]
            exact ⟨L0 - 1, Finset.mem_range.mpr hyL, hyeq.symm⟩
        · subst hz
          refine ⟨?_, ?_⟩
          · intro he
            have := inj j hj q (by omega) j hj qx hqx (by rw [he, hxq])
            omega
          · rw [h.img j hj, Finset.mem_image]
            exact ⟨q, Finset.mem_range.mpr (by omega), rfl⟩
    · rw [Function.update_of_ne hjj, gl', if_neg hjj, h.img j' hj']
      apply Finset.image_congr
      intro q hq
      rw [Finset.mem_coe, Finset.mem_range] at hq
      simp only [gs', gm']
      rw [if_neg (avoid j' hj' hjj q hq).1]
  · -- nomemb
    intro x' hx'
    rw [hg]
    by_cases hxx : x' = x
    · left; rw [if_pos (by rw [hxx])]
    · have hne : l * n + x' ≠ l * n + x := by omega
      rw [if_neg hne]
      rcases h.nomemb x' hx' with h0 | ⟨j', hj', hg', hx'P⟩
      · left; exact h0
      · right
        refine ⟨j', hj', hg', ?_⟩
        by_cases hjj : j' = j
        · subst hjj; rw [Function.update_self]; exact Finset.mem_erase.mpr ⟨hxx, hx'P⟩
        · rw [Function.update_of_ne hjj]; exact hx'P
  · -- pivs
    intro j' hj'; rw [hgp]; exact h.pivs j' hj'
  · -- disj
    intro j1 hj1 j2 hj2 hne
    rw [gs', gs', gl', gl']
    have := h.disj j1 hj1 j2 hj2 hne
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1; omega
    · subst h2; omega
    · exact this

/-- Remove member `px` from its group: swap it with the last member of the segment (BM.15–18).
Scratch registers `sp.j sp.q sp.t sp.y`. -/
def gDel : Stmt :=
  seq (wset "sp.j" (sub (load "sp.g" (rb (var "px"))) (lit 1)))
  (seq (wset "sp.q" (load "sp.gpos" (rb (var "px"))))
  (seq (wset "sp.t" (sub (add (load "sp.gs" (rb (var "sp.j"))) (load "sp.gl" (rb (var "sp.j"))))
    (lit 1)))
  (seq (wset "sp.y" (load "sp.gm" (rb (var "sp.t"))))
  (seq (wstore "sp.gm" (rb (var "sp.q")) (var "sp.y"))
  (seq (wstore "sp.gpos" (rb (var "sp.y")) (var "sp.q"))
  (seq (wstore "sp.gl" (rb (var "sp.j")) (sub (load "sp.gl" (rb (var "sp.j"))) (lit 1)))
       (wstore "sp.g" (rb (var "px")) (lit 0))))))))

/-- The group arrays. -/
def grpArrs : List String := ["sp.gm", "sp.gs", "sp.gl", "sp.gp", "sp.gpos", "sp.g"]

/-- **Swap-delete**: removes `x ∈ P j` from its group in 8 steps; writes only row `l` of
`sp.gm sp.gpos sp.gl sp.g` and the scratch registers. -/
theorem gDel_spec (st : State V) {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) (hl : st.w "lvl" = l) (hn : st.w "n" = n) {x j : ℕ}
    (hpx : st.w "px" = x) (hj : j < p) (hxj : x ∈ P j) (hcap : (l + 1) * n < st.cap) :
    Runs ops gDel st (fun st' => GrpRep st' l n p (Function.update P j ((P j).erase x)) piv ∧
      Unchanged st st' ["sp.gm", "sp.gpos", "sp.gl", "sp.g"] [] ["sp.j", "sp.q", "sp.t", "sp.y"] [] ∧
      (∀ b ∈ grpArrs, ∀ i, (i < l * n ∨ (l + 1) * n ≤ i) → st'.wa b i = st.wa b i) ∧
      st'.cost = st.cost + 8) := by
  have hx : x < n ∧ st.wa "sp.g" (l * n + x) = j + 1 := (h.mem_iff hj).mp hxj
  have hxj' := hxj
  rw [h.img j hj, Finset.mem_image] at hxj'
  obtain ⟨qx, hqx, hxq⟩ := hxj'
  rw [Finset.mem_range] at hqx
  have hq0 : st.wa "sp.gpos" (l * n + x) = gs st l n j + qx := by
    rw [← hxq]; exact h.pos j hj qx hqx
  have hseg := h.seg j hj
  have hpn := h.p_le
  have hyl : gl st l n j - 1 < gl st l n j := by omega
  have hylt : gmem st l n (gs st l n j + (gl st l n j - 1)) < n := h.mem_lt j hj _ hyl
  have hyeq : gs st l n j + gl st l n j - 1 = gs st l n j + (gl st l n j - 1) := by omega
  have hrow : ∀ a, a < n → l * n + a < (l + 1) * n := fun a ha => row_index_lt ha
  have hln : l * n < st.cap := by
    have := hrow x hx.1; omega
  have c1 : 1 < st.cap := by have := hrow x hx.1; omega
  have c0 : 0 < st.cap := by omega
  have hadd : gs st l n j + gl st l n j < st.cap := by
    have : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  have hlens := And.intro h.len_gm (And.intro h.len_gs (And.intro h.len_gl
    (And.intro h.len_gpos h.len_g)))
  have f1 : l * n + x < st.cap := by have := hrow x hx.1; omega
  have f2 : l * n + j < st.cap := by have := hrow j (by omega); omega
  have f3 : l * n + (gs st l n j + gl st l n j - 1) < st.cap := by
    have := hrow (gs st l n j + gl st l n j - 1) (by omega); omega
  have f4 : l * n + (gs st l n j + qx) < st.cap := by
    have := hrow (gs st l n j + qx) (by omega); omega
  have f5 : l * n + gmem st l n (gs st l n j + (gl st l n j - 1)) < st.cap := by
    have := hrow _ hylt; omega
  have i1 : l * n + x < st.wlen "sp.g" := by have := hrow x hx.1; omega
  have i2 : l * n + x < st.wlen "sp.gpos" := by have := hrow x hx.1; omega
  have i3 : l * n + j < st.wlen "sp.gs" := by have := hrow j (by omega); omega
  have i4 : l * n + j < st.wlen "sp.gl" := by have := hrow j (by omega); omega
  have i5 : l * n + (gs st l n j + gl st l n j - 1) < st.wlen "sp.gm" := by
    have := hrow (gs st l n j + gl st l n j - 1) (by omega); omega
  have i6 : l * n + (gs st l n j + qx) < st.wlen "sp.gm" := by
    have := hrow (gs st l n j + qx) (by omega); omega
  have i7 : l * n + gmem st l n (gs st l n j + (gl st l n j - 1)) < st.wlen "sp.gpos" := by
    have := hrow _ hylt; omega
  have hgx : st.wa "sp.g" (l * n + x) = j + 1 := hx.2
  have hgsj : st.wa "sp.gs" (l * n + j) = gs st l n j := rfl
  have hglj : st.wa "sp.gl" (l * n + j) = gl st l n j := rfl
  have hymem : st.wa "sp.gm" (l * n + (gs st l n j + gl st l n j - 1)) =
      gmem st l n (gs st l n j + (gl st l n j - 1)) := by rw [hyeq]; rfl
  apply wp_sound
  simp (config := { decide := true }) only [wp, gDel, rb, evalW_var, evalW_add', evalW_mul',
    evalW_sub', evalW_load', evalW_lit', State.charge_w, State.setW_w, State.charge_wa,
    State.setW_wa, State.storeW_wa, State.charge_wlen, State.setW_wlen, State.storeW_wlen,
    State.charge_cap, State.setW_cap, State.storeW_cap, State.storeW_w, hl, hn, hpx,
    Option.bind_some, fit_of_lt hln, fit_of_lt c1, fit_of_lt c0, fit_of_lt f1, fit_of_lt f2,
    fit_of_lt f3, fit_of_lt f4, fit_of_lt f5, fit_of_lt hadd, i1, i2, i3, i4, i5, i6, i7,
    if_true, hgx, Nat.add_sub_cancel, hgsj, hglj, hq0, hymem, ite_true, ite_false]
  simp only [true_and, false_and, ite_false]
  refine ⟨GrpRep.del h hj hxj rfl ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · funext i; simp (config := { decide := true }) [State.storeW, State.charge, State.setW]
  · funext i; simp (config := { decide := true }) [State.storeW, State.charge, State.setW]
  · intro i
    simp (config := { decide := true }) [State.storeW, State.charge, State.setW, hq0, hyeq]
  · intro i
    simp (config := { decide := true }) [State.storeW, State.charge, State.setW, hq0, hyeq]
  · intro i
    simp (config := { decide := true }) [State.storeW, State.charge, State.setW]
  · intro i
    simp (config := { decide := true }) [State.storeW, State.charge, State.setW]
  · refine ⟨fun a ha => ⟨?_, rfl⟩, fun a _ => ⟨rfl, rfl⟩, fun z hz => ?_, fun _ _ => rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      funext i
      simp [State.storeW, State.charge, State.setW, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [State.storeW, State.charge, State.setW, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
  · intro b _ i hi
    have e1 : i ≠ l * n + x := by have := hrow x hx.1; omega
    have e2 : i ≠ l * n + j := by have := hrow j (by omega); omega
    have e3 : i ≠ l * n + (gs st l n j + qx) := by have := hrow (gs st l n j + qx) (by omega); omega
    have e4 : i ≠ l * n + gmem st l n (gs st l n j + (gl st l n j - 1)) := by
      have := hrow _ hylt; omega
    simp [State.storeW, State.charge, State.setW, e1, e2, e3, e4]
  · simp [State.storeW, State.charge, State.setW]

/-- The group count of the level-`l` call: `sp.np[l] = p`. -/
def NpRep (st : State V) (l p : ℕ) : Prop := l < st.wlen "sp.np" ∧ st.wa "sp.np" l = p

end Frontier.CHD.RamLevel
