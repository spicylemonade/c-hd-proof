import Frontier.CHD.RemoveU

/-!
# AppendU — BM.24 of the recursive spine: `U := U ∪ U_i` (agent-06; B-L4, NON-GATE)

Program text = agent-08's `RamSpine.appendU` (`ramSpine_appendU_eq`, by `rfl`): the child's `U` row (level
`lvl - 1`) is appended to this level's `U` row, the `inU` bits of its vertices are set, then `copyBp`
(the slot copy `B' := B'_i`, B-LAB).  Also: `Runs.seq_inv` (inversion of `seq`) and the reassociation
lemmas `Runs.seq_assoc` / `Runs.seq_congr`.
-/

namespace Frontier.CHD.RamSpineU

open Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel

variable {V : Type} {ops : VOps V}

/-! ## Sequencing -/

/-- **Inversion of `seq`**. -/
theorem Runs.seq_inv {a b : Stmt} {s : State V} {Q : State V → Prop} (h : Runs ops (seq a b) s Q) :
    Runs ops a s (fun t => Runs ops b t Q) := by
  obtain ⟨f, r, h1, h2⟩ := h
  cases f with
  | zero => simp [exec] at h1
  | succ f =>
    rw [exec_seq, Option.bind_eq_some_iff] at h1
    obtain ⟨t, ht, hr⟩ := h1
    exact ⟨f, t, ht, f, r, hr, h2⟩

theorem Runs.seq_assoc {a b c : Stmt} {s : State V} {Q : State V → Prop} (h : Runs ops (seq (seq a b) c) s Q) :
    Runs ops (seq a (seq b c)) s Q :=
  runs_seq ((Runs.seq_inv (Runs.seq_inv h)).mono (fun _ ht => runs_seq ht))

theorem Runs.seq_assoc' {a b c : Stmt} {s : State V} {Q : State V → Prop} (h : Runs ops (seq a (seq b c)) s Q) :
    Runs ops (seq (seq a b) c) s Q :=
  runs_seq (runs_seq ((Runs.seq_inv h).mono (fun _ ht => Runs.seq_inv ht)))

theorem Runs.seq_congr {a C C' : Stmt} {s : State V} {Q : State V → Prop} (h : Runs ops (seq a C) s Q)
    (hC : ∀ t, Runs ops C t Q → Runs ops C' t Q) : Runs ops (seq a C') s Q :=
  runs_seq ((Runs.seq_inv h).mono hC)

/-! ## The program -/

def appendBody : Stmt :=
  seq (wset "px" (load "U" (chr (var "sp.i"))))
  (seq (wstore "U" (cr (load "U.len" (var "lvl"))) (var "px"))
  (seq (wstore "U.len" (var "lvl") (add (load "U.len" (var "lvl")) (lit 1)))
  (seq (wstore "sp.inU" (cr (var "px")) (lit 1))
       (incr "sp.i"))))

def appendLoop : Stmt := .while (lt (var "sp.i") (load "U.len" (sub (var "lvl") (lit 1)))) appendBody

/-- BM.24 -/
def appendU (copyBp : Stmt) : Stmt := seq (wset "sp.i" (lit 0)) (seq appendLoop copyBp)

theorem ramSpine_appendU_eq (copyBp : Stmt) : RamSpine.appendU copyBp = appendU copyBp := rfl

/-! ## The append loop -/

section AppendLoop

/-- Invariant of the append loop after `i` vertices of the child's row `xs`. -/
structure AInv (st : State V) (l n : ℕ) (U0 xs : List ℕ) (i : ℕ) (t : State V) : Prop where
  ri : t.w "sp.i" = i
  rl : t.w "lvl" = l
  rn : t.w "n" = n
  ile : i ≤ xs.length
  ucur : RowRep t "U" "U.len" n l (U0 ++ xs.take i)
  uchild : RowRep t "U" "U.len" n (l - 1) xs
  inset : ∀ x ∈ xs.take i, t.wa "sp.inU" (l * n + x) = 1
  inkeep : ∀ q, (∀ x ∈ xs.take i, q ≠ l * n + x) → t.wa "sp.inU" q = st.wa "sp.inU" q
  urow : ∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → t.wa "U" q = st.wa "U" q
  ulen : ∀ l', l' ≠ l → t.wa "U.len" l' = st.wa "U.len" l'
  warr : ∀ a, a ∉ ["U", "U.len", "sp.inU"] → t.wa a = st.wa a
  wlen : t.wlen = st.wlen
  va : t.va = st.va
  vlen : t.vlen = st.vlen
  cap : t.cap = st.cap
  procs : t.procs = st.procs
  v : t.v = st.v
  wreg : ∀ y, y ∉ ["px", "sp.i"] → t.w y = st.w y
  lo : st.cost ≤ t.cost
  cost : t.cost ≤ st.cost + 7 * i

theorem astep {st t : State V} {l n : ℕ} {U0 xs : List ℕ} {i : ℕ} (hl1 : 1 ≤ l)
    (hxs : ∀ x ∈ xs, x < n) (hroom : U0.length + xs.length ≤ n) (hinU : (l + 1) * n ≤ st.wlen "sp.inU")
    (hcap : (l + 1) * n + 2 < st.cap) (hA : AInv st l n U0 xs i t) (hi : i < xs.length) :
    Runs ops appendBody (t.charge 1) (AInv st l n U0 xs (i + 1)) := by
  have hcapt : (l + 1) * n + 2 < t.cap := by rw [hA.cap]; exact hcap
  have h1 : 1 < t.cap := by omega
  have hxn : xs[i] < n := hxs _ (List.getElem_mem hi)
  have hnln : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have htake : xs.take (i + 1) = xs.take i ++ [xs[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  have hlenU : (U0 ++ xs.take i).length < n := by
    simp only [List.length_append, List.length_take]; omega
  have hidx : l * n + xs[i] < (l + 1) * n := row_index_lt hxn
  unfold appendBody
  refine Runs.seq_congr (C := seq (rowAppend "U" "U.len" (var "px"))
    (seq (wstore "sp.inU" (cr (var "px")) (lit 1)) (incr "sp.i"))) ?_ (fun _ h => Runs.seq_assoc h)
  apply runs_seq
  refine runs_wset (a := xs[i]) (ev_px (s := t.charge 1) (by simpa using hA.rl) hl1 (by simpa using hA.rn)
    (by simpa using hA.ri) (RowRep.of_eq hA.uchild rfl rfl rfl (fun _ _ => rfl)) hi (by simp; omega)
    (by simpa using h1)) ?_
  apply runs_seq
  refine (rowAppend_spec (ops := ops) (v := xs[i]) (((t.charge 1).setW "px" xs[i]).charge 1) (by decide)
    (RowRep.of_eq hA.ucur rfl rfl rfl (fun _ _ => rfl)) (by simp [hA.rl]) (by simp [hA.rn]) hlenU (by simp)
    (by simp; omega)).mono (fun t2 ht2 => ?_)
  obtain ⟨hU2, hUn2, harr2, hlen2, hoth2, hc2, hwl2⟩ := ht2
  have hl2 : t2.w "lvl" = l := by rw [hUn2.wreg _ (by simp)]; simp [hA.rl]
  have hn2 : t2.w "n" = n := by rw [hUn2.wreg _ (by simp)]; simp [hA.rn]
  have hpx2 : t2.w "px" = xs[i] := by rw [hUn2.wreg _ (by simp)]; simp
  have hi2 : t2.w "sp.i" = i := by rw [hUn2.wreg _ (by simp)]; simp [hA.ri]
  have hcap2 : t2.cap = t.cap := by rw [hUn2.cap]; simp
  have hinU2 : t2.wa "sp.inU" = t.wa "sp.inU" := by rw [hoth2 _ (by decide) (by decide)]; rfl
  have hc2' : t2.cost = t.cost + 4 := by rw [hc2]; simp only [State.charge_cost, State.setW_cost]
  have c1 : l * n < t2.cap := by rw [hcap2]; omega
  have c2 : l * n + xs[i] < t2.cap := by rw [hcap2]; omega
  have hwinU : l * n + xs[i] < t2.wlen "sp.inU" := by
    rw [hwl2]; simp only [State.charge_wlen, State.setW_wlen]; rw [hA.wlen]; omega
  apply runs_seq
  refine runs_wstore (j := l * n + xs[i]) (a := 1)
    (by simp [cr, evalW_add', evalW_mul', hl2, hn2, hpx2, fit_of_lt c1, fit_of_lt c2])
    (evalW_lit_of (by omega)) hwinU ?_
  refine runs_wset (evalW_add_of (x := i) (y := 1) (by simp [hi2]) (evalW_lit_of (by simp; omega))
    (by simp; omega)) ?_
  have hchild2 : RowRep t2 "U" "U.len" n (l - 1) xs :=
    RowRep.other (RowRep.of_eq hA.uchild rfl rfl rfl (fun _ _ => rfl)) (by omega) hlenU
      (by rw [hwl2]; simp) (by rw [hwl2]; simp) harr2 hlen2
  refine ⟨by simp, by simp [hl2], by simp [hn2], by omega, ?_, ?_, fun x hx => ?_, fun q hq => ?_,
    fun q hq => ?_, fun l' hl' => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, ?_, ?_⟩
  · rw [htake, ← List.append_assoc]
    exact RowRep.of_eq hU2 (by simp) (by simp) (by simp) (fun _ _ => by simp)
  · exact RowRep.of_eq hchild2 (by simp) (by simp) (by simp) (fun _ _ => by simp)
  · rw [htake] at hx
    simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
    rcases List.mem_append.mp hx with hx | hx
    · by_cases hq : l * n + x = l * n + xs[i]
      · rw [if_pos hq]
      · rw [if_neg hq, hinU2]; exact hA.inset x hx
    · simp only [List.mem_singleton] at hx; subst hx; simp
  · have hq' : q ≠ l * n + xs[i] := hq _ (by rw [htake]; exact List.mem_append_right _ (List.mem_singleton_self _))
    simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and, if_neg hq']
    rw [hinU2]
    exact hA.inkeep q (fun x hx => hq x (by rw [htake]; exact List.mem_append_left _ hx))
  · have hq' : q ≠ l * n + (U0 ++ xs.take i).length := by
      have := row_index_lt (l := l) hlenU; omega
    simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    rw [if_neg (by rintro ⟨h, -⟩; exact absurd h (by decide)), harr2 q hq']
    exact hA.urow q hq
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    rw [if_neg (by rintro ⟨h, -⟩; exact absurd h (by decide)), hlen2 l' hl']
    exact hA.ulen l' hl'
  · have h1' : a ≠ "sp.inU" := fun e => ha (by simp [e])
    have h2' : a ≠ "U" := fun e => ha (by simp [e])
    have h3' : a ≠ "U.len" := fun e => ha (by simp [e])
    funext q
    simp only [State.charge_wa, State.setW_wa, State.storeW_wa, h1', false_and, if_false]
    rw [hoth2 a h2' h3']
    exact congrFun (hA.warr a ha) q
  · simp only [State.charge_wlen, State.setW_wlen, State.storeW_wlen]; rw [hwl2]; exact hA.wlen
  · simp only [State.charge_va, State.setW_va, State.storeW_va]
    funext a; rw [(hUn2.varr a (by simp)).1]; exact congrFun hA.va a
  · simp only [State.charge_vlen, State.setW_vlen, State.storeW_vlen]
    funext a; rw [(hUn2.varr a (by simp)).2]; exact congrFun hA.vlen a
  · simp only [State.charge_cap, State.setW_cap, State.storeW_cap]; rw [hcap2]; exact hA.cap
  · simp only [State.charge_procs, State.setW_procs, State.storeW_procs]; rw [hUn2.procs]; exact hA.procs
  · simp only [State.charge_v, State.setW_v, State.storeW_v]
    funext a; rw [hUn2.vreg a (by simp)]; exact congrFun hA.v a
  · have hyi : y ≠ "sp.i" := fun e => hy (by simp [e])
    have hyp : y ≠ "px" := fun e => hy (by simp [e])
    simp only [State.charge_w, State.setW_w, State.storeW_w, if_neg hyi]
    rw [hUn2.wreg y (by simp)]
    simp [hyp]
    exact hA.wreg y hy
  · simp only [State.charge_cost, State.setW_cost, State.storeW_cost]; have := hA.lo; omega
  · simp only [State.charge_cost, State.setW_cost, State.storeW_cost]; have := hA.cost; omega

/-- **BM.24's loop**: this level's `U` row becomes `U0 ++ xs` (the child's row `xs`), the `inU` bits of `xs`
are set, everything else is untouched. -/
theorem appendLoop_spec {st : State V} {l n : ℕ} {U0 xs : List ℕ}
    (hl : st.w "lvl" = l) (hl1 : 1 ≤ l) (hn : st.w "n" = n) (hi0 : st.w "sp.i" = 0)
    (hU0 : RowRep st "U" "U.len" n l U0) (hU : RowRep st "U" "U.len" n (l - 1) xs)
    (hxs : ∀ x ∈ xs, x < n) (hroom : U0.length + xs.length ≤ n) (hinU : (l + 1) * n ≤ st.wlen "sp.inU")
    (hcap : (l + 1) * n + 2 < st.cap) :
    Runs ops appendLoop st (fun r =>
      RowRep r "U" "U.len" n l (U0 ++ xs) ∧ RowRep r "U" "U.len" n (l - 1) xs ∧
      (∀ x ∈ xs, r.wa "sp.inU" (l * n + x) = 1) ∧
      (∀ q, (∀ x ∈ xs, q ≠ l * n + x) → r.wa "sp.inU" q = st.wa "sp.inU" q) ∧
      (∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → r.wa "U" q = st.wa "U" q) ∧
      (∀ l', l' ≠ l → r.wa "U.len" l' = st.wa "U.len" l') ∧
      (∀ a, a ∉ ["U", "U.len", "sp.inU"] → r.wa a = st.wa a) ∧ r.wlen = st.wlen ∧ r.va = st.va ∧
      r.vlen = st.vlen ∧ r.cap = st.cap ∧ r.procs = st.procs ∧ r.v = st.v ∧
      (∀ y, y ∉ ["px", "sp.i"] → r.w y = st.w y) ∧ r.w "sp.i" = xs.length ∧ r.w "lvl" = l ∧ r.w "n" = n ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 7 * xs.length + 1) := by
  have h1 : 1 < st.cap := by omega
  unfold appendLoop
  refine runs_while (fun i t => AInv st l n U0 xs i t) xs.length _ ?_ ?_ st
    ⟨hi0, hl, hn, Nat.zero_le _, by simpa using hU0, hU, fun x hx => by simp at hx, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, le_rfl,
      by simp⟩
  · intro i hi t hA
    have ht1 : 1 < t.cap := by rw [hA.cap]; exact h1
    refine ⟨1, ?_, one_ne_zero, astep hl1 hxs hroom hinU hcap hA hi⟩
    rw [evalW_lt_of (x := i) (y := xs.length) (by simp [hA.ri]) (ev_ulen hA.rl hl1 hA.uchild ht1) ht1,
      if_pos hi]
  · intro t hA
    have ht1 : 1 < t.cap := by rw [hA.cap]; exact h1
    have htake : xs.take xs.length = xs := List.take_length
    refine ⟨?_, ?_⟩
    · rw [evalW_lt_of (x := xs.length) (y := xs.length) (by simp [hA.ri]) (ev_ulen hA.rl hl1 hA.uchild ht1) ht1]
      simp
    · have hc := hA.ucur
      rw [htake] at hc
      refine ⟨RowRep.of_eq hc rfl rfl rfl (fun _ _ => rfl), RowRep.of_eq hA.uchild rfl rfl rfl (fun _ _ => rfl),
        fun x hx => hA.inset x (by rw [htake]; exact hx), fun q hq => hA.inkeep q (by rw [htake]; exact hq),
        fun q hq => hA.urow q hq, fun l' hl' => hA.ulen l' hl', fun a ha => hA.warr a ha, hA.wlen, hA.va,
        hA.vlen, hA.cap, hA.procs, hA.v, fun y hy => hA.wreg y hy, by simp [hA.ri], by simp [hA.rl],
        by simp [hA.rn], by simp; have := hA.lo; omega, by simp; have := hA.cost; omega⟩

end AppendLoop

/-! ## BM.24 -/

section AppendAll

/-- What BM.24's loop leaves, relative to the entry state `st`. -/
def AppendPost (st : State V) (l n : ℕ) (U0 xs : List ℕ) (r : State V) : Prop :=
  RowRep r "U" "U.len" n l (U0 ++ xs) ∧ RowRep r "U" "U.len" n (l - 1) xs ∧
  (∀ x ∈ xs, r.wa "sp.inU" (l * n + x) = 1) ∧
  (∀ q, (∀ x ∈ xs, q ≠ l * n + x) → r.wa "sp.inU" q = st.wa "sp.inU" q) ∧
  (∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → r.wa "U" q = st.wa "U" q) ∧
  (∀ l', l' ≠ l → r.wa "U.len" l' = st.wa "U.len" l') ∧
  (∀ a, a ∉ ["U", "U.len", "sp.inU"] → r.wa a = st.wa a) ∧ r.wlen = st.wlen ∧ r.va = st.va ∧
  r.vlen = st.vlen ∧ r.cap = st.cap ∧ r.procs = st.procs ∧ r.v = st.v ∧
  (∀ y, y ∉ ["px", "sp.i"] → r.w y = st.w y) ∧ r.w "lvl" = l ∧ r.w "n" = n ∧
  st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 7 * xs.length + 2

/-- **BM.24** (`U := U ∪ U_i`, `inU` bits; then the slot copy `copyBp`, given as a black box). -/
theorem appendU_spec {st : State V} {l n : ℕ} {U0 xs : List ℕ} {copyBp : Stmt} {Qc : State V → State V → Prop}
    (hl : st.w "lvl" = l) (hl1 : 1 ≤ l) (hn : st.w "n" = n)
    (hU0 : RowRep st "U" "U.len" n l U0) (hU : RowRep st "U" "U.len" n (l - 1) xs)
    (hxs : ∀ x ∈ xs, x < n) (hroom : U0.length + xs.length ≤ n) (hinU : (l + 1) * n ≤ st.wlen "sp.inU")
    (hcap : (l + 1) * n + 2 < st.cap)
    (hcp : ∀ t, AppendPost st l n U0 xs t → Runs ops copyBp t (Qc t)) :
    Runs ops (appendU copyBp) st (fun r => ∃ t, AppendPost st l n U0 xs t ∧ Qc t r) := by
  unfold appendU
  apply runs_seq
  refine runs_wset (evalW_lit_of (by omega)) ?_
  apply runs_seq
  refine (appendLoop_spec (ops := ops) (st := (st.setW "sp.i" 0).charge 1) (by simp [hl]) hl1 (by simp [hn]) (by simp)
    (RowRep.of_eq hU0 rfl rfl rfl (fun _ _ => rfl)) (RowRep.of_eq hU rfl rfl rfl (fun _ _ => rfl)) hxs hroom
    (by simpa using hinU) (by simpa using hcap)).mono (fun t ht => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18, h19⟩ := ht
  have hP : AppendPost st l n U0 xs t := by
    refine ⟨h1, h2, h3, fun q hq => (h4 q hq).trans rfl, fun q hq => (h5 q hq).trans rfl,
      fun l' hl' => (h6 l' hl').trans rfl, fun a ha => (h7 a ha).trans rfl, h8.trans rfl, h9.trans rfl,
      h10.trans rfl, h11.trans rfl, h12.trans rfl, h13.trans rfl, fun y hy => ?_, h16, h17, ?_, ?_⟩
    · rw [h14 y hy]
      have : y ≠ "sp.i" := fun e => hy (by simp [e])
      simp [this]
    · simp at h18; omega
    · simp at h19; omega
  exact (hcp t hP).mono (fun r hr => ⟨t, hP, hr⟩)

end AppendAll

end Frontier.CHD.RamSpineU
