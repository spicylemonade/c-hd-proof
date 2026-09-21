import Frontier.RAMRep
import Frontier.RAMWP
import Frontier.CHD.Select

/-!
# Frontier.CHD.SelectRAM — verified RAM selection (BFPRT) with a pluggable key comparison

Owner: agent-05 (COORD G2-5 D5(c), B-L3).  NON-GATE (Layer B).

Elements are word ids in the work array `sel.w`; their keys `κ : ℕ → α` (a linear order) are
compared by a black-box fragment `lessS` (`LessSpec`): `sl.c := [κ sl.x < κ sl.y]`.

This file, stage 1: `countSel` — selection by counting (for every element, count the elements
below it and not above it), `O(n²)` comparisons, used for small inputs and for group medians.
-/

namespace Frontier.RAM.SelectRAM

open Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V}

/-! ## Registers -/

def lessRegs : List String := ["sl.x", "sl.y", "sl.c"]
def csRegs : List String :=
  ["cs.lo", "cs.n", "cs.k", "cs.res", "cs.i", "cs.j", "cs.xi", "cs.lt", "cs.le"]
def selRegs : List String :=
  ["sel.lo", "sel.n", "sel.k", "sel.top", "sel.fp", "sel.res", "sel.go", "sel.g", "sel.m",
    "sel.p", "sel.a", "sel.b", "sel.j", "sel.x"]
/-- all registers written by the selection code itself -/
def myRegs : List String := lessRegs ++ csRegs ++ selRegs

/-! ## Unchanged helpers -/

section Unch

variable {st st' : State V} {wa va wr vr : List String}

@[simp] theorem unch_charge' (k : ℕ) :
    Unchanged st (st'.charge k) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor <;> intro h <;> exact ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩

theorem unch_setW' {x : String} (hx : x ∈ wr) (a : ℕ) :
    Unchanged st (st'.setW x a) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, h.varr, fun y hy => ?_, h.vreg, h.cap, h.procs⟩
    have hne : y ≠ x := fun e => hy (e ▸ hx)
    have := h.wreg y hy
    simp only [State.setW, if_neg hne] at this
    exact this
  · intro h
    refine ⟨h.warr, h.varr, fun y hy => ?_, h.vreg, h.cap, h.procs⟩
    have hne : y ≠ x := fun e => hy (e ▸ hx)
    simp only [State.setW, if_neg hne]
    exact h.wreg y hy

end Unch

/-! ## The comparison interface -/

variable {α : Type*} [LinearOrder α]

/-- `r` differs from `s` at most in the word registers `W` (and the cost). -/
def RegOnly (s r : State V) (W : List String) : Prop :=
  r.wa = s.wa ∧ r.wlen = s.wlen ∧ r.va = s.va ∧ r.vlen = s.vlen ∧ r.v = s.v ∧ r.cap = s.cap ∧
    r.procs = s.procs ∧ ∀ y, y ∉ W → r.w y = s.w y

theorem RegOnly.refl (s : State V) (W : List String) : RegOnly s s W :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem RegOnly.trans {s r t : State V} {W : List String} (h1 : RegOnly s r W) (h2 : RegOnly r t W) :
    RegOnly s t W :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
    fun y hy => (h2.2.2.2.2.2.2.2 y hy).trans (h1.2.2.2.2.2.2.2 y hy)⟩

theorem RegOnly.mono {s r : State V} {W W' : List String} (h : RegOnly s r W) (hW : W ⊆ W') :
    RegOnly s r W' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    fun y hy => h.2.2.2.2.2.2.2 y (fun h' => hy (hW h'))⟩

theorem RegOnly.unch {s r : State V} {W : List String} (h : RegOnly s r W) (wa va vr : List String) :
    Unchanged s r wa va W vr :=
  ⟨fun a _ => ⟨by rw [h.1], by rw [h.2.1]⟩, fun a _ => ⟨by rw [h.2.2.1], by rw [h.2.2.2.1]⟩,
    fun y hy => h.2.2.2.2.2.2.2 y hy, fun y _ => by rw [h.2.2.2.2.1], h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1⟩

/-- Specification of the key comparison fragment `lessS`: from any state satisfying the key
representation `KR` whose two ids satisfy `ok`, it sets `sl.c := [κ sl.x < κ sl.y]`, writes only `sl.c`, its scratch word
registers `lessW` (disjoint from the selection's registers) and value registers `lessV`, no
array, costs at most `Cl`, and keeps `KR`.  `KR` is stable under the selection's own register
writes and under stores into `sel.w`. -/
structure LessSpec (ops : VOps V) (lessS : Stmt) (KR : State V → Prop) (ok : ℕ → Prop) (κ : ℕ → α)
    (Cl : ℕ) (lessW lessV : List String) : Prop where
  run : ∀ st, KR st → ok (st.w "sl.x") → ok (st.w "sl.y") → Runs ops lessS st (fun r =>
    r.w "sl.c" = (if κ (st.w "sl.x") < κ (st.w "sl.y") then 1 else 0) ∧
    Unchanged st r [] [] ("sl.c" :: lessW) lessV ∧ r.cost ≤ st.cost + Cl ∧ KR r)
  /-- `KR` depends neither on `sel.w`'s contents nor on the selection's registers -/
  frame : ∀ s r, KR s → (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) → r.wlen = s.wlen → r.va = s.va →
    r.vlen = s.vlen → r.v = s.v → r.cap = s.cap → r.procs = s.procs →
    (∀ y, y ∉ myRegs → r.w y = s.w y) → KR r
  disj : ∀ x ∈ lessW, x ∉ myRegs

theorem LessSpec.regs {lessS : Stmt} {KR : State V → Prop} {ok : ℕ → Prop} {κ : ℕ → α} {Cl : ℕ}
    {lessW lessV : List String} (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (s r : State V)
    (hK : KR s) (h : RegOnly s r myRegs) : KR r :=
  hL.frame s r hK (fun b _ => by rw [h.1]) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

theorem LessSpec.storeW {lessS : Stmt} {KR : State V → Prop} {ok : ℕ → Prop} {κ : ℕ → α} {Cl : ℕ}
    {lessW lessV : List String} (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (st : State V)
    (i a : ℕ) (hK : KR st) : KR (st.storeW "sel.w" i a) :=
  hL.frame st _ hK (fun b hb => by funext q; simp [State.storeW, hb]) rfl rfl rfl rfl rfl rfl
    (fun _ _ => rfl)

/-! ## Segments and counts -/

/-- the ids in `sel.w[lo, lo + n)` -/
def seg (st : State V) (lo n : ℕ) : List ℕ := (List.range n).map (fun j => st.wa "sel.w" (lo + j))

@[simp] theorem length_seg (st : State V) (lo n : ℕ) : (seg st lo n).length = n := by simp [seg]

/-- number of the first `j` elements with key `< v` -/
def cLt (κ : ℕ → α) (e : ℕ → ℕ) (j : ℕ) (v : α) : ℕ :=
  ((List.range j).map (fun q => κ (e q))).countP (fun y => decide (y < v))

/-- number of the first `j` elements with key `≤ v` -/
def cLe (κ : ℕ → α) (e : ℕ → ℕ) (j : ℕ) (v : α) : ℕ :=
  ((List.range j).map (fun q => κ (e q))).countP (fun y => decide (y ≤ v))

theorem cLt_succ (κ : ℕ → α) (e : ℕ → ℕ) (j : ℕ) (v : α) :
    cLt κ e (j + 1) v = cLt κ e j v + (if κ (e j) < v then 1 else 0) := by
  simp only [cLt, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.countP_append, List.countP_cons, List.countP_nil]
  split_ifs <;> simp_all

theorem cLe_succ (κ : ℕ → α) (e : ℕ → ℕ) (j : ℕ) (v : α) :
    cLe κ e (j + 1) v = cLe κ e j v + (if κ (e j) ≤ v then 1 else 0) := by
  simp only [cLe, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.countP_append, List.countP_cons, List.countP_nil]
  split_ifs <;> simp_all

theorem cLt_le (κ : ℕ → α) (e : ℕ → ℕ) (j : ℕ) (v : α) : cLt κ e j v ≤ j := by
  have := List.countP_le_length (p := fun y => decide (y < v)) (l := (List.range j).map (fun q => κ (e q)))
  simpa [cLt] using this

theorem cLe_le (κ : ℕ → α) (e : ℕ → ℕ) (j : ℕ) (v : α) : cLe κ e j v ≤ j := by
  have := List.countP_le_length (p := fun y => decide (y ≤ v)) (l := (List.range j).map (fun q => κ (e q)))
  simpa [cLe] using this

theorem map_seg (κ : ℕ → α) (st : State V) (lo n : ℕ) :
    (seg st lo n).map κ = (List.range n).map (fun q => κ (st.wa "sel.w" (lo + q))) := by
  simp [seg, List.map_map, Function.comp_def]

/-! ## `countSel` -/

def csA1 : Stmt :=
  seq (wset "sl.x" (load "sel.w" (add (var "cs.lo") (var "cs.j")))) (wset "sl.y" (var "cs.xi"))
def csA2 : Stmt :=
  seq (ite (var "sl.c") (wset "cs.lt" (add (var "cs.lt") (lit 1))) skip)
    (seq (wset "sl.y" (var "sl.x")) (wset "sl.x" (var "cs.xi")))
def csA3 : Stmt :=
  seq (ite (var "sl.c") skip (wset "cs.le" (add (var "cs.le") (lit 1))))
    (wset "cs.j" (add (var "cs.j") (lit 1)))
def csInner (lessS : Stmt) : Stmt := seq csA1 (seq lessS (seq csA2 (seq lessS csA3)))
def csB1 : Stmt :=
  seq (wset "cs.xi" (load "sel.w" (add (var "cs.lo") (var "cs.i"))))
    (seq (wset "cs.lt" (lit 0)) (seq (wset "cs.le" (lit 0)) (wset "cs.j" (lit 0))))
def csB2 : Stmt :=
  seq (ite (lt (var "cs.k") (var "cs.lt")) skip
      (ite (lt (var "cs.k") (var "cs.le")) (wset "cs.res" (var "cs.xi")) skip))
    (wset "cs.i" (add (var "cs.i") (lit 1)))
def csOuter (lessS : Stmt) : Stmt :=
  seq csB1 (seq (.while (lt (var "cs.j") (var "cs.n")) (csInner lessS)) csB2)
/-- **Selection by counting** of the `cs.k`-th smallest (0-indexed) key among the ids
`sel.w[cs.lo, cs.lo + cs.n)`; the result id is left in `cs.res`. -/
def countSel (lessS : Stmt) : Stmt :=
  seq (wset "cs.i" (lit 0)) (.while (lt (var "cs.i") (var "cs.n")) (csOuter lessS))

/-! ### Straight-line pieces -/

theorem fit_one' {cap : ℕ} (h : 1 < cap) : fit cap 1 = some 1 := by simp [fit, h]

theorem csA1_run (s : State V) (hc : s.w "cs.lo" + s.w "cs.j" < s.cap)
    (hl : s.w "cs.lo" + s.w "cs.j" < s.wlen "sel.w") :
    Runs ops csA1 s (fun r => r.w "sl.x" = s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j") ∧
      r.w "sl.y" = s.w "cs.xi" ∧ RegOnly s r ["sl.x", "sl.y"] ∧ r.cost = s.cost + 2) := by
  apply wp_sound
  simp (config := { contextual := true }) [csA1, wp, fit_of_lt hc, hl, RegOnly, State.setW,
    Nat.add_assoc]

theorem csA2_run (s : State V) (h1 : 1 < s.cap) (hlt : s.w "cs.lt" + 1 < s.cap) :
    Runs ops csA2 s (fun r => r.w "cs.lt" = s.w "cs.lt" + (if s.w "sl.c" = 0 then 0 else 1) ∧
      r.w "sl.y" = s.w "sl.x" ∧ r.w "sl.x" = s.w "cs.xi" ∧
      RegOnly s r ["cs.lt", "sl.y", "sl.x"] ∧ r.cost = s.cost + 4) := by
  apply wp_sound
  by_cases hc : s.w "sl.c" = 0
  · simp (config := { contextual := true }) [csA2, wp, hc, RegOnly, State.setW, Nat.add_assoc]
  · simp (config := { contextual := true }) [csA2, wp, hc, fit_of_lt hlt, fit_one' h1, RegOnly,
      State.setW, Nat.add_assoc]

theorem csA3_run (s : State V) (h1 : 1 < s.cap) (hle : s.w "cs.le" + 1 < s.cap)
    (hj : s.w "cs.j" + 1 < s.cap) :
    Runs ops csA3 s (fun r => r.w "cs.le" = s.w "cs.le" + (if s.w "sl.c" = 0 then 1 else 0) ∧
      r.w "cs.j" = s.w "cs.j" + 1 ∧ RegOnly s r ["cs.le", "cs.j"] ∧ r.cost = s.cost + 3) := by
  apply wp_sound
  by_cases hc : s.w "sl.c" = 0
  · simp (config := { contextual := true }) [csA3, wp, hc, fit_of_lt hle, fit_of_lt hj,
      fit_one' h1, RegOnly, State.setW, Nat.add_assoc]
  · simp (config := { contextual := true }) [csA3, wp, hc, fit_of_lt hj, fit_one' h1, RegOnly,
      State.setW, Nat.add_assoc]

/-! ### The inner counting step -/

variable {lessS : Stmt} {KR : State V → Prop} {ok : ℕ → Prop} {κ : ℕ → α} {Cl : ℕ}
  {lessW lessV : List String}

theorem LessSpec.keep (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) {y : String} (hy : y ∈ myRegs)
    (hyc : y ≠ "sl.c") : y ∉ "sl.c" :: lessW := by
  intro hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact hyc h
  · exact hL.disj y h hy

theorem csInner_run (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (s : State V) (hKR : KR s)
    (hokj : ok (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j"))) (hoki : ok (s.w "cs.xi"))
    (h1 : 1 < s.cap) (hc : s.w "cs.lo" + s.w "cs.j" < s.cap)
    (hl : s.w "cs.lo" + s.w "cs.j" < s.wlen "sel.w") (hlt : s.w "cs.lt" + 1 < s.cap)
    (hle : s.w "cs.le" + 1 < s.cap) (hj : s.w "cs.j" + 1 < s.cap) :
    Runs ops (csInner lessS) s (fun r => KR r ∧
      r.w "cs.lt" = s.w "cs.lt" +
        (if κ (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j")) < κ (s.w "cs.xi") then 1 else 0) ∧
      r.w "cs.le" = s.w "cs.le" +
        (if κ (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j")) ≤ κ (s.w "cs.xi") then 1 else 0) ∧
      r.w "cs.j" = s.w "cs.j" + 1 ∧
      Unchanged s r [] [] (["sl.x", "sl.y", "sl.c", "cs.lt", "cs.le", "cs.j"] ++ lessW) lessV ∧
      r.cost ≤ s.cost + 2 * Cl + 9) := by
  set W : List String := ["sl.x", "sl.y", "sl.c", "cs.lt", "cs.le", "cs.j"] ++ lessW with hW
  have hsubL : "sl.c" :: lessW ⊆ W := by
    intro y hy; rcases List.mem_cons.mp hy with h | h
    · rw [h]; simp [hW]
    · simp [hW, h]
  unfold csInner
  apply runs_seq
  refine (csA1_run s hc hl).mono (fun s1 hs1 => ?_)
  obtain ⟨hx1, hy1, hr1, hc1⟩ := hs1
  have hKR1 : KR s1 := hL.regs s s1 hKR (hr1.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [myRegs, lessRegs]))
  have hr1' := hr1
  obtain ⟨-, -, -, -, -, hcap1, -, hw1⟩ := hr1'
  apply runs_seq
  refine (hL.run s1 hKR1 (by rw [hx1]; exact hokj) (by rw [hy1]; exact hoki)).mono (fun s2 hs2 => ?_)
  obtain ⟨hc2, hu2, hcost2, hKR2⟩ := hs2
  have hcap2 : s2.cap = s.cap := by rw [hu2.cap, hcap1]
  have k2 : ∀ y, y ∈ myRegs → y ≠ "sl.c" → s2.w y = s1.w y := fun y hy hyc =>
    hu2.wreg y (hL.keep hy hyc)
  have hlt2 : s2.w "cs.lt" = s.w "cs.lt" := by
    rw [k2 "cs.lt" (by simp [myRegs, csRegs]) (by simp), hw1 "cs.lt" (by simp)]
  have hle2 : s2.w "cs.le" = s.w "cs.le" := by
    rw [k2 "cs.le" (by simp [myRegs, csRegs]) (by simp), hw1 "cs.le" (by simp)]
  have hj2 : s2.w "cs.j" = s.w "cs.j" := by
    rw [k2 "cs.j" (by simp [myRegs, csRegs]) (by simp), hw1 "cs.j" (by simp)]
  have hxi2 : s2.w "cs.xi" = s.w "cs.xi" := by
    rw [k2 "cs.xi" (by simp [myRegs, csRegs]) (by simp), hw1 "cs.xi" (by simp)]
  have hsx2 : s2.w "sl.x" = s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j") := by
    rw [k2 "sl.x" (by simp [myRegs, lessRegs]) (by simp), hx1]
  apply runs_seq
  refine (csA2_run s2 (by rw [hcap2]; exact h1) (by rw [hcap2, hlt2]; exact hlt)).mono
    (fun s3 hs3 => ?_)
  obtain ⟨hlt3, hy3, hx3, hr3, hc3⟩ := hs3
  have hKR3 : KR s3 := hL.regs s2 s3 hKR2 (hr3.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, lessRegs, csRegs]))
  have hr3' := hr3
  obtain ⟨-, -, -, -, -, hcap3, -, hw3⟩ := hr3'
  apply runs_seq
  refine (hL.run s3 hKR3 (by rw [hx3, hxi2]; exact hoki) (by rw [hy3, hsx2]; exact hokj)).mono
    (fun s4 hs4 => ?_)
  obtain ⟨hc4, hu4, hcost4, hKR4⟩ := hs4
  have hcap4 : s4.cap = s.cap := by rw [hu4.cap, hcap3, hcap2]
  have k4 : ∀ y, y ∈ myRegs → y ≠ "sl.c" → s4.w y = s3.w y := fun y hy hyc =>
    hu4.wreg y (hL.keep hy hyc)
  have hle4 : s4.w "cs.le" = s.w "cs.le" := by
    rw [k4 "cs.le" (by simp [myRegs, csRegs]) (by simp), hw3 "cs.le" (by simp), hle2]
  have hj4 : s4.w "cs.j" = s.w "cs.j" := by
    rw [k4 "cs.j" (by simp [myRegs, csRegs]) (by simp), hw3 "cs.j" (by simp), hj2]
  refine (csA3_run s4 (by rw [hcap4]; exact h1) (by rw [hcap4, hle4]; exact hle)
    (by rw [hcap4, hj4]; exact hj)).mono (fun r hr => ?_)
  obtain ⟨hle5, hj5, hr5, hc5⟩ := hr
  have hKR5 : KR r := hL.regs s4 r hKR4 (hr5.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [myRegs, csRegs]))
  have hr5' := hr5
  obtain ⟨-, -, -, -, -, -, -, hw5⟩ := hr5'
  -- the two comparison bits
  have hc4' : s4.w "sl.c" = if κ (s.w "cs.xi") < κ (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j"))
      then 1 else 0 := by
    rw [hc4, hx3, hy3, hxi2, hsx2]
  have hc2' : s2.w "sl.c" = if κ (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j")) < κ (s.w "cs.xi")
      then 1 else 0 := by
    rw [hc2, hx1, hy1]
  refine ⟨hKR5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw5 "cs.lt" (by simp), k4 "cs.lt" (by simp [myRegs, csRegs]) (by simp), hlt3, hlt2, hc2']
    split_ifs <;> simp_all
  · rw [hle5, hle4, hc4']
    by_cases h : κ (s.w "cs.xi") < κ (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j"))
    · have : ¬ κ (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j")) ≤ κ (s.w "cs.xi") := not_le.mpr h
      simp [h, this]
    · have : κ (s.wa "sel.w" (s.w "cs.lo" + s.w "cs.j")) ≤ κ (s.w "cs.xi") := not_lt.mp h
      simp [h, this]
  · rw [hj5, hj4]
  · have u1 : Unchanged s s1 [] [] W lessV := (hr1.unch [] [] lessV).mono (List.Subset.refl _)
      (List.Subset.refl _) (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hW])
      (List.Subset.refl _)
    have u2 : Unchanged s1 s2 [] [] W lessV := hu2.mono (List.Subset.refl _) (List.Subset.refl _)
      hsubL (List.Subset.refl _)
    have u3 : Unchanged s2 s3 [] [] W lessV := (hr3.unch [] [] lessV).mono (List.Subset.refl _)
      (List.Subset.refl _) (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [hW])
      (List.Subset.refl _)
    have u4 : Unchanged s3 s4 [] [] W lessV := hu4.mono (List.Subset.refl _) (List.Subset.refl _)
      hsubL (List.Subset.refl _)
    have u5 : Unchanged s4 r [] [] W lessV := (hr5.unch [] [] lessV).mono (List.Subset.refl _)
      (List.Subset.refl _) (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hW])
      (List.Subset.refl _)
    exact u1.trans (u2.trans (u3.trans (u4.trans u5)))
  · omega

/-! ### The inner loop -/

/-- write set of the inner loop -/
def innerW (lessW : List String) : List String :=
  ["sl.x", "sl.y", "sl.c", "cs.lt", "cs.le", "cs.j"] ++ lessW

theorem RegOnly.charge (s : State V) (k : ℕ) (W : List String) : RegOnly s (s.charge k) W :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem csLoop_run (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (s0 : State V) (hKR : KR s0)
    (hok : ∀ q, q < s0.w "cs.n" → ok (s0.wa "sel.w" (s0.w "cs.lo" + q))) (hoxi : ok (s0.w "cs.xi"))
    (hj0 : s0.w "cs.j" = 0) (hlt0 : s0.w "cs.lt" = 0) (hle0 : s0.w "cs.le" = 0)
    (hcap : s0.w "cs.lo" + s0.w "cs.n" + 1 < s0.cap)
    (hlen : s0.w "cs.lo" + s0.w "cs.n" ≤ s0.wlen "sel.w") :
    Runs ops (.while (lt (var "cs.j") (var "cs.n")) (csInner lessS)) s0 (fun r => KR r ∧
      r.w "cs.lt" = cLt κ (fun q => s0.wa "sel.w" (s0.w "cs.lo" + q)) (s0.w "cs.n") (κ (s0.w "cs.xi")) ∧
      r.w "cs.le" = cLe κ (fun q => s0.wa "sel.w" (s0.w "cs.lo" + q)) (s0.w "cs.n") (κ (s0.w "cs.xi")) ∧
      Unchanged s0 r [] [] (innerW lessW) lessV ∧
      r.cost ≤ s0.cost + s0.w "cs.n" * (2 * Cl + 10) + 1) := by
  set n := s0.w "cs.n" with hn
  set lo := s0.w "cs.lo" with hlo
  set e : ℕ → ℕ := fun q => s0.wa "sel.w" (lo + q) with he
  set xi := s0.w "cs.xi" with hxi
  have hnot : ∀ y, y ∈ ["cs.n", "cs.lo", "cs.xi", "cs.k", "cs.i", "cs.res"] → y ∉ innerW lessW := by
    intro y hy hmem
    simp only [innerW, List.mem_append] at hmem
    rcases hmem with h | h
    · simp at hy h; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h
    · exact hL.disj y h (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [myRegs, csRegs])
  refine runs_while (fun k st => KR st ∧ st.w "cs.j" = k ∧ st.w "cs.lt" = cLt κ e k (κ xi) ∧
      st.w "cs.le" = cLe κ e k (κ xi) ∧ Unchanged s0 st [] [] (innerW lessW) lessV ∧
      st.cost ≤ s0.cost + k * (2 * Cl + 10)) n _ ?_ ?_ s0
    ⟨hKR, hj0, by simp [hlt0, cLt], by simp [hle0, cLe], Unchanged.refl _ _ _ _ _, by simp⟩
  · intro k hk st ⟨hK, hj, hlt, hle, hu, hc⟩
    have hcs : st.cap = s0.cap := hu.cap
    have hwa : st.wa "sel.w" = s0.wa "sel.w" := (hu.warr "sel.w" (by simp)).1
    have hwl : st.wlen "sel.w" = s0.wlen "sel.w" := (hu.warr "sel.w" (by simp)).2
    have hnst : st.w "cs.n" = n := hu.wreg "cs.n" (hnot _ (by simp))
    have hlost : st.w "cs.lo" = lo := hu.wreg "cs.lo" (hnot _ (by simp))
    have hxist : st.w "cs.xi" = xi := hu.wreg "cs.xi" (hnot _ (by simp))
    have h1 : 1 < st.cap := by rw [hcs]; omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl h1, hj, hnst, if_pos hk]
    · have hKc : KR (st.charge 1) := hL.regs _ _ hK (RegOnly.charge st 1 myRegs)
      have cltk := cLt_le κ e k (κ xi)
      have clek := cLe_le κ e k (κ xi)
      refine (csInner_run hL (st.charge 1) hKc
        (by simp only [State.charge_wa, State.charge_w]; rw [hlost, hj, hwa]; exact hok k (by omega))
        (by simp only [State.charge_w]; rw [hxist]; exact hoxi) (by simpa using h1)
        (by simp [hlost, hj, hcs]; omega) (by simp [hlost, hj, hwl]; omega)
        (by simp [hlt, hcs]; omega) (by simp [hle, hcs]; omega) (by simp [hj, hcs]; omega)).mono
        (fun r ⟨hKr, hltr, hler, hjr, hur, hcr⟩ => ?_)
      simp only [State.charge_w, State.charge_wa] at hltr hler hjr
      simp only [hlost, hj, hwa, hxist] at hltr hler
      rw [hj] at hjr
      refine ⟨hKr, hjr, ?_, ?_, ?_, ?_⟩
      · rw [hltr, hlt, cLt_succ]
      · rw [hler, hle, cLe_succ]
      · exact hu.trans ((Unchanged.charge st 1 [] [] (innerW lessW) lessV).trans hur)
      · simp only [State.charge_cost] at hcr
        rw [Nat.succ_mul]; omega
  · intro st ⟨hK, hj, hlt, hle, hu, hc⟩
    have hcs : st.cap = s0.cap := hu.cap
    have hnst : st.w "cs.n" = n := hu.wreg "cs.n" (hnot _ (by simp))
    have h1 : 1 < st.cap := by rw [hcs]; omega
    refine ⟨by rw [evalW_lt_of rfl rfl h1, hj, hnst, if_neg (lt_irrefl _)], ?_⟩
    refine ⟨hL.regs _ _ hK (RegOnly.charge st 1 myRegs), by simpa using hlt, by simpa using hle,
      by simpa using hu, by simp; omega⟩

/-! ### The outer step -/

theorem csB1_run (s : State V) (h0 : 0 < s.cap) (hc : s.w "cs.lo" + s.w "cs.i" < s.cap)
    (hl : s.w "cs.lo" + s.w "cs.i" < s.wlen "sel.w") :
    Runs ops csB1 s (fun r => r.w "cs.xi" = s.wa "sel.w" (s.w "cs.lo" + s.w "cs.i") ∧
      r.w "cs.lt" = 0 ∧ r.w "cs.le" = 0 ∧ r.w "cs.j" = 0 ∧
      RegOnly s r ["cs.xi", "cs.lt", "cs.le", "cs.j"] ∧ r.cost = s.cost + 4) := by
  apply wp_sound
  simp (config := { contextual := true }) [csB1, wp, fit_of_lt hc, fit_of_lt h0, hl, RegOnly,
    State.setW, Nat.add_assoc]

theorem csB2_run (s : State V) (h1 : 1 < s.cap) (hi : s.w "cs.i" + 1 < s.cap) :
    Runs ops csB2 s (fun r =>
      r.w "cs.res" = (if ¬ s.w "cs.k" < s.w "cs.lt" ∧ s.w "cs.k" < s.w "cs.le" then s.w "cs.xi"
        else s.w "cs.res") ∧
      r.w "cs.i" = s.w "cs.i" + 1 ∧ RegOnly s r ["cs.res", "cs.i"] ∧ r.cost ≤ s.cost + 5) := by
  apply wp_sound
  have h0 : 0 < s.cap := by omega
  by_cases ha : s.w "cs.k" < s.w "cs.lt"
  · simp (config := { contextual := true }) [csB2, wp, ha, fit_of_lt hi, fit_of_lt h0,
      fit_one' h1, RegOnly, State.setW, Nat.add_assoc]
  · by_cases hb : s.w "cs.k" < s.w "cs.le"
    · simp (config := { contextual := true }) [csB2, wp, ha, hb, fit_of_lt h0,
        fit_of_lt hi, fit_one' h1, RegOnly, State.setW, Nat.add_assoc]
    · simp (config := { contextual := true }) [csB2, wp, ha, hb, fit_of_lt h0,
        fit_of_lt hi, fit_one' h1, RegOnly, State.setW, Nat.add_assoc]

/-! ### The outer loop and the spec of `countSel` -/

/-- write set of `countSel` -/
def csW (lessW : List String) : List String :=
  ["sl.x", "sl.y", "sl.c", "cs.lt", "cs.le", "cs.j", "cs.xi", "cs.res", "cs.i"] ++ lessW

theorem innerW_sub_csW (lessW : List String) : innerW lessW ⊆ csW lessW := by
  intro y hy
  simp only [innerW, csW, List.mem_append, List.mem_cons, List.not_mem_nil] at hy ⊢
  tauto

theorem csW_not (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) :
    ∀ y, y ∈ ["cs.n", "cs.lo", "cs.k"] → y ∉ csW lessW := by
  intro y hy hmem
  simp only [csW, List.mem_append] at hmem
  rcases hmem with h | h
  · simp at hy h; rcases hy with rfl | rfl | rfl <;> simp at h
  · exact hL.disj y h (by simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, csRegs])

theorem csLoop_regs {y : String} (hy : y ∈ ["cs.n", "cs.lo", "cs.k", "cs.i", "cs.res", "cs.xi"])
    (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) : y ∉ innerW lessW := by
  intro hmem
  simp only [innerW, List.mem_append] at hmem
  rcases hmem with h | h
  · simp at hy h; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h
  · exact hL.disj y h (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [myRegs, csRegs])

/-- **Spec of `countSel`.**  For `cs.k < cs.n`, the result `cs.res` is an id of the segment whose
key is a `cs.k`-th smallest key of the segment (`Select.IsKth`); only `csW` and `lessV` are written;
the cost is at most `n (n (2 Cl + 10) + 12) + 2`. -/
theorem countSel_spec (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (st : State V) (hKR : KR st)
    (hok : ∀ x ∈ seg st (st.w "cs.lo") (st.w "cs.n"), ok x)
    (hk : st.w "cs.k" < st.w "cs.n") (hcap : st.w "cs.lo" + st.w "cs.n" + 1 < st.cap)
    (hlen : st.w "cs.lo" + st.w "cs.n" ≤ st.wlen "sel.w") :
    Runs ops (countSel lessS) st (fun r => KR r ∧
      r.w "cs.res" ∈ seg st (st.w "cs.lo") (st.w "cs.n") ∧
      Frontier.CHD.IsKth ((seg st (st.w "cs.lo") (st.w "cs.n")).map κ) (st.w "cs.k")
        (κ (r.w "cs.res")) ∧
      Unchanged st r [] [] (csW lessW) lessV ∧
      r.cost ≤ st.cost + 2 + st.w "cs.n" * (st.w "cs.n" * (2 * Cl + 10) + 12)) := by
  set n := st.w "cs.n" with hn
  set lo := st.w "cs.lo" with hlo
  set k := st.w "cs.k" with hkdef
  set e : ℕ → ℕ := fun q => st.wa "sel.w" (lo + q) with he
  let Match : ℕ → Prop := fun j => cLt κ e n (κ (e j)) ≤ k ∧ k < cLe κ e n (κ (e j))
  have h1 : 1 < st.cap := by omega
  have h0 : 0 < st.cap := by omega
  unfold countSel
  apply runs_seq
  refine runs_wset (a := 0) (evalW_lit_of h0) ?_
  set s0 := (st.setW "cs.i" 0).charge 1 with hs0
  have hr0 : RegOnly st s0 ["cs.i"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_singleton] at hy
    simp [hs0, State.setW, hy]
  have hK0 : KR s0 := hL.regs _ _ hKR (hr0.mono (by simp [myRegs, csRegs]))
  refine runs_while (fun i s => KR s ∧ s.w "cs.i" = i ∧ Unchanged st s [] [] (csW lessW) lessV ∧
      ((∃ j < i, Match j) → ∃ j < i, Match j ∧ s.w "cs.res" = e j) ∧
      s.cost ≤ st.cost + 1 + i * (n * (2 * Cl + 10) + 12)) n _ ?_ ?_ s0
    ⟨hK0, by simp [hs0], (hr0.unch [] [] lessV).mono (List.Subset.refl _) (List.Subset.refl _)
      (by simp [csW]) (List.Subset.refl _), fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j),
      by simp [hs0]⟩
  · intro i hi s ⟨hK, hsi, hu, hres, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hwa : s.wa "sel.w" = st.wa "sel.w" := (hu.warr "sel.w" (by simp)).1
    have hwl : s.wlen "sel.w" = st.wlen "sel.w" := (hu.warr "sel.w" (by simp)).2
    have hns : s.w "cs.n" = n := hu.wreg "cs.n" (csW_not hL _ (by simp))
    have hlos : s.w "cs.lo" = lo := hu.wreg "cs.lo" (csW_not hL _ (by simp))
    have hks : s.w "cs.k" = k := hu.wreg "cs.k" (csW_not hL _ (by simp))
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl h1s, hsi, hns, if_pos hi]
    · unfold csOuter
      apply runs_seq
      refine (csB1_run (s.charge 1) (by simp [hcs]; exact h0) (by simp [hlos, hsi, hcs]; omega)
        (by simp [hlos, hsi, hwl]; omega)).mono (fun s1 ⟨hxi1, hlt1, hle1, hj1, hr1, hc1⟩ => ?_)
      have hK1 : KR s1 := hL.regs _ _ (hL.regs _ _ hK (RegOnly.charge s 1 myRegs))
        (hr1.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [myRegs, csRegs]))
      have hr1' := hr1
      obtain ⟨hwa1, hwl1, -, -, -, hcap1, -, hw1⟩ := hr1'
      simp only [State.charge_w, State.charge_wa] at hxi1
      have hns1 : s1.w "cs.n" = n := by rw [hw1 "cs.n" (by simp)]; simpa using hns
      have hlos1 : s1.w "cs.lo" = lo := by rw [hw1 "cs.lo" (by simp)]; simpa using hlos
      have hks1 : s1.w "cs.k" = k := by rw [hw1 "cs.k" (by simp)]; simpa using hks
      have his1 : s1.w "cs.i" = i := by rw [hw1 "cs.i" (by simp)]; simpa using hsi
      have hres1 : s1.w "cs.res" = s.w "cs.res" := by rw [hw1 "cs.res" (by simp)]; simp
      have hwa1' : s1.wa "sel.w" = st.wa "sel.w" := by rw [hwa1]; simpa using hwa
      have hwl1' : s1.wlen "sel.w" = st.wlen "sel.w" := by rw [hwl1]; simpa using hwl
      have hcap1' : s1.cap = st.cap := by rw [hcap1]; simpa using hcs
      have hokq : ∀ q, q < s1.w "cs.n" → ok (s1.wa "sel.w" (s1.w "cs.lo" + q)) := by
        intro q hq
        rw [hns1] at hq
        rw [hwa1', hlos1]
        exact hok _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
      have hoxi : ok (s1.w "cs.xi") := by
        rw [hxi1, hlos, hsi, hwa]
        exact hok _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      apply runs_seq
      refine (csLoop_run hL s1 hK1 hokq hoxi hj1 hlt1 hle1 (by rw [hlos1, hns1, hcap1']; exact hcap)
        (by rw [hlos1, hns1, hwl1']; exact hlen)).mono
        (fun s2 ⟨hK2, hlt2, hle2, hu2, hc2⟩ => ?_)
      have hns2 : s2.w "cs.n" = n := by rw [hu2.wreg "cs.n" (csLoop_regs (by simp) hL), hns1]
      have hks2 : s2.w "cs.k" = k := by rw [hu2.wreg "cs.k" (csLoop_regs (by simp) hL), hks1]
      have his2 : s2.w "cs.i" = i := by rw [hu2.wreg "cs.i" (csLoop_regs (by simp) hL), his1]
      have hres2 : s2.w "cs.res" = s.w "cs.res" := by
        rw [hu2.wreg "cs.res" (csLoop_regs (by simp) hL), hres1]
      have hxi2 : s2.w "cs.xi" = e i := by
        rw [hu2.wreg "cs.xi" (csLoop_regs (by simp) hL), hxi1, hlos, hsi, hwa]
      have hcap2 : s2.cap = st.cap := by rw [hu2.cap, hcap1']
      simp only [hlos1, hns1, hwa1', hxi1, hlos, hsi, hwa] at hlt2 hle2
      refine (csB2_run s2 (by rw [hcap2]; exact h1) (by rw [his2, hcap2]; omega)).mono
        (fun r ⟨hresr, hir, hrr, hcr⟩ => ?_)
      have hKr : KR r := hL.regs _ _ hK2 (hrr.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [myRegs, csRegs]))
      have hr' := hrr
      obtain ⟨-, -, -, -, -, -, -, hwr⟩ := hr'
      refine ⟨hKr, by rw [hir, his2], ?_, ?_, ?_⟩
      · have u1 : Unchanged s (s.charge 1) [] [] (csW lessW) lessV := Unchanged.charge _ _ _ _ _ _
        have u2 : Unchanged (s.charge 1) s1 [] [] (csW lessW) lessV := (hr1.unch [] [] lessV).mono
          (List.Subset.refl _) (List.Subset.refl _) (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [csW]) (List.Subset.refl _)
        have u3 : Unchanged s1 s2 [] [] (csW lessW) lessV := hu2.mono (List.Subset.refl _)
          (List.Subset.refl _) (innerW_sub_csW lessW) (List.Subset.refl _)
        have u4 : Unchanged s2 r [] [] (csW lessW) lessV := (hrr.unch [] [] lessV).mono
          (List.Subset.refl _) (List.Subset.refl _) (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [csW]) (List.Subset.refl _)
        exact hu.trans (u1.trans (u2.trans (u3.trans u4)))
      · intro ⟨j, hj, hmj⟩
        rw [hresr, hks2, hlt2, hle2, hxi2]
        by_cases hmi : Match i
        · refine ⟨i, by omega, hmi, ?_⟩
          rw [if_pos ⟨not_lt.mpr hmi.1, hmi.2⟩]
        · have hji : j < i := by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
            · exact h
            · exact absurd (h ▸ hmj) hmi
          obtain ⟨j', hj', hmj', hrj'⟩ := hres ⟨j, hji, hmj⟩
          refine ⟨j', by omega, hmj', ?_⟩
          rw [if_neg (fun h => hmi ⟨not_lt.mp h.1, h.2⟩), hres2, hrj']
      · simp only [State.charge_cost] at hc1
        rw [hns1] at hc2
        rw [Nat.succ_mul]
        omega
  · intro s ⟨hK, hsi, hu, hres, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hns : s.w "cs.n" = n := hu.wreg "cs.n" (csW_not hL _ (by simp))
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    refine ⟨by rw [evalW_lt_of rfl rfl h1s, hsi, hns, if_neg (lt_irrefl _)], ?_⟩
    -- a `k`-th element exists
    set l : List α := (seg st lo n).map κ with hl
    have hl' : l = (List.range n).map (fun q => κ (e q)) := map_seg κ st lo n
    have hkl : k < l.length := by simp [hl]; exact hk
    obtain ⟨v, hsel⟩ : ∃ v, Frontier.CHD.IsKth l k v := ⟨_, Frontier.CHD.isKth_sortC l hkl⟩
    obtain ⟨hmem, hlt, hle⟩ := hsel
    rw [hl'] at hmem
    obtain ⟨j0, hj0, hj0e⟩ := List.mem_map.mp hmem
    rw [List.mem_range] at hj0
    have hcnt : ∀ x, Frontier.CHD.cntLt l x = cLt κ e n x ∧ Frontier.CHD.cntLe l x = cLe κ e n x := by
      intro x; rw [hl']; exact ⟨rfl, rfl⟩
    have hm0 : Match j0 := by
      refine ⟨?_, ?_⟩
      · rw [← (hcnt _).1, hj0e]; exact hlt
      · rw [← (hcnt _).2, hj0e]; exact hle
    obtain ⟨j, hj, hmj, hrj⟩ := hres ⟨j0, hj0, hm0⟩
    refine ⟨hL.regs _ _ hK (RegOnly.charge s 1 myRegs), ?_, ?_, by simpa using hu, by simp; omega⟩
    · simp only [State.charge_w, hrj, seg]
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    · simp only [State.charge_w, hrj]
      refine ⟨?_, ?_, ?_⟩
      · rw [hl']; exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      · rw [(hcnt _).1]; exact hmj.1
      · rw [(hcnt _).2]; exact hmj.2

/-! ## Filter passes (partition by copying)

`filt lessS gt cnt` copies, in order, the ids `x` of `sel.w[sel.lo, sel.lo + sel.n)` with
`κ x < κ p` (`gt = false`) or `κ p < κ x` (`gt = true`), `p = sel.p`, to `sel.w[sel.m, …)`, and
leaves their number in `cnt ∈ {sel.a, sel.b}`. -/

def fA (gt : Bool) : Stmt :=
  seq (wset "sel.x" (load "sel.w" (add (var "sel.lo") (var "sel.j"))))
    (if gt then seq (wset "sl.x" (var "sel.p")) (wset "sl.y" (var "sel.x"))
     else seq (wset "sl.x" (var "sel.x")) (wset "sl.y" (var "sel.p")))
def fB (cnt : String) : Stmt :=
  seq (ite (var "sl.c")
      (seq (wstore "sel.w" (add (var "sel.m") (var cnt)) (var "sel.x"))
        (wset cnt (add (var cnt) (lit 1))))
      skip)
    (wset "sel.j" (add (var "sel.j") (lit 1)))
def fBody (lessS : Stmt) (gt : Bool) (cnt : String) : Stmt := seq (fA gt) (seq lessS (fB cnt))
def filt (lessS : Stmt) (gt : Bool) (cnt : String) : Stmt :=
  seq (wset "sel.j" (lit 0)) (seq (wset cnt (lit 0))
    (.while (lt (var "sel.j") (var "sel.n")) (fBody lessS gt cnt)))

def fBGe (cnt : String) : Stmt :=
  seq (ite (var "sl.c") skip
      (seq (wstore "sel.w" (add (var "sel.m") (var cnt)) (var "sel.x"))
        (wset cnt (add (var cnt) (lit 1)))))
    (wset "sel.j" (add (var "sel.j") (lit 1)))
def fBodyGe (lessS : Stmt) (cnt : String) : Stmt := seq (fA false) (seq lessS (fBGe cnt))
/-- `filtGe lessS cnt` copies, in order, the ids `x` with `κ p ≤ κ x` (`p = sel.p`). -/
def filtGe (lessS : Stmt) (cnt : String) : Stmt :=
  seq (wset "sel.j" (lit 0)) (seq (wset cnt (lit 0))
    (.while (lt (var "sel.j") (var "sel.n")) (fBodyGe lessS cnt)))

/-- the filter predicate of a pass -/
def fP (κ : ℕ → α) (gt : Bool) (p x : ℕ) : Prop := if gt then κ p < κ x else κ x < κ p

instance (κ : ℕ → α) (gt : Bool) (p x : ℕ) : Decidable (fP κ gt p x) := by
  unfold fP; split <;> infer_instance

theorem fA_run (gt : Bool) (s : State V) (hc : s.w "sel.lo" + s.w "sel.j" < s.cap)
    (hl : s.w "sel.lo" + s.w "sel.j" < s.wlen "sel.w") :
    Runs ops (fA gt) s (fun r => r.w "sel.x" = s.wa "sel.w" (s.w "sel.lo" + s.w "sel.j") ∧
      r.w "sl.x" = (if gt then s.w "sel.p" else s.wa "sel.w" (s.w "sel.lo" + s.w "sel.j")) ∧
      r.w "sl.y" = (if gt then s.wa "sel.w" (s.w "sel.lo" + s.w "sel.j") else s.w "sel.p") ∧
      RegOnly s r ["sel.x", "sl.x", "sl.y"] ∧ r.cost = s.cost + 3) := by
  apply wp_sound
  cases gt
  · simp (config := { contextual := true }) [fA, wp, fit_of_lt hc, hl, RegOnly, State.setW,
      Nat.add_assoc]
  · simp (config := { contextual := true }) [fA, wp, fit_of_lt hc, hl, RegOnly, State.setW,
      Nat.add_assoc]

theorem fB_run (cnt : String) (hcnt : cnt ∈ ["sel.a", "sel.b"]) (s : State V) (h1 : 1 < s.cap)
    (hj : s.w "sel.j" + 1 < s.cap) (hcp : s.w cnt + 1 < s.cap)
    (hm : s.w "sel.m" + s.w cnt < s.cap) (hml : s.w "sel.m" + s.w cnt < s.wlen "sel.w") :
    Runs ops (fB cnt) s (fun r =>
      (∀ q, r.wa "sel.w" q = if s.w "sl.c" ≠ 0 ∧ q = s.w "sel.m" + s.w cnt then s.w "sel.x"
        else s.wa "sel.w" q) ∧
      (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) ∧ r.wlen = s.wlen ∧ r.va = s.va ∧ r.vlen = s.vlen ∧
      r.v = s.v ∧ r.cap = s.cap ∧ r.procs = s.procs ∧
      r.w cnt = s.w cnt + (if s.w "sl.c" = 0 then 0 else 1) ∧ r.w "sel.j" = s.w "sel.j" + 1 ∧
      (∀ y, y ≠ cnt → y ≠ "sel.j" → r.w y = s.w y) ∧ r.cost ≤ s.cost + 5) := by
  have hcj : cnt ≠ "sel.j" := by simp at hcnt; rcases hcnt with rfl | rfl <;> simp
  have hjc : "sel.j" ≠ cnt := Ne.symm hcj
  apply wp_sound
  by_cases hc : s.w "sl.c" = 0
  · simp (config := { contextual := true }) [fB, wp, hc, fit_of_lt hj, fit_one' h1, State.setW,
      Nat.add_assoc, hcj, hjc]
  · have hj' : fit s.cap (s.w "sel.j" + 1) = some (s.w "sel.j" + 1) := fit_of_lt hj
    simp (config := { contextual := true }) [fB, wp, hc, fit_one' h1,
      fit_of_lt hm, fit_of_lt hcp, hml, State.setW, State.storeW, Nat.add_assoc, hcj, hjc, hj']

theorem fBGe_run (cnt : String) (hcnt : cnt ∈ ["sel.a", "sel.b"]) (s : State V) (h1 : 1 < s.cap)
    (hj : s.w "sel.j" + 1 < s.cap) (hcp : s.w cnt + 1 < s.cap)
    (hm : s.w "sel.m" + s.w cnt < s.cap) (hml : s.w "sel.m" + s.w cnt < s.wlen "sel.w") :
    Runs ops (fBGe cnt) s (fun r =>
      (∀ q, r.wa "sel.w" q = if s.w "sl.c" = 0 ∧ q = s.w "sel.m" + s.w cnt then s.w "sel.x"
        else s.wa "sel.w" q) ∧
      (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) ∧ r.wlen = s.wlen ∧ r.va = s.va ∧ r.vlen = s.vlen ∧
      r.v = s.v ∧ r.cap = s.cap ∧ r.procs = s.procs ∧
      r.w cnt = s.w cnt + (if s.w "sl.c" = 0 then 1 else 0) ∧ r.w "sel.j" = s.w "sel.j" + 1 ∧
      (∀ y, y ≠ cnt → y ≠ "sel.j" → r.w y = s.w y) ∧ r.cost ≤ s.cost + 5) := by
  have hcj : cnt ≠ "sel.j" := by simp at hcnt; rcases hcnt with rfl | rfl <;> simp
  have hjc : "sel.j" ≠ cnt := Ne.symm hcj
  apply wp_sound
  by_cases hc : s.w "sl.c" = 0
  · have hj' : fit s.cap (s.w "sel.j" + 1) = some (s.w "sel.j" + 1) := fit_of_lt hj
    simp (config := { contextual := true }) [fBGe, wp, hc, fit_one' h1,
      fit_of_lt hm, fit_of_lt hcp, hml, State.setW, State.storeW, Nat.add_assoc, hcj, hjc, hj']
  · simp (config := { contextual := true }) [fBGe, wp, hc, fit_of_lt hj, fit_one' h1, State.setW,
      Nat.add_assoc, hcj, hjc]

/-- write set of a filter pass -/
def filtW (cnt : String) (lessW : List String) : List String :=
  ["sel.j", cnt, "sel.x", "sl.x", "sl.y", "sl.c"] ++ lessW

theorem filt_keep (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) {cnt : String}
    (hcnt : cnt ∈ ["sel.a", "sel.b"]) {y : String}
    (hy : y ∈ ["sel.lo", "sel.n", "sel.m", "sel.p", "sel.top", "sel.a", "sel.k", "sel.fp"])
    (hyc : y ≠ cnt) : y ∉ filtW cnt lessW := by
  intro hmem
  simp only [filtW, List.mem_append] at hmem
  rcases hmem with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h
    · subst h; simp at hy
    · exact hyc h
    all_goals (subst h; simp at hy)
  · exact hL.disj y h (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [myRegs, selRegs])

theorem getD_append_single_of_lt {l : List ℕ} {x : ℕ} {i : ℕ} (h : i < l.length) :
    (l ++ [x]).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_single_len {l : List ℕ} {x : ℕ} : (l ++ [x]).getD l.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

set_option maxHeartbeats 2000000 in
/-- **Spec of a filter pass.** -/
theorem filt_spec (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (gt : Bool) (cnt : String)
    (hcnt : cnt ∈ ["sel.a", "sel.b"]) (st : State V) (hKR : KR st)
    (hok : ∀ x ∈ seg st (st.w "sel.lo") (st.w "sel.n"), ok x) (hokp : ok (st.w "sel.p"))
    (hov : st.w "sel.lo" + st.w "sel.n" ≤ st.w "sel.m")
    (hlen : st.w "sel.m" + st.w "sel.n" ≤ st.wlen "sel.w")
    (hcap : st.w "sel.m" + st.w "sel.n" + 1 < st.cap) :
    Runs ops (filt lessS gt cnt) st (fun r => KR r ∧
      seg r (st.w "sel.m") (r.w cnt) =
        (seg st (st.w "sel.lo") (st.w "sel.n")).filter (fun x => decide (fP κ gt (st.w "sel.p") x)) ∧
      (∀ q, (q < st.w "sel.m" ∨ st.w "sel.m" + st.w "sel.n" ≤ q) → r.wa "sel.w" q = st.wa "sel.w" q) ∧
      r.wlen "sel.w" = st.wlen "sel.w" ∧
      Unchanged st r ["sel.w"] [] (filtW cnt lessW) lessV ∧
      r.cost ≤ st.cost + 3 + st.w "sel.n" * (Cl + 10)) := by
  set n := st.w "sel.n" with hn
  set lo := st.w "sel.lo" with hlo
  set m := st.w "sel.m" with hm
  set p := st.w "sel.p" with hp
  set e : ℕ → ℕ := fun q => st.wa "sel.w" (lo + q) with he
  let F : ℕ → List ℕ := fun j => ((List.range j).map e).filter (fun x => decide (fP κ gt p x))
  have hFs : ∀ j, F (j + 1) = F j ++ (if fP κ gt p (e j) then [e j] else []) := by
    intro j
    simp only [F, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.filter_append, List.filter_cons, List.filter_nil]
    split_ifs <;> simp_all
  have hFl : ∀ j, (F j).length ≤ j := by
    intro j
    have := List.length_filter_le (fun x => decide (fP κ gt p x)) ((List.range j).map e)
    simpa [F] using this
  have hcj : cnt ≠ "sel.j" := by simp at hcnt; rcases hcnt with rfl | rfl <;> simp
  have h1 : 1 < st.cap := by omega
  have h0 : 0 < st.cap := by omega
  have hcntW : cnt ∈ filtW cnt lessW := by simp [filtW]
  have hjW : "sel.j" ∈ filtW cnt lessW := by simp [filtW]
  unfold filt
  apply runs_seq
  refine runs_wset (a := 0) (evalW_lit_of h0) ?_
  apply runs_seq
  refine runs_wset (a := 0) (evalW_lit_of (by simpa using h0)) ?_
  set s0 := (((st.setW "sel.j" 0).charge 1).setW cnt 0).charge 1 with hs0
  have hr0 : RegOnly st s0 ["sel.j", cnt] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hs0, State.setW, hy.1, hy.2]
  have hK0 : KR s0 := hL.regs _ _ hKR (hr0.mono (by
    intro y hy; simp at hy; rcases hy with rfl | rfl
    · simp [myRegs, selRegs]
    · simp at hcnt; rcases hcnt with rfl | rfl <;> simp [myRegs, selRegs]))
  refine runs_while (fun j s => KR s ∧ s.w "sel.j" = j ∧ s.w cnt = (F j).length ∧
      (∀ q, s.wa "sel.w" q = if m ≤ q ∧ q < m + (F j).length then (F j).getD (q - m) 0
        else st.wa "sel.w" q) ∧
      Unchanged st s ["sel.w"] [] (filtW cnt lessW) lessV ∧ s.wlen "sel.w" = st.wlen "sel.w" ∧
      s.cost ≤ st.cost + 2 + j * (Cl + 10)) n _ ?_ ?_ s0 ?_
  · intro j hj s ⟨hK, hsj, hsc, harr, hu, hwl, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hks : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.m", "sel.p"] → s.w y = st.w y := by
      intro y hy
      refine hu.wreg y (filt_keep hL hcnt (by simp at hy ⊢; tauto) ?_)
      simp at hy hcnt
      rcases hy with rfl | rfl | rfl | rfl <;> rcases hcnt with rfl | rfl <;> simp
    have hns : s.w "sel.n" = n := hks "sel.n" (by simp)
    have hlos : s.w "sel.lo" = lo := hks "sel.lo" (by simp)
    have hms : s.w "sel.m" = m := hks "sel.m" (by simp)
    have hps : s.w "sel.p" = p := hks "sel.p" (by simp)
    have hFj := hFl j
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl h1s, hsj, hns, if_pos hj]
    · unfold fBody
      apply runs_seq
      refine (fA_run gt (s.charge 1) (by simp [hlos, hsj, hcs]; omega)
        (by simp [hlos, hsj, hwl]; omega)).mono (fun s1 ⟨hx1, hsx1, hsy1, hr1, hc1⟩ => ?_)
      have hK1 : KR s1 := hL.regs _ _ (hL.regs _ _ hK (RegOnly.charge s 1 myRegs))
        (hr1.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, selRegs, lessRegs]))
      have hr1' := hr1
      obtain ⟨hwa1, hwl1, -, -, -, hcap1, -, hw1⟩ := hr1'
      -- the element read is the original one
      have hej : s.wa "sel.w" (lo + j) = e j := by
        rw [harr (lo + j), if_neg (by omega)]
      simp only [State.charge_w, State.charge_wa, hlos, hsj, hps, hej] at hx1 hsx1 hsy1
      have hokej : ok (e j) := hok _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      apply runs_seq
      refine (hL.run s1 hK1 (by rw [hsx1]; cases gt <;> simpa using (by first | exact hokp | exact hokej))
        (by rw [hsy1]; cases gt <;> simpa using (by first | exact hokej | exact hokp))).mono
        (fun s2 ⟨hc2, hu2, hcost2, hK2⟩ => ?_)
      have k2 : ∀ y, y ∈ myRegs → y ≠ "sl.c" → s2.w y = s1.w y := fun y hy hyc =>
        hu2.wreg y (hL.keep hy hyc)
      have hcnt' : cnt ∈ myRegs := by
        simp at hcnt; rcases hcnt with rfl | rfl <;> simp [myRegs, selRegs]
      have hcnt2 : s2.w cnt = (F j).length := by
        rw [k2 cnt hcnt' (by simp at hcnt; rcases hcnt with rfl | rfl <;> simp),
          hw1 cnt (by simp at hcnt; rcases hcnt with rfl | rfl <;> simp)]
        simpa using hsc
      have hj2 : s2.w "sel.j" = j := by
        rw [k2 "sel.j" (by simp [myRegs, selRegs]) (by simp), hw1 "sel.j" (by simp)]; simpa using hsj
      have hm2 : s2.w "sel.m" = m := by
        rw [k2 "sel.m" (by simp [myRegs, selRegs]) (by simp), hw1 "sel.m" (by simp)]; simpa using hms
      have hx2 : s2.w "sel.x" = e j := by
        rw [k2 "sel.x" (by simp [myRegs, selRegs]) (by simp), hx1]
      have hwa2 : s2.wa "sel.w" = s.wa "sel.w" := by
        rw [(hu2.warr "sel.w" (by simp)).1, hwa1]; rfl
      have hwl2 : s2.wlen "sel.w" = st.wlen "sel.w" := by
        rw [(hu2.warr "sel.w" (by simp)).2, hwl1]; simpa using hwl
      have hcap2 : s2.cap = st.cap := by rw [hu2.cap, hcap1]; simpa using hcs
      have hbit : s2.w "sl.c" = if fP κ gt p (e j) then 1 else 0 := by
        rw [hc2, hsx1, hsy1]
        cases gt <;> simp [fP]
      refine (fB_run cnt hcnt s2 (by rw [hcap2]; exact h1) (by rw [hj2, hcap2]; omega)
        (by rw [hcnt2, hcap2]; omega) (by rw [hm2, hcnt2, hcap2]; omega)
        (by rw [hm2, hcnt2, hwl2]; omega)).mono (fun r hr => ?_)
      obtain ⟨harr', hoth, hwlr, hvar, hvlr, hvr, hcapr, hprr, hcntr, hjr, hwr, hcr⟩ := hr
      have hKr : KR r := by
        by_cases hb : s2.w "sl.c" = 0
        · refine hL.regs s2 r hK2 ⟨funext fun b => ?_, hwlr, hvar, hvlr, hvr, hcapr, hprr,
            fun y hy => ?_⟩
          · by_cases hbw : b = "sel.w"
            · subst hbw; funext q; rw [harr' q]; simp [hb]
            · rw [hoth b hbw]
          · by_cases hyc : y = cnt
            · subst hyc; rw [hcntr, hb]; simp
            · by_cases hyj : y = "sel.j"
              · subst hyj; exact absurd (by simp [myRegs, selRegs]) hy
              · exact hwr y hyc hyj
        · have hstore : KR (s2.storeW "sel.w" (s2.w "sel.m" + s2.w cnt) (s2.w "sel.x")) :=
            hL.storeW _ _ _ hK2
          refine hL.regs _ r hstore ⟨funext fun b => ?_, hwlr, hvar, hvlr, hvr, hcapr, hprr,
            fun y hy => ?_⟩
          · by_cases hbw : b = "sel.w"
            · subst hbw; funext q; rw [harr' q]; simp [State.storeW, hb]
            · rw [hoth b hbw]; simp [State.storeW, hbw]
          · have hyc : y ≠ cnt := by
              intro e; subst e; exact hy hcnt'
            have hyj : y ≠ "sel.j" := by
              intro e; subst e; exact hy (by simp [myRegs, selRegs])
            rw [hwr y hyc hyj]; rfl
      refine ⟨hKr, by rw [hjr, hj2], ?_, fun q => ?_, ?_, by rw [hwlr, hwl2], ?_⟩
      · rw [hcntr, hcnt2, hFs j, hbit]
        by_cases hPj : fP κ gt p (e j)
        · simp only [hPj, if_true, one_ne_zero, if_false, List.length_append, List.length_singleton]
        · simp only [hPj, if_false, if_true, List.append_nil, Nat.add_zero]
      · rw [harr' q, hbit, hm2, hcnt2, hx2, hwa2, harr q, hFs j]
        by_cases hPj : fP κ gt p (e j)
        · simp only [hPj, if_true, ne_eq, one_ne_zero, not_false_eq_true, true_and,
            List.length_append, List.length_singleton]
          by_cases hq : q = m + (F j).length
          · rw [if_pos hq, if_pos ⟨by omega, by omega⟩, hq, Nat.add_sub_cancel_left]
            exact getD_append_single_len.symm
          · rw [if_neg hq]
            by_cases hq2 : m ≤ q ∧ q < m + (F j).length
            · rw [if_pos hq2, if_pos ⟨hq2.1, by omega⟩, getD_append_single_of_lt (by omega)]
            · rw [if_neg hq2, if_neg (by omega)]
        · simp only [hPj, if_false, ne_eq, not_true_eq_false, false_and, List.append_nil]
      · have u1 : Unchanged s (s.charge 1) ["sel.w"] [] (filtW cnt lessW) lessV :=
          Unchanged.charge _ _ _ _ _ _
        have u2 : Unchanged (s.charge 1) s1 ["sel.w"] [] (filtW cnt lessW) lessV :=
          (hr1.unch ["sel.w"] [] lessV).mono (List.Subset.refl _) (List.Subset.refl _)
            (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [filtW])
            (List.Subset.refl _)
        have u3 : Unchanged s1 s2 ["sel.w"] [] (filtW cnt lessW) lessV :=
          hu2.mono (by simp) (List.Subset.refl _) (by
            intro y hy; rcases List.mem_cons.mp hy with h | h
            · rw [h]; simp [filtW]
            · simp [filtW, h]) (List.Subset.refl _)
        have u4 : Unchanged s2 r ["sel.w"] [] (filtW cnt lessW) lessV := by
          refine ⟨fun b hb => ?_, fun b _ => ⟨hvar ▸ rfl, hvlr ▸ rfl⟩, fun y hy => ?_, fun y _ => by rw [hvr],
            hcapr, hprr⟩
          · have hbw : b ≠ "sel.w" := by simpa using hb
            exact ⟨hoth b hbw, by rw [hwlr]⟩
          · have hyc : y ≠ cnt := fun e => hy (e ▸ hcntW)
            have hyj : y ≠ "sel.j" := fun e => hy (e ▸ hjW)
            exact hwr y hyc hyj
        exact hu.trans (u1.trans (u2.trans (u3.trans u4)))
      · simp only [State.charge_cost] at hc1
        rw [Nat.succ_mul]
        omega
  · intro s ⟨hK, hsj, hsc, harr, hu, hwl, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hns : s.w "sel.n" = n := hu.wreg "sel.n" (filt_keep hL hcnt (by simp)
      (by simp at hcnt; rcases hcnt with rfl | rfl <;> simp))
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    refine ⟨by rw [evalW_lt_of rfl rfl h1s, hsj, hns, if_neg (lt_irrefl _)], ?_⟩
    have hFn := hFl n
    have hFn' : (seg st lo n).filter (fun x => decide (fP κ gt p x)) = F n := rfl
    refine ⟨hL.regs _ _ hK (RegOnly.charge s 1 myRegs), ?_, fun q hq => ?_, by simpa using hwl,
      by simpa using hu, by simp; omega⟩
    · rw [hFn']
      simp only [State.charge_w, hsc]
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [seg, List.getElem_map, List.getElem_range, State.charge_wa]
        rw [harr (m + i), if_pos ⟨by omega, by simp at h1; omega⟩, Nat.add_sub_cancel_left]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem h2]
        rfl
    · simp only [State.charge_wa]
      rw [harr q, if_neg (by omega)]
  · exact ⟨hK0, by simp [hs0, hcj], by simp [hs0, F], fun q => by simp [hs0, F],
      (hr0.unch ["sel.w"] [] lessV).mono (List.Subset.refl _) (List.Subset.refl _)
        (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [filtW]) (List.Subset.refl _),
      by simp [hs0], by simp [hs0]⟩

set_option maxHeartbeats 2000000 in
/-- **Spec of the `≥` filter pass** (`hiOf` / Pull's remainder). -/
theorem filtGe_spec (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (cnt : String)
    (hcnt : cnt ∈ ["sel.a", "sel.b"]) (st : State V) (hKR : KR st)
    (hok : ∀ x ∈ seg st (st.w "sel.lo") (st.w "sel.n"), ok x) (hokp : ok (st.w "sel.p"))
    (hov : st.w "sel.lo" + st.w "sel.n" ≤ st.w "sel.m")
    (hlen : st.w "sel.m" + st.w "sel.n" ≤ st.wlen "sel.w")
    (hcap : st.w "sel.m" + st.w "sel.n" + 1 < st.cap) :
    Runs ops (filtGe lessS cnt) st (fun r => KR r ∧
      seg r (st.w "sel.m") (r.w cnt) =
        (seg st (st.w "sel.lo") (st.w "sel.n")).filter (fun x => decide (κ (st.w "sel.p") ≤ κ x)) ∧
      (∀ q, (q < st.w "sel.m" ∨ st.w "sel.m" + st.w "sel.n" ≤ q) → r.wa "sel.w" q = st.wa "sel.w" q) ∧
      r.wlen "sel.w" = st.wlen "sel.w" ∧
      Unchanged st r ["sel.w"] [] (filtW cnt lessW) lessV ∧
      r.cost ≤ st.cost + 3 + st.w "sel.n" * (Cl + 10)) := by
  set n := st.w "sel.n" with hn
  set lo := st.w "sel.lo" with hlo
  set m := st.w "sel.m" with hm
  set p := st.w "sel.p" with hp
  set e : ℕ → ℕ := fun q => st.wa "sel.w" (lo + q) with he
  let F : ℕ → List ℕ := fun j => ((List.range j).map e).filter (fun x => decide (κ p ≤ κ x))
  have hFs : ∀ j, F (j + 1) = F j ++ (if κ p ≤ κ (e j) then [e j] else []) := by
    intro j
    by_cases h : κ p ≤ κ (e j) <;>
      simp [F, List.range_succ, List.map_append, List.filter_append, List.filter_cons, h]
  have hFl : ∀ j, (F j).length ≤ j := by
    intro j
    have := List.length_filter_le (fun x => decide (κ p ≤ κ x)) ((List.range j).map e)
    simpa [F] using this
  have hcj : cnt ≠ "sel.j" := by simp at hcnt; rcases hcnt with rfl | rfl <;> simp
  have h1 : 1 < st.cap := by omega
  have h0 : 0 < st.cap := by omega
  have hcntW : cnt ∈ filtW cnt lessW := by simp [filtW]
  have hjW : "sel.j" ∈ filtW cnt lessW := by simp [filtW]
  unfold filtGe
  apply runs_seq
  refine runs_wset (a := 0) (evalW_lit_of h0) ?_
  apply runs_seq
  refine runs_wset (a := 0) (evalW_lit_of (by simpa using h0)) ?_
  set s0 := (((st.setW "sel.j" 0).charge 1).setW cnt 0).charge 1 with hs0
  have hr0 : RegOnly st s0 ["sel.j", cnt] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hs0, State.setW, hy.1, hy.2]
  have hK0 : KR s0 := hL.regs _ _ hKR (hr0.mono (by
    intro y hy; simp at hy; rcases hy with rfl | rfl
    · simp [myRegs, selRegs]
    · simp at hcnt; rcases hcnt with rfl | rfl <;> simp [myRegs, selRegs]))
  refine runs_while (fun j s => KR s ∧ s.w "sel.j" = j ∧ s.w cnt = (F j).length ∧
      (∀ q, s.wa "sel.w" q = if m ≤ q ∧ q < m + (F j).length then (F j).getD (q - m) 0
        else st.wa "sel.w" q) ∧
      Unchanged st s ["sel.w"] [] (filtW cnt lessW) lessV ∧ s.wlen "sel.w" = st.wlen "sel.w" ∧
      s.cost ≤ st.cost + 2 + j * (Cl + 10)) n _ ?_ ?_ s0 ?_
  · intro j hj s ⟨hK, hsj, hsc, harr, hu, hwl, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hks : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.m", "sel.p"] → s.w y = st.w y := by
      intro y hy
      refine hu.wreg y (filt_keep hL hcnt (by simp at hy ⊢; tauto) ?_)
      simp at hy hcnt
      rcases hy with rfl | rfl | rfl | rfl <;> rcases hcnt with rfl | rfl <;> simp
    have hns : s.w "sel.n" = n := hks "sel.n" (by simp)
    have hlos : s.w "sel.lo" = lo := hks "sel.lo" (by simp)
    have hms : s.w "sel.m" = m := hks "sel.m" (by simp)
    have hps : s.w "sel.p" = p := hks "sel.p" (by simp)
    have hFj := hFl j
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl h1s, hsj, hns, if_pos hj]
    · unfold fBodyGe
      apply runs_seq
      refine (fA_run false (s.charge 1) (by simp [hlos, hsj, hcs]; omega)
        (by simp [hlos, hsj, hwl]; omega)).mono (fun s1 ⟨hx1, hsx1, hsy1, hr1, hc1⟩ => ?_)
      have hK1 : KR s1 := hL.regs _ _ (hL.regs _ _ hK (RegOnly.charge s 1 myRegs))
        (hr1.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, selRegs, lessRegs]))
      have hr1' := hr1
      obtain ⟨hwa1, hwl1, -, -, -, hcap1, -, hw1⟩ := hr1'
      -- the element read is the original one
      have hej : s.wa "sel.w" (lo + j) = e j := by
        rw [harr (lo + j), if_neg (by omega)]
      simp only [State.charge_w, State.charge_wa, hlos, hsj, hps, hej] at hx1 hsx1 hsy1
      have hokej : ok (e j) := hok _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      apply runs_seq
      refine (hL.run s1 hK1 (by rw [hsx1]; simpa using hokej) (by rw [hsy1]; simpa using hokp)).mono
        (fun s2 ⟨hc2, hu2, hcost2, hK2⟩ => ?_)
      have k2 : ∀ y, y ∈ myRegs → y ≠ "sl.c" → s2.w y = s1.w y := fun y hy hyc =>
        hu2.wreg y (hL.keep hy hyc)
      have hcnt' : cnt ∈ myRegs := by
        simp at hcnt; rcases hcnt with rfl | rfl <;> simp [myRegs, selRegs]
      have hcnt2 : s2.w cnt = (F j).length := by
        rw [k2 cnt hcnt' (by simp at hcnt; rcases hcnt with rfl | rfl <;> simp),
          hw1 cnt (by simp at hcnt; rcases hcnt with rfl | rfl <;> simp)]
        simpa using hsc
      have hj2 : s2.w "sel.j" = j := by
        rw [k2 "sel.j" (by simp [myRegs, selRegs]) (by simp), hw1 "sel.j" (by simp)]; simpa using hsj
      have hm2 : s2.w "sel.m" = m := by
        rw [k2 "sel.m" (by simp [myRegs, selRegs]) (by simp), hw1 "sel.m" (by simp)]; simpa using hms
      have hx2 : s2.w "sel.x" = e j := by
        rw [k2 "sel.x" (by simp [myRegs, selRegs]) (by simp), hx1]
      have hwa2 : s2.wa "sel.w" = s.wa "sel.w" := by
        rw [(hu2.warr "sel.w" (by simp)).1, hwa1]; rfl
      have hwl2 : s2.wlen "sel.w" = st.wlen "sel.w" := by
        rw [(hu2.warr "sel.w" (by simp)).2, hwl1]; simpa using hwl
      have hcap2 : s2.cap = st.cap := by rw [hu2.cap, hcap1]; simpa using hcs
      have hbit : s2.w "sl.c" = if κ (e j) < κ p then 1 else 0 := by
        rw [hc2, hsx1, hsy1]; simp
      refine (fBGe_run cnt hcnt s2 (by rw [hcap2]; exact h1) (by rw [hj2, hcap2]; omega)
        (by rw [hcnt2, hcap2]; omega) (by rw [hm2, hcnt2, hcap2]; omega)
        (by rw [hm2, hcnt2, hwl2]; omega)).mono (fun r hr => ?_)
      obtain ⟨harr', hoth, hwlr, hvar, hvlr, hvr, hcapr, hprr, hcntr, hjr, hwr, hcr⟩ := hr
      have hKr : KR r := hL.frame s2 r hK2 hoth hwlr hvar hvlr hvr hcapr hprr
        (fun y hy => hwr y (fun e => hy (e ▸ hcnt')) (fun e => hy (e ▸ (by simp [myRegs, selRegs]))))
      refine ⟨hKr, by rw [hjr, hj2], ?_, fun q => ?_, ?_, by rw [hwlr, hwl2], ?_⟩
      · rw [hcntr, hcnt2, hFs j, hbit]
        by_cases hPj : κ (e j) < κ p
        · simp [hPj, not_le.mpr hPj]
        · simp [hPj, not_lt.mp hPj]
      · rw [harr' q, hbit, hm2, hcnt2, hx2, hwa2, harr q, hFs j]
        by_cases hPj : κ (e j) < κ p
        · simp only [hPj, if_true, one_ne_zero, false_and, if_false, not_le.mpr hPj, List.append_nil]
        · have hge : κ p ≤ κ (e j) := not_lt.mp hPj
          simp only [hPj, if_false, true_and, hge, if_true, List.length_append, List.length_singleton]
          by_cases hq : q = m + (F j).length
          · rw [if_pos hq, if_pos ⟨by omega, by omega⟩, hq, Nat.add_sub_cancel_left]
            exact getD_append_single_len.symm
          · rw [if_neg hq]
            by_cases hq2 : m ≤ q ∧ q < m + (F j).length
            · rw [if_pos hq2, if_pos ⟨hq2.1, by omega⟩, getD_append_single_of_lt (by omega)]
            · rw [if_neg hq2, if_neg (by omega)]
      · have u1 : Unchanged s (s.charge 1) ["sel.w"] [] (filtW cnt lessW) lessV :=
          Unchanged.charge _ _ _ _ _ _
        have u2 : Unchanged (s.charge 1) s1 ["sel.w"] [] (filtW cnt lessW) lessV :=
          (hr1.unch ["sel.w"] [] lessV).mono (List.Subset.refl _) (List.Subset.refl _)
            (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [filtW])
            (List.Subset.refl _)
        have u3 : Unchanged s1 s2 ["sel.w"] [] (filtW cnt lessW) lessV :=
          hu2.mono (by simp) (List.Subset.refl _) (by
            intro y hy; rcases List.mem_cons.mp hy with h | h
            · rw [h]; simp [filtW]
            · simp [filtW, h]) (List.Subset.refl _)
        have u4 : Unchanged s2 r ["sel.w"] [] (filtW cnt lessW) lessV := by
          refine ⟨fun b hb => ?_, fun b _ => ⟨hvar ▸ rfl, hvlr ▸ rfl⟩, fun y hy => ?_, fun y _ => by rw [hvr],
            hcapr, hprr⟩
          · have hbw : b ≠ "sel.w" := by simpa using hb
            exact ⟨hoth b hbw, by rw [hwlr]⟩
          · have hyc : y ≠ cnt := fun e => hy (e ▸ hcntW)
            have hyj : y ≠ "sel.j" := fun e => hy (e ▸ hjW)
            exact hwr y hyc hyj
        exact hu.trans (u1.trans (u2.trans (u3.trans u4)))
      · simp only [State.charge_cost] at hc1
        rw [Nat.succ_mul]
        omega
  · intro s ⟨hK, hsj, hsc, harr, hu, hwl, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hns : s.w "sel.n" = n := hu.wreg "sel.n" (filt_keep hL hcnt (by simp)
      (by simp at hcnt; rcases hcnt with rfl | rfl <;> simp))
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    refine ⟨by rw [evalW_lt_of rfl rfl h1s, hsj, hns, if_neg (lt_irrefl _)], ?_⟩
    have hFn := hFl n
    have hFn' : (seg st lo n).filter (fun x => decide (κ p ≤ κ x)) = F n := rfl
    refine ⟨hL.regs _ _ hK (RegOnly.charge s 1 myRegs), ?_, fun q hq => ?_, by simpa using hwl,
      by simpa using hu, by simp; omega⟩
    · rw [hFn']
      simp only [State.charge_w, hsc]
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [seg, List.getElem_map, List.getElem_range, State.charge_wa]
        rw [harr (m + i), if_pos ⟨by omega, by simp at h1; omega⟩, Nat.add_sub_cancel_left]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem h2]
        rfl
    · simp only [State.charge_wa]
      rw [harr q, if_neg (by omega)]
  · exact ⟨hK0, by simp [hs0, hcj], by simp [hs0, F], fun q => by simp [hs0, F],
      (hr0.unch ["sel.w"] [] lessV).mono (List.Subset.refl _) (List.Subset.refl _)
        (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [filtW]) (List.Subset.refl _),
      by simp [hs0], by simp [hs0]⟩

/-! ## Groups of five and their medians (list level) -/

theorem chunk5_getElem? : ∀ (l : List α) (q : ℕ),
    (Frontier.CHD.chunk5 l)[q]? = if 5 * q < l.length then some ((l.drop (5 * q)).take 5) else none
  | [], q => by simp [Frontier.CHD.chunk5]
  | a :: l, 0 => by rw [Frontier.CHD.chunk5]; simp
  | a :: l, q + 1 => by
    rw [Frontier.CHD.chunk5, List.getElem?_cons_succ, chunk5_getElem? ((a :: l).drop 5) q]
    simp only [List.length_drop, List.drop_drop]
    have e : 5 * q + 5 = 5 * (q + 1) := by ring
    rw [Nat.add_comm 5 (5 * q), e]
    congr 1
    exact propext (by omega)
termination_by l => l.length
decreasing_by all_goals (simp_wf; try omega)

/-- the ids of group `q` of the segment `[lo, lo + n)` -/
def grp (st : State V) (lo n q : ℕ) : List ℕ := seg st (lo + 5 * q) (min 5 (n - 5 * q))

theorem grp_sub_seg {st : State V} {lo n q x : ℕ} (hx : x ∈ grp st lo n q) : x ∈ seg st lo n := by
  simp only [grp, seg, List.mem_map, List.mem_range] at hx ⊢
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨5 * q + j, by omega, by rw [Nat.add_assoc]⟩


theorem chunk5_seg (κ : ℕ → α) (st : State V) (lo n q : ℕ) (hq : 5 * q < n) :
    (Frontier.CHD.chunk5 ((seg st lo n).map κ))[q]? = some ((grp st lo n q).map κ) := by
  rw [chunk5_getElem?, if_pos (by simpa using hq)]
  congr 1
  apply List.ext_getElem
  · simp [grp]
  · intro i h1 h2
    simp [grp, seg, Nat.add_assoc]

theorem isKth_med [Inhabited α] {g : List α} (hg : g ≠ []) :
    Frontier.CHD.IsKth g ((g.length - 1) / 2) (Frontier.CHD.med g) := by
  rw [Frontier.CHD.med_eq hg]
  exact Frontier.CHD.isKth_sortC g (by have := List.length_pos_of_ne_nil hg; omega)

/-- A group median: an id of the group whose key has rank `(|g| - 1) / 2` in the group. -/
def MedOK (κ : ℕ → α) (st : State V) (lo n q x : ℕ) : Prop :=
  x ∈ grp st lo n q ∧
    Frontier.CHD.IsKth ((grp st lo n q).map κ) ((min 5 (n - 5 * q) - 1) / 2) (κ x)

/-- The keys of a list of group medians are the medians of `chunk5` (agent-04's `mom_bound`
applies to them). -/
theorem medians_eq [Inhabited α] (κ : ℕ → α) (st : State V) (lo n : ℕ) (ms : List ℕ)
    (hlen : ms.length = (n + 4) / 5)
    (hms : ∀ q (hq : q < ms.length), MedOK κ st lo n q (ms[q])) :
    ms.map κ = (Frontier.CHD.chunk5 ((seg st lo n).map κ)).map Frontier.CHD.med := by
  apply List.ext_getElem
  · simp [Frontier.CHD.length_chunk5, hlen]
  · intro q h1 h2
    have hq : q < ms.length := by simpa using h1
    have h5q : 5 * q < n := by rw [hlen] at hq; omega
    have hc := chunk5_seg κ st lo n q h5q
    simp only [List.getElem_map]
    have hcq : (Frontier.CHD.chunk5 ((seg st lo n).map κ))[q]'(by simpa using h2) =
        (grp st lo n q).map κ := by
      rw [List.getElem?_eq_getElem (by simpa using h2)] at hc
      exact Option.some.inj hc
    rw [hcq]
    have hne : (grp st lo n q).map κ ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [grp] at this
      omega
    have hlg : ((grp st lo n q).map κ).length = min 5 (n - 5 * q) := by simp [grp]
    have h1' := isKth_med hne
    rw [hlg] at h1'
    exact Frontier.CHD.IsKth.unique (hms q hq).2 h1'

/-! ## The medians loop -/

def mA : Stmt :=
  seq (wset "cs.lo" (add (var "sel.lo") (mul (var "sel.g") (lit 5))))
  (seq (wset "sel.m" (sub (var "sel.n") (mul (var "sel.g") (lit 5))))
  (seq (ite (lt (lit 5) (var "sel.m")) (wset "cs.n" (lit 5)) (wset "cs.n" (var "sel.m")))
       (wset "cs.k" (div (sub (var "cs.n") (lit 1)) (lit 2)))))
def mB : Stmt :=
  seq (wstore "sel.w" (add (var "sel.top") (var "sel.g")) (var "cs.res"))
    (wset "sel.g" (add (var "sel.g") (lit 1)))
def medBody (lessS : Stmt) : Stmt := seq mA (seq (countSel lessS) mB)
/-- medians of the groups of five of `sel.w[sel.lo, sel.lo + sel.n)` into `sel.w[sel.top, …)` -/
def medLoop (lessS : Stmt) : Stmt :=
  seq (wset "sel.g" (lit 0)) (.while (lt (mul (var "sel.g") (lit 5)) (var "sel.n")) (medBody lessS))

@[simp] theorem evalW_div'' (s : State V) (a b : WExpr) :
    evalW s (.div a b) = (evalW s a).bind (fun x => (evalW s b).bind
      (fun y => if y = 0 then none else some (x / y))) := rfl

theorem mA_run (s : State V) (h6 : 6 < s.cap) (hc : s.w "sel.lo" + s.w "sel.g" * 5 < s.cap)
    (hg : s.w "sel.g" * 5 < s.cap) :
    Runs ops mA s (fun r => r.w "cs.lo" = s.w "sel.lo" + s.w "sel.g" * 5 ∧
      r.w "cs.n" = min 5 (s.w "sel.n" - s.w "sel.g" * 5) ∧
      r.w "cs.k" = (min 5 (s.w "sel.n" - s.w "sel.g" * 5) - 1) / 2 ∧
      RegOnly s r ["cs.lo", "sel.m", "cs.n", "cs.k"] ∧ r.cost = s.cost + 5) := by
  apply wp_sound
  have h5 : fit s.cap 5 = some 5 := fit_of_lt (by omega)
  have h1 : fit s.cap 1 = some 1 := fit_of_lt (by omega)
  have h2 : fit s.cap 2 = some 2 := fit_of_lt (by omega)
  have h0 : 0 < s.cap := by omega
  have h1' : 1 < s.cap := by omega
  by_cases hm : 5 < s.w "sel.n" - s.w "sel.g" * 5
  · have hmin : min 5 (s.w "sel.n" - s.w "sel.g" * 5) = 5 := by omega
    simp (config := { contextual := true }) [mA, wp, h5, h1, h2, fit_of_lt hc, fit_of_lt hg,
      fit_of_lt h0, fit_of_lt h1', hm, hmin, RegOnly, State.setW, Nat.add_assoc]
  · have hmin : min 5 (s.w "sel.n" - s.w "sel.g" * 5) = s.w "sel.n" - s.w "sel.g" * 5 := by omega
    simp (config := { contextual := true }) [mA, wp, h5, h1, h2, fit_of_lt hc, fit_of_lt hg,
      fit_of_lt h0, fit_of_lt h1', hm, hmin, RegOnly, State.setW, Nat.add_assoc]

theorem mB_run (s : State V) (h1 : 1 < s.cap) (hc : s.w "sel.top" + s.w "sel.g" < s.cap)
    (hl : s.w "sel.top" + s.w "sel.g" < s.wlen "sel.w") (hg : s.w "sel.g" + 1 < s.cap) :
    Runs ops mB s (fun r =>
      (∀ q, r.wa "sel.w" q = if q = s.w "sel.top" + s.w "sel.g" then s.w "cs.res"
        else s.wa "sel.w" q) ∧
      (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) ∧ r.wlen = s.wlen ∧ r.va = s.va ∧ r.vlen = s.vlen ∧
      r.v = s.v ∧ r.cap = s.cap ∧ r.procs = s.procs ∧ r.w "sel.g" = s.w "sel.g" + 1 ∧
      (∀ y, y ≠ "sel.g" → r.w y = s.w y) ∧ r.cost = s.cost + 2 ∧
      r = ((((s.storeW "sel.w" (s.w "sel.top" + s.w "sel.g") (s.w "cs.res")).charge 1).setW
        "sel.g" (s.w "sel.g" + 1)).charge 1)) := by
  apply wp_sound
  simp (config := { contextual := true }) [mB, wp, fit_of_lt hc, hl, fit_of_lt hg, fit_one' h1,
    State.setW, State.storeW, Nat.add_assoc]

/-- write set of the medians loop -/
def medW (lessW : List String) : List String :=
  ["sel.g", "cs.lo", "sel.m", "cs.n", "cs.k"] ++ csW lessW

theorem medW_keep (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) {y : String}
    (hy : y ∈ ["sel.lo", "sel.n", "sel.top", "sel.k", "sel.fp"]) : y ∉ medW lessW := by
  intro hmem
  simp only [medW, csW, List.mem_append] at hmem
  rcases hmem with h | h | h
  · simp at hy h; rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp at h
  · simp at hy h; rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp at h
  · exact hL.disj y h (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs])

theorem csW_keep (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) {y : String}
    (hy : y ∈ ["sel.lo", "sel.n", "sel.top", "sel.g", "sel.k", "sel.fp"]) : y ∉ csW lessW := by
  intro hmem
  simp only [csW, List.mem_append] at hmem
  rcases hmem with h | h
  · simp at hy h; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h
  · exact hL.disj y h (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [myRegs, selRegs])

set_option maxHeartbeats 2000000 in
/-- **Spec of the medians loop.** -/
theorem medLoop_spec (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (st : State V) (hKR : KR st)
    (hok : ∀ x ∈ seg st (st.w "sel.lo") (st.w "sel.n"), ok x)
    (hn1 : 1 ≤ st.w "sel.n") (hov : st.w "sel.lo" + st.w "sel.n" ≤ st.w "sel.top")
    (hlen : st.w "sel.top" + st.w "sel.n" ≤ st.wlen "sel.w")
    (hcap : st.w "sel.top" + 5 * st.w "sel.n" + 10 < st.cap) :
    Runs ops (medLoop lessS) st (fun r => KR r ∧ r.w "sel.g" = (st.w "sel.n" + 4) / 5 ∧
      (∀ q < (st.w "sel.n" + 4) / 5,
        MedOK κ st (st.w "sel.lo") (st.w "sel.n") q (r.wa "sel.w" (st.w "sel.top" + q))) ∧
      (∀ q', (q' < st.w "sel.top" ∨ st.w "sel.top" + (st.w "sel.n" + 4) / 5 ≤ q') →
        r.wa "sel.w" q' = st.wa "sel.w" q') ∧
      r.wlen "sel.w" = st.wlen "sel.w" ∧
      Unchanged st r ["sel.w"] [] (medW lessW) lessV ∧
      r.cost ≤ st.cost + 2 + (st.w "sel.n" + 4) / 5 * (50 * Cl + 320)) := by
  set n := st.w "sel.n" with hn
  set lo := st.w "sel.lo" with hlo
  set top := st.w "sel.top" with htop
  set G := (n + 4) / 5 with hG
  have hGn : G ≤ n := by omega
  have h0 : 0 < st.cap := by omega
  have h1 : 1 < st.cap := by omega
  have hgW : "sel.g" ∈ medW lessW := by simp [medW]
  unfold medLoop
  apply runs_seq
  refine runs_wset (a := 0) (evalW_lit_of h0) ?_
  set s0 := (st.setW "sel.g" 0).charge 1 with hs0
  have hr0 : RegOnly st s0 ["sel.g"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_singleton] at hy
    simp [hs0, State.setW, hy]
  refine runs_while (fun g s => KR s ∧ s.w "sel.g" = g ∧
      (∀ q < g, MedOK κ st lo n q (s.wa "sel.w" (top + q))) ∧
      (∀ q', (q' < top ∨ top + g ≤ q') → s.wa "sel.w" q' = st.wa "sel.w" q') ∧
      s.wlen "sel.w" = st.wlen "sel.w" ∧ Unchanged st s ["sel.w"] [] (medW lessW) lessV ∧
      s.cost ≤ st.cost + 1 + g * (50 * Cl + 320)) G _ ?_ ?_ s0
    ⟨hL.regs _ _ hKR (hr0.mono (by simp [myRegs, selRegs])), by simp [hs0],
      fun q hq => absurd hq (Nat.not_lt_zero q), fun q' _ => by simp [hs0], by simp [hs0],
      (hr0.unch ["sel.w"] [] lessV).mono (List.Subset.refl _) (List.Subset.refl _)
        (by simp [medW]) (List.Subset.refl _), by simp [hs0]⟩
  · intro g hg s ⟨hK, hsg, hmed, hout, hwl, hu, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hks : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.top", "sel.k", "sel.fp"] → s.w y = st.w y :=
      fun y hy => hu.wreg y (medW_keep hL hy)
    have hns : s.w "sel.n" = n := hks "sel.n" (by simp)
    have hlos : s.w "sel.lo" = lo := hks "sel.lo" (by simp)
    have htops : s.w "sel.top" = top := hks "sel.top" (by simp)
    have h5g : 5 * g < n := by omega
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    have ha : evalW s (mul (var "sel.g") (lit 5)) = some (g * 5) := by
      simp [evalW_mul', evalW_var, evalW_lit', hsg, hcs, fit_of_lt (show 5 < st.cap by omega),
        fit_of_lt (show g * 5 < st.cap by omega)]
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of ha rfl h1s, hns, if_pos (by omega)]
    · unfold medBody
      apply runs_seq
      refine (mA_run (s.charge 1) (by simp [hcs]; omega) (by simp [hlos, hsg, hcs]; omega)
        (by simp [hsg, hcs]; omega)).mono (fun s1 ⟨hlo1, hn1', hk1, hr1, hc1⟩ => ?_)
      simp only [State.charge_w, hlos, hsg, hns] at hlo1 hn1' hk1
      have hK1 : KR s1 := hL.regs _ _ (hL.regs _ _ hK (RegOnly.charge s 1 myRegs))
        (hr1.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [myRegs, csRegs, selRegs]))
      have hr1' := hr1
      obtain ⟨hwa1, hwl1, -, -, -, hcap1, -, hw1⟩ := hr1'
      set mm := min 5 (n - g * 5) with hmm
      have hmm1 : 1 ≤ mm := by omega
      have hmm5 : mm ≤ 5 := by omega
      have hwl1' : s1.wlen "sel.w" = st.wlen "sel.w" := by rw [hwl1]; simpa using hwl
      have hcap1' : s1.cap = st.cap := by rw [hcap1]; simpa using hcs
      -- the group read by countSel is the original group
      have hgrp : seg s1 (s1.w "cs.lo") (s1.w "cs.n") = grp st lo n g := by
        rw [hlo1, hn1', hmm]
        simp only [seg, grp]
        rw [Nat.mul_comm g 5]
        apply List.map_congr_left
        intro j hj
        rw [List.mem_range] at hj
        rw [hwa1]
        simp only [State.charge_wa]
        rw [hout _ (Or.inl (by omega))]
      apply runs_seq
      refine (countSel_spec hL s1 hK1 (fun x hx => hok x (grp_sub_seg (hgrp ▸ hx)))
        (by rw [hk1, hn1']; omega)
        (by rw [hlo1, hn1', hcap1']; omega) (by rw [hlo1, hn1', hwl1']; omega)).mono
        (fun s2 ⟨hK2, hres2, hkth2, hu2, hc2⟩ => ?_)
      have hcap2 : s2.cap = st.cap := by rw [hu2.cap, hcap1']
      have hk2 : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.top", "sel.g", "sel.k", "sel.fp"] →
          s2.w y = s1.w y := fun y hy => hu2.wreg y (csW_keep hL hy)
      have htop2 : s2.w "sel.top" = top := by
        rw [hk2 "sel.top" (by simp), hw1 "sel.top" (by simp)]; simpa using htops
      have hg2 : s2.w "sel.g" = g := by
        rw [hk2 "sel.g" (by simp), hw1 "sel.g" (by simp)]; simpa using hsg
      have hwa2 : s2.wa "sel.w" = s.wa "sel.w" := by
        rw [(hu2.warr "sel.w" (by simp)).1, hwa1]; rfl
      have hwl2 : s2.wlen "sel.w" = st.wlen "sel.w" := by
        rw [(hu2.warr "sel.w" (by simp)).2, hwl1']
      have hkk : s1.w "cs.k" = (min 5 (n - 5 * g) - 1) / 2 := by rw [hk1, hmm, Nat.mul_comm g 5]
      rw [hgrp, hkk] at hkth2
      rw [hgrp] at hres2
      refine (mB_run s2 (by rw [hcap2]; exact h1) (by rw [htop2, hg2, hcap2]; omega)
        (by rw [htop2, hg2, hwl2]; omega) (by rw [hg2, hcap2]; omega)).mono
        (fun r ⟨harr, hoth, hwlr, hvar, hvlr, hvr, hcapr, hprr, hgr, hwr, hcr, hreq⟩ => ?_)
      have hKr : KR r := by
        rw [hreq]
        exact hL.regs _ _ (hL.storeW _ _ _ hK2) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => by
          have : y ≠ "sel.g" := fun e => hy (by rw [e]; simp [myRegs, selRegs])
          simp [State.setW, this]⟩
      refine ⟨hKr, by rw [hgr, hg2], fun q hq => ?_, fun q' hq' => ?_, by rw [hwlr, hwl2], ?_, ?_⟩
      · rw [harr, htop2, hg2]
        by_cases hqg : q = g
        · subst hqg; rw [if_pos rfl]; exact ⟨hres2, hkth2⟩
        · rw [if_neg (by omega), hwa2]; exact hmed q (by omega)
      · rw [harr, htop2, hg2, if_neg (by omega), hwa2]
        exact hout q' (by omega)
      · have u1 : Unchanged s (s.charge 1) ["sel.w"] [] (medW lessW) lessV :=
          Unchanged.charge _ _ _ _ _ _
        have u2 : Unchanged (s.charge 1) s1 ["sel.w"] [] (medW lessW) lessV :=
          (hr1.unch ["sel.w"] [] lessV).mono (List.Subset.refl _) (List.Subset.refl _)
            (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [medW])
            (List.Subset.refl _)
        have u3 : Unchanged s1 s2 ["sel.w"] [] (medW lessW) lessV :=
          hu2.mono (List.nil_subset _) (List.Subset.refl _)
            (fun y hy => by simp only [medW, List.mem_append]; exact Or.inr hy) (List.Subset.refl _)
        have u4 : Unchanged s2 r ["sel.w"] [] (medW lessW) lessV := by
          refine ⟨fun b hb => ?_, fun b _ => ⟨hvar ▸ rfl, hvlr ▸ rfl⟩, fun y hy => ?_,
            fun y _ => by rw [hvr], hcapr, hprr⟩
          · have hbw : b ≠ "sel.w" := by simpa using hb
            exact ⟨hoth b hbw, by rw [hwlr]⟩
          · exact hwr y (fun e => hy (e ▸ hgW))
        exact hu.trans (u1.trans (u2.trans (u3.trans u4)))
      · simp only [State.charge_cost] at hc1
        have hcnt : mm * (mm * (2 * Cl + 10) + 12) ≤ 5 * (5 * (2 * Cl + 10) + 12) :=
          Nat.mul_le_mul hmm5 (Nat.add_le_add_right (Nat.mul_le_mul_right _ hmm5) _)
        rw [hn1'] at hc2
        rw [Nat.succ_mul]
        nlinarith
  · intro s ⟨hK, hsg, hmed, hout, hwl, hu, hc⟩
    have hcs : s.cap = st.cap := hu.cap
    have hns : s.w "sel.n" = n := hu.wreg "sel.n" (medW_keep hL (by simp))
    have h1s : 1 < s.cap := by rw [hcs]; exact h1
    have ha : evalW s (mul (var "sel.g") (lit 5)) = some (G * 5) := by
      simp [evalW_mul', evalW_var, evalW_lit', hsg, hcs, fit_of_lt (show 5 < st.cap by omega),
        fit_of_lt (show G * 5 < st.cap by omega)]
    refine ⟨?_, ?_⟩
    · rw [evalW_lt_of ha rfl h1s, hns, if_neg (by omega)]
    · refine ⟨hL.regs _ _ hK (RegOnly.charge s 1 myRegs), by simpa using hsg, fun q hq => ?_,
        fun q' hq' => ?_, by simpa using hwl, by simpa using hu, by simp; omega⟩
      · simpa using hmed q hq
      · simpa using hout q' hq'

/-! ## The selection procedure -/

def saveBlk : Stmt :=
  seq (wset "sel.x" (add (var "sel.top") (var "sel.g")))
  (seq (wstore "sel.w" (var "sel.x") (var "sel.lo"))
  (seq (wstore "sel.w" (add (var "sel.x") (lit 1)) (var "sel.n"))
  (seq (wstore "sel.w" (add (var "sel.x") (lit 2)) (var "sel.k"))
  (seq (wstore "sel.w" (add (var "sel.x") (lit 3)) (var "sel.top"))
  (seq (wstore "sel.w" (add (var "sel.x") (lit 4)) (var "sel.fp"))
  (seq (wset "sel.fp" (var "sel.x"))
  (seq (wset "sel.lo" (var "sel.top"))
  (seq (wset "sel.n" (var "sel.g"))
  (seq (wset "sel.k" (div (sub (var "sel.g") (lit 1)) (lit 2)))
       (wset "sel.top" (add (var "sel.x") (lit 5))))))))))))
def restoreBlk : Stmt :=
  seq (wset "sel.p" (var "sel.res"))
  (seq (wset "sel.lo" (load "sel.w" (var "sel.fp")))
  (seq (wset "sel.n" (load "sel.w" (add (var "sel.fp") (lit 1))))
  (seq (wset "sel.k" (load "sel.w" (add (var "sel.fp") (lit 2))))
  (seq (wset "sel.top" (load "sel.w" (add (var "sel.fp") (lit 3))))
  (seq (wset "sel.fp" (load "sel.w" (add (var "sel.fp") (lit 4))))
       (wset "sel.go" (lit 1)))))))
def partBlk (lessS : Stmt) : Stmt :=
  seq (wset "sel.m" (var "sel.top")) (seq (filt lessS false "sel.a")
    (seq (wset "sel.m" (add (var "sel.top") (var "sel.a"))) (filt lessS true "sel.b")))
def branchBlk : Stmt :=
  ite (lt (var "sel.k") (var "sel.a"))
    (seq (wset "sel.lo" (var "sel.top")) (seq (wset "sel.n" (var "sel.a"))
      (wset "sel.top" (add (var "sel.top") (add (var "sel.a") (var "sel.b"))))))
    (ite (lt (var "sel.k") (sub (var "sel.n") (var "sel.b")))
      (seq (wset "sel.res" (var "sel.p")) (wset "sel.go" (lit 0)))
      (seq (wset "sel.lo" (add (var "sel.top") (var "sel.a")))
      (seq (wset "sel.k" (sub (var "sel.k") (sub (var "sel.n") (var "sel.b"))))
      (seq (wset "sel.n" (var "sel.b"))
        (wset "sel.top" (add (var "sel.top") (add (var "sel.a") (var "sel.b"))))))))
def baseCase (lessS : Stmt) : Stmt :=
  seq (wset "cs.lo" (var "sel.lo")) (seq (wset "cs.n" (var "sel.n"))
  (seq (wset "cs.k" (var "sel.k")) (seq (countSel lessS)
  (seq (wset "sel.res" (var "cs.res")) (wset "sel.go" (lit 0))))))
def recCase (lessS : Stmt) (pSel : ℕ) : Stmt :=
  seq (medLoop lessS) (seq saveBlk (seq (call pSel) (seq restoreBlk (seq (partBlk lessS) branchBlk))))
def selIter (lessS : Stmt) (pSel : ℕ) : Stmt :=
  ite (lt (var "sel.n") (lit 201)) (baseCase lessS) (recCase lessS pSel)
/-- **The selection procedure** (procedure number `pSel`): the `sel.k`-th smallest key of
`sel.w[sel.lo, sel.lo + sel.n)`, scratch above `sel.top`, result in `sel.res`. -/
def selBody (lessS : Stmt) (pSel : ℕ) : Stmt :=
  seq (wset "sel.go" (lit 1)) (.while (var "sel.go") (selIter lessS pSel))

/-- the state after `saveBlk` -/
def saveState (s : State V) : State V :=
  let F := s.w "sel.top" + s.w "sel.g"
  let s1 := (s.setW "sel.x" F).charge 1
  let s2 := (s1.storeW "sel.w" F (s.w "sel.lo")).charge 1
  let s3 := (s2.storeW "sel.w" (F + 1) (s.w "sel.n")).charge 1
  let s4 := (s3.storeW "sel.w" (F + 2) (s.w "sel.k")).charge 1
  let s5 := (s4.storeW "sel.w" (F + 3) (s.w "sel.top")).charge 1
  let s6 := (s5.storeW "sel.w" (F + 4) (s.w "sel.fp")).charge 1
  let s7 := (s6.setW "sel.fp" F).charge 1
  let s8 := (s7.setW "sel.lo" (s.w "sel.top")).charge 1
  let s9 := (s8.setW "sel.n" (s.w "sel.g")).charge 1
  let s10 := (s9.setW "sel.k" ((s.w "sel.g" - 1) / 2)).charge 1
  (s10.setW "sel.top" (F + 5)).charge 1

theorem saveBlk_run (s : State V) (hc : s.w "sel.top" + s.w "sel.g" + 5 < s.cap)
    (hl : s.w "sel.top" + s.w "sel.g" + 4 < s.wlen "sel.w") :
    Runs ops saveBlk s (fun r => r = saveState s) := by
  have h1 : 1 < s.cap := by omega
  set F := s.w "sel.top" + s.w "sel.g" with hF
  unfold saveBlk
  apply runs_seq
  refine runs_wset (a := F)
    (by simp [fit_of_lt (show s.w "sel.top" + s.w "sel.g" < s.cap by omega), hF]) ?_
  apply runs_seq
  refine runs_wstore (j := F) (a := s.w "sel.lo") (by simp) (by simp) (by simp; omega) ?_
  apply runs_seq
  refine runs_wstore (j := F + 1) (a := s.w "sel.n")
    (by simp [fit_of_lt (show F + 1 < s.cap by omega), fit_of_lt h1]) (by simp)
    (by simp; omega) ?_
  apply runs_seq
  refine runs_wstore (j := F + 2) (a := s.w "sel.k")
    (by simp [fit_of_lt (show F + 2 < s.cap by omega), fit_of_lt (show 2 < s.cap by omega)])
    (by simp) (by simp; omega) ?_
  apply runs_seq
  refine runs_wstore (j := F + 3) (a := s.w "sel.top")
    (by simp [fit_of_lt (show F + 3 < s.cap by omega), fit_of_lt (show 3 < s.cap by omega)])
    (by simp) (by simp; omega) ?_
  apply runs_seq
  refine runs_wstore (j := F + 4) (a := s.w "sel.fp")
    (by simp [fit_of_lt (show F + 4 < s.cap by omega), fit_of_lt (show 4 < s.cap by omega)])
    (by simp) (by simp; omega) ?_
  apply runs_seq
  refine runs_wset (a := F) (by simp) ?_
  apply runs_seq
  refine runs_wset (a := s.w "sel.top") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := s.w "sel.g") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := (s.w "sel.g" - 1) / 2)
    (by simp [fit_of_lt h1, fit_of_lt (show 2 < s.cap by omega)]) ?_
  exact runs_wset (a := F + 5)
    (by simp [fit_of_lt (show F + 5 < s.cap by omega), fit_of_lt (show 5 < s.cap by omega)]) rfl

/-- the state after `restoreBlk` -/
def restoreState (s : State V) : State V :=
  let f := s.w "sel.fp"
  let s1 := (s.setW "sel.p" (s.w "sel.res")).charge 1
  let s2 := (s1.setW "sel.lo" (s.wa "sel.w" f)).charge 1
  let s3 := (s2.setW "sel.n" (s.wa "sel.w" (f + 1))).charge 1
  let s4 := (s3.setW "sel.k" (s.wa "sel.w" (f + 2))).charge 1
  let s5 := (s4.setW "sel.top" (s.wa "sel.w" (f + 3))).charge 1
  let s6 := (s5.setW "sel.fp" (s.wa "sel.w" (f + 4))).charge 1
  (s6.setW "sel.go" 1).charge 1

theorem restoreBlk_run (s : State V) (hc : s.w "sel.fp" + 4 < s.cap)
    (hl : s.w "sel.fp" + 4 < s.wlen "sel.w") :
    Runs ops restoreBlk s (fun r => r = restoreState s) := by
  set f := s.w "sel.fp" with hf
  unfold restoreBlk
  apply runs_seq
  refine runs_wset (a := s.w "sel.res") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := s.wa "sel.w" f)
    (by simp [hf, show s.w "sel.fp" < s.wlen "sel.w" by omega]) ?_
  apply runs_seq
  refine runs_wset (a := s.wa "sel.w" (f + 1))
    (by simp [hf, fit_of_lt (show s.w "sel.fp" + 1 < s.cap by omega),
      fit_of_lt (show 1 < s.cap by omega), show s.w "sel.fp" + 1 < s.wlen "sel.w" by omega]) ?_
  apply runs_seq
  refine runs_wset (a := s.wa "sel.w" (f + 2))
    (by simp [hf, fit_of_lt (show s.w "sel.fp" + 2 < s.cap by omega),
      fit_of_lt (show 2 < s.cap by omega), show s.w "sel.fp" + 2 < s.wlen "sel.w" by omega]) ?_
  apply runs_seq
  refine runs_wset (a := s.wa "sel.w" (f + 3))
    (by simp [hf, fit_of_lt (show s.w "sel.fp" + 3 < s.cap by omega),
      fit_of_lt (show 3 < s.cap by omega), show s.w "sel.fp" + 3 < s.wlen "sel.w" by omega]) ?_
  apply runs_seq
  refine runs_wset (a := s.wa "sel.w" (f + 4))
    (by simp [hf, fit_of_lt (show s.w "sel.fp" + 4 < s.cap by omega),
      fit_of_lt (show 4 < s.cap by omega), show s.w "sel.fp" + 4 < s.wlen "sel.w" by omega]) ?_
  exact runs_wset (a := 1) (by simp [fit_of_lt (show 1 < s.cap by omega)]) rfl

theorem branch_lo (s : State V) (h1 : 1 < s.cap)
    (hc : s.w "sel.top" + (s.w "sel.a" + s.w "sel.b") < s.cap) (hka : s.w "sel.k" < s.w "sel.a") :
    Runs ops branchBlk s (fun r => r.w "sel.lo" = s.w "sel.top" ∧ r.w "sel.n" = s.w "sel.a" ∧
      r.w "sel.top" = s.w "sel.top" + (s.w "sel.a" + s.w "sel.b") ∧
      RegOnly s r ["sel.lo", "sel.n", "sel.top"] ∧ r.cost = s.cost + 4) := by
  apply wp_sound
  have hab : s.w "sel.a" + s.w "sel.b" < s.cap := by omega
  simp (config := { contextual := true }) [branchBlk, wp, hka, fit_of_lt h1, fit_of_lt hab,
    fit_of_lt hc, RegOnly, State.setW, Nat.add_assoc]

theorem branch_mid (s : State V) (h1 : 1 < s.cap) (hka : ¬ s.w "sel.k" < s.w "sel.a")
    (hkb : s.w "sel.k" < s.w "sel.n" - s.w "sel.b") :
    Runs ops branchBlk s (fun r => r.w "sel.res" = s.w "sel.p" ∧ r.w "sel.go" = 0 ∧
      RegOnly s r ["sel.res", "sel.go"] ∧ r.cost = s.cost + 4) := by
  apply wp_sound
  have h0 : 0 < s.cap := by omega
  simp (config := { contextual := true }) [branchBlk, wp, hka, hkb, fit_of_lt h1, fit_of_lt h0,
    RegOnly, State.setW, Nat.add_assoc]

theorem branch_hi (s : State V) (h1 : 1 < s.cap)
    (hc : s.w "sel.top" + (s.w "sel.a" + s.w "sel.b") < s.cap) (hka : ¬ s.w "sel.k" < s.w "sel.a")
    (hkb : ¬ s.w "sel.k" < s.w "sel.n" - s.w "sel.b") :
    Runs ops branchBlk s (fun r => r.w "sel.lo" = s.w "sel.top" + s.w "sel.a" ∧
      r.w "sel.k" = s.w "sel.k" - (s.w "sel.n" - s.w "sel.b") ∧ r.w "sel.n" = s.w "sel.b" ∧
      r.w "sel.top" = s.w "sel.top" + (s.w "sel.a" + s.w "sel.b") ∧
      RegOnly s r ["sel.lo", "sel.k", "sel.n", "sel.top"] ∧ r.cost = s.cost + 6) := by
  apply wp_sound
  have hab : s.w "sel.a" + s.w "sel.b" < s.cap := by omega
  have ha : s.w "sel.top" + s.w "sel.a" < s.cap := by omega
  have h0 : 0 < s.cap := by omega
  simp (config := { contextual := true }) [branchBlk, wp, hka, hkb, fit_of_lt h0, fit_of_lt hab,
    fit_of_lt hc, fit_of_lt ha, RegOnly, State.setW, Nat.add_assoc]

theorem myRegs_sub {W : List String} (h : ∀ y ∈ W, y ∈ myRegs) (lessW : List String) :
    W ⊆ myRegs ++ lessW := fun y hy => List.mem_append_left _ (h y hy)

theorem csW_sub (lessW : List String) : csW lessW ⊆ myRegs ++ lessW := by
  intro y hy
  simp only [csW, List.mem_append] at hy
  rcases hy with h | h
  · exact List.mem_append_left _ (by simp at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [myRegs, lessRegs, csRegs])
  · exact List.mem_append_right _ h

theorem filtW_sub {cnt : String} (hcnt : cnt ∈ ["sel.a", "sel.b"]) (lessW : List String) :
    filtW cnt lessW ⊆ myRegs ++ lessW := by
  intro y hy
  simp only [filtW, List.mem_append] at hy
  rcases hy with h | h
  · refine List.mem_append_left _ ?_
    simp at h hcnt
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [myRegs, selRegs]
    · rcases hcnt with rfl | rfl <;> simp [myRegs, selRegs]
    all_goals simp [myRegs, selRegs, lessRegs]
  · exact List.mem_append_right _ h

theorem medW_sub (lessW : List String) : medW lessW ⊆ myRegs ++ lessW := by
  intro y hy
  simp only [medW, List.mem_append] at hy
  rcases hy with h | h
  · exact List.mem_append_left _ (by simp at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs, csRegs])
  · exact csW_sub lessW (by simpa [csW] using h)

/-- **The base case**: selection by counting. -/
theorem baseCase_run (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (s : State V) (hK : KR s)
    (hok : ∀ x ∈ seg s (s.w "sel.lo") (s.w "sel.n"), ok x)
    (hk : s.w "sel.k" < s.w "sel.n") (hcap : s.w "sel.lo" + s.w "sel.n" + 1 < s.cap)
    (hlen : s.w "sel.lo" + s.w "sel.n" ≤ s.wlen "sel.w") :
    Runs ops (baseCase lessS) s (fun r => KR r ∧
      r.w "sel.res" ∈ seg s (s.w "sel.lo") (s.w "sel.n") ∧
      Frontier.CHD.IsKth ((seg s (s.w "sel.lo") (s.w "sel.n")).map κ) (s.w "sel.k")
        (κ (r.w "sel.res")) ∧
      r.w "sel.go" = 0 ∧ r.wa "sel.w" = s.wa "sel.w" ∧ r.wlen "sel.w" = s.wlen "sel.w" ∧
      r.w "sel.fp" = s.w "sel.fp" ∧
      Unchanged s r ["sel.w"] [] (myRegs ++ lessW) lessV ∧
      r.cost ≤ s.cost + 7 + s.w "sel.n" * (s.w "sel.n" * (2 * Cl + 10) + 12)) := by
  have h0 : 0 < s.cap := by omega
  unfold baseCase
  apply runs_seq
  refine runs_wset (a := s.w "sel.lo") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := s.w "sel.n") (by simp) ?_
  apply runs_seq
  refine runs_wset (a := s.w "sel.k") (by simp) ?_
  set s3 := ((((((s.setW "cs.lo" (s.w "sel.lo")).charge 1).setW "cs.n" (s.w "sel.n")).charge 1).setW
    "cs.k" (s.w "sel.k")).charge 1) with hs3
  have hr3 : RegOnly s s3 ["cs.lo", "cs.n", "cs.k"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hs3, State.setW, hy.1, hy.2.1, hy.2.2]
  have hK3 : KR s3 := hL.regs _ _ hK (hr3.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, csRegs]))
  have e1 : s3.w "cs.lo" = s.w "sel.lo" := by simp [hs3]
  have e2 : s3.w "cs.n" = s.w "sel.n" := by simp [hs3]
  have e3 : s3.w "cs.k" = s.w "sel.k" := by simp [hs3]
  have hseg : seg s3 (s3.w "cs.lo") (s3.w "cs.n") = seg s (s.w "sel.lo") (s.w "sel.n") := by
    rw [e1, e2]; simp [seg, hs3]
  apply runs_seq
  refine (countSel_spec hL s3 hK3 (by rw [hseg]; exact hok) (by rw [e2, e3]; exact hk) (by rw [e1, e2]; simpa [hs3] using hcap)
    (by rw [e1, e2]; simpa [hs3] using hlen)).mono (fun s4 ⟨hK4, hm4, hkth4, hu4, hc4⟩ => ?_)
  rw [hseg, e3] at hkth4
  rw [hseg] at hm4
  have hwa4 : s4.wa "sel.w" = s.wa "sel.w" := by rw [(hu4.warr "sel.w" (by simp)).1]; simp [hs3]
  have hwl4 : s4.wlen "sel.w" = s.wlen "sel.w" := by rw [(hu4.warr "sel.w" (by simp)).2]; simp [hs3]
  apply runs_seq
  refine runs_wset (a := s4.w "cs.res") (by simp) ?_
  refine runs_wset (a := 0) (evalW_lit_of (by simp only [State.charge_cap, State.setW_cap]; rw [hu4.cap]; simpa [hs3] using h0)) ?_
  set r := (((s4.setW "sel.res" (s4.w "cs.res")).charge 1).setW "sel.go" 0).charge 1 with hr
  have hr5 : RegOnly s4 r ["sel.res", "sel.go"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hr, State.setW, hy.1, hy.2]
  refine ⟨hL.regs _ _ hK4 (hr5.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [myRegs, selRegs])),
    by simpa [hr] using hm4, by simpa [hr] using hkth4, by simp [hr], by simp [hr, hwa4],
    by simp [hr, hwl4], ?_, ?_, ?_⟩
  · have := hu4.wreg "sel.fp" (csW_keep hL (by simp))
    simp [hr, this, hs3]
  · have u1 : Unchanged s s3 ["sel.w"] [] (myRegs ++ lessW) lessV := (hr3.unch _ _ _).mono
      (List.Subset.refl _) (List.Subset.refl _)
      (myRegs_sub (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, csRegs]) _)
      (List.Subset.refl _)
    have u2 : Unchanged s3 s4 ["sel.w"] [] (myRegs ++ lessW) lessV := hu4.mono (List.nil_subset _)
      (List.Subset.refl _) (csW_sub lessW) (List.Subset.refl _)
    have u3 : Unchanged s4 r ["sel.w"] [] (myRegs ++ lessW) lessV := (hr5.unch _ _ _).mono
      (List.Subset.refl _) (List.Subset.refl _)
      (myRegs_sub (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [myRegs, selRegs]) _)
      (List.Subset.refl _)
    exact u1.trans (u2.trans u3)
  · simp only [hr, State.charge_cost, State.setW_cost]
    simp only [hs3, State.charge_cost, State.setW_cost, State.charge_w, State.setW_w] at hc4
    simp at hc4
    omega

theorem seg_congr {s r : State V} {lo n : ℕ} (h : ∀ q, lo ≤ q → q < lo + n → r.wa "sel.w" q = s.wa "sel.w" q) :
    seg r lo n = seg s lo n := by
  simp only [seg]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact h _ (by omega) (by omega)

theorem length_filter_seg (st : State V) (lo n : ℕ) (P : ℕ → Bool) :
    ((seg st lo n).filter P).length ≤ n := by
  have := List.length_filter_le P (seg st lo n)
  simpa using this

set_option maxHeartbeats 2000000 in
/-- **The partition**: two filter passes into `[top, top + a)` and `[top + a, top + a + b)`. -/
theorem partBlk_run (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (s : State V) (hK : KR s)
    (hok : ∀ x ∈ seg s (s.w "sel.lo") (s.w "sel.n"), ok x) (hokp : ok (s.w "sel.p"))
    (hov : s.w "sel.lo" + s.w "sel.n" ≤ s.w "sel.top")
    (hlen : s.w "sel.top" + 2 * s.w "sel.n" ≤ s.wlen "sel.w")
    (hcap : s.w "sel.top" + 2 * s.w "sel.n" + 1 < s.cap) :
    Runs ops (partBlk lessS) s (fun r => KR r ∧
      seg r (s.w "sel.top") (r.w "sel.a") =
        (seg s (s.w "sel.lo") (s.w "sel.n")).filter (fun x => decide (fP κ false (s.w "sel.p") x)) ∧
      seg r (s.w "sel.top" + r.w "sel.a") (r.w "sel.b") =
        (seg s (s.w "sel.lo") (s.w "sel.n")).filter (fun x => decide (fP κ true (s.w "sel.p") x)) ∧
      (∀ q, q < s.w "sel.top" → r.wa "sel.w" q = s.wa "sel.w" q) ∧
      r.wlen "sel.w" = s.wlen "sel.w" ∧
      (∀ y ∈ ["sel.lo", "sel.n", "sel.k", "sel.top", "sel.p", "sel.fp", "sel.go", "sel.res", "sel.g"],
        r.w y = s.w y) ∧
      Unchanged s r ["sel.w"] [] (myRegs ++ lessW) lessV ∧
      r.cost ≤ s.cost + 8 + 2 * (s.w "sel.n" * (Cl + 10))) := by
  set lo := s.w "sel.lo" with hlo
  set n := s.w "sel.n" with hn
  set top := s.w "sel.top" with htop
  set p := s.w "sel.p" with hp
  have hkeep : ∀ (cnt : String), cnt ∈ ["sel.a", "sel.b"] → ∀ y,
      y ∈ ["sel.lo", "sel.n", "sel.k", "sel.top", "sel.p", "sel.fp", "sel.go", "sel.res", "sel.g"] →
      y ∉ filtW cnt lessW := by
    intro cnt hcnt y hy hmem
    simp only [filtW, List.mem_append] at hmem
    rcases hmem with h | h
    · simp at hy h hcnt
      rcases hcnt with rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h
    · exact hL.disj y h (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs])
  unfold partBlk
  apply runs_seq
  refine runs_wset (a := top) rfl ?_
  set s1 := (s.setW "sel.m" top).charge 1 with hs1
  have hr1 : RegOnly s s1 ["sel.m"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_singleton] at hy
    simp [hs1, State.setW, hy]
  have hK1 : KR s1 := hL.regs _ _ hK (hr1.mono (by simp [myRegs, selRegs]))
  have e1 : ∀ y, y ≠ "sel.m" → s1.w y = s.w y := fun y hy => hr1.2.2.2.2.2.2.2 y (by simpa using hy)
  apply runs_seq
  refine (filt_spec hL false "sel.a" (by simp) s1 hK1
    (fun x hx => hok x (by simpa [seg, hs1] using hx)) (by rw [e1 _ (by simp)]; exact hokp)
    (by rw [e1 _ (by simp), e1 _ (by simp)]; simp [hs1]; omega)
    (by simp [hs1]; omega) (by simp [hs1]; omega)).mono
    (fun s2 ⟨hK2, hseg2, hout2, hwl2, hu2, hc2⟩ => ?_)
  have hm1 : s1.w "sel.m" = top := by simp [hs1]
  have hlo1 : s1.w "sel.lo" = lo := e1 _ (by simp)
  have hn1 : s1.w "sel.n" = n := e1 _ (by simp)
  have hp1 : s1.w "sel.p" = p := e1 _ (by simp)
  have hseg1 : seg s1 lo n = seg s lo n := by simp [seg, hs1]
  rw [hm1, hlo1, hn1, hp1, hseg1] at hseg2
  rw [hm1, hn1] at hout2
  have hk2 : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.k", "sel.top", "sel.p", "sel.fp", "sel.go", "sel.res", "sel.g"] →
      s2.w y = s.w y := by
    intro y hy
    rw [hu2.wreg y (hkeep "sel.a" (by simp) y hy)]
    exact e1 y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have ha2 : s2.w "sel.a" ≤ n := by
    have := congrArg List.length hseg2
    simp only [length_seg] at this
    rw [this]; exact length_filter_seg _ _ _ _
  have hcap2 : s2.cap = s.cap := by rw [hu2.cap]; simp [hs1]
  apply runs_seq
  have hT2 : s2.w "sel.top" = top := hk2 "sel.top" (by simp)
  refine runs_wset (a := top + s2.w "sel.a")
    (evalW_add_of (by rw [evalW_var, hT2]) rfl (by rw [hcap2]; omega)) ?_
  set s3 := (s2.setW "sel.m" (top + s2.w "sel.a")).charge 1 with hs3
  have hr3 : RegOnly s2 s3 ["sel.m"] := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    simp only [List.mem_singleton] at hy
    simp [hs3, State.setW, hy]
  have hK3 : KR s3 := hL.regs _ _ hK2 (hr3.mono (by simp [myRegs, selRegs]))
  have e3 : ∀ y, y ≠ "sel.m" → s3.w y = s2.w y := fun y hy => hr3.2.2.2.2.2.2.2 y (by simpa using hy)
  have hlo3 : s3.w "sel.lo" = lo := by rw [e3 _ (by simp), hk2 _ (by simp)]
  have hn3 : s3.w "sel.n" = n := by rw [e3 _ (by simp), hk2 _ (by simp)]
  have hp3 : s3.w "sel.p" = p := by rw [e3 _ (by simp), hk2 _ (by simp)]
  have hm3 : s3.w "sel.m" = top + s2.w "sel.a" := by simp [hs3]
  have hwl3 : s3.wlen "sel.w" = s.wlen "sel.w" := by simp [hs3, hwl2, hs1]
  have hcap3 : s3.cap = s.cap := by simp [hs3, hcap2]
  have hseg3 : seg s3 lo n = seg s lo n := by
    rw [← hseg1]
    apply seg_congr
    intro q h1 h2
    simp only [hs3, State.charge_wa, State.setW_wa]
    rw [hout2 q (Or.inl (by omega))]
  refine (filt_spec hL true "sel.b" (by simp) s3 hK3 (by rw [hlo3, hn3, hseg3]; exact hok)
    (by rw [hp3]; exact hokp) (by rw [hlo3, hn3, hm3]; omega)
    (by rw [hm3, hn3, hwl3]; omega) (by rw [hm3, hn3, hcap3]; omega)).mono
    (fun r ⟨hKr, hsegr, houtr, hwlr, hur, hcr⟩ => ?_)
  rw [hm3, hlo3, hn3, hp3] at hsegr
  rw [hm3, hn3] at houtr
  rw [hseg3] at hsegr
  have hra : r.w "sel.a" = s2.w "sel.a" := by
    rw [hur.wreg "sel.a" (by simp [filtW]; intro h; exact hL.disj _ h (by simp [myRegs, selRegs])),
      e3 _ (by simp)]
  refine ⟨hKr, ?_, by rw [hra]; exact hsegr, fun q hq => ?_, by rw [hwlr, hwl3], fun y hy => ?_, ?_, ?_⟩
  · rw [hra, ← hseg2]
    apply seg_congr
    intro q h1 h2
    rw [houtr q (Or.inl (by omega))]
    simp [hs3]
  · rw [houtr q (Or.inl (by omega))]
    simp only [hs3, State.charge_wa, State.setW_wa]
    rw [hout2 q (Or.inl hq)]
    simp [hs1]
  · rw [hur.wreg y (hkeep "sel.b" (by simp) y hy), e3 y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    exact hk2 y hy
  · have u1 : Unchanged s s1 ["sel.w"] [] (myRegs ++ lessW) lessV := (hr1.unch _ _ _).mono
      (List.Subset.refl _) (List.Subset.refl _) (myRegs_sub (by simp [myRegs, selRegs]) _)
      (List.Subset.refl _)
    have u2 : Unchanged s1 s2 ["sel.w"] [] (myRegs ++ lessW) lessV := hu2.mono (List.Subset.refl _)
      (List.Subset.refl _) (filtW_sub (by simp) lessW) (List.Subset.refl _)
    have u3 : Unchanged s2 s3 ["sel.w"] [] (myRegs ++ lessW) lessV := (hr3.unch _ _ _).mono
      (List.Subset.refl _) (List.Subset.refl _) (myRegs_sub (by simp [myRegs, selRegs]) _)
      (List.Subset.refl _)
    have u4 : Unchanged s3 r ["sel.w"] [] (myRegs ++ lessW) lessV := hur.mono (List.Subset.refl _)
      (List.Subset.refl _) (filtW_sub (by simp) lessW) (List.Subset.refl _)
    exact u1.trans (u2.trans (u3.trans u4))
  · have hc2' : s2.cost ≤ s.cost + 4 + n * (Cl + 10) := by
      rw [hn1] at hc2; simp only [hs1, State.charge_cost, State.setW_cost] at hc2; omega
    have hcr' : r.cost ≤ s2.cost + 4 + n * (Cl + 10) := by
      rw [hn3] at hcr; simp only [hs3, State.charge_cost, State.setW_cost] at hcr; omega
    omega

/-! ## Specification of the selection procedure -/

/-- the cost constant of selection -/
def Ksel (Cl : ℕ) : ℕ := 400 * Cl + 2100

variable (lessS KR ok κ Cl lessW lessV) in
/-- precondition of a call of the selection procedure on `n` elements -/
def SelPre (pSel : ℕ) (st : State V) (n : ℕ) : Prop :=
  KR st ∧ (∀ x ∈ seg st (st.w "sel.lo") n, ok x) ∧
    st.procs[pSel]? = some (selBody lessS pSel) ∧ st.w "sel.n" = n ∧ 1 ≤ n ∧
    st.w "sel.k" < n ∧ st.w "sel.lo" + n ≤ st.w "sel.top" ∧
    st.w "sel.top" + 5 * n + 60 ≤ st.wlen "sel.w" ∧ st.w "sel.top" + 5 * n + 60 < st.cap ∧
    300 < st.cap

variable (KR κ Cl lessW lessV) in
/-- postcondition of a call of the selection procedure on `n` elements -/
def SelPost (st : State V) (n : ℕ) (r : State V) : Prop :=
  KR r ∧ r.w "sel.res" ∈ seg st (st.w "sel.lo") n ∧
    Frontier.CHD.IsKth ((seg st (st.w "sel.lo") n).map κ) (st.w "sel.k") (κ (r.w "sel.res")) ∧
    r.w "sel.fp" = st.w "sel.fp" ∧ (∀ q, q < st.w "sel.top" → r.wa "sel.w" q = st.wa "sel.w" q) ∧
    r.wlen "sel.w" = st.wlen "sel.w" ∧ Unchanged st r ["sel.w"] [] (myRegs ++ lessW) lessV ∧
    r.cost ≤ st.cost + Ksel Cl * n + 100

theorem map_filter_fP (κ : ℕ → α) (gt : Bool) (p : ℕ) (L : List ℕ) :
    (L.filter (fun x => decide (fP κ gt p x))).map κ =
      (L.map κ).filter (fun y => decide (if gt then κ p < y else y < κ p)) := by
  cases gt
  · simp only [fP, Bool.false_eq_true, if_false]
    induction L with
    | nil => rfl
    | cons a L ih =>
      by_cases h : κ a < κ p
      · simp [List.filter_cons, h, ih]
      · simp [List.filter_cons, h, ih]
  · simp only [fP, if_true]
    induction L with
    | nil => rfl
    | cons a L ih =>
      by_cases h : κ p < κ a
      · simp [List.filter_cons, h, ih]
      · simp [List.filter_cons, h, ih]

theorem isKth_mem_of {l : List α} {k : ℕ} {x : α} (h : Frontier.CHD.IsKth l k x) : x ∈ l := h.1

/-! ## The loop of the selection procedure -/

variable (KR κ Cl lessW lessV) in
/-- invariant of the selection loop, relative to the call state `st` on `n` elements -/
structure LI (st : State V) (n : ℕ) (s : State V) : Prop where
  kr : KR s
  procs : s.procs = st.procs
  cap : s.cap = st.cap
  wlen : s.wlen "sel.w" = st.wlen "sel.w"
  fp : s.w "sel.fp" = st.w "sel.fp"
  low : ∀ q, q < st.w "sel.top" → s.wa "sel.w" q = st.wa "sel.w" q
  unch : Unchanged st s ["sel.w"] [] (myRegs ++ lessW) lessV
  run : s.w "sel.go" ≠ 0 →
    1 ≤ s.w "sel.n" ∧ s.w "sel.k" < s.w "sel.n" ∧ s.w "sel.lo" + s.w "sel.n" ≤ s.w "sel.top" ∧
    st.w "sel.top" ≤ s.w "sel.top" ∧ s.w "sel.top" + 5 * s.w "sel.n" ≤ st.w "sel.top" + 5 * n ∧
    (∀ x ∈ seg s (s.w "sel.lo") (s.w "sel.n"), x ∈ seg st (st.w "sel.lo") n) ∧
    (∀ v, Frontier.CHD.IsKth ((seg s (s.w "sel.lo") (s.w "sel.n")).map κ) (s.w "sel.k") v →
      Frontier.CHD.IsKth ((seg st (st.w "sel.lo") n).map κ) (st.w "sel.k") v) ∧
    s.cost + Ksel Cl * s.w "sel.n" ≤ st.cost + 2 + Ksel Cl * n
  done : s.w "sel.go" = 0 →
    s.w "sel.res" ∈ seg st (st.w "sel.lo") n ∧
    Frontier.CHD.IsKth ((seg st (st.w "sel.lo") n).map κ) (st.w "sel.k") (κ (s.w "sel.res")) ∧
    s.cost ≤ st.cost + Ksel Cl * n + 99

/-- measure of the selection loop -/
def selMu (s : State V) : ℕ := if s.w "sel.go" = 0 then 0 else s.w "sel.n" + 1

theorem sel_cost_base (n Cl : ℕ) (hn : n ≤ 200) :
    n * (n * (2 * Cl + 10) + 12) ≤ Ksel Cl * n := by
  unfold Ksel
  calc n * (n * (2 * Cl + 10) + 12) ≤ n * (200 * (2 * Cl + 10) + 12) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
    _ ≤ (400 * Cl + 2100) * n := by nlinarith

theorem sel_cost_step (n G n' Cl : ℕ) (hn : 201 ≤ n) (hG : 5 * G ≤ n + 4)
    (hn' : 10 * n' ≤ 7 * n + 30) :
    G * (50 * Cl + 320 + Ksel Cl) + 100 + 2 * n * (Cl + 10) + 60 + Ksel Cl * n' ≤ Ksel Cl * n := by
  unfold Ksel; nlinarith

theorem sel_cost_mid (n G Cl : ℕ) (hn : 201 ≤ n) (hG : 5 * G ≤ n + 4) :
    G * (50 * Cl + 320 + Ksel Cl) + 100 + 2 * n * (Cl + 10) + 60 ≤ Ksel Cl * n := by
  unfold Ksel; nlinarith

/-- **One base iteration** (`n ≤ 200`). -/
theorem baseIter_run (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (pSel : ℕ) (st : State V) (n : ℕ)
    (hcapst : st.w "sel.top" + 5 * n + 60 < st.cap) (h300 : 300 < st.cap)
    (hspace : st.w "sel.top" + 5 * n + 60 ≤ st.wlen "sel.w")
    (hok0 : ∀ x ∈ seg st (st.w "sel.lo") n, ok x)
    (s : State V) (hI : LI KR κ Cl lessW lessV st n s) (hgo : s.w "sel.go" ≠ 0)
    (hsmall : s.w "sel.n" < 201) :
    Runs ops (selIter lessS pSel) (s.charge 1) (fun r =>
      LI KR κ Cl lessW lessV st n r ∧ selMu r < selMu s) := by
  obtain ⟨hn1, hk, hov, htop0, hsp, hsub, htr, hcost⟩ := hI.run hgo
  have hcs : s.cap = st.cap := hI.cap
  have h1 : 1 < s.cap := by rw [hcs]; omega
  have hwl : s.wlen "sel.w" = st.wlen "sel.w" := hI.wlen
  unfold selIter
  refine runs_ite_true (x := 1) ?_ one_ne_zero ?_
  · rw [evalW_lt_of rfl (evalW_lit_of (by simp; omega)) (by simpa using h1)]
    simp [hsmall]
  set s1 := (s.charge 1).charge 1 with hs1
  have hK1 : KR s1 := hL.regs _ _ hI.kr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  refine (baseCase_run hL s1 hK1 (fun x hx => hok0 x (hsub x (by simpa [seg, hs1] using hx)))
    (by simpa [hs1] using hk) (by simp [hs1]; omega)
    (by simp [hs1, hwl]; omega)).mono
    (fun r ⟨hKr, hres, hkth, hgor, hwar, hwlr, hfpr, hur, hcr⟩ => ?_)
  have hseg1 : seg s1 (s1.w "sel.lo") (s1.w "sel.n") = seg s (s.w "sel.lo") (s.w "sel.n") := by
    simp [seg, hs1]
  have hk1 : s1.w "sel.k" = s.w "sel.k" := by simp [hs1]
  rw [hseg1] at hres
  rw [hseg1, hk1] at hkth
  have hn' : s1.w "sel.n" = s.w "sel.n" := by simp [hs1]
  rw [hn'] at hcr
  refine ⟨⟨hKr, by rw [hur.procs]; simp [hs1, hI.procs], by rw [hur.cap]; simp [hs1, hcs], by rw [hwlr]; simp [hs1, hwl],
    by rw [hfpr]; simp [hs1, hI.fp], fun q hq => by rw [hwar]; simp [hs1, hI.low q hq],
    hI.unch.trans ((Unchanged.charge _ _ _ _ _ _).trans ((Unchanged.charge _ _ _ _ _ _).trans hur)),
    fun h => absurd hgor h, fun _ => ⟨hsub _ hres, htr _ hkth, ?_⟩⟩, ?_⟩
  · have hb := sel_cost_base (s.w "sel.n") Cl (by omega)
    simp only [hs1, State.charge_cost] at hcr
    omega
  · simp [selMu, hgor, hgo]

theorem sel_cost_step' (n G n' Cl : ℕ) (hn : 201 ≤ n) (hG : 5 * G ≤ n + 4)
    (hn' : 10 * n' ≤ 7 * n + 30) :
    G * (50 * Cl + 320) + Ksel Cl * G + 2 * (n * (Cl + 10)) + 160 + Ksel Cl * n' ≤ Ksel Cl * n := by
  unfold Ksel; nlinarith

theorem sel_cost_mid' (n G Cl : ℕ) (hn : 201 ≤ n) (hG : 5 * G ≤ n + 4) :
    G * (50 * Cl + 320) + Ksel Cl * G + 2 * (n * (Cl + 10)) + 160 ≤ Ksel Cl * n := by
  unfold Ksel; nlinarith

section SaveRestore

variable (s : State V)

theorem saveState_w (y : String) : (saveState s).w y =
    if y = "sel.top" then s.w "sel.top" + s.w "sel.g" + 5
    else if y = "sel.k" then (s.w "sel.g" - 1) / 2
    else if y = "sel.n" then s.w "sel.g"
    else if y = "sel.lo" then s.w "sel.top"
    else if y = "sel.fp" then s.w "sel.top" + s.w "sel.g"
    else if y = "sel.x" then s.w "sel.top" + s.w "sel.g"
    else s.w y := by
  simp only [saveState, State.charge_w, State.setW_w, State.storeW_w]

theorem saveState_wa (q : ℕ) : (saveState s).wa "sel.w" q =
    if q = s.w "sel.top" + s.w "sel.g" + 4 then s.w "sel.fp"
    else if q = s.w "sel.top" + s.w "sel.g" + 3 then s.w "sel.top"
    else if q = s.w "sel.top" + s.w "sel.g" + 2 then s.w "sel.k"
    else if q = s.w "sel.top" + s.w "sel.g" + 1 then s.w "sel.n"
    else if q = s.w "sel.top" + s.w "sel.g" then s.w "sel.lo"
    else s.wa "sel.w" q := by
  simp only [saveState, State.charge_wa, State.setW_wa, State.storeW_wa, true_and]

theorem saveState_wa_other (b : String) (hb : b ≠ "sel.w") : (saveState s).wa b = s.wa b := by
  funext q; simp [saveState, State.storeW, hb]

@[simp] theorem saveState_wlen : (saveState s).wlen = s.wlen := by simp [saveState]
@[simp] theorem saveState_va : (saveState s).va = s.va := by simp [saveState]
@[simp] theorem saveState_vlen : (saveState s).vlen = s.vlen := by simp [saveState]
@[simp] theorem saveState_v : (saveState s).v = s.v := by simp [saveState]
@[simp] theorem saveState_cap : (saveState s).cap = s.cap := by simp [saveState]
@[simp] theorem saveState_procs : (saveState s).procs = s.procs := by simp [saveState]
@[simp] theorem saveState_cost : (saveState s).cost = s.cost + 11 := by simp [saveState]

theorem restoreState_w (y : String) : (restoreState s).w y =
    if y = "sel.go" then 1
    else if y = "sel.fp" then s.wa "sel.w" (s.w "sel.fp" + 4)
    else if y = "sel.top" then s.wa "sel.w" (s.w "sel.fp" + 3)
    else if y = "sel.k" then s.wa "sel.w" (s.w "sel.fp" + 2)
    else if y = "sel.n" then s.wa "sel.w" (s.w "sel.fp" + 1)
    else if y = "sel.lo" then s.wa "sel.w" (s.w "sel.fp")
    else if y = "sel.p" then s.w "sel.res"
    else s.w y := by
  simp only [restoreState, State.charge_w, State.setW_w, State.charge_wa, State.setW_wa]

theorem restoreState_regOnly :
    RegOnly s (restoreState s) ["sel.p", "sel.lo", "sel.n", "sel.k", "sel.top", "sel.fp", "sel.go"] := by
  refine ⟨by simp [restoreState], by simp [restoreState], by simp [restoreState],
    by simp [restoreState], by simp [restoreState], by simp [restoreState],
    by simp [restoreState], fun y hy => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  rw [restoreState_w]
  simp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1, hy.2.2.2.2.2.2]

@[simp] theorem restoreState_cost : (restoreState s).cost = s.cost + 7 := by simp [restoreState]

end SaveRestore

theorem saveState_unch (s : State V) (lessW lessV : List String) :
    Unchanged s (saveState s) ["sel.w"] [] (myRegs ++ lessW) lessV := by
  refine ⟨fun b hb => ?_, fun b _ => ⟨by simp, by simp⟩, fun y hy => ?_, fun y _ => by simp, by simp,
    by simp⟩
  · have hbw : b ≠ "sel.w" := by simpa using hb
    exact ⟨saveState_wa_other s b hbw, by simp⟩
  · have hy' : y ∉ myRegs := fun h => hy (List.mem_append_left _ h)
    rw [saveState_w]
    have h1 : y ≠ "sel.top" := fun e => hy' (by rw [e]; simp [myRegs, selRegs])
    have h2 : y ≠ "sel.k" := fun e => hy' (by rw [e]; simp [myRegs, selRegs])
    have h3 : y ≠ "sel.n" := fun e => hy' (by rw [e]; simp [myRegs, selRegs])
    have h4 : y ≠ "sel.lo" := fun e => hy' (by rw [e]; simp [myRegs, selRegs])
    have h5 : y ≠ "sel.fp" := fun e => hy' (by rw [e]; simp [myRegs, selRegs])
    have h6 : y ≠ "sel.x" := fun e => hy' (by rw [e]; simp [myRegs, selRegs])
    simp [h1, h2, h3, h4, h5, h6]

set_option maxHeartbeats 8000000 in
/-- **One recursive iteration** (`n > 200`): medians, recursive pivot call, partition, branch. -/
theorem recIter_run [Inhabited α] (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (pSel : ℕ)
    (st : State V) (n : ℕ)
    (hcapst : st.w "sel.top" + 5 * n + 60 < st.cap) (h300 : 300 < st.cap)
    (hspace : st.w "sel.top" + 5 * n + 60 ≤ st.wlen "sel.w")
    (hprocs : st.procs[pSel]? = some (selBody lessS pSel))
    (hih : ∀ m < n, ∀ st', SelPre lessS KR ok pSel st' m →
      Runs ops (.call pSel) st' (SelPost KR κ Cl lessW lessV st' m))
    (hok0 : ∀ x ∈ seg st (st.w "sel.lo") n, ok x)
    (s : State V) (hI : LI KR κ Cl lessW lessV st n s) (hgo : s.w "sel.go" ≠ 0)
    (hbig : ¬ s.w "sel.n" < 201) :
    Runs ops (selIter lessS pSel) (s.charge 1) (fun r =>
      LI KR κ Cl lessW lessV st n r ∧ selMu r < selMu s) := by
  obtain ⟨hn1, hk, hov, htop0, hsp, hsub, htr, hcost⟩ := hI.run hgo
  set lo := s.w "sel.lo" with hlo
  set n' := s.w "sel.n" with hn'
  set k := s.w "sel.k" with hkk
  set top := s.w "sel.top" with htop
  set G := (n' + 4) / 5 with hG
  have hcs : s.cap = st.cap := hI.cap
  have hwl : s.wlen "sel.w" = st.wlen "sel.w" := hI.wlen
  have hnn : n' ≤ n := by omega
  have hGlt : G < n := by omega
  unfold selIter
  refine runs_ite_false ?_ ?_
  · rw [evalW_lt_of rfl (evalW_lit_of (by simp; omega)) (by simp; omega)]
    split_ifs with h
    · exact absurd (by simpa using h) hbig
    · rfl
  set s1 := (s.charge 1).charge 1 with hs1
  have hK1 : KR s1 := hL.regs _ _ hI.kr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hs1w : ∀ y, s1.w y = s.w y := fun y => by simp [hs1]
  have hs1wa : s1.wa "sel.w" = s.wa "sel.w" := by simp [hs1]
  unfold recCase
  -- medians
  apply runs_seq
  refine (medLoop_spec hL s1 hK1 (fun x hx => hok0 x (hsub x (by simpa [seg, hs1] using hx)))
    (by rw [hs1w]; exact hn1) (by rw [hs1w, hs1w, hs1w]; exact hov)
    (by rw [hs1w, hs1w]; simp [hs1, hwl]; omega) (by rw [hs1w, hs1w]; simp [hs1, hcs]; omega)).mono
    (fun s2 ⟨hK2, hg2, hmed2, hout2, hwl2, hu2, hc2⟩ => ?_)
  simp only [hs1w] at hg2 hmed2 hout2 hc2
  have hk2 : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.top", "sel.k", "sel.fp"] → s2.w y = s.w y := by
    intro y hy; rw [hu2.wreg y (medW_keep hL hy), hs1w]
  have hcap2 : s2.cap = st.cap := by rw [hu2.cap]; simp [hs1, hcs]
  have hwl2' : s2.wlen "sel.w" = st.wlen "sel.w" := by rw [hwl2]; simp [hs1, hwl]
  have hprocs2 : s2.procs = st.procs := by rw [hu2.procs]; simp [hs1, hI.procs]
  -- save the frame
  apply runs_seq
  refine (saveBlk_run s2 (by rw [hk2 "sel.top" (by simp), hg2, hcap2]; omega)
    (by rw [hk2 "sel.top" (by simp), hg2, hwl2']; omega)).mono (fun s3 hs3 => ?_)
  subst hs3
  have hK3 : KR (saveState s2) := hL.frame _ _ hK2 (fun b hb => saveState_wa_other _ b hb)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (fun y hy => by
      rw [saveState_w]
      have h1 : y ≠ "sel.top" := fun e => hy (by rw [e]; simp [myRegs, selRegs])
      have h2 : y ≠ "sel.k" := fun e => hy (by rw [e]; simp [myRegs, selRegs])
      have h3 : y ≠ "sel.n" := fun e => hy (by rw [e]; simp [myRegs, selRegs])
      have h4 : y ≠ "sel.lo" := fun e => hy (by rw [e]; simp [myRegs, selRegs])
      have h5 : y ≠ "sel.fp" := fun e => hy (by rw [e]; simp [myRegs, selRegs])
      have h6 : y ≠ "sel.x" := fun e => hy (by rw [e]; simp [myRegs, selRegs])
      simp [h1, h2, h3, h4, h5, h6])
  have e3 : ∀ y, (saveState s2).w y = _ := saveState_w s2
  have h3n : (saveState s2).w "sel.n" = G := by rw [e3]; simp [hg2]; try rfl
  have h3k : (saveState s2).w "sel.k" = (G - 1) / 2 := by rw [e3]; simp [hg2]; try rfl
  have h3lo : (saveState s2).w "sel.lo" = top := by rw [e3]; simp [hk2 "sel.top" (by simp)]; try rfl
  have h3top : (saveState s2).w "sel.top" = top + G + 5 := by
    rw [e3]; simp [hk2 "sel.top" (by simp), hg2]; try rfl
  have h3fp : (saveState s2).w "sel.fp" = top + G := by
    rw [e3]; simp [hk2 "sel.top" (by simp), hg2]; try rfl
  have hg2' : s2.w "sel.g" = G := hg2
  have hsw : ∀ q, (saveState s2).wa "sel.w" q =
      if q = top + G + 4 then s.w "sel.fp" else if q = top + G + 3 then top
      else if q = top + G + 2 then k else if q = top + G + 1 then n'
      else if q = top + G then lo else s2.wa "sel.w" q := by
    intro q
    rw [saveState_wa, hk2 "sel.top" (by simp), hg2', hk2 "sel.fp" (by simp), hk2 "sel.k" (by simp),
      hk2 "sel.n" (by simp), hk2 "sel.lo" (by simp)]
  have hmedcell : ∀ q, q < G → (saveState s2).wa "sel.w" (top + q) = s2.wa "sel.w" (top + q) := by
    intro q hq
    rw [hsw, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  have hokmed : ∀ x ∈ seg (saveState s2) ((saveState s2).w "sel.lo") G, ok x := by
    rw [h3lo]
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hq
    rw [hmedcell q hq]
    have h1 := (hmed2 q hq).1
    exact hok0 _ (hsub _ (by simpa [seg, hs1] using grp_sub_seg h1))
  -- the recursive call
  apply runs_seq
  refine (hih G hGlt (saveState s2) ⟨hK3, hokmed, by rw [saveState_procs, hprocs2]; exact hprocs, h3n,
    by omega, by rw [h3k]; omega, by rw [h3lo, h3top]; omega,
    by rw [h3top, saveState_wlen, hwl2']; omega, by rw [h3top, saveState_cap, hcap2]; omega,
    by rw [saveState_cap, hcap2]; exact h300⟩).mono
    (fun s4 ⟨hK4, hres4, hkth4, hfp4, hlow4, hwl4, hu4, hc4⟩ => ?_)
  rw [h3lo] at hres4
  rw [h3lo, h3k] at hkth4
  rw [h3top] at hlow4
  have hcap4 : s4.cap = st.cap := by rw [hu4.cap, saveState_cap, hcap2]
  have hwl4' : s4.wlen "sel.w" = st.wlen "sel.w" := by rw [hwl4, saveState_wlen, hwl2']
  -- restore
  apply runs_seq
  refine (restoreBlk_run s4 (by rw [hfp4, h3fp, hcap4]; omega)
    (by rw [hfp4, h3fp, hwl4']; omega)).mono (fun s5 hs5 => ?_)
  subst hs5
  have hro5 := restoreState_regOnly s4
  have hK5 : KR (restoreState s4) := hL.regs _ _ hK4 (hro5.mono (by
    intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs]))
  have hf0 : s4.wa "sel.w" (top + G) = lo := by
    rw [hlow4 _ (by omega), hsw]; simp
  have hf1 : s4.wa "sel.w" (top + G + 1) = n' := by
    rw [hlow4 _ (by omega), hsw]; simp
  have hf2 : s4.wa "sel.w" (top + G + 2) = k := by
    rw [hlow4 _ (by omega), hsw]; simp
  have hf3 : s4.wa "sel.w" (top + G + 3) = top := by
    rw [hlow4 _ (by omega), hsw]; simp
  have hf4 : s4.wa "sel.w" (top + G + 4) = s.w "sel.fp" := by
    rw [hlow4 _ (by omega), hsw]; simp
  -- after the restore
  have hfp4' : s4.w "sel.fp" = top + G := by rw [hfp4, h3fp]
  set s5 := restoreState s4 with hs5
  have e5 : ∀ y, s5.w y = _ := restoreState_w s4
  have h5lo : s5.w "sel.lo" = lo := by rw [e5]; simp [hfp4', hf0]
  have h5n : s5.w "sel.n" = n' := by rw [e5]; simp [hfp4', hf1]
  have h5k : s5.w "sel.k" = k := by rw [e5]; simp [hfp4', hf2]
  have h5top : s5.w "sel.top" = top := by rw [e5]; simp [hfp4', hf3]
  have h5fp : s5.w "sel.fp" = s.w "sel.fp" := by rw [e5]; simp [hfp4', hf4]
  have h5p : s5.w "sel.p" = s4.w "sel.res" := by rw [e5]; simp
  have h5wa : s5.wa "sel.w" = s4.wa "sel.w" := by rw [hs5]; exact congrFun hro5.1 "sel.w"
  have hcap5 : s5.cap = st.cap := by rw [hs5, hro5.2.2.2.2.2.1, hcap4]
  have hwl5 : s5.wlen "sel.w" = st.wlen "sel.w" := by rw [hs5, hro5.2.1, hwl4']
  -- cells below `top` are the original ones
  have hlowtop : ∀ q, q < top → s5.wa "sel.w" q = s.wa "sel.w" q := by
    intro q hq
    rw [h5wa, hlow4 q (by omega), hsw q, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), hout2 q (Or.inl hq), hs1wa]
  have hseg5 : seg s5 lo n' = seg s lo n' := seg_congr (fun q _ h2 => hlowtop q (by omega))
  have hseg1 : seg s1 lo n' = seg s lo n' := by simp [seg, hs1]
  -- the medians and the pivot
  set p := s4.w "sel.res" with hp
  have hms : ∀ q (hq : q < (seg (saveState s2) top G).length),
      MedOK κ s1 lo n' q ((seg (saveState s2) top G)[q]) := by
    intro q hq
    have hq' : q < G := by simpa using hq
    simp only [seg, List.getElem_map, List.getElem_range]
    rw [hmedcell q hq']
    exact hmed2 q hq'
  have hmeq := medians_eq κ s1 lo n' (seg (saveState s2) top G) (by simp [hG]) hms
  rw [hmeq] at hkth4
  set l := (seg s1 lo n').map κ with hl
  have hlen_l : l.length = n' := by simp [hl]
  have hmlen : ((Frontier.CHD.chunk5 l).map Frontier.CHD.med).length = G := by
    simp [Frontier.CHD.length_chunk5, hlen_l, hG]
  rw [← hmlen] at hkth4
  obtain ⟨hlo10, hhi10⟩ := Frontier.CHD.mom_bound l (κ p) hkth4
  rw [hlen_l] at hlo10 hhi10
  have hpmem : p ∈ seg s lo n' := by
    obtain ⟨q, hq, hpq⟩ := List.mem_map.mp hres4
    rw [List.mem_range] at hq
    have h1 := (hmed2 q hq).1
    rw [← hmedcell q hq] at h1
    rw [hpq] at h1
    rw [← hseg1]; exact grp_sub_seg h1
  -- partition
  apply runs_seq
  refine (partBlk_run hL s5 hK5 (by rw [h5lo, h5n, hseg5]; exact fun x hx => hok0 x (hsub x hx))
    (by rw [h5p]; exact hok0 _ (hsub _ hpmem)) (by rw [h5lo, h5n, h5top]; exact hov)
    (by rw [h5top, h5n, hwl5]; omega) (by rw [h5top, h5n, hcap5]; omega)).mono
    (fun s6 ⟨hK6, hsa6, hsb6, hout6, hwl6, hregs6, hu6, hc6⟩ => ?_)
  rw [h5top, h5lo, h5n, h5p, hseg5] at hsa6 hsb6
  rw [h5top] at hout6
  have h6 : ∀ y, y ∈ ["sel.lo", "sel.n", "sel.k", "sel.top", "sel.p", "sel.fp", "sel.go", "sel.res", "sel.g"] →
      s6.w y = s5.w y := hregs6
  have h6k : s6.w "sel.k" = k := by rw [h6 _ (by simp), h5k]
  have h6n : s6.w "sel.n" = n' := by rw [h6 _ (by simp), h5n]
  have h6top : s6.w "sel.top" = top := by rw [h6 _ (by simp), h5top]
  have h6p : s6.w "sel.p" = p := by rw [h6 _ (by simp), h5p]
  have h6fp : s6.w "sel.fp" = s.w "sel.fp" := by rw [h6 _ (by simp), h5fp]
  have h6go : s6.w "sel.go" = 1 := by rw [h6 _ (by simp), e5]; simp
  -- sizes of the two parts
  have hseg1' : l = (seg s lo n').map κ := by rw [hl, hseg1]
  have hmapa : ((seg s lo n').filter (fun x => decide (fP κ false p x))).map κ =
      l.filter (fun y => decide (y < κ p)) := by
    rw [map_filter_fP, hseg1']; simp
  have hmapb : ((seg s lo n').filter (fun x => decide (fP κ true p x))).map κ =
      l.filter (fun y => decide (κ p < y)) := by
    rw [map_filter_fP, hseg1']; simp
  have ha_eq : s6.w "sel.a" = Frontier.CHD.cntLt l (κ p) := by
    have h1 := congrArg List.length hsa6
    simp only [length_seg] at h1
    rw [h1, ← List.length_map (f := κ), hmapa, ← List.countP_eq_length_filter]; rfl
  have hb_eq : s6.w "sel.b" = (l.filter (fun y => decide (κ p < y))).length := by
    have h1 := congrArg List.length hsb6
    simp only [length_seg] at h1
    rw [h1, ← List.length_map (f := κ), hmapb]
  have hle_eq := Frontier.CHD.length_filter_gt_add_cntLe l (κ p)
  rw [hlen_l, ← hb_eq] at hle_eq
  have hltle : Frontier.CHD.cntLt l (κ p) ≤ Frontier.CHD.cntLe l (κ p) :=
    List.countP_mono_left (fun y _ hy => by simp at hy ⊢; exact hy.le)
  set a := s6.w "sel.a" with ha
  set b := s6.w "sel.b" with hb
  have hab : a + b ≤ n' := by omega
  have h10a : 10 * a ≤ 7 * n' + 30 := by rw [ha_eq]; exact hlo10
  have h10b : 10 * b ≤ 7 * n' + 30 := by rw [hb_eq]; exact hhi10
  have hpl : κ p ∈ l := by rw [hseg1']; exact List.mem_map_of_mem hpmem
  -- the common frame facts
  have hcap6 : s6.cap = st.cap := by rw [hu6.cap, hcap5]
  have hwl6' : s6.wlen "sel.w" = st.wlen "sel.w" := by rw [hwl6, hwl5]
  have hprocs6 : s6.procs = st.procs := by
    rw [hu6.procs, hs5, hro5.2.2.2.2.2.2.1, hu4.procs, saveState_procs, hprocs2]
  have hu_all : Unchanged st s6 ["sel.w"] [] (myRegs ++ lessW) lessV := by
    have u1 : Unchanged s s1 ["sel.w"] [] (myRegs ++ lessW) lessV :=
      (Unchanged.charge _ _ _ _ _ _).trans (Unchanged.charge _ _ _ _ _ _)
    have u2 : Unchanged s1 s2 ["sel.w"] [] (myRegs ++ lessW) lessV := hu2.mono (List.Subset.refl _)
      (List.Subset.refl _) (medW_sub lessW) (List.Subset.refl _)
    have u3 := saveState_unch s2 lessW lessV
    have u5 : Unchanged s4 s5 ["sel.w"] [] (myRegs ++ lessW) lessV := (hro5.unch _ _ _).mono
      (List.Subset.refl _) (List.Subset.refl _)
      (myRegs_sub (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs]) _)
      (List.Subset.refl _)
    exact hI.unch.trans (u1.trans (u2.trans (u3.trans (hu4.trans (u5.trans hu6)))))
  have hlow6 : ∀ q, q < st.w "sel.top" → s6.wa "sel.w" q = st.wa "sel.w" q := by
    intro q hq
    rw [hout6 q (by omega), hlowtop q (by omega), hI.low q hq]
  have hcost6 : s6.cost + Ksel Cl * 0 ≤ s.cost + G * (50 * Cl + 320) + Ksel Cl * G +
      2 * (n' * (Cl + 10)) + 132 := by
    have hc2' : s2.cost ≤ s1.cost + 2 + G * (50 * Cl + 320) := hc2
    rw [h5n] at hc6
    simp only [hs5, restoreState_cost, saveState_cost] at hc6 hc4
    simp only [hs1, State.charge_cost] at hc2'
    omega
  have hGb : 5 * G ≤ n' + 4 := by omega
  have hn201 : 201 ≤ n' := by omega
  -- the branch
  have hcap6' : 1 < s6.cap := by rw [hcap6]; omega
  have hcab : s6.w "sel.top" + (s6.w "sel.a" + s6.w "sel.b") < s6.cap := by
    rw [h6top, hcap6]; omega
  by_cases hka : k < a
  · refine (branch_lo s6 hcap6' hcab (by rw [h6k]; exact hka)).mono
      (fun r ⟨hlor, hnr, htopr, hror, hcr⟩ => ?_)
    rw [h6top] at hlor htopr
    rw [← ha] at hnr
    rw [← ha, ← hb] at htopr
    have hw : ∀ y, y ∉ ["sel.lo", "sel.n", "sel.top"] → r.w y = s6.w y := hror.2.2.2.2.2.2.2
    have hkr : r.w "sel.k" = k := by rw [hw _ (by simp), h6k]
    have hgor : r.w "sel.go" = 1 := by rw [hw _ (by simp), h6go]
    have hfpr : r.w "sel.fp" = s.w "sel.fp" := by rw [hw _ (by simp), h6fp]
    have hwar : r.wa "sel.w" = s6.wa "sel.w" := congrFun hror.1 "sel.w"
    have hsegr : seg r top a = (seg s lo n').filter (fun x => decide (fP κ false p x)) := by
      rw [← hsa6]; simp [seg, hwar]
    refine ⟨⟨hL.regs _ _ hK6 (hror.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, selRegs])),
      by rw [hror.2.2.2.2.2.2.1, hprocs6], by rw [hror.2.2.2.2.2.1, hcap6],
      by rw [hror.2.1, hwl6'], by rw [hfpr, hI.fp],
      fun q hq => by rw [hwar, hlow6 q hq],
      hu_all.trans ((hror.unch _ _ _).mono (List.Subset.refl _) (List.Subset.refl _)
        (myRegs_sub (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [myRegs, selRegs]) _)
        (List.Subset.refl _)),
      fun _ => ?_, fun h => absurd h (by rw [hgor]; decide)⟩, ?_⟩
    · rw [hlor, hnr, hkr, htopr]
      refine ⟨by omega, hka, by omega, by omega, by omega, fun x hx => ?_, fun v hv => ?_, ?_⟩
      · rw [hsegr] at hx
        exact hsub x (List.mem_filter.mp hx).1
      · rw [hsegr, hmapa] at hv
        exact htr v (hseg1' ▸ Frontier.CHD.isKth_of_filter_lt hv)
      · have hstep := sel_cost_step' n' G a Cl hn201 hGb h10a
        omega
    · simp [selMu, hgor, hgo, hnr]; omega
  · by_cases hkb : k < n' - b
    · refine (branch_mid s6 hcap6' (by rw [h6k]; exact hka)
        (by rw [h6k, h6n]; exact hkb)).mono (fun r ⟨hresr, hgor, hror, hcr⟩ => ?_)
      have hw : ∀ y, y ∉ ["sel.res", "sel.go"] → r.w y = s6.w y := hror.2.2.2.2.2.2.2
      have hfpr : r.w "sel.fp" = s.w "sel.fp" := by rw [hw _ (by simp), h6fp]
      have hwar : r.wa "sel.w" = s6.wa "sel.w" := congrFun hror.1 "sel.w"
      rw [h6p] at hresr
      refine ⟨⟨hL.regs _ _ hK6 (hror.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [myRegs, selRegs])),
        by rw [hror.2.2.2.2.2.2.1, hprocs6], by rw [hror.2.2.2.2.2.1, hcap6],
        by rw [hror.2.1, hwl6'], by rw [hfpr, hI.fp],
        fun q hq => by rw [hwar, hlow6 q hq],
        hu_all.trans ((hror.unch _ _ _).mono (List.Subset.refl _) (List.Subset.refl _)
          (myRegs_sub (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [myRegs, selRegs]) _)
          (List.Subset.refl _)),
        fun h => absurd hgor h, fun _ => ⟨?_, ?_, ?_⟩⟩, ?_⟩
      · rw [hresr]; exact hsub p hpmem
      · rw [hresr]
        refine htr (κ p) ⟨?_, ?_, ?_⟩
        · rw [← hseg1']; exact hpl
        · rw [← hseg1']; omega
        · rw [← hseg1']; omega
      · have hmid := sel_cost_mid' n' G Cl hn201 hGb
        omega
      · simp [selMu, hgor, hgo]
    · refine (branch_hi s6 hcap6' hcab (by rw [h6k]; exact hka)
        (by rw [h6k, h6n]; exact hkb)).mono (fun r ⟨hlor, hkr, hnr, htopr, hror, hcr⟩ => ?_)
      rw [h6top, ← ha] at hlor
      rw [h6top, ← ha, ← hb] at htopr
      rw [h6k, h6n, ← hb] at hkr
      rw [← hb] at hnr
      have hw : ∀ y, y ∉ ["sel.lo", "sel.k", "sel.n", "sel.top"] → r.w y = s6.w y :=
        hror.2.2.2.2.2.2.2
      have hgor : r.w "sel.go" = 1 := by rw [hw _ (by simp), h6go]
      have hfpr : r.w "sel.fp" = s.w "sel.fp" := by rw [hw _ (by simp), h6fp]
      have hwar : r.wa "sel.w" = s6.wa "sel.w" := congrFun hror.1 "sel.w"
      have hsegr : seg r (top + a) b = (seg s lo n').filter (fun x => decide (fP κ true p x)) := by
        rw [← hsb6]; simp [seg, hwar]
      refine ⟨⟨hL.regs _ _ hK6 (hror.mono (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs])),
        by rw [hror.2.2.2.2.2.2.1, hprocs6], by rw [hror.2.2.2.2.2.1, hcap6],
        by rw [hror.2.1, hwl6'], by rw [hfpr, hI.fp],
        fun q hq => by rw [hwar, hlow6 q hq],
        hu_all.trans ((hror.unch _ _ _).mono (List.Subset.refl _) (List.Subset.refl _)
          (myRegs_sub (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [myRegs, selRegs]) _)
          (List.Subset.refl _)),
        fun _ => ?_, fun h => absurd h (by rw [hgor]; decide)⟩, ?_⟩
      · rw [hlor, hnr, hkr, htopr]
        refine ⟨by omega, by omega, by omega, by omega, by omega, fun x hx => ?_, fun v hv => ?_, ?_⟩
        · rw [hsegr] at hx
          exact hsub x (List.mem_filter.mp hx).1
        · rw [hsegr, hmapb] at hv
          have h2 := Frontier.CHD.isKth_of_filter_gt hv
          have hk' : k - (n' - b) + Frontier.CHD.cntLe l (κ p) = k := by omega
          rw [hk'] at h2
          exact htr v (hseg1' ▸ h2)
        · have hstep := sel_cost_step' n' G b Cl hn201 hGb h10b
          omega
      · simp [selMu, hgor, hgo, hnr]; omega

/-! ## The main theorem -/

/-- **Verified RAM selection (BFPRT).**  If the procedure table holds `selBody lessS pSel` at
`pSel`, a call on the ids `sel.w[sel.lo, sel.lo + n)` (all satisfying `ok`; `1 ≤ n`, `sel.k < n`, scratch space
`5 n + 60` above `sel.top`) returns in `sel.res` an id of the segment whose key has rank `sel.k`
(`Select.IsKth`, ties allowed), keeps `sel.fp`, the key representation and every cell below
`sel.top`, writes only `sel.w`, the selection registers and the comparison's scratch, and costs at
most `(400 Cl + 2100) n + 100`. -/
theorem sel_spec [Inhabited α] (hL : LessSpec ops lessS KR ok κ Cl lessW lessV) (pSel : ℕ) :
    ∀ n (st : State V), SelPre lessS KR ok pSel st n →
      Runs ops (.call pSel) st (SelPost KR κ Cl lessW lessV st n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro st ⟨hK, hok0, hp, hn, hn1, hk, hov, hlen, hcap, h300⟩
  apply runs_call hp
  unfold selBody
  apply runs_seq
  refine runs_wset (a := 1) (evalW_lit_of (by simp; omega)) ?_
  set s0 := (st.enter.setW "sel.go" 1).charge 1 with hs0
  have hw0 : ∀ y, y ≠ "sel.go" → s0.w y = st.w y := fun y hy => by simp [hs0, hy]
  have hwa0 : s0.wa = st.wa := by simp [hs0]
  have hK0 : KR s0 := hL.frame st s0 hK (fun b _ => by rw [hwa0]) (by simp [hs0]) (by simp [hs0])
    (by simp [hs0]) (by simp [hs0]) (by simp [hs0]) (by simp [hs0])
    (fun y hy => hw0 y (fun e => hy (by rw [e]; simp [myRegs, selRegs])))
  have hI0 : LI KR κ Cl lessW lessV st n s0 := by
    refine ⟨hK0, by simp [hs0], by simp [hs0], by simp [hs0], hw0 _ (by simp),
      fun q _ => by rw [hwa0], ?_, fun _ => ?_, fun h => absurd h (by simp [hs0])⟩
    · refine ⟨fun a _ => ⟨by rw [hwa0], by simp [hs0]⟩, fun a _ => ⟨by simp [hs0], by simp [hs0]⟩,
        fun y hy => hw0 y (fun e => hy (by rw [e]; simp [myRegs, selRegs])), fun y _ => by simp [hs0],
        by simp [hs0], by simp [hs0]⟩
    · rw [hw0 _ (by simp), hw0 _ (by simp), hw0 _ (by simp), hw0 _ (by simp), hn]
      have hseg0 : seg s0 (st.w "sel.lo") n = seg st (st.w "sel.lo") n := by simp [seg, hwa0]
      refine ⟨hn1, hn ▸ hk, by omega, le_rfl, le_rfl, fun x hx => by rwa [hseg0] at hx,
        fun v hv => by rwa [hseg0] at hv, by simp [hs0]⟩
  refine runs_while_var (LI KR κ Cl lessW lessV st n) selMu _ ?_ s0 hI0
  intro s hs
  refine ⟨s.w "sel.go", rfl, fun hgo => ?_, fun hgo => ?_⟩
  · by_cases hsmall : s.w "sel.n" < 201
    · exact baseIter_run hL pSel st n hcap h300 hlen hok0 s hs hgo hsmall
    · exact recIter_run hL pSel st n hcap h300 hlen hp (fun m hm st' hpre => ih m hm st' hpre)
        hok0 s hs hgo hsmall
  · obtain ⟨hres, hkth, hc⟩ := hs.done hgo
    exact ⟨hL.regs _ _ hs.kr (RegOnly.charge s 1 myRegs), by simpa using hres, by simpa using hkth,
      by simpa using hs.fp, fun q hq => by simpa using hs.low q hq, by simpa using hs.wlen,
      by simpa using hs.unch, by simp; omega⟩

end Frontier.RAM.SelectRAM
