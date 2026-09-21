import Frontier.RAMRep
import Frontier.RAMWP
import Frontier.CHD.LabTab
import Frontier.CHD.FindPivots
import Frontier.CHD.BM

/-!
# LabRAM — RAM fragments of the shared label layer (agent-02, B-LAB, NON-GATE)

Machine side of `LabTab`.  A label is held either in the label TABLE (arrays `dfin dlen dhops de
dver vcnt`, one entry per vertex) or in a register BLOCK `X : LReg` (value register `X.l`, word
registers `X.h X.v X.e X.r`).  Fragments (each with a `wp`-spec and an `Unchanged` write set in
agent-08's frame convention):

* `cmp X Y c1 c2 out` : `out := [X < Y]` in the machine order (generic value domain);
* `candLab X`          : `X := cand` for the edge in `re` from the tail in `ru`;
* `loadLab vx X xf`    : `X := d[vx]`, `xf := dfin[vx]`;
* `storeLab vx X`      : `d[vx] := X`, `dfin[vx] := 1`, `vcnt[vx] += 1`;
* `relaxFP`            : FindPivots `Relax` (`relaxL`, re-confirmation included), `lab.ok := [Ok]`;
* `ltB X K kf ...`     : `out := [X < K]` for a bound `K` that may be `⊤` (`kf = 0`).

Word budget: label counters (`dhops`, `vcnt`) grow by one per strict relaxation, so the table
invariant bounds them by the machine cost, and fragments assume `G.m + cost + 64 ≤ cap`.
-/

open scoped ENNReal NNReal

namespace Frontier.RAM

variable {V : Type}

/-! ### Frame lemmas in `simp` form -/

section Unch

variable {st st' : State V} {wa va wr vr : List String}

@[simp] theorem unch_charge (k : ℕ) :
    Unchanged st (st'.charge k) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor <;> intro h <;> exact ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩

theorem unch_setW {x : String} (hx : x ∈ wr) (a : ℕ) :
    Unchanged st (st'.setW x a) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, h.varr, fun y hy => ?_, h.vreg, h.cap, h.procs⟩
    have := h.wreg y hy
    have hyx : y ≠ x := fun h' => hy (h' ▸ hx)
    simpa [State.setW, hyx] using this
  · intro h
    refine ⟨h.warr, h.varr, fun y hy => ?_, h.vreg, h.cap, h.procs⟩
    have hyx : y ≠ x := fun h' => hy (h' ▸ hx)
    simpa [State.setW, hyx] using h.wreg y hy

theorem unch_setV {x : String} (hx : x ∈ vr) (a : V) :
    Unchanged st (st'.setV x a) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, h.varr, h.wreg, fun y hy => ?_, h.cap, h.procs⟩
    have := h.vreg y hy
    have hyx : y ≠ x := fun h' => hy (h' ▸ hx)
    simpa [State.setV, hyx] using this
  · intro h
    refine ⟨h.warr, h.varr, h.wreg, fun y hy => ?_, h.cap, h.procs⟩
    have hyx : y ≠ x := fun h' => hy (h' ▸ hx)
    simpa [State.setV, hyx] using h.vreg y hy

theorem unch_storeW {arr : String} (ha : arr ∈ wa) (i a : ℕ) :
    Unchanged st (st'.storeW arr i a) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor
  · intro h
    refine ⟨fun b hb => ?_, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩
    have := h.warr b hb
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, this.2⟩
    funext j; have := congrFun this.1 j; simpa [State.storeW, hba] using this
  · intro h
    refine ⟨fun b hb => ?_, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, (h.warr b hb).2⟩
    funext j; simpa [State.storeW, hba] using congrFun (h.warr b hb).1 j

theorem unch_storeV {arr : String} (ha : arr ∈ va) (i : ℕ) (a : V) :
    Unchanged st (st'.storeV arr i a) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, fun b hb => ?_, h.wreg, h.vreg, h.cap, h.procs⟩
    have := h.varr b hb
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, this.2⟩
    funext j; have := congrFun this.1 j; simpa [State.storeV, hba] using this
  · intro h
    refine ⟨h.warr, fun b hb => ?_, h.wreg, h.vreg, h.cap, h.procs⟩
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, (h.varr b hb).2⟩
    funext j; simpa [State.storeV, hba] using congrFun (h.varr b hb).1 j

theorem unch_allocW {arr : String} (ha : arr ∈ wa) (k : ℕ) :
    Unchanged st (st'.allocW arr k) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor
  · intro h
    refine ⟨fun b hb => ?_, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩
    have := h.warr b hb
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, ?_⟩
    · funext j; have := congrFun this.1 j; simpa [State.allocW, hba] using this
    · simpa [State.allocW, hba] using this.2
  · intro h
    refine ⟨fun b hb => ?_, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, ?_⟩
    · funext j; simpa [State.allocW, hba] using congrFun (h.warr b hb).1 j
    · simpa [State.allocW, hba] using (h.warr b hb).2

theorem unch_allocV {arr : String} (ha : arr ∈ va) (k : ℕ) (z : V) :
    Unchanged st (st'.allocV arr k z) wa va wr vr ↔ Unchanged st st' wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, fun b hb => ?_, h.wreg, h.vreg, h.cap, h.procs⟩
    have := h.varr b hb
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, ?_⟩
    · funext j; have := congrFun this.1 j; simpa [State.allocV, hba] using this
    · simpa [State.allocV, hba] using this.2
  · intro h
    refine ⟨h.warr, fun b hb => ?_, h.wreg, h.vreg, h.cap, h.procs⟩
    have hba : b ≠ arr := fun h' => hb (h' ▸ ha)
    refine ⟨?_, ?_⟩
    · funext j; simpa [State.allocV, hba] using congrFun (h.varr b hb).1 j
    · simpa [State.allocV, hba] using (h.varr b hb).2

@[simp] theorem unch_self : Unchanged st st wa va wr vr ↔ True :=
  ⟨fun _ => trivial, fun _ => Unchanged.refl st wa va wr vr⟩

end Unch

/-- Composing frames: write sets add up. -/
theorem Unchanged.comp {s1 s2 s3 : State V} {wa va wr vr wa' va' wr' vr' : List String}
    (h1 : Unchanged s1 s2 wa va wr vr) (h2 : Unchanged s2 s3 wa' va' wr' vr') :
    Unchanged s1 s3 (wa ++ wa') (va ++ va') (wr ++ wr') (vr ++ vr') :=
  (h1.mono (List.subset_append_left _ _) (List.subset_append_left _ _)
      (List.subset_append_left _ _) (List.subset_append_left _ _)).trans
    (h2.mono (List.subset_append_right _ _) (List.subset_append_right _ _)
      (List.subset_append_right _ _) (List.subset_append_right _ _))

/-! ### Register blocks and the generic comparison macro -/

/-- A register block holding one machine label: value register `l` (length) and word registers
`h` (hops), `v` (end vertex), `e` (encoded last edge: `0` = none, `e+1`), `r` (tail version). -/
structure LReg where
  l : String
  h : String
  v : String
  e : String
  r : String

/-- The word registers of a block. -/
def LReg.ws (X : LReg) : List String := [X.h, X.v, X.e, X.r]

namespace LabRAM

open WExpr Stmt

/-- Word-level "strictly smaller" for the integer part of a label (versions reversed). -/
def wordLt (xh xv xe xr yh yv ye yr : ℕ) : Prop :=
  xh < yh ∨ (xh = yh ∧ (xv < yv ∨ (xv = yv ∧ (xe < ye ∨ (xe = ye ∧ yr < xr)))))

instance (xh xv xe xr yh yv ye yr : ℕ) : Decidable (wordLt xh xv xe xr yh yv ye yr) := by
  unfold wordLt; infer_instance

/-- Integer part of the comparison, as nested tests (no value operations). -/
def cmpW (X Y : LReg) (out : String) : Stmt :=
  ite (lt (var X.h) (var Y.h)) (wset out (lit 1))
  (ite (lt (var Y.h) (var X.h)) (wset out (lit 0))
  (ite (lt (var X.v) (var Y.v)) (wset out (lit 1))
  (ite (lt (var Y.v) (var X.v)) (wset out (lit 0))
  (ite (lt (var X.e) (var Y.e)) (wset out (lit 1))
  (ite (lt (var Y.e) (var X.e)) (wset out (lit 0))
  (ite (lt (var Y.r) (var X.r)) (wset out (lit 1)) (wset out (lit 0))))))))

/-- Full comparison `out := [X < Y]`: two value comparisons decide `<`, `>` or `=` on lengths
(scratch word registers `c1 c2`). -/
def cmp (X Y : LReg) (c1 c2 out : String) : Stmt :=
  seq (vle c1 (.var X.l) (.var Y.l))
  (seq (vle c2 (.var Y.l) (.var X.l))
  (ite (var c2)
     (ite (var c1) (cmpW X Y out) (wset out (lit 0)))
     (wset out (lit 1))))

theorem fit_bit {cap : ℕ} (h : 1 < cap) (c : Prop) [Decidable c] :
    fit cap (if c then 1 else 0) = some (if c then 1 else 0) := by
  split_ifs <;> simp [fit] <;> omega

theorem fit_one {cap : ℕ} (h : 1 < cap) : fit cap 1 = some 1 := by simp [fit, h]
theorem fit_zero {cap : ℕ} (h : 1 < cap) : fit cap 0 = some 0 := by simp [fit]; omega

variable {ops : VOps V}

/-! One-level `wp` unfolding (keeps sub-fragments folded). -/
theorem wp_seq (a b : Stmt) (Q : State V → Prop) (s : State V) :
    wp ops (.seq a b) Q s = wp ops a (wp ops b Q) s := rfl
theorem wp_ite_var (x : String) (a b : Stmt) (Q : State V → Prop) (s : State V) :
    wp ops (.ite (.var x) a b) Q s =
      ((s.w x ≠ 0 → wp ops a Q (s.charge 1)) ∧ (s.w x = 0 → wp ops b Q (s.charge 1))) := rfl
theorem wp_skip (Q : State V → Prop) (s : State V) : wp ops .skip Q s = Q (s.charge 1) := rfl
theorem wp_wset_of {x : String} {e : WExpr} {Q : State V → Prop} {s : State V} {a : ℕ}
    (he : evalW s e = some a) : wp ops (.wset x e) Q s = Q ((s.setW x a).charge 1) := by
  simp [wp, he]

theorem wset_lit_wp (x : String) (a : ℕ) (s : State V) (ha : a < s.cap) :
    wp ops (.wset x (.lit a)) (fun r => r.w x = a ∧ Unchanged s r [] [] [x] [] ∧
      r.cost = s.cost + 1) s := by
  simp [wp, fit, ha, unch_setW]

theorem wset_eqz_wp (x y : String) (s : State V) (hcap : 1 < s.cap) :
    wp ops (.wset x (.eq (.var y) (.lit 0))) (fun r => r.w x = (if s.w y = 0 then 1 else 0) ∧
      Unchanged s r [] [] [x] [] ∧ r.cost = s.cost + 1) s := by
  have h0 : fit s.cap 0 = some 0 := by simp [fit]; omega
  simp only [wp, evalW_eq', evalW_var, evalW_lit', h0, Option.bind_some, fit_bit hcap]
  simp [unch_setW]

theorem skip_wp (s : State V) :
    wp ops .skip (fun r => Unchanged s r [] [] [] [] ∧ r.cost = s.cost + 1) s := by
  simp [wp]

/-- The bit computed by `cmpW` on the registers of `s`. -/
def wbit (s : State V) (X Y : LReg) : ℕ :=
  if wordLt (s.w X.h) (s.w X.v) (s.w X.e) (s.w X.r) (s.w Y.h) (s.w Y.v) (s.w Y.e) (s.w Y.r)
  then 1 else 0

theorem cmpW_wp (X Y : LReg) (out : String) (s : State V) (hcap : 1 < s.cap) :
    wp ops (cmpW X Y out) (fun r => r.w out = wbit s X Y ∧ Unchanged s r [] [] [out] [] ∧
      s.cost + 1 ≤ r.cost ∧ r.cost ≤ s.cost + 9) s := by
  have hU : ∀ (t : State V) (a : ℕ), Unchanged s t [] [] [out] [] →
      Unchanged s (t.setW out a) [] [] [out] [] := fun t a h =>
    (unch_setW (List.mem_singleton_self out) a).mpr h
  simp only [cmpW, wp, evalW_var, evalW_lt', evalW_lit', Option.bind_some, fit_bit hcap,
    fit_one hcap, fit_zero hcap, State.charge_w, State.charge_cap, State.charge_cost,
    State.setW_w, State.setW_cost, wbit, wordLt, unch_charge]
  by_cases a1 : s.w X.h < s.w Y.h
  · simp (config := { contextual := true }) [a1, hU, State.setW_cost]
  by_cases a2 : s.w Y.h < s.w X.h
  · have hne : ¬ s.w X.h = s.w Y.h := by omega
    simp (config := { contextual := true }) [a1, a2, hne, hU]
  have e1 : s.w X.h = s.w Y.h := by omega
  by_cases a3 : s.w X.v < s.w Y.v
  · simp (config := { contextual := true }) [a1, a2, a3, e1, hU]
  by_cases a4 : s.w Y.v < s.w X.v
  · have hne : ¬ s.w X.v = s.w Y.v := by omega
    simp (config := { contextual := true }) [a1, a2, a3, a4, e1, hne, hU]
  have e2 : s.w X.v = s.w Y.v := by omega
  by_cases a5 : s.w X.e < s.w Y.e
  · simp (config := { contextual := true }) [a1, a2, a3, a4, a5, e1, e2, hU]
  by_cases a6 : s.w Y.e < s.w X.e
  · have hne : ¬ s.w X.e = s.w Y.e := by omega
    simp (config := { contextual := true }) [a1, a2, a3, a4, a5, a6, e1, e2, hne, hU]
  have e3 : s.w X.e = s.w Y.e := by omega
  by_cases a7 : s.w Y.r < s.w X.r
  · simp (config := { contextual := true }) [a1, a2, a3, a4, a5, a6, a7, e1, e2, e3, hU]
  · simp (config := { contextual := true }) [a1, a2, a3, a4, a5, a6, a7, e1, e2, e3, hU]


/-- The bit computed by `cmp` (lengths first, then `wordLt`). -/
def cbit [LinearOrder V] (s : State V) (X Y : LReg) : ℕ :=
  if s.v X.l < s.v Y.l ∨ (s.v X.l = s.v Y.l ∧
    wordLt (s.w X.h) (s.w X.v) (s.w X.e) (s.w X.r) (s.w Y.h) (s.w Y.v) (s.w Y.e) (s.w Y.r))
  then 1 else 0

/-- Scratch registers `c1 c2` are distinct and not among the compared word registers. -/
structure CmpFresh (X Y : LReg) (c1 c2 : String) : Prop where
  ne : c1 ≠ c2
  x1 : c1 ∉ X.ws
  x2 : c2 ∉ X.ws
  y1 : c1 ∉ Y.ws
  y2 : c2 ∉ Y.ws

/-- **Spec of the comparison macro** (generic value domain whose `ops.le` is the order test):
`out := [X < Y]` in the machine order, only `c1 c2 out` written, cost at most `13`. -/
theorem cmp_wp [LinearOrder V] (hle : ∀ a b : V, ops.le a b = decide (a ≤ b)) {X Y : LReg}
    {c1 c2 : String} (out : String) (hf : CmpFresh X Y c1 c2) (s : State V) (hcap : 1 < s.cap) :
    wp ops (cmp X Y c1 c2 out) (fun r => r.w out = cbit s X Y ∧
      Unchanged s r [] [] [c1, c2, out] [] ∧ s.cost + 1 ≤ r.cost ∧ r.cost ≤ s.cost + 13) s := by
  have h12 := hf.ne
  have hx1 := hf.x1; have hx2 := hf.x2; have hy1 := hf.y1; have hy2 := hf.y2
  simp only [LReg.ws, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx1 hx2 hy1 hy2
  obtain ⟨a1, a2, a3, a4⟩ := hx1
  obtain ⟨b1, b2, b3, b4⟩ := hx2
  obtain ⟨c1', c2', c3', c4'⟩ := hy1
  obtain ⟨d1, d2, d3, d4⟩ := hy2
  have hU2 : ∀ (a b : ℕ), Unchanged s
      ((((s.setW c1 a).charge 1).setW c2 b).charge 1) [] [] [c1, c2, out] [] := by
    intro a b
    simp [unch_setW]
  by_cases hyx : s.v Y.l ≤ s.v X.l
  · by_cases hxy : s.v X.l ≤ s.v Y.l
    · have heq : s.v X.l = s.v Y.l := le_antisymm hxy hyx
      have hb1 : ops.le (s.v X.l) (s.v Y.l) = true := by simp [hle, hxy]
      have hb2 : ops.le (s.v Y.l) (s.v X.l) = true := by simp [hle, hyx]
      simp only [cmp, wp, evalV_var', State.charge_v, State.setW_v, hb1, hb2, State.charge_cap,
        State.setW_cap, hcap, true_and, evalW_var, State.charge_w, State.setW_w, h12,
        ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true, forall_const, false_implies,
        and_true, not_true_eq_false]
      refine wp_mono _ ?_ _ (cmpW_wp X Y out _ (by simpa using hcap))
      rintro r ⟨hr1, hr2, hr3, hr4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hr1]
        simp only [wbit, cbit, State.charge_w, State.setW_w, Ne.symm a1, Ne.symm a2, Ne.symm a3,
          Ne.symm a4, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm b4, Ne.symm c1', Ne.symm c2',
          Ne.symm c3', Ne.symm c4', Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, ↓reduceIte,
          heq, lt_irrefl, false_or, true_and]
      · have h0 : Unchanged s ((((((s.setW c1 1).charge 1).setW c2 1).charge 1).charge 1).charge 1)
            [] [] [c1, c2, out] [] := by simp [unch_setW]
        exact h0.trans ((hr2.mono (by simp) (by simp) (by simp) (by simp)))
      · simp only [State.charge_cost, State.setW_cost] at hr3; omega
      · simp only [State.charge_cost, State.setW_cost] at hr4; omega
    · have hlt : s.v Y.l < s.v X.l := lt_of_not_ge hxy
      have hb1 : ops.le (s.v X.l) (s.v Y.l) = false := by simp [hle, hxy]
      have hb2 : ops.le (s.v Y.l) (s.v X.l) = true := by simp [hle, hyx]
      simp only [cmp, wp, evalV_var', State.charge_v, State.setW_v, hb1, hb2, State.charge_cap,
        State.setW_cap, hcap, true_and, evalW_var, State.charge_w, State.setW_w, h12, ↓reduceIte,
        Bool.false_eq_true, ne_eq, one_ne_zero, not_false_eq_true, forall_const,
        not_true_eq_false, false_implies, and_true, zero_ne_one, true_implies, evalW_lit',
        fit_zero hcap, cbit, hlt.not_gt, hlt.ne', false_and, or_false, State.charge_cost,
        State.setW_cost, unch_charge]
      refine ⟨?_, by omega, by omega⟩
      simp [unch_setW]
  · have hlt : s.v X.l < s.v Y.l := lt_of_not_ge hyx
    have hb1 : ops.le (s.v X.l) (s.v Y.l) = true := by simp [hle, hlt.le]
    have hb2 : ops.le (s.v Y.l) (s.v X.l) = false := by simp [hle, hyx]
    simp only [cmp, wp, evalV_var', State.charge_v, State.setW_v, hb1, hb2, State.charge_cap,
      State.setW_cap, hcap, true_and, evalW_var, State.charge_w, State.setW_w, h12, ↓reduceIte,
      Bool.false_eq_true, ne_eq, not_true_eq_false, false_implies, evalW_lit', fit_one hcap,
      cbit, hlt, true_or, State.charge_cost, State.setW_cost, unch_charge, zero_ne_one,
      not_false_eq_true, forall_const, and_true, true_implies]
    refine ⟨?_, by omega, by omega⟩
    simp [unch_setW]


/-! ### Labels in register blocks and in the table -/

section Labels

open Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph}

/-- Block `X` holds the machine label `x` (last edge encoded by `encE`). -/
def Holds (st : State ℝ≥0) (X : LReg) (x : MLabel G) : Prop :=
  st.v X.l = x.len ∧ st.w X.h = x.hops ∧ st.w X.v = x.v ∧ st.w X.e = encE x.e ∧ st.w X.r = x.ver

open Classical in
/-- **Bridge**: on blocks holding machine labels, `cmp` computes `MLabel.lt`. -/
theorem cbit_eq {st : State ℝ≥0} {X Y : LReg} {x y : MLabel G} (hx : Holds st X x)
    (hy : Holds st Y y) : cbit st X Y = if x.lt y then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  obtain ⟨k1, k2, k3, k4, k5⟩ := hy
  simp only [cbit, wordLt, h1, h2, h3, h4, h5, k1, k2, k3, k4, k5]
  by_cases hA : x.lt y
  · rw [if_pos ((mlt_iff_fields x y).mp hA), if_pos hA]
  · rw [if_neg (fun h => hA ((mlt_iff_fields x y).mpr h)), if_neg hA]

theorem Holds.of_unchanged {st r : State ℝ≥0} {X : LReg} {x : MLabel G}
    {wa va wr vr : List String} (h : Holds st X x) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ X.ws, a ∉ wr) (hv : X.l ∉ vr) : Holds r X x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.vreg _ hv, h1]
  · rw [hu.wreg _ (hw _ (by simp [LReg.ws])), h2]
  · rw [hu.wreg _ (hw _ (by simp [LReg.ws])), h3]
  · rw [hu.wreg _ (hw _ (by simp [LReg.ws])), h4]
  · rw [hu.wreg _ (hw _ (by simp [LReg.ws])), h5]

theorem Holds.charge {st : State ℝ≥0} {X : LReg} {x : MLabel G} (h : Holds st X x) (k : ℕ) :
    Holds (st.charge k) X x := h

/-- The graph arrays of the core (agent-10's L6 format): heads and weights per edge slot. -/
structure GraphAt (st : State ℝ≥0) (G : Graph) : Prop where
  head : WArr st "gHead" (fun e : Fin G.m => ((G.dst e : Fin G.n) : ℕ))
  w : VArr st "gW" G.w 0

/-- The label table stored in a machine state. -/
def tabOf (st : State ℝ≥0) : Tab G where
  fin v := st.wa "dfin" v
  len v := st.va "dlen" v
  hops v := st.wa "dhops" v
  enc v := st.wa "de" v
  ver v := st.wa "dver" v
  vcnt v := st.wa "vcnt" v

/-- The label arrays are allocated for `n` vertices. -/
structure LabLens (st : State ℝ≥0) (n : ℕ) : Prop where
  fin : n ≤ st.wlen "dfin"
  len : n ≤ st.vlen "dlen"
  hops : n ≤ st.wlen "dhops"
  enc : n ≤ st.wlen "de"
  ver : n ≤ st.wlen "dver"
  vcnt : n ≤ st.wlen "vcnt"

theorem LabLens.charge {st : State ℝ≥0} {n : ℕ} (h : LabLens st n) (k : ℕ) :
    LabLens (st.charge k) n :=
  ⟨h.fin, h.len, h.hops, h.enc, h.ver, h.vcnt⟩

/-- Word arrays of the label table. -/
def labW : List String := ["dfin", "dhops", "de", "dver", "vcnt"]
/-- Value arrays of the label table. -/
def labV : List String := ["dlen"]

/-- A state whose label arrays are untouched has the same table. -/
theorem tabOf_of_unchanged {st r : State ℝ≥0} {wa va wr vr : List String}
    (h : Unchanged st r wa va wr vr) (hw : ∀ a ∈ labW, a ∉ wa) (hv : "dlen" ∉ va) :
    tabOf (G := G) r = tabOf st ∧ (LabLens st G.n → LabLens r G.n) := by
  have e1 := h.warr "dfin" (hw _ (by simp [labW]))
  have e2 := h.varr "dlen" hv
  have e3 := h.warr "dhops" (hw _ (by simp [labW]))
  have e4 := h.warr "de" (hw _ (by simp [labW]))
  have e5 := h.warr "dver" (hw _ (by simp [labW]))
  have e6 := h.warr "vcnt" (hw _ (by simp [labW]))
  refine ⟨?_, fun hl => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [tabOf, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1]
  · rw [e1.2]; exact hl.fin
  · rw [e2.2]; exact hl.len
  · rw [e3.2]; exact hl.hops
  · rw [e4.2]; exact hl.enc
  · rw [e5.2]; exact hl.ver
  · rw [e6.2]; exact hl.vcnt

theorem graphAt_of_unchanged {st r : State ℝ≥0} {wa va wr vr : List String}
    (h : Unchanged st r wa va wr vr) (hw : "gHead" ∉ wa) (hv : "gW" ∉ va) (hg : GraphAt st G) :
    GraphAt r G :=
  ⟨WSeg.of_unchanged hg.head h hw, VSeg.of_unchanged hg.w h hv⟩

/-! #### The candidate `X := d[ru] ⊕ re` -/

open WExpr Stmt in
/-- `X := cand` for the edge slot in `re` out of the tail in `ru` (5 statements). -/
def candLab (X : LReg) : Stmt :=
  seq (vset X.l (.add (.load "dlen" (var "ru")) (.load "gW" (var "re"))))
  (seq (wset X.h (add (load "dhops" (var "ru")) (lit 1)))
  (seq (wset X.v (load "gHead" (var "re")))
  (seq (wset X.e (add (var "re") (lit 1)))
       (wset X.r (load "vcnt" (var "ru"))))))

/-- Freshness for `candLab`: distinct word registers, not the inputs. -/
structure CandFresh (X : LReg) : Prop where
  nd : X.ws.Nodup
  ru : "ru" ∉ X.ws
  re : "re" ∉ X.ws

theorem candLab_wp (X : LReg) (hX : CandFresh X) (st : State ℝ≥0) (e : Fin G.m)
    (hlens : LabLens st G.n) (hg : GraphAt st G) (hru : st.w "ru" = G.src e)
    (hre : st.w "re" = e) (hc1 : st.wa "dhops" (G.src e) + 1 < st.cap)
    (hc2 : (e : ℕ) + 1 < st.cap) :
    wp realOps (candLab X) (fun r => Holds r X (cand (tabOf (G := G) st) e) ∧
      Unchanged st r [] [] X.ws [X.l] ∧ r.cost = st.cost + 5) st := by
  have hnd := hX.nd
  have hru' := hX.ru
  have hre' := hX.re
  simp only [LReg.ws, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd hru' hre'
  obtain ⟨⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩ := hnd
  obtain ⟨u1, u2, u3, u4⟩ := hru'
  obtain ⟨r1, r2, r3, r4⟩ := hre'
  have l1 : ((G.src e : Fin G.n) : ℕ) < st.vlen "dlen" := lt_of_lt_of_le (G.src e).isLt hlens.len
  have l2 : (e : ℕ) < st.vlen "gW" := by have := hg.w.1; simp at this; omega
  have l3 : ((G.src e : Fin G.n) : ℕ) < st.wlen "dhops" := lt_of_lt_of_le (G.src e).isLt hlens.hops
  have l4 : (e : ℕ) < st.wlen "gHead" := by have := hg.head.1; simp at this; omega
  have l5 : ((G.src e : Fin G.n) : ℕ) < st.wlen "vcnt" := lt_of_lt_of_le (G.src e).isLt hlens.vcnt
  have hw : st.va "gW" e = G.w e := hg.w.read e
  have hh : st.wa "gHead" e = G.dst e := hg.head.read e
  simp only [candLab, wp, evalV_add', evalV_load', evalW_var, evalW_add', evalW_load',
    evalW_lit', State.charge_w, State.charge_wa, State.charge_va, State.charge_wlen,
    State.charge_vlen, State.charge_cap, State.setV_w, State.setV_wa, State.setV_va,
    State.setV_wlen, State.setV_vlen, State.setV_cap, State.setW_w, State.setW_wa,
    State.setW_wlen, State.setW_cap, hru, hre, l1, l2, l3, l4, l5, ↓reduceIte, Option.bind_some,
    r1, r2, u1, u2, u3, fit_of_lt hc1, fit_of_lt hc2,
    fit_of_lt (show 1 < st.cap by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [State.setW, State.setV, State.charge, cand, tabOf, realOps, hw]
  · simp [State.setW, State.setV, State.charge, cand, tabOf, n12, n13, n14]
  · simp [State.setW, State.setV, State.charge, cand, tabOf, n23, n24, hh]
  · simp [State.setW, State.setV, State.charge, cand, tabOf, n34, encE]
  · simp [State.setW, State.setV, State.charge, cand, tabOf]
  · simp only [unch_charge]
    rw [unch_setW (by simp [LReg.ws]), unch_charge, unch_setW (by simp [LReg.ws]), unch_charge,
      unch_setW (by simp [LReg.ws]), unch_charge, unch_setW (by simp [LReg.ws]), unch_charge,
      unch_setV (by simp)]
    simp
  · simp [State.setW, State.setV, State.charge]

/-! #### Loading `X := d[vx]` -/

open WExpr Stmt in
/-- `X := d[vx]` and `xf := dfin[vx]` (6 statements; `X.v := vx` last, so `X.v = vx` is allowed). -/
def loadLab (vx : String) (X : LReg) (xf : String) : Stmt :=
  seq (vset X.l (.load "dlen" (var vx)))
  (seq (wset X.h (load "dhops" (var vx)))
  (seq (wset X.e (load "de" (var vx)))
  (seq (wset X.r (load "dver" (var vx)))
  (seq (wset xf (load "dfin" (var vx)))
       (wset X.v (var vx))))))

/-- Freshness for `loadLab`. -/
structure LoadFresh (vx : String) (X : LReg) (xf : String) : Prop where
  nd : [X.h, X.v, X.e, X.r, xf].Nodup
  vx : vx ∉ [X.h, X.e, X.r, xf]

/-- What `loadLab` leaves: the raw fields of `v`'s table entry. -/
def Loaded (r : State ℝ≥0) (T : Tab G) (X : LReg) (xf : String) (v : Fin G.n) : Prop :=
  r.v X.l = T.len v ∧ r.w X.h = T.hops v ∧ r.w X.v = v ∧ r.w X.e = T.enc v ∧
    r.w X.r = T.ver v ∧ r.w xf = T.fin v

theorem loadLab_wp (vx : String) (X : LReg) (xf : String) (hF : LoadFresh vx X xf)
    (st : State ℝ≥0) (v : Fin G.n) (hlens : LabLens st G.n) (hv : st.w vx = v) :
    wp realOps (loadLab vx X xf) (fun r => Loaded r (tabOf (G := G) st) X xf v ∧
      Unchanged st r [] [] (xf :: X.ws) [X.l] ∧ r.cost = st.cost + 6) st := by
  have hnd := hF.nd
  have hvx := hF.vx
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd hvx
  obtain ⟨⟨n12, n13, n14, n15⟩, ⟨n23, n24, n25⟩, ⟨n34, n35⟩, n45⟩ := hnd
  obtain ⟨v1, v2, v3, v4⟩ := hvx
  have l1 : ((v : Fin G.n) : ℕ) < st.vlen "dlen" := lt_of_lt_of_le v.isLt hlens.len
  have l2 : ((v : Fin G.n) : ℕ) < st.wlen "dhops" := lt_of_lt_of_le v.isLt hlens.hops
  have l3 : ((v : Fin G.n) : ℕ) < st.wlen "de" := lt_of_lt_of_le v.isLt hlens.enc
  have l4 : ((v : Fin G.n) : ℕ) < st.wlen "dver" := lt_of_lt_of_le v.isLt hlens.ver
  have l5 : ((v : Fin G.n) : ℕ) < st.wlen "dfin" := lt_of_lt_of_le v.isLt hlens.fin
  simp only [loadLab, wp, evalV_load', evalW_var, evalW_load', State.charge_w, State.charge_wa,
    State.charge_va, State.charge_wlen, State.charge_vlen, State.setV_w, State.setV_wa,
    State.setV_va, State.setV_wlen, State.setV_vlen, State.setW_w, State.setW_wa, State.setW_va,
    State.setW_wlen, State.setW_vlen, hv, l1, l2, l3, l4, l5, ↓reduceIte, Option.bind_some,
    v1, v2, v3, v4]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [State.setW, State.setV, State.charge, tabOf]
  · simp [State.setW, State.setV, State.charge, tabOf, n12, n13, n14, n15]
  · simp [State.setW, State.setV, State.charge, tabOf]
  · simp [State.setW, State.setV, State.charge, tabOf, n34, n35, Ne.symm n23]
  · simp [State.setW, State.setV, State.charge, tabOf, n45, Ne.symm n24]
  · simp [State.setW, State.setV, State.charge, tabOf, Ne.symm n25]
  · simp only [unch_charge]
    rw [unch_setW (by simp [LReg.ws]), unch_charge, unch_setW (by simp [LReg.ws]), unch_charge,
      unch_setW (by simp [LReg.ws]), unch_charge, unch_setW (by simp [LReg.ws]), unch_charge,
      unch_setW (by simp [LReg.ws]), unch_charge, unch_setV (by simp)]
    simp
  · simp [State.setW, State.setV, State.charge]

/-- `encE ∘ decE` is the identity on valid encodings. -/
theorem encE_decE {k : ℕ} (hk : k ≤ G.m) : encE (decE G k) = k := by
  unfold decE
  by_cases h : 0 < k
  · have h2 : k - 1 < G.m := by omega
    rw [dif_pos ⟨h, h2⟩]; simp [encE]; omega
  · rw [dif_neg (fun h' => h h'.1)]; simp [encE]; omega

/-- A loaded FINITE label is held as the machine label of the table entry. -/
theorem Loaded.holds {r : State ℝ≥0} {T : Tab G} {X : LReg} {xf : String} {v : Fin G.n}
    {s : Fin G.n} {d : Labels G s} {H : Fin G.n → ℕ → List (Fin G.m)}
    (hL : Loaded r T X xf v) (hR : Represents (s := s) T d H) (hv : d v ≠ ⊤) :
    Holds r X (T.lab v) := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hL
  refine ⟨h1, h2, h3, ?_, h5⟩
  rw [h4]; exact (encE_decE (hR.enc_lt v hv)).symm

/-! #### Storing `d[vx] := X` (with the version bump) -/

open WExpr Stmt in
/-- `d[vx] := X`, `dfin[vx] := 1`, `vcnt[vx] := vcnt[vx] + 1` (6 statements). -/
def storeLab (vx : String) (X : LReg) : Stmt :=
  seq (vstore "dlen" (var vx) (.var X.l))
  (seq (wstore "dhops" (var vx) (var X.h))
  (seq (wstore "de" (var vx) (var X.e))
  (seq (wstore "dver" (var vx) (var X.r))
  (seq (wstore "dfin" (var vx) (lit 1))
       (wstore "vcnt" (var vx) (add (load "vcnt" (var vx)) (lit 1)))))))

theorem storeLab_wp (vx : String) (X : LReg) (st : State ℝ≥0) (e : Fin G.m)
    (hlens : LabLens st G.n) (hv : st.w vx = G.dst e) (hX : Holds st X (cand (tabOf (G := G) st) e))
    (hc : st.wa "vcnt" (G.dst e) + 1 < st.cap) :
    wp realOps (storeLab vx X) (fun r => tabOf (G := G) r = (tabOf st).put e ∧ LabLens r G.n ∧
      Unchanged st r labW labV [] [] ∧ r.cost = st.cost + 6) st := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := hX
  have l0 : ((G.dst e : Fin G.n) : ℕ) < st.vlen "dlen" := lt_of_lt_of_le (G.dst e).isLt hlens.len
  have l2 : ((G.dst e : Fin G.n) : ℕ) < st.wlen "dhops" := lt_of_lt_of_le (G.dst e).isLt hlens.hops
  have l3 : ((G.dst e : Fin G.n) : ℕ) < st.wlen "de" := lt_of_lt_of_le (G.dst e).isLt hlens.enc
  have l4 : ((G.dst e : Fin G.n) : ℕ) < st.wlen "dver" := lt_of_lt_of_le (G.dst e).isLt hlens.ver
  have l5 : ((G.dst e : Fin G.n) : ℕ) < st.wlen "dfin" := lt_of_lt_of_le (G.dst e).isLt hlens.fin
  have l6 : ((G.dst e : Fin G.n) : ℕ) < st.wlen "vcnt" := lt_of_lt_of_le (G.dst e).isLt hlens.vcnt
  simp only [storeLab, wp, evalV_var', evalW_var, evalW_load', evalW_add', evalW_lit',
    State.charge_w, State.charge_v, State.charge_wa, State.charge_wlen, State.charge_vlen,
    State.charge_cap, State.storeV_w, State.storeV_v, State.storeV_wa, State.storeV_wlen,
    State.storeV_vlen, State.storeV_cap, State.storeW_w, State.storeW_v, State.storeW_wa,
    State.storeW_wlen, State.storeW_vlen, State.storeW_cap, hv, l0, l2, l3, l4, l5, l6,
    ↓reduceIte, Option.bind_some, true_and, fit_of_lt (show 1 < st.cap by omega),
    String.reduceEq, and_false, false_and, and_self, fit_of_lt hc]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [tabOf, Tab.put, Tab.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext w <;>
      by_cases hw : w = G.dst e <;> simp [State.storeW, State.storeV, State.charge, hw,
        Fin.val_inj, x1, x2, x4, x5, cand, encE, realOps]
    all_goals rfl
  · simp [State.storeW, State.storeV, State.charge]; exact hlens.fin
  · simp [State.storeW, State.storeV, State.charge]; exact hlens.len
  · simp [State.storeW, State.storeV, State.charge]; exact hlens.hops
  · simp [State.storeW, State.storeV, State.charge]; exact hlens.enc
  · simp [State.storeW, State.storeV, State.charge]; exact hlens.ver
  · simp [State.storeW, State.storeV, State.charge]; exact hlens.vcnt
  · simp only [unch_charge]
    rw [unch_storeW (by simp [labW]), unch_charge, unch_storeW (by simp [labW]), unch_charge,
      unch_storeW (by simp [labW]), unch_charge, unch_storeW (by simp [labW]), unch_charge,
      unch_storeW (by simp [labW]), unch_charge, unch_storeV (by simp [labV])]
    simp
  · simp [State.storeW, State.storeV, State.charge]

/-! #### The table invariant with the clock (agent-08's budget design, 12:00) -/

/-- The version counters of a state. -/
def vc (st : State ℝ≥0) : Fin G.n → ℕ := fun v => st.wa "vcnt" v

/-- The machine state holds a label table representing `d` with ghost history `H`; label
counters are bounded by the cost elapsed since the clock origin `c0`. -/
structure LabAt {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) : Prop where
  lens : LabLens st G.n
  rep : Represents (s := s) (tabOf st) d H
  hops_le : ∀ v : Fin G.n, st.wa "dhops" v + c0 ≤ st.cost
  vcnt_le : ∀ v : Fin G.n, st.wa "vcnt" v + c0 ≤ st.cost

/-- Fragments that do not write the label arrays preserve `LabAt`. -/
theorem LabAt.of_unchanged {s : Fin G.n} {st r : State ℝ≥0} {d : Labels G s}
    {H : Fin G.n → ℕ → List (Fin G.m)} {c0 : ℕ} {wa va wr vr : List String}
    (hL : LabAt st d H c0) (h : Unchanged st r wa va wr vr) (hw : ∀ a ∈ labW, a ∉ wa)
    (hv : "dlen" ∉ va) (hc : st.cost ≤ r.cost) : LabAt r d H c0 := by
  obtain ⟨htab, hlens⟩ := tabOf_of_unchanged (G := G) h hw hv
  have e3 := h.warr "dhops" (hw _ (by simp [labW]))
  have e6 := h.warr "vcnt" (hw _ (by simp [labW]))
  refine ⟨hlens hL.lens, htab ▸ hL.rep, fun v => ?_, fun v => ?_⟩
  · rw [e3.1]; exact (hL.hops_le v).trans hc
  · rw [e6.1]; exact (hL.vcnt_le v).trans hc

theorem vc_of_unchanged {st r : State ℝ≥0} {wa va wr vr : List String}
    (h : Unchanged st r wa va wr vr) (hw : "vcnt" ∉ wa) : vc (G := G) r = vc st := by
  funext v; simp [vc, (h.warr "vcnt" hw).1]

/-! #### FindPivots `Relax` (`relaxL`, with re-confirmation) -/

/-- B-LAB scratch blocks: `X0` = candidate, `Y0` = current label of the head. -/
def X0 : LReg := ⟨"lab.xl", "lab.xh", "lab.xv", "lab.xe", "lab.xr"⟩
def Y0 : LReg := ⟨"lab.yl", "lab.yh", "lab.yv", "lab.ye", "lab.yr"⟩

open WExpr Stmt in
/-- The core of `Relax` once the candidate is in `X0` (with `X0.v = dst e`): `Y0 := d[v]`;
`ok := [X0 ≤ d[v]]`; on a strict decrease `d[v] := X0` (version bump).  Reusable after any other
tests that leave `X0` and the label arrays alone (FindPivots scan, BM relax). -/
def relaxCore : Stmt :=
  seq (loadLab X0.v Y0 "lab.yf")
  (seq (ite (var "lab.yf")
          (seq (cmp X0 Y0 "lab.c1" "lab.c2" "lab.lt") (cmp Y0 X0 "lab.c1" "lab.c2" "lab.gt"))
          (seq (wset "lab.lt" (lit 1)) (wset "lab.gt" (lit 0))))
  (seq (wset "ok" (eq (var "lab.gt") (lit 0)))
       (ite (var "lab.lt") (storeLab X0.v X0) skip)))

/-- `Relax(u, e)` of FindPivots (FH.10 / `relaxL`): candidate `X0 := d[u] ⊕ e` from the inputs
`ru = u`, `re = e`, then `relaxCore`. -/
def relaxFP : Stmt := seq (candLab X0) relaxCore

/-- Word registers `relaxFP` may write. -/
def relaxW : List String :=
  ["lab.xh", "lab.xv", "lab.xe", "lab.xr", "lab.yh", "lab.yv", "lab.ye", "lab.yr", "lab.yf",
   "lab.c1", "lab.c2", "lab.lt", "lab.gt", "lab.lb", "ok"]
/-- Value registers `relaxFP` may write. -/
def relaxV : List String := ["lab.xl", "lab.yl"]

theorem relaxL_of_ok {s : Fin G.n} {d : Labels G s} {u : Fin G.n} {e : Fin G.m} (h : Ok d u e) :
    relaxL d u e = Function.update d (G.dst e) (ext (d u) e) := by
  simp [relaxL, h]

open Classical in
/-- Postcondition of `relaxCore`, relative to its entry state `r1`. -/
def CorePost {s : Fin G.n} (r1 : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m))
    (c0 : ℕ) (e : Fin G.m) (r : State ℝ≥0) : Prop :=
  ∃ H', LabAt r (relaxL d (G.src e) e) H' c0 ∧
    HExt H (vc r1) H' (vc r) ∧
    r.w "ok" = (if Ok d (G.src e) e then 1 else 0) ∧
    Holds r X0 (cand (tabOf (G := G) r1) e) ∧
    (∀ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) →
      Rep (s := s) H' (vc r) (cand (tabOf (G := G) r1) e) (p ++ [e])) ∧
    Unchanged r1 r labW labV relaxW relaxV ∧ r1.cost + 1 ≤ r.cost ∧ r.cost ≤ r1.cost + 42

open Classical in
/-- Postcondition of `relaxFP` (see `relaxFP_spec`). -/
def RelaxPost {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m))
    (c0 : ℕ) (e : Fin G.m) (r : State ℝ≥0) : Prop :=
  ∃ H', LabAt r (relaxL d (G.src e) e) H' c0 ∧
    HExt H (vc st) H' (vc r) ∧
    r.w "ok" = (if Ok d (G.src e) e then 1 else 0) ∧
    Holds r X0 (cand (tabOf (G := G) st) e) ∧
    (∀ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) →
      Rep (s := s) H' (vc r) (cand (tabOf (G := G) st) e) (p ++ [e])) ∧
    GraphAt r G ∧ Unchanged st r labW labV relaxW relaxV ∧ r.cost ≤ st.cost + 60

theorem one_lt_cap_of_labAt {s : Fin G.n} {st : State ℝ≥0} {d : Labels G s}
    {H : Fin G.n → ℕ → List (Fin G.m)} {c0 : ℕ} (hL : LabAt st d H c0) (v : Fin G.n)
    (hB : st.cost + 2 ≤ c0 + st.cap) : 1 < st.cap := by
  have := hL.vcnt_le v; omega

open Classical in
/-- The tail of `relaxCore` (`ok := [gt = 0]`, then the conditional store), from any state after
the comparison stage; `st` is the entry state of `relaxCore`. -/
theorem relaxCore_tail {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (hL : LabAt st d H c0)
    (e : Fin G.m) (p0 : List (Fin G.m)) (hp : d (G.src e) = ((toW p0 : WalkOrd G s) : WLab G s))
    (hB : st.cost + 16 ≤ c0 + st.cap) (r3 : State ℝ≥0) (LT GT : ℕ)
    (hlt3 : r3.w "lab.lt" = LT) (hgt3 : r3.w "lab.gt" = GT)
    (hX3 : Holds r3 X0 (cand (tabOf (G := G) st) e))
    (hU3 : Unchanged st r3 [] [] relaxW relaxV) (hc3lo : st.cost + 1 ≤ r3.cost)
    (hc3hi : r3.cost ≤ st.cost + 34)
    (hstrict : LT ≠ 0 → ext (d (G.src e)) e < d (G.dst e))
    (heqc : LT = 0 → Ok d (G.src e) e → ext (d (G.src e)) e = d (G.dst e))
    (hok : GT = 0 ↔ Ok d (G.src e) e) :
    wp realOps (.seq (.wset "ok" (.eq (.var "lab.gt") (.lit 0)))
      (.ite (.var "lab.lt") (storeLab X0.v X0) .skip)) (CorePost st d H c0 e) r3 := by
  have hcap3 : 1 < r3.cap := by
    rw [hU3.cap]; exact one_lt_cap_of_labAt hL (G.src e) (by omega)
  rw [wp_seq]
  refine wp_mono _ ?_ _ (wset_eqz_wp (ops := realOps) "ok" "lab.gt" r3 hcap3)
  rintro r4 ⟨hok4, hU4, hc4⟩
  rw [hgt3] at hok4
  have hU34 : Unchanged st r4 [] [] relaxW relaxV :=
    (hU3.comp hU4).mono (by simp) (by simp) (by simp [relaxW]) (by simp)
  have hT4 : tabOf (G := G) r4 = tabOf st :=
    (tabOf_of_unchanged (G := G) hU34 (by decide) (by decide)).1
  have hlens4 : LabLens r4 G.n :=
    (tabOf_of_unchanged (G := G) hU34 (by decide) (by decide)).2 hL.lens
  have hX4 : Holds r4 X0 (cand (tabOf (G := G) st) e) := hX3.of_unchanged hU4 (by decide) (by decide)
  have hlt4 : r4.w "lab.lt" = LT := by rw [hU4.wreg _ (by decide)]; exact hlt3
  have hok4' : r4.w "ok" = if Ok d (G.src e) e then 1 else 0 := by
    rw [hok4]; by_cases h : Ok d (G.src e) e
    · rw [if_pos (hok.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hok.mp h')), if_neg h]
  rw [wp_ite_var]
  refine ⟨fun hne => ?_, fun hz => ?_⟩
  · -- strict decrease: store the candidate
    rw [hlt4] at hne
    have hs := hstrict hne
    have hOk : Ok d (G.src e) e := le_of_lt hs
    have hxv : (r4.charge 1).w X0.v = G.dst e := hX4.2.2.1
    have hvcw : (r4.charge 1).wa "vcnt" (G.dst e) = st.wa "vcnt" (G.dst e) := by
      have := congrArg Tab.vcnt hT4
      exact congrFun this (G.dst e)
    have hvc : (r4.charge 1).wa "vcnt" (G.dst e) + 1 < (r4.charge 1).cap := by
      rw [hvcw]; have := hL.vcnt_le (G.dst e)
      have hc : (r4.charge 1).cap = st.cap := hU34.cap
      rw [hc]; omega
    refine wp_mono _ ?_ _ (storeLab_wp X0.v X0 (r4.charge 1) e (hlens4.charge 1) hxv
      (by rw [show tabOf (G := G) (r4.charge 1) = tabOf st from hT4]; exact hX4.charge 1) hvc)
    rintro r5 ⟨hT5, hlens5, hU5, hc5⟩
    rw [show tabOf (G := G) (r4.charge 1) = tabOf st from hT4] at hT5
    have hvc5 : vc (G := G) r5 = ((tabOf (G := G) st).put e).vcnt := by
      show (tabOf (G := G) r5).vcnt = _
      rw [hT5]
    have hext : HExt H (vc (G := G) st) (Hput H (tabOf (G := G) st) e (p0 ++ [e])) (vc r5) := by
      rw [hvc5]; exact HExt.put H (tabOf st) e (p0 ++ [e])
    have hc5' : r5.cost = r4.cost + 7 := by rw [hc5]; rfl
    have hU5' : Unchanged st r5 labW labV relaxW relaxV :=
      ((hU34.comp (Unchanged.charge r4 1 [] [] [] [])).comp hU5).mono (by simp)
        (by simp) (by simp) (by simp)
    refine ⟨Hput H (tabOf (G := G) st) e (p0 ++ [e]), ⟨hlens5, ?_, ?_, ?_⟩, hext, ?_, ?_, ?_,
      hU5', ?_, ?_⟩
    · rw [hT5, relaxL_of_ok hOk]; exact hL.rep.put e hp hs
    · intro w
      have hw5 : r5.wa "dhops" w = ((tabOf (G := G) st).put e).hops w := by rw [← hT5]; rfl
      rw [hw5]
      by_cases hwv : w = G.dst e
      · subst hwv
        simp only [Tab.put, Function.update_self]
        have := hL.hops_le (G.src e); simp only [tabOf]; omega
      · simp only [Tab.put, Function.update_of_ne hwv]
        have := hL.hops_le w; simp only [tabOf]; omega
    · intro w
      have hw5 : r5.wa "vcnt" w = ((tabOf (G := G) st).put e).vcnt w := by rw [← hT5]; rfl
      rw [hw5]
      by_cases hwv : w = G.dst e
      · subst hwv
        simp only [Tab.put, Function.update_self]
        have := hL.vcnt_le (G.dst e); simp only [tabOf]; omega
      · simp only [Tab.put, Function.update_of_ne hwv]
        have := hL.vcnt_le w; simp only [tabOf]; omega
    · rw [hU5.wreg _ (by simp)]; exact hok4'
    · exact (hX4.charge 1).of_unchanged hU5 (by simp) (by simp)
    · intro p hp'
      exact Rep.ext (cand_rep hL.rep e hp') hext
    · omega
    · omega
  · -- no strict decrease: nothing is written
    rw [hlt4] at hz
    rw [wp_skip]
    have hrl : relaxL d (G.src e) e = d := by
      by_cases hOk : Ok d (G.src e) e
      · rw [relaxL_of_ok hOk, heqc hz hOk]; exact Function.update_eq_self _ _
      · exact relaxL_of_not_ok hOk
    have hU5 : Unchanged st ((r4.charge 1).charge 1) [] [] relaxW relaxV := by
      simpa only [unch_charge] using hU34
    have hvc5 : vc (G := G) ((r4.charge 1).charge 1) = vc st := vc_of_unchanged hU5 (by decide)
    refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrl]
      exact hL.of_unchanged hU5 (by decide) (by decide)
        (by simp only [State.charge_cost]; omega)
    · rw [hvc5]; exact HExt.refl _ _
    · exact hok4'
    · exact (hX4.charge 1).charge 1
    · intro p hp'
      rw [hvc5]; exact cand_rep hL.rep e hp'
    · exact hU5.mono (by simp) (by simp) (by simp) (by simp)
    · simp only [State.charge_cost]; omega
    · simp only [State.charge_cost]; omega

open Classical in
/-- **Spec of `relaxCore`** (refines `relaxL`, FH.10, re-confirmation included).  From a state
holding the label table of `d` (clock origin `c0`, budget `cost + 16 ≤ c0 + cap`) with the
candidate for `e` in `X0` and `d (src e)` finite: `CorePost`. -/
theorem relaxCore_wp {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (hL : LabAt st d H c0) (e : Fin G.m)
    (hX : Holds st X0 (cand (tabOf (G := G) st) e)) (hu : d (G.src e) ≠ ⊤)
    (hB : st.cost + 16 ≤ c0 + st.cap) :
    wp realOps relaxCore (CorePost st d H c0 e) st := by
  obtain ⟨p0, hp⟩ : ∃ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hu
    exact ⟨q, hq.symm⟩
  have hR : Represents (s := s) (tabOf (G := G) st) d H := hL.rep
  have hcand : Rep (s := s) H (tabOf (G := G) st).vcnt (cand (tabOf (G := G) st) e) (p0 ++ [e]) :=
    cand_rep hR e hp
  have hext : ext (d (G.src e)) e = ((toW (p0 ++ [e]) : WalkOrd G s) : WLab G s) := cand_ext e hp
  have hcap : 1 < st.cap := one_lt_cap_of_labAt hL (G.src e) (by omega)
  rw [relaxCore, wp_seq]
  refine wp_mono _ ?_ _ (loadLab_wp X0.v Y0 "lab.yf" ⟨by decide, by decide⟩ st (G.dst e) hL.lens
    hX.2.2.1)
  rintro r2 ⟨hY2, hU2, hc2⟩
  have hX2 : Holds r2 X0 (cand (tabOf (G := G) st) e) :=
    hX.of_unchanged hU2 (by decide) (by decide)
  have hU12 : Unchanged st r2 [] [] relaxW relaxV :=
    hU2.mono (by simp) (by simp) (by decide) (by decide)
  have hcap2 : 1 < (r2.charge 1).cap := by
    rw [show (r2.charge 1).cap = st.cap from hU12.cap]; exact hcap
  rw [wp_seq, wp_ite_var]
  by_cases hv : d (G.dst e) = ⊤
  · -- `d[v] = ⊤`: the candidate is strictly smaller
    have hyf : r2.w "lab.yf" = 0 := by rw [hY2.2.2.2.2.2]; exact (hR.fin_iff _).mpr hv
    refine ⟨fun h => absurd hyf h, fun _ => ?_⟩
    rw [wp_seq]
    refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "lab.lt" 1 (r2.charge 1) hcap2)
    rintro r3a ⟨hlt3a, hU3a, hc3a⟩
    refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "lab.gt" 0 r3a
      (by rw [hU3a.cap]; omega))
    rintro r3 ⟨hgt3, hU3, hc3⟩
    have hU23 : Unchanged st r3 [] [] relaxW relaxV :=
      ((hU12.comp (Unchanged.charge r2 1 [] [] [] [])).comp (hU3a.comp hU3)).mono (by simp)
        (by simp) (by decide) (by decide)
    refine relaxCore_tail st d H c0 hL e p0 hp hB r3 1 0
      (by rw [hU3.wreg _ (by decide)]; exact hlt3a) hgt3
      ((hX2.charge 1).of_unchanged (hU3a.comp hU3) (by decide) (by decide)) hU23
      (by simp only [State.charge_cost] at hc3a; omega)
      (by simp only [State.charge_cost] at hc3a; omega) ?_ ?_ ?_
    · intro _; rw [hv, hext]; exact WithTop.coe_lt_top _
    · intro h; exact absurd h one_ne_zero
    · simp only [true_iff]
      show ext (d (G.src e)) e ≤ d (G.dst e)
      rw [hv]; exact le_top
  · -- `d[v]` finite: two comparisons decide `<`, `=`, `>`
    obtain ⟨q, hq⟩ : ∃ q : List (Fin G.m), d (G.dst e) = ((toW q : WalkOrd G s) : WLab G s) := by
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hv; exact ⟨q, hq.symm⟩
    have hyf : r2.w "lab.yf" ≠ 0 := by
      rw [hY2.2.2.2.2.2]; exact fun h => hv ((hR.fin_iff _).mp h)
    refine ⟨fun _ => ?_, fun h => absurd h hyf⟩
    have hYv : Holds r2 Y0 ((tabOf (G := G) st).lab (G.dst e)) := Loaded.holds hY2 hR hv
    have hrepq : Rep (s := s) H (tabOf (G := G) st).vcnt ((tabOf (G := G) st).lab (G.dst e)) q :=
      hR.rep _ q hq
    rw [wp_seq]
    refine wp_mono _ ?_ _ (cmp_wp (ops := realOps) (fun a b => rfl) "lab.lt"
      ⟨by decide, by decide, by decide, by decide, by decide⟩ (r2.charge 1) hcap2)
    rintro r3a ⟨hlt3a, hU3a, hc3a, hc3a'⟩
    refine wp_mono _ ?_ _ (cmp_wp (ops := realOps) (fun a b => rfl) "lab.gt"
      ⟨by decide, by decide, by decide, by decide, by decide⟩ r3a (by rw [hU3a.cap]; exact hcap2))
    rintro r3 ⟨hgt3, hU3, hc3, hc3'⟩
    have hX3a := (hX2.charge 1).of_unchanged hU3a (by decide) (by decide)
    have hY3a := (hYv.charge 1).of_unchanged hU3a (by decide) (by decide)
    rw [cbit_eq (hX2.charge 1) (hYv.charge 1)] at hlt3a
    rw [cbit_eq hY3a hX3a] at hgt3
    have hU23 : Unchanged st r3 [] [] relaxW relaxV :=
      ((hU12.comp (Unchanged.charge r2 1 [] [] [] [])).comp (hU3a.comp hU3)).mono (by simp)
        (by simp) (by decide) (by decide)
    have iff1 := lt_iff hR.hist hcand hrepq
    have iff2 := lt_iff hR.hist hrepq hcand
    have hle_of_ok : Ok d (G.src e) e → toW (s := s) (p0 ++ [e]) ≤ toW q := by
      intro hOk
      have h' : ext (d (G.src e)) e ≤ d (G.dst e) := hOk
      rw [hext, hq] at h'
      exact WithTop.coe_le_coe.mp h'
    refine relaxCore_tail st d H c0 hL e p0 hp hB r3 _ _
      ((hU3.wreg "lab.lt" (by decide)).trans hlt3a) hgt3
      (hX3a.of_unchanged hU3 (by decide) (by decide)) hU23
      (by simp only [State.charge_cost] at hc3a; omega)
      (by simp only [State.charge_cost] at hc3a'; omega) ?_ ?_ ?_
    · intro hne
      have h1 : (cand (tabOf (G := G) st) e).lt ((tabOf (G := G) st).lab (G.dst e)) := by
        by_contra h; exact hne (if_neg h)
      rw [hext, hq]; exact WithTop.coe_lt_coe.mpr (iff1.mp h1)
    · intro hz hOk
      have h1 : ¬ (cand (tabOf (G := G) st) e).lt ((tabOf (G := G) st).lab (G.dst e)) := by
        intro h; rw [if_pos h] at hz; exact one_ne_zero hz
      have hnlt : ¬ toW (s := s) (p0 ++ [e]) < toW q := fun h => h1 (iff1.mpr h)
      rw [hext, hq]
      exact congrArg _ (le_antisymm (hle_of_ok hOk) (not_lt.mp hnlt))
    · constructor
      · intro hz
        have h2 : ¬ ((tabOf (G := G) st).lab (G.dst e)).lt (cand (tabOf (G := G) st) e) := by
          intro h; rw [if_pos h] at hz; exact one_ne_zero hz
        show ext (d (G.src e)) e ≤ d (G.dst e)
        rw [hext, hq]
        exact WithTop.coe_le_coe.mpr (not_lt.mp (fun h => h2 (iff2.mpr h)))
      · intro hOk
        exact if_neg (fun h => absurd (iff2.mp h) (not_lt.mpr (hle_of_ok hOk)))

open Classical in
/-- **Spec of `relaxFP`** (refines FindPivots' `relaxL`, FH.10, re-confirmation included).  From a
state holding the label table of `d` (clock origin `c0`) with `ru = src e`, `re = e`, `d (src e)`
finite and budget `cost + 64 ≤ c0 + cap`: afterwards the table represents `relaxL d (src e) e`
with an extended history, `ok = [Ok d (src e) e]`, `X0` holds the candidate (representing
`d (src e) ⊕ e` for the new history), only label arrays and B-LAB scratch registers are
written, and the cost is at most `60`. -/
theorem relaxFP_spec {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (hL : LabAt st d H c0) (hg : GraphAt st G)
    (e : Fin G.m) (hru : st.w "ru" = G.src e) (hre : st.w "re" = e) (hu : d (G.src e) ≠ ⊤)
    (hB : st.cost + 64 ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap) :
    Runs realOps relaxFP st (RelaxPost st d H c0 e) := by
  have hsrc : st.wa "dhops" (G.src e) + 1 < st.cap := by have := hL.hops_le (G.src e); omega
  have he1 : (e : ℕ) + 1 < st.cap := by have := e.isLt; omega
  apply wp_sound
  rw [relaxFP, wp_seq]
  refine wp_mono _ ?_ _ (candLab_wp X0 ⟨by decide, by decide, by decide⟩ st e hL.lens hg hru hre
    hsrc he1)
  rintro r1 ⟨hX1, hU1, hc1⟩
  have hT1 := (tabOf_of_unchanged (G := G) hU1 (by decide) (by decide)).1
  have hL1 : LabAt r1 d H c0 := hL.of_unchanged hU1 (by decide) (by decide) (by omega)
  have hvc1 : vc (G := G) r1 = vc st := vc_of_unchanged hU1 (by decide)
  refine wp_mono _ ?_ _ (relaxCore_wp r1 d H c0 hL1 e (by rw [hT1]; exact hX1) hu
    (by rw [hU1.cap]; omega))
  rintro r ⟨H', hL', hext, hok, hX, hrep, hU, hclo, hchi⟩
  rw [hT1] at hX hrep
  have hUst : Unchanged st r labW labV relaxW relaxV :=
    (hU1.comp hU).mono (by simp) (by simp) (by decide) (by decide)
  exact ⟨H', hL', hvc1 ▸ hext, hok, hX, hrep, graphAt_of_unchanged hUst (by decide) (by decide) hg,
    hUst, by omega⟩

/-! #### Bounds that may be `⊤`: `ltB`, `headLtB` -/

/-- A flagged block holds the WALK label `b` (possibly `⊤`): flag `xf = 0` iff `b = ⊤`; a finite
`b` is represented by the machine label in the block (history `H`, counters `V`). -/
def WHolds {s : Fin G.n} (st : State ℝ≥0) (X : LReg) (xf : String)
    (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (b : WLab G s) : Prop :=
  (st.w xf = 0 ↔ b = ⊤) ∧ ∀ q : List (Fin G.m), b = ((toW q : WalkOrd G s) : WLab G s) →
    ∃ x : MLabel G, Holds st X x ∧ Rep (s := s) H V x q

theorem WHolds.of_unchanged {s : Fin G.n} {st r : State ℝ≥0} {X : LReg} {xf : String}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s}
    {wa va wr vr : List String} (h : WHolds st X xf H V b) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ X.ws, a ∉ wr) (hv : X.l ∉ vr) (hf : xf ∉ wr) : WHolds r X xf H V b := by
  refine ⟨by rw [hu.wreg _ hf]; exact h.1, fun q hq => ?_⟩
  obtain ⟨x, hx, hxq⟩ := h.2 q hq
  exact ⟨x, hx.of_unchanged hu hw hv, hxq⟩

theorem WHolds.ext {s : Fin G.n} {st : State ℝ≥0} {X : LReg} {xf : String}
    {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ} {b : WLab G s}
    (h : WHolds st X xf H V b) (hE : HExt H V H' V') : WHolds st X xf H' V' b := by
  refine ⟨h.1, fun q hq => ?_⟩
  obtain ⟨x, hx, hxq⟩ := h.2 q hq
  exact ⟨x, hx, Rep.ext hxq hE⟩

open WExpr Stmt in
/-- `out := [X < K]` for a bound block `K` with flag `kf` (`kf = 0`: `K = ⊤`, so `out := 1`). -/
def ltB (X K : LReg) (kf c1 c2 out : String) : Stmt :=
  ite (var kf) (cmp X K c1 c2 out) (wset out (lit 1))

theorem ltB_wp (X K : LReg) (kf c1 c2 out : String) (hf : CmpFresh X K c1 c2) (st : State ℝ≥0)
    (hcap : 1 < st.cap) :
    wp realOps (ltB X K kf c1 c2 out) (fun r =>
      r.w out = (if st.w kf = 0 then 1 else cbit st X K) ∧
      Unchanged st r [] [] [c1, c2, out] [] ∧ st.cost + 1 ≤ r.cost ∧ r.cost ≤ st.cost + 14) st := by
  rw [ltB, wp_ite_var]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · refine wp_mono _ ?_ _ (cmp_wp (ops := realOps) (fun a b => rfl) out hf (st.charge 1) hcap)
    rintro r ⟨h1, h2, h3, h4⟩
    refine ⟨by rw [h1, if_neg hk]; rfl, ?_, ?_, ?_⟩
    · exact ((Unchanged.charge st 1 [] [] [] []).comp h2).mono (by simp) (by simp) (by simp)
        (by simp)
    · simp only [State.charge_cost] at h3; omega
    · simp only [State.charge_cost] at h4; omega
  · refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) out 1 (st.charge 1) hcap)
    rintro r ⟨h1, h2, h3⟩
    refine ⟨by rw [h1, if_pos hk], ?_, ?_, ?_⟩
    · exact ((Unchanged.charge st 1 [] [] [] []).comp h2).mono (by simp) (by simp) (by simp)
        (by simp)
    · simp only [State.charge_cost] at h3; omega
    · simp only [State.charge_cost] at h3; omega

open Classical in
/-- The bit of `ltB` is `[p < B]` in the walk order, for a represented finite `X` and a bound `B`
held in a flagged block. -/
theorem ltB_bit {s : Fin G.n} {st : State ℝ≥0} {X K : LReg} {kf : String}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} (hH : GoodHist (s := s) H V)
    {x : MLabel G} {p : List (Fin G.m)} (hx : Holds st X x) (hxp : Rep (s := s) H V x p)
    {B : WLab G s} (hK : WHolds st K kf H V B) :
    (if st.w kf = 0 then 1 else cbit st X K) =
      if ((toW p : WalkOrd G s) : WLab G s) < B then 1 else 0 := by
  by_cases hk : st.w kf = 0
  · have hB : B = ⊤ := hK.1.mp hk
    rw [if_pos hk, hB, if_pos (WithTop.coe_lt_top _)]
  · rw [if_neg hk]
    have hB : B ≠ ⊤ := fun h => hk (hK.1.mpr h)
    obtain ⟨q, hq⟩ : ∃ q : List (Fin G.m), B = ((toW q : WalkOrd G s) : WLab G s) := by
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hB; exact ⟨q, hq.symm⟩
    obtain ⟨k, hk1, hk2⟩ := hK.2 q hq
    rw [cbit_eq hx hk1, hq]
    have hiff := lt_iff hH hxp hk2
    by_cases h : x.lt k
    · rw [if_pos h, if_pos (WithTop.coe_lt_coe.mpr (hiff.mp h))]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr (WithTop.coe_lt_coe.mp h')))]

open WExpr Stmt in
/-- `out := [d[vx] < K]` (`⊤ < K` is false): FindPivots' test `d (dst e) < L_X`. -/
def headLtB (vx : String) (Y K : LReg) (yf kf c1 c2 out : String) : Stmt :=
  seq (loadLab vx Y yf) (ite (var yf) (ltB Y K kf c1 c2 out) (wset out (lit 0)))

open Classical in
theorem headLtB_wp {s : Fin G.n} (vx : String) (Y K : LReg) (yf kf c1 c2 out : String)
    (hF : LoadFresh vx Y yf) (hC : CmpFresh Y K c1 c2) (hKw : ∀ a ∈ K.ws, a ∉ yf :: Y.ws)
    (hKl : K.l ∉ [Y.l]) (hkf : kf ∉ yf :: Y.ws)
    (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (hL : LabAt st d H c0) (v : Fin G.n) (hv : st.w vx = v) (Bl : WLab G s)
    (hK : WHolds st K kf H (vc st) Bl) (hcap : 1 < st.cap) :
    wp realOps (headLtB vx Y K yf kf c1 c2 out) (fun r => r.w out = (if d v < Bl then 1 else 0) ∧
      Unchanged st r [] [] ((yf :: Y.ws) ++ [c1, c2, out]) [Y.l] ∧ r.cost ≤ st.cost + 22) st := by
  have hR := hL.rep
  rw [headLtB, wp_seq]
  refine wp_mono _ ?_ _ (loadLab_wp vx Y yf hF st v hL.lens hv)
  rintro r2 ⟨hY2, hU2, hc2⟩
  have hK2 : WHolds r2 K kf H (vc st) Bl := hK.of_unchanged hU2 hKw hKl hkf
  have hcap2 : 1 < (r2.charge 1).cap := by rw [show (r2.charge 1).cap = st.cap from hU2.cap]; exact hcap
  rw [wp_ite_var]
  refine ⟨fun hyf => ?_, fun hyf => ?_⟩
  · have hv' : d v ≠ ⊤ := fun h => hyf (by rw [hY2.2.2.2.2.2]; exact (hR.fin_iff v).mpr h)
    obtain ⟨q, hq⟩ : ∃ q : List (Fin G.m), d v = ((toW q : WalkOrd G s) : WLab G s) := by
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hv'; exact ⟨q, hq.symm⟩
    have hYv : Holds r2 Y ((tabOf (G := G) st).lab v) := Loaded.holds hY2 hR hv'
    refine wp_mono _ ?_ _ (ltB_wp Y K kf c1 c2 out hC (r2.charge 1) hcap2)
    rintro r ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hq]
      exact ltB_bit (V := vc st) hR.hist (hYv.charge 1) (hR.rep v q hq) hK2
    · exact ((hU2.comp (Unchanged.charge r2 1 [] [] [] [])).comp h2).mono (by simp)
        (by simp) (by intro a; first | (simp; done) | (simp; tauto)) (by simp)
    · simp only [State.charge_cost] at h4; omega
  · have hv' : d v = ⊤ := (hR.fin_iff v).mp (by rw [← hY2.2.2.2.2.2]; exact hyf)
    refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) out 0 (r2.charge 1) (by omega))
    rintro r ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hv', if_neg (not_top_lt)]
    · exact ((hU2.comp (Unchanged.charge r2 1 [] [] [] [])).comp h2).mono (by simp)
        (by simp) (by intro a; first | (simp; done) | (simp; tauto)) (by simp)
    · simp only [State.charge_cost] at h3; omega

/-! #### BM relaxation: the `ValidRelax` guard (BM.19–21, BM.27–28, BC.7) -/

open WExpr Stmt in
/-- BM `Relax` with bound `B` (block `K`, flag `kf`): `X0 := d[u] ⊕ e`; `lab.lb := [X0 < B]`;
then `relaxCore` if so, else `ok := 0`.  Afterwards `ok = [ValidRelax]` and `X0` holds the
candidate for the caller's `D.Insert` / `lo` test. -/
def relaxBM (K : LReg) (kf : String) : Stmt :=
  seq (candLab X0)
  (seq (ltB X0 K kf "lab.c1" "lab.c2" "lab.lb")
  (ite (var "lab.lb") relaxCore (wset "ok" (lit 0))))

/-- The bound registers are disjoint from the B-LAB scratch registers. -/
structure BoundRegs (K : LReg) (kf : String) : Prop where
  ws : ∀ a ∈ K.ws, a ∉ relaxW
  l : K.l ∉ relaxV
  f : kf ∉ relaxW

open Classical in
/-- The label part of `relaxIns` (BM.lean). -/
theorem relaxIns_fst {s : Fin G.n} (B : WLab G s) (lo : Option (WLab G s))
    (st : Labels G s × DS G s) (e : Fin G.m) :
    (BM.relaxIns G s B lo st e).1 = if BM.ValidRelax G s st.1 B e then
      Function.update st.1 (G.dst e) (ext (st.1 (G.src e)) e) else st.1 := by
  unfold BM.relaxIns
  by_cases h : BM.ValidRelax G s st.1 B e
  · simp only [h, if_true]
  · simp only [h, if_false]

open Classical in
/-- Postcondition of `relaxBM` (see `relaxBM_spec`). -/
def RelaxBPost {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (B : WLab G s) (e : Fin G.m) (r : State ℝ≥0) :
    Prop :=
  ∃ H', LabAt r (if BM.ValidRelax G s d B e then
      Function.update d (G.dst e) (ext (d (G.src e)) e) else d) H' c0 ∧
    HExt H (vc st) H' (vc r) ∧
    r.w "ok" = (if BM.ValidRelax G s d B e then 1 else 0) ∧
    Holds r X0 (cand (tabOf (G := G) st) e) ∧
    (∀ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) →
      Rep (s := s) H' (vc r) (cand (tabOf (G := G) st) e) (p ++ [e])) ∧
    GraphAt r G ∧ Unchanged st r labW labV relaxW relaxV ∧ r.cost ≤ st.cost + 70

open Classical in
/-- **Spec of `relaxBM`**: the label part of BM's `relaxIns` with bound `B`
(`= if ValidRelax then update else d`, cf. `relaxIns_fst`), `ok = [ValidRelax d B e]`, the
candidate in `X0` (representing `d (src e) ⊕ e` for the new history), cost at most `70`. -/
theorem relaxBM_spec {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (hL : LabAt st d H c0) (hg : GraphAt st G)
    (e : Fin G.m) (hru : st.w "ru" = G.src e) (hre : st.w "re" = e) (hu : d (G.src e) ≠ ⊤)
    (K : LReg) (kf : String) (hKr : BoundRegs K kf) (B : WLab G s)
    (hK : WHolds st K kf H (vc st) B)
    (hB : st.cost + 64 ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap) :
    Runs realOps (relaxBM K kf) st (RelaxBPost st d H c0 B e) := by
  obtain ⟨p0, hp⟩ : ∃ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hu
    exact ⟨q, hq.symm⟩
  have hsrc : st.wa "dhops" (G.src e) + 1 < st.cap := by have := hL.hops_le (G.src e); omega
  have he1 : (e : ℕ) + 1 < st.cap := by have := e.isLt; omega
  have hcand : Rep (s := s) H (vc (G := G) st) (cand (tabOf (G := G) st) e) (p0 ++ [e]) :=
    cand_rep hL.rep e hp
  have hKX : ∀ a ∈ K.ws, a ∉ X0.ws := fun a ha h => hKr.ws a ha (by
    simp only [X0, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> subst h <;> decide)
  have hKl : K.l ∉ [X0.l] := fun h => hKr.l (by
    simp only [X0, List.mem_singleton] at h; rw [h]; decide)
  have hkf : kf ∉ X0.ws := fun h => hKr.f (by
    simp only [X0, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> subst h <;> decide)
  have hc1K : "lab.c1" ∉ K.ws := fun h => hKr.ws _ h (by decide)
  have hc2K : "lab.c2" ∉ K.ws := fun h => hKr.ws _ h (by decide)
  apply wp_sound
  rw [relaxBM, wp_seq]
  refine wp_mono _ ?_ _ (candLab_wp X0 ⟨by decide, by decide, by decide⟩ st e hL.lens hg hru hre
    hsrc he1)
  rintro r1 ⟨hX1, hU1, hc1⟩
  have hT1 := (tabOf_of_unchanged (G := G) hU1 (by decide) (by decide)).1
  have hL1 : LabAt r1 d H c0 := hL.of_unchanged hU1 (by decide) (by decide) (by omega)
  have hvc1 : vc (G := G) r1 = vc st := vc_of_unchanged hU1 (by decide)
  have hK1 : WHolds r1 K kf H (vc st) B := hK.of_unchanged hU1 hKX hKl hkf
  have hcap1 : 1 < r1.cap := by rw [hU1.cap]; omega
  rw [wp_seq]
  refine wp_mono _ ?_ _ (ltB_wp X0 K kf "lab.c1" "lab.c2" "lab.lb"
    ⟨by decide, by decide, by decide, hc1K, hc2K⟩ r1 hcap1)
  rintro r2 ⟨hlb2, hU2, hc2lo, hc2hi⟩
  have hbit : r2.w "lab.lb" = if ext (d (G.src e)) e < B then 1 else 0 := by
    rw [hlb2, ltB_bit (V := vc st) hL.rep.hist hX1 hcand hK1, cand_ext e hp]
  have hU12 : Unchanged st r2 [] [] relaxW relaxV :=
    (hU1.comp hU2).mono (by simp) (by simp) (by decide) (by decide)
  have hT2 : tabOf (G := G) r2 = tabOf st :=
    (tabOf_of_unchanged (G := G) hU12 (by decide) (by decide)).1
  have hvc2 : vc (G := G) r2 = vc st := vc_of_unchanged hU12 (by decide)
  have hX2 : Holds r2 X0 (cand (tabOf (G := G) st) e) := hX1.of_unchanged hU2 (by decide) (by decide)
  rw [wp_ite_var]
  refine ⟨fun hlb => ?_, fun hlb => ?_⟩
  · -- `ext < B`: the guard reduces to `Ok`, run `relaxCore`
    have hlt : ext (d (G.src e)) e < B := by
      by_contra h; rw [hbit, if_neg h] at hlb; exact hlb rfl
    have hL2 : LabAt (r2.charge 1) d H c0 :=
      hL.of_unchanged (hU12.comp (Unchanged.charge r2 1 [] [] [] [])) (by decide) (by decide)
        (by simp only [State.charge_cost]; omega)
    have hT2' : tabOf (G := G) (r2.charge 1) = tabOf st := hT2
    refine wp_mono _ ?_ _ (relaxCore_wp (r2.charge 1) d H c0 hL2 e
      (by rw [hT2']; exact hX2.charge 1) hu (by
        simp only [State.charge_cost, State.charge_cap]; rw [hU12.cap]; omega))
    rintro r ⟨H', hL', hext, hok, hX, hrep, hU, hclo, hchi⟩
    rw [hT2'] at hX hrep
    have hvr : BM.ValidRelax G s d B e ↔ Ok d (G.src e) e := ⟨fun h => h.1, fun h => ⟨h, hlt⟩⟩
    have hdl : (if BM.ValidRelax G s d B e then
        Function.update d (G.dst e) (ext (d (G.src e)) e) else d) = relaxL d (G.src e) e := by
      by_cases hOk : Ok d (G.src e) e
      · rw [if_pos (hvr.mpr hOk), relaxL_of_ok hOk]
      · rw [if_neg (fun h => hOk (hvr.mp h)), relaxL_of_not_ok hOk]
    have hUst : Unchanged st r labW labV relaxW relaxV :=
      ((hU12.comp (Unchanged.charge r2 1 [] [] [] [])).comp hU).mono (by simp) (by simp)
        (by intro a; simp) (by intro a; simp)
    refine ⟨H', by rw [hdl]; exact hL', ?_, ?_, hX, hrep,
      graphAt_of_unchanged hUst (by decide) (by decide) hg, hUst, ?_⟩
    · have : vc (G := G) (r2.charge 1) = vc st := hvc2
      rw [this] at hext; exact hext
    · rw [hok]
      by_cases hOk : Ok d (G.src e) e
      · rw [if_pos hOk, if_pos (hvr.mpr hOk)]
      · rw [if_neg hOk, if_neg (fun h => hOk (hvr.mp h))]
    · simp only [State.charge_cost] at hchi; omega
  · -- `¬ ext < B`: invalid, nothing is written
    have hnlt : ¬ ext (d (G.src e)) e < B := by
      intro h; rw [hbit, if_pos h] at hlb; exact one_ne_zero hlb
    have hnv : ¬ BM.ValidRelax G s d B e := fun h => hnlt h.2
    refine wp_mono _ ?_ _ (wset_lit_wp (ops := realOps) "ok" 0 (r2.charge 1) (by
      rw [show (r2.charge 1).cap = st.cap from hU12.cap]; omega))
    rintro r ⟨h1, h2, h3⟩
    have hUst : Unchanged st r [] [] relaxW relaxV :=
      ((hU12.comp (Unchanged.charge r2 1 [] [] [] [])).comp h2).mono (by simp) (by simp)
        (by intro a; first | (simp; done) | (simp [relaxW]; done) | (simp [relaxW]; tauto))
        (by simp)
    have hvcr : vc (G := G) r = vc st := vc_of_unchanged hUst (by decide)
    refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg hnv]
      exact hL.of_unchanged hUst (by decide) (by decide) (by simp only [State.charge_cost] at h3; omega)
    · rw [hvcr]; exact HExt.refl _ _
    · rw [h1, if_neg hnv]
    · exact (hX2.charge 1).of_unchanged h2 (by decide) (by decide)
    · intro p hp'; rw [hvcr]; exact cand_rep hL.rep e hp'
    · exact graphAt_of_unchanged hUst (by decide) (by decide) hg
    · exact hUst.mono (by simp) (by simp) (by simp) (by simp)
    · simp only [State.charge_cost] at h3; omega

/-! #### FH.8: candidate plus bound test (`candB`) -/

open WExpr Stmt in
/-- FindPivots FH.8: `X0 := d[u] ⊕ e` (inputs `ru`, `re`) and `out := [X0 < K]`. -/
def candB (K : LReg) (kf out : String) : Stmt :=
  seq (candLab X0) (ltB X0 K kf "lab.c1" "lab.c2" out)

open Classical in
theorem candB_spec {s : Fin G.n} (st : State ℝ≥0) (d : Labels G s)
    (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (hL : LabAt st d H c0) (hg : GraphAt st G)
    (e : Fin G.m) (hru : st.w "ru" = G.src e) (hre : st.w "re" = e) (hu : d (G.src e) ≠ ⊤)
    (K : LReg) (kf out : String) (hKr : BoundRegs K kf) (hout : out ∉ X0.ws) (B : WLab G s)
    (hK : WHolds st K kf H (vc st) B)
    (hB : st.cost + 32 ≤ c0 + st.cap) (hm : G.m + 2 ≤ st.cap) :
    Runs realOps (candB K kf out) st (fun r => LabAt r d H c0 ∧ vc (G := G) r = vc st ∧
      Holds r X0 (cand (tabOf (G := G) st) e) ∧ tabOf (G := G) r = tabOf st ∧
      r.w out = (if ext (d (G.src e)) e < B then 1 else 0) ∧
      Unchanged st r [] [] (X0.ws ++ ["lab.c1", "lab.c2", out]) [X0.l] ∧
      st.cost + 1 ≤ r.cost ∧ r.cost ≤ st.cost + 19) := by
  obtain ⟨p0, hp⟩ : ∃ p : List (Fin G.m), d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hu
    exact ⟨q, hq.symm⟩
  have hsrc : st.wa "dhops" (G.src e) + 1 < st.cap := by have := hL.hops_le (G.src e); omega
  have he1 : (e : ℕ) + 1 < st.cap := by have := e.isLt; omega
  have hcand : Rep (s := s) H (vc (G := G) st) (cand (tabOf (G := G) st) e) (p0 ++ [e]) :=
    cand_rep hL.rep e hp
  have hKX : ∀ a ∈ K.ws, a ∉ X0.ws := fun a ha h => hKr.ws a ha (by
    simp only [X0, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> subst h <;> decide)
  have hKl : K.l ∉ [X0.l] := fun h => hKr.l (by
    simp only [X0, List.mem_singleton] at h; rw [h]; decide)
  have hkf : kf ∉ X0.ws := fun h => hKr.f (by
    simp only [X0, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> subst h <;> decide)
  have hc1K : "lab.c1" ∉ K.ws := fun h => hKr.ws _ h (by decide)
  have hc2K : "lab.c2" ∉ K.ws := fun h => hKr.ws _ h (by decide)
  apply wp_sound
  rw [candB, wp_seq]
  refine wp_mono _ ?_ _ (candLab_wp X0 ⟨by decide, by decide, by decide⟩ st e hL.lens hg hru hre
    hsrc he1)
  rintro r1 ⟨hX1, hU1, hc1⟩
  have hK1 : WHolds r1 K kf H (vc st) B := hK.of_unchanged hU1 hKX hKl hkf
  have hcap1 : 1 < r1.cap := by rw [hU1.cap]; omega
  refine wp_mono _ ?_ _ (ltB_wp X0 K kf "lab.c1" "lab.c2" out
    ⟨by decide, by decide, by decide, hc1K, hc2K⟩ r1 hcap1)
  rintro r2 ⟨hlb2, hU2, hc2lo, hc2hi⟩
  have hU12 := hU1.comp hU2
  have hT2 : tabOf (G := G) r2 = tabOf st :=
    (tabOf_of_unchanged (G := G) hU12 (by decide) (by decide)).1
  refine ⟨hL.of_unchanged hU12 (by decide) (by decide) (by omega),
    vc_of_unchanged hU12 (by decide), ?_, hT2, ?_, ?_, by omega, by omega⟩
  · refine hX1.of_unchanged hU2 (fun a ha h => ?_) (by simp [X0])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · subst h; revert ha; decide
    · subst h; revert ha; decide
    · subst h; exact hout ha
  · rw [hlb2, ltB_bit (V := vc st) hL.rep.hist hX1 hcand hK1, cand_ext e hp]
  · exact hU12.mono (by simp) (by simp) (by intro a; simp) (by intro a; simp)

/-! #### Source initialization and output decoding -/

open WExpr Stmt in
/-- Allocate the label table for `gN` vertices and set `d[gS] := (0, 0, gS, none, ver 0)`,
`vcnt[gS] := 1`; all other entries are `⊤` (`dfin = 0`, `vcnt = 0`). -/
def initLab : Stmt :=
  seq (walloc "dfin" (var "gN")) (seq (valloc "dlen" (var "gN"))
  (seq (walloc "dhops" (var "gN")) (seq (walloc "de" (var "gN"))
  (seq (walloc "dver" (var "gN")) (seq (walloc "vcnt" (var "gN"))
  (seq (wstore "dfin" (var "gS") (lit 1)) (wstore "vcnt" (var "gS") (lit 1))))))))

/-- The initial ghost history: the empty walk. -/
def H0 : Fin G.n → ℕ → List (Fin G.m) := fun _ _ => []

/-- The table right after `initLab`. -/
def T0 (s : Fin G.n) : Tab G :=
  ⟨fun v => if v = s then 1 else 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun v => if v = s then 1 else 0⟩

theorem represents_T0 (s : Fin G.n) :
    Represents (s := s) (T0 (G := G) s) (BM.initLabels s) H0 := by
  have hinit : ∀ v, BM.initLabels (G := G) s v =
      if v = s then ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) else ⊤ := fun _ => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro u a ha1 ha
    simp only [T0] at ha
    by_cases hu : u = s
    · subst hu; exact Graph.IsWalk.nil u
    · rw [if_neg hu] at ha; omega
  · intro u a b ha1 hab hb
    simp only [T0] at hb
    split_ifs at hb <;> omega
  · intro v
    simp only [T0, hinit]
    by_cases hv : v = s
    · simp [hv]
    · simp [hv]
  · intro v
    simp only [T0, hinit]
    by_cases hv : v = s
    · simp [hv]
    · simp [hv]
  · intro v p hp
    rw [hinit] at hp
    by_cases hv : v = s
    · rw [if_pos hv] at hp
      have hp' : p = [] := (WithTop.coe_inj.mp hp).symm
      subst hv hp'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [walkOf, Tab.lab, T0, decE]
      · simp [Tab.lab, T0]
      · simp [Tab.lab, T0]
      · simp [Tab.lab, T0, endV]
      · intro _; simp [Tab.lab, T0]
      · intro e he; simp [Tab.lab, T0, decE] at he
    · rw [if_neg hv] at hp; exact absurd hp.symm WithTop.coe_ne_top
  · intro v p hp
    rw [hinit] at hp
    by_cases hv : v = s
    · rw [if_pos hv] at hp
      have hp' : p = [] := (WithTop.coe_inj.mp hp).symm
      subst hp'; rfl
    · rw [if_neg hv] at hp; exact absurd hp.symm WithTop.coe_ne_top
  · intro v _; simp [T0]

theorem initPost (st r : State ℝ≥0) (s : Fin G.n) (htab : tabOf (G := G) r = T0 s)
    (hlens : LabLens r G.n) (hU : Unchanged st r labW labV [] [])
    (hc : r.cost = st.cost + 6 * G.n + 8) :
    LabAt (s := s) r (BM.initLabels s) H0 st.cost ∧ Unchanged st r labW labV [] [] ∧
      r.cost = st.cost + 6 * G.n + 8 := by
  refine ⟨⟨hlens, htab ▸ represents_T0 s, fun v => ?_, fun v => ?_⟩, hU, hc⟩
  · have : r.wa "dhops" v = (tabOf (G := G) r).hops v := rfl
    rw [this, htab]; simp only [T0]; omega
  · have : r.wa "vcnt" v = (tabOf (G := G) r).vcnt v := rfl
    rw [this, htab]; simp only [T0]; split_ifs <;> omega

theorem walloc_wp {ops : VOps ℝ≥0} {arr : String} {e : WExpr} {Q : State ℝ≥0 → Prop}
    {s : State ℝ≥0} {k : ℕ} (he : evalW s e = some k) :
    wp ops (.walloc arr e) Q s = Q ((s.allocW arr k).charge (k + 1)) := by
  simp [wp, he]

theorem valloc_wp {ops : VOps ℝ≥0} {arr : String} {e : WExpr} {Q : State ℝ≥0 → Prop}
    {s : State ℝ≥0} {k : ℕ} (he : evalW s e = some k) :
    wp ops (.valloc arr e) Q s = Q ((s.allocV arr k ops.zero).charge (k + 1)) := by
  simp [wp, he]

theorem wstore_wp {ops : VOps ℝ≥0} {arr : String} {i e : WExpr} {Q : State ℝ≥0 → Prop}
    {s : State ℝ≥0} {j a : ℕ} (hi : evalW s i = some j) (he : evalW s e = some a) :
    wp ops (.wstore arr i e) Q s = (j < s.wlen arr ∧ Q ((s.storeW arr j a).charge 1)) := by
  simp [wp, hi, he]

theorem initLab_wp (st : State ℝ≥0) (s : Fin G.n) (hn : st.w "gN" = G.n) (hs : st.w "gS" = s)
    (hcap : 1 < st.cap) :
    wp realOps initLab (fun r => LabAt (s := s) r (BM.initLabels s) H0 st.cost ∧
      Unchanged st r labW labV [] [] ∧ r.cost = st.cost + 6 * G.n + 8) st := by
  have hsn : (s : ℕ) < G.n := s.isLt
  rw [initLab, wp_seq, walloc_wp (k := G.n) (by simp [hn]), wp_seq,
    valloc_wp (k := G.n) (by simp [hn]), wp_seq, walloc_wp (k := G.n) (by simp [hn]), wp_seq,
    walloc_wp (k := G.n) (by simp [hn]), wp_seq, walloc_wp (k := G.n) (by simp [hn]), wp_seq,
    walloc_wp (k := G.n) (by simp [hn]), wp_seq, wstore_wp (j := s) (a := 1) (by simp [hs])
    (by simp [fit_of_lt hcap, State.allocW, State.allocV, State.charge]),
    wstore_wp (j := s) (a := 1) (by simp [hs])
    (by simp [fit_of_lt hcap, State.allocW, State.allocV, State.charge, State.storeW])]
  refine ⟨by simp [State.allocW, State.allocV, State.charge, hsn],
    by simp [State.allocW, State.allocV, State.charge, State.storeW, hsn],
    initPost st _ s ?_ ?_ ?_ ?_⟩
  · simp only [tabOf, T0, Tab.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext v <;>
      simp [State.allocW, State.allocV, State.charge, State.storeW, Fin.val_inj, realOps]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [State.allocW, State.allocV, State.charge, State.storeW]
  · simp only [unch_charge]
    rw [unch_storeW (by simp [labW]), unch_charge, unch_storeW (by simp [labW]), unch_charge,
      unch_allocW (by simp [labW]), unch_charge, unch_allocW (by simp [labW]), unch_charge,
      unch_allocW (by simp [labW]), unch_charge, unch_allocW (by simp [labW]), unch_charge,
      unch_allocV (by simp [labV]), unch_charge, unch_allocW (by simp [labW])]
    simp
  · simp [State.allocW, State.allocV, State.charge, State.storeW]; ring

/-- Output decoding: the table's `(dfin, dlen)` read as `State.label` gives `labelLen` of the
represented labels (so the back-mapping may read `dfin`/`dlen` directly). -/
theorem LabAt.labelLen {s : Fin G.n} {st : State ℝ≥0} {d : Labels G s}
    {H : Fin G.n → ℕ → List (Fin G.m)} {c0 : ℕ} (hL : LabAt st d H c0) (v : Fin G.n) :
    (if st.wa "dfin" v = 0 then (⊤ : ℝ≥0∞) else ((st.va "dlen" v : ℝ≥0) : ℝ≥0∞)) =
      labelLen (d v) := by
  by_cases hv : d v = ⊤
  · have : st.wa "dfin" v = 0 := (hL.rep.fin_iff v).mpr hv
    rw [if_pos this, hv]; rfl
  · have hf : st.wa "dfin" v ≠ 0 := fun h => hv ((hL.rep.fin_iff v).mp h)
    obtain ⟨q, hq⟩ : ∃ q : List (Fin G.m), d v = ((toW q : WalkOrd G s) : WLab G s) := by
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hv; exact ⟨q, hq.symm⟩
    rw [if_neg hf, hq]
    have hlen := (hL.rep.rep v q hq).2.1
    simp only [Tab.lab, tabOf] at hlen
    rw [hlen]; rfl

/-! #### Label arrays (D entry pools, block separators, per-level bound slots) -/

/-- A label array: value array `l` and word arrays `h v e r` (entry `i` = one machine label). -/
structure LArr where
  l : String
  h : String
  v : String
  e : String
  r : String

/-- The word arrays of a label array. -/
def LArr.ws (A : LArr) : List String := [A.h, A.v, A.e, A.r]

/-- Entry `i` of `A` holds the machine label `x` (edge encoded by `encE`). -/
def AHolds (st : State ℝ≥0) (A : LArr) (i : ℕ) (x : MLabel G) : Prop :=
  st.va A.l i = x.len ∧ st.wa A.h i = x.hops ∧ st.wa A.v i = x.v ∧ st.wa A.e i = encE x.e ∧
    st.wa A.r i = x.ver

/-- Entry `i` of `A` is inside all five arrays. -/
def LArr.InB (st : State ℝ≥0) (A : LArr) (i : ℕ) : Prop :=
  i < st.vlen A.l ∧ i < st.wlen A.h ∧ i < st.wlen A.v ∧ i < st.wlen A.e ∧ i < st.wlen A.r

open WExpr Stmt in
/-- `X := A[ix]` (5 loads). -/
def loadA (A : LArr) (ix : String) (X : LReg) : Stmt :=
  seq (vset X.l (.load A.l (var ix)))
  (seq (wset X.h (load A.h (var ix)))
  (seq (wset X.v (load A.v (var ix)))
  (seq (wset X.e (load A.e (var ix)))
       (wset X.r (load A.r (var ix))))))

open WExpr Stmt in
/-- `A[ix] := X` (5 stores). -/
def storeA (A : LArr) (ix : String) (X : LReg) : Stmt :=
  seq (vstore A.l (var ix) (.var X.l))
  (seq (wstore A.h (var ix) (var X.h))
  (seq (wstore A.v (var ix) (var X.v))
  (seq (wstore A.e (var ix) (var X.e))
       (wstore A.r (var ix) (var X.r)))))

/-- Freshness for `loadA`: distinct target registers, index register not overwritten early. -/
structure LoadAFresh (ix : String) (X : LReg) : Prop where
  nd : X.ws.Nodup
  ix : ix ∉ [X.h, X.v, X.e]

theorem loadA_wp (A : LArr) (ix : String) (X : LReg) (hF : LoadAFresh ix X) (st : State ℝ≥0)
    (i : ℕ) (hi : st.w ix = i) (hb : A.InB st i) (x : MLabel G) (hx : AHolds st A i x) :
    wp realOps (loadA A ix X) (fun r => Holds r X x ∧ Unchanged st r [] [] X.ws [X.l] ∧
      r.cost = st.cost + 5) st := by
  have hnd := hF.nd
  have hix := hF.ix
  simp only [LReg.ws, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd hix
  obtain ⟨⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩ := hnd
  obtain ⟨i1, i2, i3⟩ := hix
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  obtain ⟨x1, x2, x3, x4, x5⟩ := hx
  simp only [loadA, wp, evalV_load', evalW_var, evalW_load', State.charge_w, State.charge_wa,
    State.charge_va, State.charge_wlen, State.charge_vlen, State.setV_w, State.setV_wa,
    State.setV_va, State.setV_wlen, State.setV_vlen, State.setW_w, State.setW_wa, State.setW_va,
    State.setW_wlen, State.setW_vlen, hi, b1, b2, b3, b4, b5, ↓reduceIte, Option.bind_some,
    i1, i2, i3]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [State.setW, State.setV, State.charge, x1]
  · simp [State.setW, State.setV, State.charge, n12, n13, n14, x2]
  · simp [State.setW, State.setV, State.charge, n23, n24, x3]
  · simp [State.setW, State.setV, State.charge, n34, x4]
  · simp [State.setW, State.setV, State.charge, x5]
  · simp only [unch_charge]
    rw [unch_setW (by simp [LReg.ws]), unch_charge, unch_setW (by simp [LReg.ws]), unch_charge,
      unch_setW (by simp [LReg.ws]), unch_charge, unch_setW (by simp [LReg.ws]), unch_charge,
      unch_setV (by simp)]
    simp
  · simp [State.setW, State.setV, State.charge]

/-- The five arrays of `A` are distinct. -/
def LArr.Nodup (A : LArr) : Prop := A.ws.Nodup

theorem storeA_wp (A : LArr) (hA : A.Nodup) (ix : String) (X : LReg) (st : State ℝ≥0) (i : ℕ)
    (hi : st.w ix = i) (hb : A.InB st i) (x : MLabel G) (hx : Holds st X x) :
    wp realOps (storeA A ix X) (fun r => AHolds r A i x ∧
      (∀ j, j ≠ i → ∀ y : MLabel G, AHolds st A j y → AHolds r A j y) ∧
      (∀ j, A.InB st j → A.InB r j) ∧
      Unchanged st r A.ws [A.l] [] [] ∧ r.cost = st.cost + 5) st := by
  simp only [LArr.Nodup, LArr.ws, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hA
  obtain ⟨⟨n12, n13, n14⟩, ⟨n23, n24⟩, n34⟩ := hA
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  obtain ⟨x1, x2, x3, x4, x5⟩ := hx
  simp only [storeA, wp, evalV_var', evalW_var, State.charge_w, State.charge_v,
    State.charge_wlen, State.charge_vlen, State.storeV_w, State.storeV_v, State.storeV_wlen,
    State.storeV_vlen, State.storeW_w, State.storeW_v, State.storeW_wlen, State.storeW_vlen, hi,
    b1, b2, b3, b4, b5, ↓reduceIte, Option.bind_some, true_and]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [State.storeW, State.storeV, State.charge, x1]
  · simp [State.storeW, State.storeV, State.charge, n12, n13, n14, x2]
  · simp [State.storeW, State.storeV, State.charge, n23, n24, x3]
  · simp [State.storeW, State.storeV, State.charge, n34, x4]
  · simp [State.storeW, State.storeV, State.charge, x5]
  · intro j hj y ⟨y1, y2, y3, y4, y5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [State.storeW, State.storeV, State.charge, hj, y1, y2, y3, y4, y5]
  · intro j ⟨c1, c2, c3, c4, c5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simpa [State.storeW, State.storeV, State.charge]
  · simp only [unch_charge]
    rw [unch_storeW (by simp [LArr.ws]), unch_charge, unch_storeW (by simp [LArr.ws]), unch_charge,
      unch_storeW (by simp [LArr.ws]), unch_charge, unch_storeW (by simp [LArr.ws]), unch_charge,
      unch_storeV (by simp)]
    simp
  · simp [State.storeW, State.storeV, State.charge]

/-- Reading back: an entry stored from a block holding a represented label represents it. -/
theorem AHolds.of_unchanged {st r : State ℝ≥0} {A : LArr} {i : ℕ} {x : MLabel G}
    {wa va wr vr : List String} (h : AHolds st A i x) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ A.ws, a ∉ wa) (hv : A.l ∉ va) : AHolds r A i x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [(hu.varr _ hv).1, h1]
  · rw [(hu.warr _ (hw _ (by simp [LArr.ws]))).1, h2]
  · rw [(hu.warr _ (hw _ (by simp [LArr.ws]))).1, h3]
  · rw [(hu.warr _ (hw _ (by simp [LArr.ws]))).1, h4]
  · rw [(hu.warr _ (hw _ (by simp [LArr.ws]))).1, h5]

end Labels

end LabRAM

end Frontier.RAM
