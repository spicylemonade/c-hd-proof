import Frontier.CHD.TreeRAM2
import Frontier.CHD.FindPivots

/-!
# Frontier.CHD.TreeRAM3 — (T2, part 1) the re-rooting path walk of `mergeTree` (owner agent-03)

**NON-GATE** (Layer B).  On a contact `(u, v)` the search `K` is re-rooted along `kpath kpar x |K| u` and appended
to the tree of `v` (agent-05's `mergeTree`).  `pwLoop` walks that path exactly as `kpath` (stopping at the root `x`
or when the fuel runs out), and for each path vertex `w` sets `tr.inP[w] := 1`, `tr.tid[w] := t`, `fp.fm[w] := 1`,
`fp.par[w] := prev` (`reroot`: the contact head `v` for the first vertex, then the previous path vertex), links `w`
after the current tail `tr.pv`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- The last element of a list, or `d`. -/
def lastOr {α : Type*} (L : List α) (d : α) : α := L.getLast?.getD d

theorem lastOr_nil {α : Type*} (d : α) : lastOr ([] : List α) d = d := rfl

theorem lastOr_snoc {α : Type*} (L : List α) (a d : α) : lastOr (L ++ [a]) d = a := by
  simp [lastOr]

theorem lastOr_map {α β : Type*} (f : α → β) (L : List α) (d : α) : lastOr (L.map f) (f d) = f (lastOr L d) := by
  unfold lastOr
  cases h : L.getLast? with
  | none =>
    have : L = [] := List.getLast?_eq_none_iff.mp h
    subst this; rfl
  | some a =>
    rw [List.getLast?_map, h]; rfl

/-- `reroot` along a path extended by one vertex. -/
theorem reroot_snoc {α : Type*} [DecidableEq α] :
    ∀ (P : List α) (prev c : α) (f : α → α),
      reroot (P ++ [c]) prev f = Function.update (reroot P prev f) c (lastOr P prev)
  | [], prev, c, f => by simp [reroot, lastOr]
  | w :: ws, prev, c, f => by
    simp only [List.cons_append, reroot]
    rw [reroot_snoc ws w c (Function.update f w prev)]
    congr 1
    unfold lastOr
    cases ws with
    | nil => rfl
    | cons a l => simp [List.getLast?_cons]

/-- `kpath` one step: the fuel-exact unfolding. -/
theorem kpath_step {α : Type*} [DecidableEq α] (kpar : α → α) (x : α) (f : ℕ) (c : α) :
    kpath kpar x f c = if c = x ∨ f = 0 then [c] else c :: kpath kpar x (f - 1) (kpar c) := by
  cases f with
  | zero => simp [kpath]
  | succ f =>
    simp only [kpath, Nat.add_sub_cancel, Nat.succ_ne_zero, or_false]

/-! ## The path walk -/


theorem getLast_cons_eq_lastOr {α : Type*} (a : α) (L : List α) :
    (a :: L).getLast (List.cons_ne_nil a L) = lastOr L a := by
  unfold lastOr
  cases L with
  | nil => rfl
  | cons b l =>
    rw [List.getLast_cons (List.cons_ne_nil b l)]
    simp [List.getLast?_eq_getLast]

/-- Invariant of the path walk after the processed prefix `Pr` of the path `P`, with measure `n`. -/
structure PWI (st0 : State V) {N : ℕ} (kpar : Fin N → Fin N) (x v : Fin N) (P : List (Fin N)) (ot t c0 : ℕ)
    (n : ℕ) (Pr : List (Fin N)) (st : State V) : Prop where
  pre : Pr <+: P
  ctl : (n = 0 ∧ Pr = P ∧ st.w "tr.x" = 0) ∨
    (0 < n ∧ st.w "tr.x" = 1 ∧ ∃ (c : Fin N) (f : ℕ), st.w "tr.c" = c.val ∧ st.w "tr.f" = f ∧ n = f + 1 ∧
      Pr ++ kpath kpar x f c = P)
  inP : ∀ i, st.wa "tr.inP" i = if i ∈ Pr.map Fin.val then 1 else st0.wa "tr.inP" i
  tid : ∀ i, st.wa "tr.tid" i = if i ∈ Pr.map Fin.val then t else st0.wa "tr.tid" i
  fm : ∀ i, st.wa "fp.fm" i = if i ∈ Pr.map Fin.val then 1 else st0.wa "fp.fm" i
  par : ∀ w ∈ Pr, st.wa "fp.par" w.val = (reroot Pr v id w).val
  par' : ∀ i, i ∉ Pr.map Fin.val → st.wa "fp.par" i = st0.wa "fp.par" i
  ll : LL st "tr.nx" (ot :: Pr.map Fin.val)
  nx : ∀ i, i ∉ (ot :: Pr.map Fin.val).dropLast → st.wa "tr.nx" i = st0.wa "tr.nx" i
  pv : st.w "tr.pv" = lastOr (Pr.map Fin.val) ot
  u : st.w "tr.u" = (lastOr Pr v).val
  arr : ∀ arr i, arr ≠ "tr.inP" → arr ≠ "tr.tid" → arr ≠ "fp.fm" → arr ≠ "fp.par" → arr ≠ "tr.nx" →
    st.wa arr i = st0.wa arr i
  reg : ∀ y, y ≠ "tr.c" → y ≠ "tr.f" → y ≠ "tr.x" → y ≠ "tr.pv" → y ≠ "tr.u" → st.w y = st0.w y
  wlen : st.wlen = st0.wlen
  cap : st.cap = st0.cap
  cost : st.cost + 14 * n ≤ c0

/-- The facts of the path walk at the processed prefix `Pr'`, independent of the control registers. -/
structure PWA (st0 : State V) {N : ℕ} (v : Fin N) (ot t : ℕ) (Pr : List (Fin N)) (st : State V) : Prop where
  inP : ∀ i, st.wa "tr.inP" i = if i ∈ Pr.map Fin.val then 1 else st0.wa "tr.inP" i
  tid : ∀ i, st.wa "tr.tid" i = if i ∈ Pr.map Fin.val then t else st0.wa "tr.tid" i
  fm : ∀ i, st.wa "fp.fm" i = if i ∈ Pr.map Fin.val then 1 else st0.wa "fp.fm" i
  par : ∀ w ∈ Pr, st.wa "fp.par" w.val = (reroot Pr v id w).val
  par' : ∀ i, i ∉ Pr.map Fin.val → st.wa "fp.par" i = st0.wa "fp.par" i
  ll : LL st "tr.nx" (ot :: Pr.map Fin.val)
  nx : ∀ i, i ∉ (ot :: Pr.map Fin.val).dropLast → st.wa "tr.nx" i = st0.wa "tr.nx" i
  pv : st.w "tr.pv" = lastOr (Pr.map Fin.val) ot
  u : st.w "tr.u" = (lastOr Pr v).val
  arr : ∀ arr i, arr ≠ "tr.inP" → arr ≠ "tr.tid" → arr ≠ "fp.fm" → arr ≠ "fp.par" → arr ≠ "tr.nx" →
    st.wa arr i = st0.wa arr i
  reg : ∀ y, y ≠ "tr.c" → y ≠ "tr.f" → y ≠ "tr.x" → y ≠ "tr.pv" → y ≠ "tr.u" → st.w y = st0.w y
  wlen : st.wlen = st0.wlen
  cap : st.cap = st0.cap

theorem PWA.of_PWI {st0 : State V} {N : ℕ} {kpar : Fin N → Fin N} {x v : Fin N} {P : List (Fin N)}
    {ot t c0 n : ℕ} {Pr : List (Fin N)} {st : State V} (h : PWI st0 kpar x v P ot t c0 n Pr st) :
    PWA st0 v ot t Pr st :=
  ⟨h.inP, h.tid, h.fm, h.par, h.par', h.ll, h.nx, h.pv, h.u, h.arr, h.reg, h.wlen, h.cap⟩

/-- `PWA` is insensitive to the control registers and to charging. -/
theorem PWA.frame {st0 : State V} {N : ℕ} {v : Fin N} {ot t : ℕ} {Pr : List (Fin N)} {st st' : State V}
    (h : PWA st0 v ot t Pr st) (hwa : st'.wa = st.wa)
    (hreg : ∀ y, y ≠ "tr.c" → y ≠ "tr.f" → y ≠ "tr.x" → st'.w y = st.w y)
    (hlen : st'.wlen = st.wlen) (hcap : st'.cap = st.cap) : PWA st0 v ot t Pr st' := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun w hw => ?_, fun i hi => ?_, LL.frame h.ll (fun j _ => by
    rw [hwa]), fun i hi => ?_, ?_, ?_, fun arr i a b c d e => ?_, fun y a b c d e => ?_, ?_, ?_⟩
  · rw [hwa]; exact h.inP i
  · rw [hwa]; exact h.tid i
  · rw [hwa]; exact h.fm i
  · rw [hwa]; exact h.par w hw
  · rw [hwa]; exact h.par' i hi
  · rw [hwa]; exact h.nx i hi
  · rw [hreg _ (by decide) (by decide) (by decide)]; exact h.pv
  · rw [hreg _ (by decide) (by decide) (by decide)]; exact h.u
  · rw [hwa]; exact h.arr arr i a b c d e
  · rw [hreg y a b c]; exact h.reg y a b c d e
  · rw [hlen]; exact h.wlen
  · rw [hcap]; exact h.cap

theorem PWI.of_PWA {st0 : State V} {N : ℕ} {kpar : Fin N → Fin N} {x v : Fin N} {P : List (Fin N)}
    {ot t c0 n : ℕ} {Pr : List (Fin N)} {st : State V} (hA : PWA st0 v ot t Pr st) (hpre : Pr <+: P)
    (hctl : (n = 0 ∧ Pr = P ∧ st.w "tr.x" = 0) ∨
      (0 < n ∧ st.w "tr.x" = 1 ∧ ∃ (c : Fin N) (f : ℕ), st.w "tr.c" = c.val ∧ st.w "tr.f" = f ∧ n = f + 1 ∧
        Pr ++ kpath kpar x f c = P))
    (hcost : st.cost + 14 * n ≤ c0) : PWI st0 kpar x v P ot t c0 n Pr st :=
  ⟨hpre, hctl, hA.inP, hA.tid, hA.fm, hA.par, hA.par', hA.ll, hA.nx, hA.pv, hA.u, hA.arr, hA.reg, hA.wlen, hA.cap,
    hcost⟩

/-- The first seven statements of a path step: record `c` and advance the tail. -/
def pwRec : Stmt :=
  .seq (.wstore "tr.inP" (.var "tr.c") (.lit 1)) <|
  .seq (.wstore "tr.tid" (.var "tr.c") (.var "tr.t")) <|
  .seq (.wstore "fp.fm" (.var "tr.c") (.lit 1)) <|
  .seq (.wstore "fp.par" (.var "tr.c") (.var "tr.u")) <|
  .seq (.wstore "tr.nx" (.var "tr.pv") (.var "tr.c")) <|
  .seq (.wset "tr.pv" (.var "tr.c"))
       (.wset "tr.u" (.var "tr.c"))

/-- **Recording one path vertex** extends the processed prefix. -/
theorem pwRec_spec {st0 st : State V} {N : ℕ} {v : Fin N} {ot t : ℕ} {Pr : List (Fin N)} {c : Fin N}
    (h : PWA st0 v ot t Pr st) (hc : st.w "tr.c" = c.val) (hcPr : c ∉ Pr) (hPrnd : Pr.Nodup)
    (hot : ot ∉ Pr.map Fin.val) (hotc : ot ≠ c.val) (ht : st0.w "tr.t" = t)
    (hlens : N ≤ st0.wlen "tr.inP" ∧ N ≤ st0.wlen "tr.tid" ∧ N ≤ st0.wlen "fp.fm" ∧ N ≤ st0.wlen "fp.par" ∧
      N ≤ st0.wlen "tr.nx") (hotN : ot < st0.wlen "tr.nx") (hcap : 1 < st0.cap) :
    Runs ops pwRec st (fun st' => PWA st0 v ot t (Pr ++ [c]) st' ∧ st'.w "tr.c" = st.w "tr.c" ∧
      st'.w "tr.f" = st.w "tr.f" ∧ st'.w "tr.x" = st.w "tr.x" ∧ st'.cost = st.cost + 7) := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hlens
  have hcN : c.val < N := c.2
  have hcap' : 1 < st.cap := by rw [h.cap]; exact hcap
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap'
  have htt : st.w "tr.t" = t := by rw [h.reg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht
  have hpvlt : lastOr (Pr.map Fin.val) ot < st.wlen "tr.nx" := by
    rw [h.wlen]
    unfold lastOr
    cases hL : (Pr.map Fin.val).getLast? with
    | none => exact hotN
    | some a =>
      have : a ∈ Pr.map Fin.val := List.mem_of_getLast? hL
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp this
      simp only [Option.getD_some]
      have := w.2; omega
  apply runs_seq
  refine runs_wstore (j := c.val) (a := 1) (by simp [hc]) (by simp [hfit1]) (by rw [h.wlen]; omega) ?_
  apply runs_seq
  refine runs_wstore (j := c.val) (a := t) (by simp [hc]) (by simp [htt]) (by simp; rw [h.wlen]; omega) ?_
  apply runs_seq
  refine runs_wstore (j := c.val) (a := 1) (by simp [hc]) (by simp [hfit1]) (by simp; rw [h.wlen]; omega) ?_
  apply runs_seq
  refine runs_wstore (j := c.val) (a := (lastOr Pr v).val) (by simp [hc]) (by simp [h.u])
    (by simp; rw [h.wlen]; omega) ?_
  apply runs_seq
  refine runs_wstore (j := lastOr (Pr.map Fin.val) ot) (a := c.val) (by simp [h.pv]) (by simp [hc])
    (by simpa using hpvlt) ?_
  apply runs_seq
  refine runs_wset (a := c.val) (by simp [hc]) ?_
  refine runs_wset (a := c.val) (by simp [hc]) ?_
  have hmap : (Pr ++ [c]).map Fin.val = Pr.map Fin.val ++ [c.val] := by simp
  have hcnot : c.val ∉ Pr.map Fin.val := by
    intro hm
    obtain ⟨w, hw, hwc⟩ := List.mem_map.mp hm
    exact hcPr (Fin.ext hwc ▸ hw)
  refine ⟨⟨fun i => ?_, fun i => ?_, fun i => ?_, fun w hw => ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_,
    fun arr i a b c' d e => ?_, fun y a b c' d e => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [hmap, h.inP i]
    by_cases hic : i = c.val
    · subst hic; simp
    · simp [hic]
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [hmap, h.tid i]
    by_cases hic : i = c.val
    · subst hic; simp
    · simp [hic]
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [hmap, h.fm i]
    by_cases hic : i = c.val
    · subst hic; simp
    · simp [hic]
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [reroot_snoc]
    rcases List.mem_append.mp hw with hw' | hw'
    · have hwc : w ≠ c := fun h' => hcPr (h' ▸ hw')
      have hwc' : w.val ≠ c.val := fun h' => hwc (Fin.ext h')
      rw [if_neg hwc', Function.update_of_ne hwc]
      exact h.par w hw'
    · rw [List.mem_singleton] at hw'
      subst hw'
      simp
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [hmap] at hi
    have hic : i ≠ c.val := fun h' => hi (by rw [h']; simp)
    rw [if_neg hic]
    exact h.par' i (fun h' => hi (List.mem_append_left _ h'))
  · -- the chain
    rw [hmap, ← List.cons_append]
    refine LL.append (LL.frame h.ll (fun j hj => ?_)) LL.cons_single (List.cons_ne_nil _ _) (by simp) ?_
    · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
      have hnd : (ot :: Pr.map Fin.val).Nodup :=
        List.nodup_cons.mpr ⟨hot, hPrnd.map Fin.val_injective⟩
      have hlast := getLast_not_mem_dropLast hnd (List.cons_ne_nil _ _)
      rw [getLast_cons_eq_lastOr] at hlast
      rw [if_neg (by rintro ⟨-, rfl⟩; exact hlast hj)]
    · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and, List.head_cons]
      rw [getLast_cons_eq_lastOr]
      simp
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
    rw [hmap, ← List.cons_append, List.dropLast_concat] at hi
    have hipv : i ≠ lastOr (Pr.map Fin.val) ot := by
      intro h'
      apply hi
      rw [h', ← getLast_cons_eq_lastOr]
      exact List.getLast_mem _
    rw [if_neg (by rintro ⟨-, h'⟩; exact hipv h')]
    refine h.nx i (fun h' => hi (List.dropLast_subset _ h'))
  · simp only [State.charge_w, State.setW_w, String.reduceEq, if_false, if_true]
    rw [hmap, lastOr_snoc]
  · simp only [State.charge_w, State.setW_w, if_true]
    rw [lastOr_snoc]
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    rw [if_neg (by rintro ⟨h', -⟩; exact e h'), if_neg (by rintro ⟨h', -⟩; exact d h'),
      if_neg (by rintro ⟨h', -⟩; exact c' h'), if_neg (by rintro ⟨h', -⟩; exact b h'),
      if_neg (by rintro ⟨h', -⟩; exact a h')]
    exact h.arr arr i a b c' d e
  · simp only [State.charge_w, State.setW_w, State.storeW_w, if_neg e, if_neg d]
    exact h.reg y a b c' d e
  · simp [h.wlen]
  · simp [h.cap]
  · simp
  · simp
  · simp
  · simp

/-- Stop at the root or when out of fuel; otherwise move to the search parent. -/
def pwIte : Stmt :=
  .ite (.eq (.var "tr.c") (.var "fp.x")) (.wset "tr.x" (.lit 0))
    (.ite (.eq (.var "tr.f") (.lit 0)) (.wset "tr.x" (.lit 0))
      (.seq (.wset "tr.c" (.load "fp.kp" (.var "tr.c")))
            (.wset "tr.f" (.sub (.var "tr.f") (.lit 1)))))

/-- One path vertex. -/
def pwBody : Stmt := .seq pwRec pwIte

/-- The path walk (runs while `tr.x ≠ 0`). -/
def pwLoop : Stmt := .while (.var "tr.x") pwBody

theorem pwLoop_spec {st0 : State V} {N : ℕ} {kpar : Fin N → Fin N} {x v : Fin N} {P K : List (Fin N)}
    {ot t c0 : ℕ}
    (hPnd : P.Nodup) (hPK : ∀ w ∈ P, w ∈ K) (hot : ot ∉ P.map Fin.val)
    (hkp : ∀ w ∈ K, st0.wa "fp.kp" w.val = (kpar w).val) (hx : st0.w "fp.x" = x.val) (ht : st0.w "tr.t" = t)
    (hlens : N ≤ st0.wlen "tr.inP" ∧ N ≤ st0.wlen "tr.tid" ∧ N ≤ st0.wlen "fp.fm" ∧ N ≤ st0.wlen "fp.par" ∧
      N ≤ st0.wlen "tr.nx" ∧ N ≤ st0.wlen "fp.kp")
    (hotN : ot < st0.wlen "tr.nx") (hcap : N + 2 < st0.cap) :
    ∀ n st, (∃ Pr, PWI st0 kpar x v P ot t c0 n Pr st) →
      Runs ops pwLoop st (fun st' => PWI st0 kpar x v P ot t (c0 + 1) 0 P st') := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlens
  apply runs_while_nat
  rintro n st ⟨Pr, hI⟩
  have hA := PWA.of_PWI hI
  have hcap1 : 1 < st.cap := by rw [hI.cap]; omega
  have hcost0 := hI.cost
  refine ⟨st.w "tr.x", by simp, fun hx0 => ?_, fun hx0 => ?_⟩
  · rcases hI.ctl with ⟨rfl, -, h0⟩ | ⟨hn, hx1, c, f, hc, hf, hnf, hPr⟩
    · exact absurd h0 hx0
    have hcP : c ∈ P := by rw [← hPr, kpath_step]; split_ifs <;> simp
    have hcK := hPK c hcP
    have hPrnd : Pr.Nodup := hPnd.sublist hI.pre.sublist
    have hcPr : c ∉ Pr := by
      intro hm
      have hnd := hPnd
      rw [← hPr] at hnd
      have h1 : c ∈ kpath kpar x f c := by rw [kpath_step]; split_ifs <;> simp
      exact (List.nodup_append.mp hnd).2.2 c hm c h1 rfl
    have hotPr : ot ∉ Pr.map Fin.val := fun h => hot ((hI.pre.sublist.map Fin.val).subset h)
    have hotc : ot ≠ c.val := fun h => hot (h ▸ List.mem_map_of_mem hcP)
    have hA1 : PWA st0 v ot t Pr (st.charge 1) := hA.frame rfl (fun _ _ _ _ => rfl) rfl rfl
    apply runs_seq
    refine Runs.mono (pwRec_spec hA1 (by simpa using hc) hcPr hPrnd hotPr hotc ht ⟨l1, l2, l3, l4, l5⟩ hotN
      (by omega)) ?_
    rintro s7 ⟨hA7, h7c, h7f, h7x, h7cost⟩
    have h7c1 : s7.cost = st.cost + 8 := by rw [h7cost]; simp
    have h7c' : s7.w "tr.c" = c.val := by rw [h7c]; simpa using hc
    have h7f' : s7.w "tr.f" = f := by rw [h7f]; simpa using hf
    have h7x' : s7.w "tr.x" = 1 := by rw [h7x]; simpa using hx1
    have h7xx : s7.w "fp.x" = x.val := by
      rw [hA7.reg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx
    have hcap7 : 1 < s7.cap := by rw [hA7.cap]; omega
    have hfit0 : fit s7.cap 0 = some 0 := fit_of_lt (by omega)
    have hfit1 : fit s7.cap 1 = some 1 := fit_of_lt hcap7
    have hPr' : Pr ++ [c] <+: P := by
      rw [← hPr, kpath_step]
      split_ifs
      · exact List.prefix_refl _
      · exact ⟨kpath kpar x (f - 1) (kpar c), by simp⟩
    by_cases hcx : c = x
    · -- the root: stop
      subst hcx
      refine runs_ite_true (x := 1) (by simp [h7c', h7xx, hfit1]) one_ne_zero ?_
      refine runs_wset (a := 0) (by simp [hfit0]) ?_
      have hP : Pr ++ [c] = P := by rw [← hPr, kpath_step]; simp
      exact ⟨0, by omega, Pr ++ [c], PWI.of_PWA (hA7.frame rfl (fun y _ _ hy => by simp [hy]) rfl rfl) hPr'
        (Or.inl ⟨rfl, hP, by simp⟩) (by simp; omega)⟩
    · have hcx' : c.val ≠ x.val := fun h => hcx (Fin.ext h)
      refine runs_ite_false (by simp [h7c', h7xx, hcx', hfit0]) ?_
      by_cases hf0 : f = 0
      · -- out of fuel: stop
        subst hf0
        refine runs_ite_true (x := 1) (by simp [h7f', hfit1, hfit0]) one_ne_zero ?_
        refine runs_wset (a := 0) (by simp [hfit0]) ?_
        have hP : Pr ++ [c] = P := by rw [← hPr, kpath_step]; simp
        exact ⟨0, by omega, Pr ++ [c], PWI.of_PWA (hA7.frame rfl (fun y _ _ hy => by simp [hy]) rfl rfl) hPr'
          (Or.inl ⟨rfl, hP, by simp⟩) (by simp; omega)⟩
      · -- move to the search parent
        refine runs_ite_false (by simp [h7f', hf0, hfit0]) ?_
        have hkpc : s7.wa "fp.kp" c.val = (kpar c).val := by
          rw [hA7.arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hkp c hcK
        have hcl : c.val < s7.wlen "fp.kp" := by rw [hA7.wlen]; have := c.2; omega
        apply runs_seq
        refine runs_wset (a := (kpar c).val) (by simp [h7c', hcl, hkpc]) ?_
        refine runs_wset (a := f - 1) (by simp [h7f', hfit1]) ?_
        have hkp' : (Pr ++ [c]) ++ kpath kpar x (f - 1) (kpar c) = P := by
          rw [List.append_assoc, List.singleton_append, ← hPr, kpath_step kpar x f c]
          simp [hcx, hf0]
        exact ⟨f, by omega, Pr ++ [c], PWI.of_PWA (hA7.frame rfl (fun y hy1 hy2 _ => by simp [hy1, hy2]) rfl rfl)
          hPr' (Or.inr ⟨by omega, by simp [h7x'], kpar c, f - 1, by simp, by simp, by omega, hkp'⟩)
          (by simp; omega)⟩
  · rcases hI.ctl with ⟨rfl, hPP, h0⟩ | ⟨hn, hx1, -⟩
    · subst hPP
      have hA1 : PWA st0 v ot t Pr (st.charge 1) := hA.frame rfl (fun _ _ _ _ => rfl) rfl rfl
      exact PWI.of_PWA hA1 (List.prefix_refl _) (Or.inl ⟨rfl, rfl, by simpa using h0⟩) (by simp; omega)
    · rw [hx1] at hx0; exact absurd hx0 one_ne_zero

end Frontier.CHD.PartitionRAM
