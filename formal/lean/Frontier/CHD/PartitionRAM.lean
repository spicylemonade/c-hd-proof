import Frontier.CHD.Partition
import Frontier.RAMLogic
import Frontier.RAMWP

/-!
# Frontier.CHD.PartitionRAM — Layer B for the tree partition (owner: agent-03)

**NON-GATE.** RAM fragments for DMSY26 Algorithm 5 (`Partition.run` / `pieces`) and MakePivots, plus their
refinement to the Layer-A functions of `Frontier.CHD.Partition`.

Representation. Every container (an accumulator of an unprocessed vertex, or a reported piece) is
`top :: T`. The TAIL `T` is a linked list through ONE shared next-array `pt.nx`, which is sound because tails of distinct
containers are disjoint (`Partition.Inv.tails`, a permutation of processed vertices). Tops are stored separately (a vertex
can be the top of several containers).
* accumulator of `w`: `pt.an[w] = |T|`, `pt.af[w] = head T`, `pt.al[w] = last T` (the last two only meaningful if
  `T ≠ []`);
* piece `j`: `pt.PT[j]` (top), `pt.PN[j]`, `pt.PF[j]`, `pt.PL[j]`.
Splicing `acc v` into `acc p` is `O(1)`: link `last T_p → v → head T_v`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM

variable {V : Type} {ops : VOps V}


/-! ## Linked lists through a next-array -/

/-- `LL st arr L`: the nonempty list `L` is a chain through the word array `arr`
(`arr[L[i]] = L[i+1]`). Only the non-last nodes are read. The empty list is trivially a chain. -/
def LL (st : State V) (arr : String) : List ℕ → Prop
  | [] => True
  | [_] => True
  | x :: y :: t => st.wa arr x = y ∧ LL st arr (y :: t)

theorem LL.frame {st st' : State V} {arr : String} :
    ∀ {L : List ℕ}, LL st arr L → (∀ j ∈ L.dropLast, st'.wa arr j = st.wa arr j) → LL st' arr L
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | x :: y :: t, ⟨h1, h2⟩, hfr => by
    refine ⟨by rw [hfr x (by simp)]; exact h1, LL.frame h2 (fun j hj => hfr j ?_)⟩
    simp only [List.dropLast_cons₂]
    exact List.mem_cons_of_mem _ hj

theorem LL.append {st : State V} {arr : String} :
    ∀ {L L' : List ℕ}, LL st arr L → LL st arr L' → (hL : L ≠ []) → (hL' : L' ≠ []) →
      st.wa arr (L.getLast hL) = L'.head hL' → LL st arr (L ++ L')
  | [], _, _, _, hL, _, _ => absurd rfl hL
  | [x], y :: t, _, h', _, _, hlink => by
    simp only [List.getLast_singleton, List.head_cons] at hlink
    exact ⟨hlink, h'⟩
  | x :: y :: t, L', ⟨h1, h2⟩, h', _, hL', hlink => by
    refine ⟨h1, ?_⟩
    have := LL.append h2 h' (List.cons_ne_nil y t) hL' (by
      rw [List.getLast_cons (List.cons_ne_nil y t)] at hlink; exact hlink)
    simpa using this

theorem LL.cons_single {st : State V} {arr : String} {v : ℕ} : LL st arr [v] := trivial

theorem LL.cons {st : State V} {arr : String} {v : ℕ} {T : List ℕ} (hT : LL st arr T) (hne : T ≠ [])
    (hv : st.wa arr v = T.head hne) : LL st arr (v :: T) := by
  cases T with
  | nil => exact absurd rfl hne
  | cons y t => exact ⟨hv, hT⟩


theorem LL.frame_store {st : State V} {arr : String} {L : List ℕ} (h : LL st arr L) {j a : ℕ}
    (hj : j ∉ L.dropLast) : LL (st.storeW arr j a) arr L := by
  refine LL.frame h (fun i hi => ?_)
  simp only [State.storeW]
  rw [if_neg (by rintro ⟨-, rfl⟩; exact hj hi)]

theorem LL.frame_store_ne {st : State V} {arr arr' : String} {L : List ℕ} (h : LL st arr L) (hne : arr' ≠ arr)
    (j a : ℕ) : LL (st.storeW arr' j a) arr L := by
  refine LL.frame h (fun i _ => ?_)
  simp only [State.storeW]
  rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1.symm)]

theorem LL.frame_charge {st : State V} {arr : String} {L : List ℕ} (h : LL st arr L) (k : ℕ) :
    LL (st.charge k) arr L := LL.frame h (fun _ _ => rfl)

theorem LL.frame_setW {st : State V} {arr : String} {L : List ℕ} (h : LL st arr L) (x : String) (a : ℕ) :
    LL (st.setW x a) arr L := LL.frame h (fun _ _ => rfl)

/-! ## The Algorithm-5 loop body (one absorbed vertex) -/

/-- Splice block (steps 1–8): absorb `v := fp.TV[pt.b + pt.i]` into `p := fp.par[v]`. -/
def spliceBlk : Stmt :=
  .seq (.wset "pt.v" (.load "fp.TV" (.add (.var "pt.b") (.var "pt.i")))) <|
  .seq (.wset "pt.p" (.load "fp.par" (.var "pt.v"))) <|
  .seq (.wset "pt.ap" (.load "pt.an" (.var "pt.p"))) <|
  .seq (.wset "pt.av" (.load "pt.an" (.var "pt.v"))) <|
  .seq (.ite (.eq (.var "pt.ap") (.lit 0))
          (.wstore "pt.af" (.var "pt.p") (.var "pt.v"))
          (.wstore "pt.nx" (.load "pt.al" (.var "pt.p")) (.var "pt.v"))) <|
  .seq (.ite (.eq (.var "pt.av") (.lit 0))
          (.wstore "pt.al" (.var "pt.p") (.var "pt.v"))
          (.seq (.wstore "pt.nx" (.var "pt.v") (.load "pt.af" (.var "pt.v")))
                (.wstore "pt.al" (.var "pt.p") (.load "pt.al" (.var "pt.v"))))) <|
  .seq (.wset "pt.ap" (.add (.add (.var "pt.ap") (.lit 1)) (.var "pt.av")))
       (.wstore "pt.an" (.var "pt.p") (.var "pt.ap"))


/-- Facts about the splice block's input state. -/
structure SpliceIn (st : State V) (b i v p : ℕ) (Tp Tv : List ℕ) : Prop where
  rb : st.w "pt.b" = b
  ri : st.w "pt.i" = i
  tvlen : b + i < st.wlen "fp.TV"
  tv : st.wa "fp.TV" (b + i) = v
  parlen : v < st.wlen "fp.par"
  par : st.wa "fp.par" v = p
  anlen : p < st.wlen "pt.an" ∧ v < st.wlen "pt.an"
  aflen : p < st.wlen "pt.af" ∧ v < st.wlen "pt.af"
  allen : p < st.wlen "pt.al" ∧ v < st.wlen "pt.al"
  nxlen : v < st.wlen "pt.nx" ∧ ∀ h : Tp ≠ [], Tp.getLast h < st.wlen "pt.nx"
  cap : b + i < st.cap ∧ 1 < st.cap ∧ Tp.length + 1 + Tv.length < st.cap
  anp : st.wa "pt.an" p = Tp.length
  anv : st.wa "pt.an" v = Tv.length
  afp : ∀ h : Tp ≠ [], st.wa "pt.af" p = Tp.head h
  alp : ∀ h : Tp ≠ [], st.wa "pt.al" p = Tp.getLast h
  afv : ∀ h : Tv ≠ [], st.wa "pt.af" v = Tv.head h
  alv : ∀ h : Tv ≠ [], st.wa "pt.al" v = Tv.getLast h
  LLp : LL st "pt.nx" Tp
  LLv : LL st "pt.nx" Tv
  pv : p ≠ v
  vTv : v ∉ Tv
  vTp : v ∉ Tp
  Tpnd : Tp.Nodup
  dis : ∀ h : Tp ≠ [], Tp.getLast h ∉ Tv
  lastv : ∀ h : Tp ≠ [], Tp.getLast h ≠ v

theorem spliceBlk_spec {st : State V} {b i v p : ℕ} {Tp Tv : List ℕ} (h : SpliceIn st b i v p Tp Tv) :
    Runs ops spliceBlk st (fun st' =>
      st'.w "pt.v" = v ∧ st'.w "pt.p" = p ∧ st'.w "pt.ap" = (Tp ++ v :: Tv).length ∧
      st'.wa "pt.an" p = (Tp ++ v :: Tv).length ∧
      st'.wa "pt.af" p = (Tp ++ v :: Tv).head (by simp) ∧
      st'.wa "pt.al" p = (Tp ++ v :: Tv).getLast (by simp) ∧
      LL st' "pt.nx" (Tp ++ v :: Tv) ∧
      (∀ w, w ≠ p → st'.wa "pt.an" w = st.wa "pt.an" w ∧ st'.wa "pt.af" w = st.wa "pt.af" w ∧
        st'.wa "pt.al" w = st.wa "pt.al" w) ∧
      (∀ j, j ≠ v → (∀ hTp : Tp ≠ [], j ≠ Tp.getLast hTp) → st'.wa "pt.nx" j = st.wa "pt.nx" j) ∧
      (∀ arr j, arr ≠ "pt.an" → arr ≠ "pt.af" → arr ≠ "pt.al" → arr ≠ "pt.nx" → st'.wa arr j = st.wa arr j) ∧
      st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
      (∀ x, x ≠ "pt.v" → x ≠ "pt.p" → x ≠ "pt.ap" → x ≠ "pt.av" → st'.w x = st.w x) ∧
      st'.cost ≤ st.cost + 20) := by
  obtain ⟨hb, hi, htvl, htv, hparl, hpar, ⟨hanp_l, hanv_l⟩, ⟨hafp_l, hafv_l⟩, ⟨halp_l, halv_l⟩, ⟨hnxv_l, hnxl⟩,
    ⟨hc1, hc2, hc3⟩, hanp, hanv, hafp, halp, hafv, halv, hLLp, hLLv, hpv, hvTv, hvTp, hTpnd, hdis, hlastv⟩ := h
  apply wp_sound
  have hfit1 : fit st.cap (b + i) = some (b + i) := fit_of_lt hc1
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfitone : fit st.cap 1 = some 1 := fit_of_lt hc2
  have h10 : ((1 : ℕ) = 0) = False := by decide
  by_cases hTp : Tp = []
  · subst hTp
    by_cases hTv : Tv = []
    · subst hTv
      simp only [spliceBlk, wp, evalW_load', evalW_add', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
        State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap, State.storeW_w,
        State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost, State.setW_cost, State.storeW_cost,
        hb, hi, hfit1, Option.bind_some, htvl, ite_true, htv, hparl, hpar, hanp_l, hanv_l, hanp, hanv,
        String.reduceEq, ite_false, hfit0, hfitone, List.length_nil, true_and, and_true, false_and, and_false,
        ne_eq, one_ne_zero, not_false_eq_true, true_implies, List.nil_append, List.length_singleton,
        List.head_cons, List.getLast_singleton, hafp_l, halp_l, if_true, if_false, h10, false_implies, and_true]
      refine ⟨LL.cons_single, ?_, ?_, ?_, ?_, by omega⟩
      · intro w hw; simp [hw]
      · intro j _ _; trivial
      · intro arr j h1 h2 h3 _; simp [h1, h2, h3]
      · intro x h1 h2 h3 h4; simp [h1, h2, h3, h4]
    · have hlv : (Tv.length = 0) = False := by simp [hTv]
      have hlv' : (0 = Tv.length) = False := by simp [eq_comm, hTv]
      have hafv' := hafv hTv
      have halv' := halv hTv
      have hfitL : fit st.cap (0 + 1 + Tv.length) = some (0 + 1 + Tv.length) := fit_of_lt (by simpa using hc3)
      have hfitL' : fit st.cap (0 + 1) = some (0 + 1) := fit_of_lt (by omega)
      simp only [spliceBlk, wp, evalW_load', evalW_add', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
        State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap, State.storeW_w,
        State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost, State.setW_cost, State.storeW_cost,
        hb, hi, hfit1, Option.bind_some, htvl, ite_true, htv, hparl, hpar, hanp_l, hanv_l, hanp, hanv,
        String.reduceEq, ite_false, hfit0, hfitone, List.length_nil, true_and, and_true, false_and, and_false,
        ne_eq, one_ne_zero, not_false_eq_true, true_implies, List.nil_append, List.length_cons,
        List.head_cons, hafp_l, halp_l, if_true, if_false, h10, false_implies, hlv, hlv', hnxv_l, hafv_l, halv_l,
        hafv', halv', hfitL, hfitL', Nat.zero_add, not_true_eq_false, (show (v = p) = False by simp [Ne.symm hpv])]
      refine ⟨by omega, by omega, by simp [List.getLast_cons hTv], ?_, ?_, ?_, ?_, ?_, by omega⟩
      · refine LL.cons (LL.frame hLLv (fun j hj => ?_)) hTv (by simp)
        have hjv : j ≠ v := fun h => hvTv (h ▸ List.dropLast_subset _ hj)
        simp [hjv]
      · intro w hw; simp [hw]
      · intro j hj _; simp [hj]
      · intro arr j h1 h2 h3 h4; simp [h1, h2, h3, h4]
      · intro x h1 h2 h3 h4; simp [h1, h2, h3, h4]
  · have hlp : (Tp.length = 0) = False := by simp [hTp]
    have hafp' := hafp hTp
    have halp' := halp hTp
    have hnxl' := hnxl hTp
    have hlastv' := hlastv hTp
    have hdis' := hdis hTp
    -- the last node of `Tp` is not a non-last node of `Tp` (duplicate-free)
    have hlastdrop : Tp.getLast hTp ∉ Tp.dropLast := by
      intro hm
      have := List.dropLast_append_getLast hTp
      have hnd := hTpnd
      rw [← this] at hnd
      exact (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_singleton_self _) rfl
    by_cases hTv : Tv = []
    · subst hTv
      have hfitL : fit st.cap (Tp.length + 1 + 0) = some (Tp.length + 1 + 0) := fit_of_lt (by simpa using hc3)
      have hfitL' : fit st.cap (Tp.length + 1) = some (Tp.length + 1) := fit_of_lt (by simp at hc3; omega)
      simp only [spliceBlk, wp, evalW_load', evalW_add', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
        State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap, State.storeW_w,
        State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost, State.setW_cost, State.storeW_cost,
        hb, hi, hfit1, Option.bind_some, htvl, ite_true, htv, hparl, hpar, hanp_l, hanv_l, hanp, hanv,
        String.reduceEq, ite_false, hfit0, hfitone, List.length_nil, true_and, and_true, false_and, and_false,
        ne_eq, one_ne_zero, not_false_eq_true, true_implies, List.length_append, List.length_cons,
        hafp_l, halp_l, if_true, if_false, h10, false_implies, hlp, hnxv_l, hafv_l, halv_l,
        hafp', halp', hnxl', hfitL, hfitL', Nat.add_zero, not_true_eq_false, (show (v = p) = False by simp [Ne.symm hpv])]
      refine ⟨by simp [List.head_append_of_ne_nil hTp], by simp, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · refine LL.append (LL.frame hLLp (fun j hj => ?_)) LL.cons_single hTp (List.cons_ne_nil _ _) (by simp)
        have hjl : j ≠ Tp.getLast hTp := fun h => hlastdrop (h ▸ hj)
        simp [hjl]
      · intro w hw; simp [hw]
      · intro j _ hj; simp [hj hTp]
      · intro arr j h1 h2 h3 h4; simp [h1, h3, h4]
      · intro x h1 h2 h3 h4; simp [h1, h2, h3, h4]
    · have hlv : (Tv.length = 0) = False := by simp [hTv]
      have hafv' := hafv hTv
      have halv' := halv hTv
      have hfitL : fit st.cap (Tp.length + 1 + Tv.length) = some (Tp.length + 1 + Tv.length) := fit_of_lt hc3
      have hfitL' : fit st.cap (Tp.length + 1) = some (Tp.length + 1) := fit_of_lt (by omega)
      have hvl : (v = Tp.getLast hTp) = False := by simp; exact fun h => hlastv' h.symm
      simp only [spliceBlk, wp, evalW_load', evalW_add', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
        State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap, State.storeW_w,
        State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost, State.setW_cost, State.storeW_cost,
        hb, hi, hfit1, Option.bind_some, htvl, ite_true, htv, hparl, hpar, hanp_l, hanv_l, hanp, hanv,
        String.reduceEq, ite_false, hfit0, hfitone, true_and, and_true, false_and,
        ne_eq, one_ne_zero, not_false_eq_true, true_implies, List.length_append, List.length_cons,
        hafp_l, halp_l, if_true, if_false, h10, false_implies, hlp, hlv, hnxv_l, hafv_l, halv_l,
        hafp', halp', hnxl', hafv', halv', hfitL, hfitL', not_true_eq_false,
        (show (v = p) = False by simp [Ne.symm hpv]), hvl]
      refine ⟨by omega, by omega, by simp [List.head_append_of_ne_nil hTp], ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · rw [List.getLast_append_of_right_ne_nil _ _ (List.cons_ne_nil v Tv), List.getLast_cons hTv]
      · refine LL.append (LL.frame hLLp (fun j hj => ?_)) (LL.cons (LL.frame hLLv (fun j hj => ?_)) hTv ?_)
          hTp (List.cons_ne_nil _ _) ?_
        · have hjl : j ≠ Tp.getLast hTp := fun h => hlastdrop (h ▸ hj)
          have hjv : j ≠ v := fun h => hvTp (h ▸ List.dropLast_subset _ hj)
          simp [hjl, hjv]
        · have hjl : j ≠ Tp.getLast hTp := fun h => hdis' (h ▸ List.dropLast_subset _ hj)
          have hjv : j ≠ v := fun h => hvTv (h ▸ List.dropLast_subset _ hj)
          simp [hjl, hjv]
        · simp
        · simp [hlastv']
      · intro w hw; simp [hw]
      · intro j hj hj2; simp [hj, hj2 hTp]
      · intro arr j h1 h2 h3 h4; simp [h1, h3, h4]
      · intro x h1 h2 h3 h4; simp [h1, h2, h3, h4]


/-- Report block (step 9): if the grown accumulator has at least `s` members (`s - 1 ≤ ap`), record it as
piece `np` and reset the accumulator of `p` to `[p]`. -/
def reportBlk : Stmt :=
  .ite (.lt (.var "pt.ap") (.var "pt.km1"))
    .skip
    (.seq (.wstore "pt.PT" (.var "pt.np") (.var "pt.p")) <|
     .seq (.wstore "pt.PF" (.var "pt.np") (.load "pt.af" (.var "pt.p"))) <|
     .seq (.wstore "pt.PL" (.var "pt.np") (.load "pt.al" (.var "pt.p"))) <|
     .seq (.wstore "pt.PN" (.var "pt.np") (.var "pt.ap")) <|
     .seq (.wset "pt.np" (.add (.var "pt.np") (.lit 1)))
          (.wstore "pt.an" (.var "pt.p") (.lit 0)))

/-- The Algorithm-5 loop body: splice, report, decrement the position. -/
def bodyA : Stmt := .seq spliceBlk (.seq reportBlk (.wset "pt.i" (.sub (.var "pt.i") (.lit 1))))

/-- The Algorithm-5 loop over positions `pt.i = |rest|, …, 1` of the tree segment. -/
def loopA : Stmt := .while (.lt (.lit 0) (.var "pt.i")) bodyA


/-- The report block when the accumulator is still small (`ap < km1`): nothing changes but the clock. -/
theorem reportBlk_skip {st : State V} {ap km1 : ℕ} (hap : st.w "pt.ap" = ap) (hkm1 : st.w "pt.km1" = km1)
    (hcap : 1 < st.cap) (hlt : ap < km1) :
    Runs ops reportBlk st (fun st' => st'.w = st.w ∧ st'.wa = st.wa ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
      st'.cost = st.cost + 2) := by
  apply wp_sound
  have hfitone : fit st.cap 1 = some 1 := fit_of_lt hcap
  simp [reportBlk, wp, hap, hkm1, hlt, hfitone]

/-- The report block when the accumulator is large (`km1 ≤ ap`): record piece `np` and reset `an[p]`. -/
theorem reportBlk_rep {st : State V} {p ap np km1 : ℕ} (hp : st.w "pt.p" = p) (hap : st.w "pt.ap" = ap)
    (hnp : st.w "pt.np" = np) (hkm1 : st.w "pt.km1" = km1) (hcap : np + 1 < st.cap) (hge : km1 ≤ ap)
    (hPT : np < st.wlen "pt.PT") (hPF : np < st.wlen "pt.PF") (hPL : np < st.wlen "pt.PL")
    (hPN : np < st.wlen "pt.PN") (hafl : p < st.wlen "pt.af") (hall : p < st.wlen "pt.al")
    (hanl : p < st.wlen "pt.an") :
    Runs ops reportBlk st (fun st' =>
      st'.wa "pt.PT" np = p ∧ st'.wa "pt.PF" np = st.wa "pt.af" p ∧ st'.wa "pt.PL" np = st.wa "pt.al" p ∧
      st'.wa "pt.PN" np = ap ∧ st'.w "pt.np" = np + 1 ∧ st'.wa "pt.an" p = 0 ∧
      (∀ arr j, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PL" ∨ arr = "pt.PN") → j ≠ np →
        st'.wa arr j = st.wa arr j) ∧
      (∀ j, j ≠ p → st'.wa "pt.an" j = st.wa "pt.an" j) ∧
      (∀ arr j, arr ≠ "pt.PT" → arr ≠ "pt.PF" → arr ≠ "pt.PL" → arr ≠ "pt.PN" → arr ≠ "pt.an" →
        st'.wa arr j = st.wa arr j) ∧
      (∀ x, x ≠ "pt.np" → st'.w x = st.w x) ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
      st'.cost = st.cost + 7) := by
  apply wp_sound
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfitone : fit st.cap 1 = some 1 := fit_of_lt (by omega)
  have hfitnp : fit st.cap (np + 1) = some (np + 1) := fit_of_lt hcap
  have hnlt : ¬ ap < km1 := by omega
  simp only [reportBlk, wp, evalW_load', evalW_add', evalW_var, evalW_lit', evalW_lt', State.setW_w, State.charge_w,
    State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap,
    State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost, State.setW_cost,
    State.storeW_cost, hp, hap, hnp, hkm1, hnlt, hfit0, hfitone, hfitnp, Option.bind_some, hPT, hPF, hPL,
    hPN, hafl, hall, hanl, String.reduceEq, ne_eq, not_true_eq_false, false_implies, true_implies,
    true_and, and_true, one_ne_zero, false_and, ite_false, ite_true, eq_self_iff_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro arr j harr hj
    rcases harr with rfl | rfl | rfl | rfl <;> simp [hj]
  · intro j hj; simp [hj]
  · intro arr j h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]
  · intro x hx; simp [hx]


/-! ## Representation of a Partition state -/

open Frontier.CHD.Partition

/-- RAM representation of the tail `T` of the accumulator of `w`. -/
structure AccRep (st : State V) (w : ℕ) (T : List ℕ) : Prop where
  an : st.wa "pt.an" w = T.length
  af : ∀ h : T ≠ [], st.wa "pt.af" w = T.head h
  al : ∀ h : T ≠ [], st.wa "pt.al" w = T.getLast h
  ll : LL st "pt.nx" T

/-- RAM representation of piece record `g` holding the container `G = top :: tail`. -/
structure PieceRep (st : State V) (g : ℕ) (G : List ℕ) : Prop where
  ne : G ≠ []
  top : st.wa "pt.PT" g = G.head ne
  pn : st.wa "pt.PN" g = G.tail.length
  pf : ∀ h : G.tail ≠ [], st.wa "pt.PF" g = G.tail.head h
  pl : ∀ h : G.tail ≠ [], st.wa "pt.PL" g = G.tail.getLast h
  ll : LL st "pt.nx" G.tail

/-- RAM representation of a Partition state: the accumulators of the active vertices `act` and the reported groups,
stored as records `np0, np0 + 1, …`. -/
structure Rep (st : State V) (np0 : ℕ) (act : List ℕ) (A : PState ℕ) : Prop where
  acc : ∀ w ∈ act, AccRep st w (A.acc w).tail
  np : st.w "pt.np" = np0 + A.groups.length
  grp : ∀ g (h : g < A.groups.length), PieceRep st (np0 + g) A.groups[g]

theorem AccRep.frame {st st' : State V} {w : ℕ} {T : List ℕ} (h : AccRep st w T)
    (han : st'.wa "pt.an" w = st.wa "pt.an" w) (haf : st'.wa "pt.af" w = st.wa "pt.af" w)
    (hal : st'.wa "pt.al" w = st.wa "pt.al" w) (hnx : ∀ j ∈ T.dropLast, st'.wa "pt.nx" j = st.wa "pt.nx" j) :
    AccRep st' w T :=
  ⟨han ▸ h.an, fun hT => haf ▸ h.af hT, fun hT => hal ▸ h.al hT, LL.frame h.ll hnx⟩

theorem PieceRep.frame {st st' : State V} {g : ℕ} {G : List ℕ} (h : PieceRep st g G)
    (hPT : st'.wa "pt.PT" g = st.wa "pt.PT" g) (hPN : st'.wa "pt.PN" g = st.wa "pt.PN" g)
    (hPF : st'.wa "pt.PF" g = st.wa "pt.PF" g) (hPL : st'.wa "pt.PL" g = st.wa "pt.PL" g)
    (hnx : ∀ j ∈ G.tail.dropLast, st'.wa "pt.nx" j = st.wa "pt.nx" j) : PieceRep st' g G :=
  ⟨h.ne, hPT ▸ h.top, hPN ▸ h.pn, fun hT => hPF ▸ h.pf hT, fun hT => hPL ▸ h.pl hT, LL.frame h.ll hnx⟩

/-! ## Disjointness facts from the Layer-A invariant -/

section Disj

variable {s : ℕ} {par : ℕ → ℕ} {root : ℕ} {pre post : List ℕ} {A : PState ℕ}

theorem tails_nodup (hI : Inv s par root pre post A) (hnd : pre.Nodup) :
    (((post ++ [root]).flatMap (fun w => (A.acc w).tail)) ++ A.groups.flatMap List.tail).Nodup :=
  hI.tails.nodup_iff.mpr hnd

theorem acc_tail_mem_pre (hI : Inv s par root pre post A) {w x : ℕ} (hw : w ∈ post ++ [root])
    (hx : x ∈ (A.acc w).tail) : x ∈ pre :=
  hI.tails.mem_iff.mp (List.mem_append_left _ (List.mem_flatMap.mpr ⟨w, hw, hx⟩))

theorem grp_tail_mem_pre (hI : Inv s par root pre post A) {G : List ℕ} {x : ℕ} (hG : G ∈ A.groups)
    (hx : x ∈ G.tail) : x ∈ pre :=
  hI.tails.mem_iff.mp (List.mem_append_right _ (List.mem_flatMap.mpr ⟨G, hG, hx⟩))

theorem acc_tail_nodup (hI : Inv s par root pre post A) (hnd : pre.Nodup) {w : ℕ} (hw : w ∈ post ++ [root]) :
    ((A.acc w).tail).Nodup :=
  (List.nodup_flatMap.mp (List.nodup_append.mp (tails_nodup hI hnd)).1).1 w hw

theorem acc_tail_disj (hI : Inv s par root pre post A) (hnd : pre.Nodup)
    {w w' : ℕ} (hw : w ∈ post ++ [root]) (hw' : w' ∈ post ++ [root]) (hne : w ≠ w') {x : ℕ}
    (hx : x ∈ (A.acc w).tail) : x ∉ (A.acc w').tail := by
  have hpw := (List.nodup_flatMap.mp (List.nodup_append.mp (tails_nodup hI hnd)).1).2
  haveI : Std.Symm (Function.onFun List.Disjoint (fun w => (A.acc w).tail)) :=
    ⟨fun _ _ h => List.Disjoint.symm h⟩
  exact fun hx' => hpw.forall hw hw' hne hx hx'

theorem acc_grp_disj (hI : Inv s par root pre post A) (hnd : pre.Nodup) {w x : ℕ} {G : List ℕ}
    (hw : w ∈ post ++ [root]) (hx : x ∈ (A.acc w).tail) (hG : G ∈ A.groups) : x ∉ G.tail := fun hxG =>
  (List.nodup_append.mp (tails_nodup hI hnd)).2.2 x (List.mem_flatMap.mpr ⟨w, hw, hx⟩) x
    (List.mem_flatMap.mpr ⟨G, hG, hxG⟩) rfl

end Disj

/-! ## One Algorithm-5 step: the splice preconditions from the representation -/

section StepFacts

variable {s : ℕ} {par : ℕ → ℕ} {root : ℕ}

/-- The facts about the active accumulators of `p = par v` and `v` needed by the splice block, at the moment `v` is
processed (`rest = pre ++ v :: post`). -/
theorem step_facts (hs : 2 ≤ s) {rest : List ℕ} (ht : TreeOrder par rest root) {pre post : List ℕ} {v : ℕ}
    (hrest : rest = pre ++ v :: post) {A : PState ℕ} (hI : Inv s par root pre (v :: post) A) :
    par v ∈ post ++ [root] ∧ par v ≠ v ∧ v ∉ (A.acc (par v)).tail ∧ v ∉ (A.acc v).tail ∧
    ((A.acc (par v)).tail).Nodup ∧ (∀ x ∈ (A.acc (par v)).tail, x ∉ (A.acc v).tail) ∧
    (A.acc (par v)).tail.length + 1 < s ∧ (A.acc v).tail.length + 1 < s := by
  have hnd : rest.Nodup := ht.nodup
  have hpre : pre.Nodup := by rw [hrest] at hnd; exact (List.nodup_append.mp hnd).1
  have hvpost : v ∉ post := by
    rw [hrest] at hnd; exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hvpre : v ∉ pre := by
    rw [hrest] at hnd; exact fun h => (List.nodup_append.mp hnd).2.2 v h v List.mem_cons_self rfl
  have hvroot : v ≠ root := fun h => ht.root_nmem (h ▸ by rw [hrest]; simp)
  have hpar : par v ∈ post ++ [root] := by
    rcases ht.childFirst pre post v hrest with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (h ▸ List.mem_singleton_self _)
  have hpv : par v ≠ v := by
    intro h; rw [h] at hpar
    rcases List.mem_append.mp hpar with h1 | h1
    · exact hvpost h1
    · exact hvroot (List.mem_singleton.mp h1)
  have hpact : par v ∈ (v :: post) ++ [root] := List.mem_cons_of_mem _ hpar
  have hvact : v ∈ (v :: post) ++ [root] := List.mem_cons_self
  refine ⟨hpar, hpv, fun h => hvpre (acc_tail_mem_pre hI hpact h), fun h => hvpre (acc_tail_mem_pre hI hvact h),
    acc_tail_nodup hI hpre hpact, fun x hx => acc_tail_disj hI hpre hpact hvact hpv hx, ?_, ?_⟩
  · obtain ⟨t, ht'⟩ := hI.head _ hpact
    have := hI.small _ hpact
    rw [ht'] at this ⊢; simpa using this
  · obtain ⟨t, ht'⟩ := hI.head _ hvact
    have := hI.small _ hvact
    rw [ht'] at this ⊢; simpa using this

end StepFacts

/-! ## One Algorithm-5 step on the RAM -/

theorem nx_frame_of {st st1 : State V} {v : ℕ} {Tp L : List ℕ}
    (hfr : ∀ j, j ≠ v → (∀ hTp : Tp ≠ [], j ≠ Tp.getLast hTp) → st1.wa "pt.nx" j = st.wa "pt.nx" j)
    (hv : v ∉ L) (hl : ∀ hTp : Tp ≠ [], Tp.getLast hTp ∉ L) :
    ∀ j ∈ L.dropLast, st1.wa "pt.nx" j = st.wa "pt.nx" j := by
  intro j hj
  have hjL := List.dropLast_subset _ hj
  exact hfr j (fun h => hv (h ▸ hjL)) (fun hTp h => hl hTp (h ▸ hjL))

/-- The arrays written by the partition loop. -/
def ptArrs : List String := ["pt.an", "pt.af", "pt.al", "pt.nx", "pt.PT", "pt.PF", "pt.PL", "pt.PN"]

section Body

variable {s : ℕ} {par : ℕ → ℕ} {root : ℕ}

/-- **One step.** Splice + report refine `Partition.step` on the representation. -/
theorem body_step (hs : 2 ≤ s) {rest : List ℕ} (ht : TreeOrder par rest root) {pre post : List ℕ} {v : ℕ}
    (hrest : rest = pre ++ v :: post) {A : PState ℕ} (hI : Inv s par root pre (v :: post) A)
    {st : State V} {np0 b i : ℕ} (hR : Rep st np0 ((v :: post) ++ [root]) A)
    (hb : st.w "pt.b" = b) (hi : st.w "pt.i" = i) (hk : st.w "pt.km1" = s - 1)
    (htvl : b + i < st.wlen "fp.TV") (htv : st.wa "fp.TV" (b + i) = v)
    (hparv : st.wa "fp.par" v = par v)
    (hN : ∀ x ∈ rest ++ [root], x < st.wlen "fp.par" ∧ x < st.wlen "pt.an" ∧ x < st.wlen "pt.af" ∧
      x < st.wlen "pt.al" ∧ x < st.wlen "pt.nx")
    (hP : np0 + A.groups.length < st.wlen "pt.PT" ∧ np0 + A.groups.length < st.wlen "pt.PF" ∧
      np0 + A.groups.length < st.wlen "pt.PL" ∧ np0 + A.groups.length < st.wlen "pt.PN")
    (hcap : b + i < st.cap ∧ 2 * s < st.cap ∧ np0 + A.groups.length + 1 < st.cap) :
    Runs ops (.seq spliceBlk reportBlk) st (fun st' =>
      Rep st' np0 (post ++ [root]) (step s par A v) ∧
      (∀ j, j ∉ rest ++ [root] → st'.wa "pt.nx" j = st.wa "pt.nx" j ∧ st'.wa "pt.an" j = st.wa "pt.an" j ∧
          st'.wa "pt.af" j = st.wa "pt.af" j ∧ st'.wa "pt.al" j = st.wa "pt.al" j) ∧
      (∀ arr g, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PL" ∨ arr = "pt.PN") →
          g < np0 + A.groups.length → st'.wa arr g = st.wa arr g) ∧
      (∀ arr j, arr ∉ ptArrs → st'.wa arr j = st.wa arr j) ∧
      (∀ x, x ≠ "pt.v" → x ≠ "pt.p" → x ≠ "pt.ap" → x ≠ "pt.av" → x ≠ "pt.np" → st'.w x = st.w x) ∧
      st'.wlen = st.wlen ∧ st'.cap = st.cap ∧ st'.cost ≤ st.cost + 27) := by
  obtain ⟨hpar, hpv, hvTp, hvTv, hTpnd, hdisj, hsp, hsv⟩ := step_facts hs ht hrest hI
  have hnd : rest.Nodup := ht.nodup
  have hpre : pre.Nodup := by rw [hrest] at hnd; exact (List.nodup_append.mp hnd).1
  have hvpre : v ∉ pre := by
    rw [hrest] at hnd; exact fun h => (List.nodup_append.mp hnd).2.2 v h v List.mem_cons_self rfl
  set p := par v with hp_def
  have hpact : p ∈ (v :: post) ++ [root] := List.mem_cons_of_mem _ hpar
  have hvact : v ∈ (v :: post) ++ [root] := List.mem_cons_self
  obtain ⟨tp, htp⟩ := hI.head _ hpact
  obtain ⟨tv, htv'⟩ := hI.head _ hvact
  have hTp : (A.acc p).tail = tp := by rw [htp]; rfl
  have hTv : (A.acc v).tail = tv := by rw [htv']; rfl
  have hRp := hR.acc p hpact
  have hRv := hR.acc v hvact
  rw [hTp] at hRp hvTp hTpnd hdisj hsp
  rw [hTv] at hRv hvTv hdisj hsv
  have hmem_rest : ∀ x ∈ rest ++ [root], x ∈ rest ++ [root] := fun x h => h
  have hv_in : v ∈ rest ++ [root] := by rw [hrest]; simp
  have hp_in : p ∈ rest ++ [root] := by
    rw [hrest]; rcases List.mem_append.mp hpar with h | h
    · simp [h]
    · simp at h; simp [h]
  have htp_in : ∀ x ∈ tp, x ∈ rest ++ [root] := fun x hx => by
    have := acc_tail_mem_pre hI hpact (hTp ▸ hx); rw [hrest]; simp [this]
  obtain ⟨hNv1, hNv2, hNv3, hNv4, hNv5⟩ := hN v hv_in
  obtain ⟨-, hNp2, hNp3, hNp4, -⟩ := hN p hp_in
  have hSI : SpliceIn st b i v p tp tv :=
    { rb := hb, ri := hi, tvlen := htvl, tv := htv, parlen := hNv1, par := hparv,
      anlen := ⟨hNp2, hNv2⟩, aflen := ⟨hNp3, hNv3⟩, allen := ⟨hNp4, hNv4⟩,
      nxlen := ⟨hNv5, fun h => (hN _ (htp_in _ (List.getLast_mem h))).2.2.2.2⟩,
      cap := ⟨hcap.1, by omega, by omega⟩,
      anp := hRp.an, anv := hRv.an, afp := hRp.af, alp := hRp.al, afv := hRv.af, alv := hRv.al,
      LLp := hRp.ll, LLv := hRv.ll, pv := hpv, vTv := hvTv, vTp := hvTp, Tpnd := hTpnd,
      dis := fun h => hdisj _ (List.getLast_mem h), lastv := fun h hl => hvTp (hl ▸ List.getLast_mem h) }
  apply runs_seq
  refine Runs.mono (spliceBlk_spec hSI) ?_
  rintro st1 ⟨h1v, h1p, h1ap, h1an, h1af, h1al, h1LL, h1w, h1nx, h1arr, h1len, h1cap, h1reg, h1cost⟩
  -- frames of the splice on the other containers
  have hlast_notin : ∀ w ∈ (v :: post) ++ [root], w ≠ p → ∀ hTp : tp ≠ [], tp.getLast hTp ∉ (A.acc w).tail :=
    fun w hw hwp hTp' => acc_tail_disj hI hpre hpact hw (Ne.symm hwp) (hTp ▸ List.getLast_mem hTp')
  have hv_notin : ∀ w ∈ (v :: post) ++ [root], v ∉ (A.acc w).tail := fun w hw h => hvpre (acc_tail_mem_pre hI hw h)
  have hlast_notin_g : ∀ G ∈ A.groups, ∀ hTp : tp ≠ [], tp.getLast hTp ∉ G.tail :=
    fun G hG hTp' => acc_grp_disj hI hpre hpact (hTp ▸ List.getLast_mem hTp') hG
  have hv_notin_g : ∀ G ∈ A.groups, v ∉ G.tail := fun G hG h => hvpre (grp_tail_mem_pre hI hG h)
  have hlen_acc : (A.acc p ++ A.acc v).length = (tp ++ v :: tv).length + 1 := by
    rw [htp, htv']; simp
  by_cases hrep : s ≤ (A.acc p ++ A.acc v).length
  · -- report
    have hstep : step s par A v =
        { acc := Function.update A.acc p [p], groups := A.groups ++ [A.acc p ++ A.acc v] } := by
      simp only [step, ← hp_def, hrep, ite_true]
    have hge : s - 1 ≤ (tp ++ v :: tv).length := by omega
    refine Runs.mono (reportBlk_rep (st := st1) (p := p) (ap := (tp ++ v :: tv).length)
      (np := np0 + A.groups.length) (km1 := s - 1) h1p h1ap
      (by rw [h1reg _ (by decide) (by decide) (by decide) (by decide)]; exact hR.np)
      (by rw [h1reg _ (by decide) (by decide) (by decide) (by decide)]; exact hk)
      (by rw [h1cap]; exact hcap.2.2) hge
      (by rw [h1len]; exact hP.1) (by rw [h1len]; exact hP.2.1) (by rw [h1len]; exact hP.2.2.1)
      (by rw [h1len]; exact hP.2.2.2) (by rw [h1len]; exact hNp3) (by rw [h1len]; exact hNp4)
      (by rw [h1len]; exact hNp2)) ?_
    rintro st2 ⟨h2PT, h2PF, h2PL, h2PN, h2np, h2an, h2P, h2anw, h2arr, h2reg, h2len, h2cap, h2cost⟩
    rw [hstep]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [h2len, h1len], by rw [h2cap, h1cap], by omega⟩
    · -- accumulators
      intro w hw
      by_cases hwp : w = p
      · subst hwp
        simp only [Function.update_self, List.tail_cons]
        exact ⟨by rw [h2an]; rfl, fun h => absurd rfl h, fun h => absurd rfl h, trivial⟩
      · simp only [Function.update_of_ne hwp]
        have hw' : w ∈ (v :: post) ++ [root] := List.mem_cons_of_mem _ hw
        obtain ⟨han1, haf1, hal1⟩ := h1w w hwp
        refine AccRep.frame (hR.acc w hw') ?_ ?_ ?_ ?_
        · rw [h2anw w hwp, han1]
        · rw [h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide), haf1]
        · rw [h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide), hal1]
        · intro j hj
          rw [h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact nx_frame_of h1nx (hv_notin w hw') (hlast_notin w hw' hwp) j hj
    · simp only [List.length_append, List.length_singleton]; rw [h2np]; omega
    · intro g hg
      simp only [List.length_append, List.length_singleton] at hg
      by_cases hgl : g < A.groups.length
      · rw [List.getElem_append_left hgl]
        have hG : A.groups[g] ∈ A.groups := List.getElem_mem hgl
        have hne : np0 + g ≠ np0 + A.groups.length := by omega
        refine PieceRep.frame (hR.grp g hgl) ?_ ?_ ?_ ?_ ?_
        · rw [h2P _ _ (Or.inl rfl) hne, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
        · rw [h2P _ _ (Or.inr (Or.inr (Or.inr rfl))) hne, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
        · rw [h2P _ _ (Or.inr (Or.inl rfl)) hne, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
        · rw [h2P _ _ (Or.inr (Or.inr (Or.inl rfl))) hne, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
        · intro j hj
          rw [h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact nx_frame_of h1nx (hv_notin_g _ hG) (hlast_notin_g _ hG) j hj
      · have hgeq : g = A.groups.length := by omega
        subst hgeq
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        rw [htp, htv']
        refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
        · simp [h2PT]
        · simp only [List.cons_append, List.tail_cons]; rw [h2PN]
        · intro h; simp only [List.cons_append, List.tail_cons]; rw [h2PF, h1af]
        · intro h; simp only [List.cons_append, List.tail_cons]; rw [h2PL, h1al]
        · simp only [List.cons_append, List.tail_cons]
          exact LL.frame h1LL (fun j _ => h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    · -- local frame
      intro j hj
      have hjv : j ≠ v := fun h => hj (h ▸ hv_in)
      have hjp : j ≠ p := fun h => hj (h ▸ hp_in)
      have hjl : ∀ hTp : tp ≠ [], j ≠ tp.getLast hTp := fun hTp h => hj (h ▸ htp_in _ (List.getLast_mem hTp))
      obtain ⟨han1, haf1, hal1⟩ := h1w j hjp
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide), h1nx j hjv hjl]
      · rw [h2anw j hjp, han1]
      · rw [h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide), haf1]
      · rw [h2arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide), hal1]
    · intro arr g harr hg
      have hne : g ≠ np0 + A.groups.length := by omega
      rw [h2P _ _ harr hne]
      rcases harr with rfl | rfl | rfl | rfl <;>
        exact h1arr _ _ (by decide) (by decide) (by decide) (by decide)
    · intro arr j harr
      simp only [ptArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at harr
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := harr
      rw [h2arr _ _ a5 a6 a7 a8 a1, h1arr _ _ a1 a2 a3 a4]
    · intro x x1 x2 x3 x4 x5
      rw [h2reg x x5, h1reg x x1 x2 x3 x4]
  · -- no report
    have hstep : step s par A v =
        { acc := Function.update A.acc p (A.acc p ++ A.acc v), groups := A.groups } := by
      simp only [step, ← hp_def, hrep, ite_false]
    have hlt : (tp ++ v :: tv).length < s - 1 := by omega
    refine Runs.mono (reportBlk_skip (st := st1) h1ap
      (by rw [h1reg _ (by decide) (by decide) (by decide) (by decide)]; exact hk)
      (by rw [h1cap]; omega) hlt) ?_
    rintro st2 ⟨h2w, h2wa, h2len, h2cap, h2cost⟩
    rw [hstep]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [h2len, h1len], by rw [h2cap, h1cap], by omega⟩
    · intro w hw
      by_cases hwp : w = p
      · subst hwp
        simp only [Function.update_self]
        rw [htp, htv']
        simp only [List.cons_append, List.tail_cons]
        refine ⟨by rw [h2wa, h1an], fun h => by rw [h2wa, h1af], fun h => by rw [h2wa, h1al], ?_⟩
        exact LL.frame h1LL (fun j _ => by rw [h2wa])
      · simp only [Function.update_of_ne hwp]
        have hw' : w ∈ (v :: post) ++ [root] := List.mem_cons_of_mem _ hw
        obtain ⟨han1, haf1, hal1⟩ := h1w w hwp
        refine AccRep.frame (hR.acc w hw') ?_ ?_ ?_ ?_
        · rw [h2wa, han1]
        · rw [h2wa, haf1]
        · rw [h2wa, hal1]
        · intro j hj
          rw [h2wa]
          exact nx_frame_of h1nx (hv_notin w hw') (hlast_notin w hw' hwp) j hj
    · rw [h2w, h1reg _ (by decide) (by decide) (by decide) (by decide)]; exact hR.np
    · intro g hg
      have hG : A.groups[g] ∈ A.groups := List.getElem_mem hg
      refine PieceRep.frame (hR.grp g hg) ?_ ?_ ?_ ?_ ?_
      · rw [h2wa, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
      · rw [h2wa, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
      · rw [h2wa, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
      · rw [h2wa, h1arr _ _ (by decide) (by decide) (by decide) (by decide)]
      · intro j hj
        rw [h2wa]
        exact nx_frame_of h1nx (hv_notin_g _ hG) (hlast_notin_g _ hG) j hj
    · intro j hj
      have hjv : j ≠ v := fun h => hj (h ▸ hv_in)
      have hjp : j ≠ p := fun h => hj (h ▸ hp_in)
      have hjl : ∀ hTp : tp ≠ [], j ≠ tp.getLast hTp := fun hTp h => hj (h ▸ htp_in _ (List.getLast_mem hTp))
      obtain ⟨han1, haf1, hal1⟩ := h1w j hjp
      exact ⟨by rw [h2wa, h1nx j hjv hjl], by rw [h2wa, han1], by rw [h2wa, haf1], by rw [h2wa, hal1]⟩
    · intro arr g harr _
      rw [h2wa]
      rcases harr with rfl | rfl | rfl | rfl <;>
        exact h1arr _ _ (by decide) (by decide) (by decide) (by decide)
    · intro arr j harr
      simp only [ptArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at harr
      obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := harr
      rw [h2wa, h1arr _ _ a1 a2 a3 a4]
    · intro x x1 x2 x3 x4 _
      rw [h2w, h1reg x x1 x2 x3 x4]

end Body


/-! ## The Algorithm-5 loop over one tree -/

theorem Rep.frame {st st' : State V} {np0 : ℕ} {act : List ℕ} {A : PState ℕ} (h : Rep st np0 act A)
    (hwa : st'.wa = st.wa) (hnp : st'.w "pt.np" = st.w "pt.np") : Rep st' np0 act A :=
  ⟨fun w hw => AccRep.frame (h.acc w hw) (by rw [hwa]) (by rw [hwa]) (by rw [hwa]) (fun j _ => by rw [hwa]),
    hnp ▸ h.np,
    fun g hg => PieceRep.frame (h.grp g hg) (by rw [hwa]) (by rw [hwa]) (by rw [hwa]) (by rw [hwa])
      (fun j _ => by rw [hwa])⟩

/-- The number of reported groups is at most the number of processed vertices (each group has a nonempty tail). -/
theorem groups_length_le {s : ℕ} (hs : 2 ≤ s) {par : ℕ → ℕ} {root : ℕ} {pre post : List ℕ} {A : PState ℕ}
    (hI : Inv s par root pre post A) : A.groups.length ≤ pre.length := by
  have h1 := len_mul_le_sum A.groups 1 (fun F hF => by
    have := (hI.gsize F hF).1
    rw [List.length_tail]; omega)
  have h2 : (A.groups.map (fun F => F.tail.length)).sum = (A.groups.flatMap List.tail).length := by
    rw [List.length_flatMap]
  have h3 := hI.tails.length_eq
  rw [List.length_append] at h3
  omega

/-- Registers the partition loop may write. -/
def loopRegs : List String := ["pt.v", "pt.p", "pt.ap", "pt.av", "pt.np", "pt.i"]

/-- Frame of the partition work on one tree `ord`, relative to the tree-start state `st0`. -/
structure LFrame (st0 st : State V) (np0 : ℕ) (ord : List ℕ) : Prop where
  loc : ∀ j, j ∉ ord → st.wa "pt.nx" j = st0.wa "pt.nx" j ∧ st.wa "pt.an" j = st0.wa "pt.an" j ∧
      st.wa "pt.af" j = st0.wa "pt.af" j ∧ st.wa "pt.al" j = st0.wa "pt.al" j
  old : ∀ arr g, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PL" ∨ arr = "pt.PN") → g < np0 →
      st.wa arr g = st0.wa arr g
  arr : ∀ arr j, arr ∉ ptArrs → st.wa arr j = st0.wa arr j
  reg : ∀ x, x ∉ loopRegs → st.w x = st0.w x
  wlen : st.wlen = st0.wlen
  cap : st.cap = st0.cap

theorem LFrame.refl (st : State V) (np0 : ℕ) (ord : List ℕ) : LFrame st st np0 ord :=
  ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem LFrame.trans {st0 st1 st2 : State V} {np0 : ℕ} {ord : List ℕ} (h1 : LFrame st0 st1 np0 ord)
    (h2 : LFrame st1 st2 np0 ord) : LFrame st0 st2 np0 ord where
  loc j hj := by
    obtain ⟨a1, b1, c1, d1⟩ := h1.loc j hj
    obtain ⟨a2, b2, c2, d2⟩ := h2.loc j hj
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1⟩
  old arr g ha hg := (h2.old arr g ha hg).trans (h1.old arr g ha hg)
  arr a j ha := (h2.arr a j ha).trans (h1.arr a j ha)
  reg x hx := (h2.reg x hx).trans (h1.reg x hx)
  wlen := h2.wlen.trans h1.wlen
  cap := h2.cap.trans h1.cap

theorem LFrame.charge {st0 st : State V} {np0 : ℕ} {ord : List ℕ} (h : LFrame st0 st np0 ord) (k : ℕ) :
    LFrame st0 (st.charge k) np0 ord := h.trans ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem LFrame.setW {st0 st : State V} {np0 : ℕ} {ord : List ℕ} (h : LFrame st0 st np0 ord) {x : String}
    (hx : x ∈ loopRegs) (a : ℕ) : LFrame st0 (st.setW x a) np0 ord :=
  h.trans ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun y hy => by simp only [State.setW_w]; rw [if_neg (fun (h : y = x) => hy (h ▸ hx))], rfl, rfl⟩

/-- Hypotheses on the tree-start state for the tree with parent-first order `ord` (head `root`), stored at
`fp.TV[b, b + |ord|)`, parents in `fp.par`, first piece record `np0`, piece size `s`. -/
structure TCtx (st0 : State V) (s b np0 root : ℕ) (ord : List ℕ) : Prop where
  hs : 2 ≤ s
  pf : ParentFirst (st0.wa "fp.par") root ord
  seg : ∀ j (h : j < ord.length), st0.wa "fp.TV" (b + j) = ord[j]
  tvlen : b + ord.length ≤ st0.wlen "fp.TV"
  vlen : ∀ x ∈ ord, x < st0.wlen "fp.par" ∧ x < st0.wlen "pt.an" ∧ x < st0.wlen "pt.af" ∧
    x < st0.wlen "pt.al" ∧ x < st0.wlen "pt.nx"
  plen : np0 + ord.length ≤ st0.wlen "pt.PT" ∧ np0 + ord.length ≤ st0.wlen "pt.PF" ∧
    np0 + ord.length ≤ st0.wlen "pt.PL" ∧ np0 + ord.length ≤ st0.wlen "pt.PN"
  cap : b + ord.length < st0.cap ∧ 2 * s < st0.cap ∧ np0 + ord.length + 1 < st0.cap
  rb : st0.w "pt.b" = b
  rk : st0.w "pt.km1" = s - 1

/-- The loop body as executed: splice, report, then `i := i - 1`. -/
def bodyA' : Stmt := .seq (.seq spliceBlk reportBlk) (.wset "pt.i" (.sub (.var "pt.i") (.lit 1)))

/-- The Algorithm-5 loop: positions `i = |ord| - 1, …, 1` of the tree segment. -/
def loopA' : Stmt := .while (.lt (.lit 0) (.var "pt.i")) bodyA'

/-- Loop invariant at `pt.i = i`: the first `|ord| - 1 - i` vertices of `rest = ord.tail.reverse` are processed. -/
def LI (st0 : State V) (s b np0 root : ℕ) (ord : List ℕ) (c0 : ℕ) (i : ℕ) (st : State V) : Prop :=
  i ≤ ord.length - 1 ∧ st.w "pt.i" = i ∧
  Rep st np0 (ord.tail.reverse.drop (ord.length - 1 - i) ++ [root])
    ((ord.tail.reverse.take (ord.length - 1 - i)).foldl (step s (st0.wa "fp.par")) init) ∧
  LFrame st0 st np0 ord ∧ st.cost + 30 * i ≤ c0

theorem rev_tail_getElem {ord : List ℕ} {i : ℕ} (hi0 : 0 < i) (hi : i < ord.length)
    (hn : ord.length - 1 - i < ord.tail.reverse.length) :
    ord.tail.reverse[ord.length - 1 - i] = ord[i] := by
  rw [List.getElem_reverse, List.getElem_tail]
  congr 1
  simp only [List.length_tail]
  omega

/-- **The Algorithm-5 loop** runs to completion and leaves exactly `Partition.run` represented. -/
theorem loopA_spec {st0 : State V} {s b np0 root : ℕ} {ord : List ℕ} (hC : TCtx st0 s b np0 root ord) {c0 : ℕ} :
    ∀ i st, LI st0 s b np0 root ord c0 i st → Runs ops loopA' st (fun st' =>
      Rep st' np0 [root] (run s (st0.wa "fp.par") ord.tail.reverse) ∧ LFrame st0 st' np0 ord ∧
      st'.w "pt.i" = 0 ∧ st'.cost ≤ c0 + 1) := by
  have ht := treeOrder_of_parentFirst hC.pf
  have hlen := length_ord_of_parentFirst hC.pf
  have hmem := mem_ord_iff_of_parentFirst hC.pf
  set par := st0.wa "fp.par" with hpar_def
  set rest := ord.tail.reverse with hrest_def
  apply runs_while_nat
  intro i st hLI
  obtain ⟨hile, hri, hR, hF, hcost⟩ := hLI
  have hcap1 : 1 < st.cap := by rw [hF.cap]; have := hC.cap.2.1; have := hC.hs; omega
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  refine ⟨if 0 < i then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_lit', evalW_var, hri, hfit0, Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hi0 : 0 < i := by by_contra h; simp [h] at hx
    -- the vertex processed at this iteration
    set n := ord.length - 1 - i with hn_def
    have hnlt : n < rest.length := by
      simp only [hrest_def, List.length_reverse, List.length_tail]; omega
    set v := rest[n] with hv_def
    have hdrop : rest.drop n = v :: rest.drop (n + 1) := List.drop_eq_getElem_cons hnlt
    have htake : rest.take (n + 1) = rest.take n ++ [v] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hnlt]; rfl
    have hrest : rest = rest.take n ++ v :: rest.drop (n + 1) := by
      rw [← hdrop, List.take_append_drop]
    have hIn := inv_prefix hC.hs ht n (le_of_lt hnlt)
    rw [hdrop] at hIn
    set A := (rest.take n).foldl (step s par) init with hA_def
    have hR' : Rep (st.charge 1) np0 ((v :: rest.drop (n + 1)) ++ [root]) A := by
      rw [← hdrop]; exact hR.frame rfl rfl
    have hF1 := hF.charge 1
    have hgl := groups_length_le hC.hs hIn
    rw [List.length_take, min_eq_left (le_of_lt hnlt)] at hgl
    have hilen : i < ord.length := by omega
    have hvord : v = ord[i] := by
      rw [hv_def]; exact rev_tail_getElem hi0 hilen hnlt
    have hbody := body_step (ops := ops) hC.hs ht hrest hIn (st := st.charge 1) (b := b) (i := i) hR'
      (by rw [hF1.reg _ (by decide)]; exact hC.rb) (by simpa using hri)
      (by rw [hF1.reg _ (by decide)]; exact hC.rk)
      (by rw [hF1.wlen]; have := hC.tvlen; omega)
      (by rw [hF1.arr _ _ (by decide), hC.seg i hilen, hvord])
      (by rw [hF1.arr _ _ (by decide)])
      (fun x hx => by
        have hxo : x ∈ ord := (hmem x).mpr hx
        rw [hF1.wlen]; exact hC.vlen x hxo)
      (by rw [hF1.wlen]; obtain ⟨p1, p2, p3, p4⟩ := hC.plen; omega)
      (by rw [hF1.cap]; obtain ⟨c1, c2, c3⟩ := hC.cap; omega)
    apply runs_seq
    refine Runs.mono hbody ?_
    rintro st2 ⟨hR2, hloc2, hold2, harr2, hreg2, hlen2, hcap2, hcost2⟩
    have hfit1' : fit st2.cap 1 = some 1 := fit_of_lt (by rw [hcap2]; simpa using hcap1)
    have hri2 : st2.w "pt.i" = i := by
      rw [hreg2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simpa using hri
    apply runs_wset (a := i - 1) (by simp [hri2, hfit1'])
    refine ⟨i - 1, by omega, by omega, by simp, ?_, ?_, ?_⟩
    · -- representation after the step
      have hn1 : ord.length - 1 - (i - 1) = n + 1 := by omega
      rw [hn1, htake, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine Rep.frame hR2 rfl ?_
      simp
    · -- frame
      refine (hF.charge 1).trans ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        have hj' : j ∉ rest ++ [root] := fun h => hj ((hmem j).mpr h)
        simpa using hloc2 j hj'
      · intro arr g ha hg
        simpa using hold2 arr g ha (by omega)
      · intro arr j ha; simpa using harr2 arr j ha
      · intro x hx
        simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
        simp only [State.charge_w, State.setW_w, if_neg x6]
        exact hreg2 x x1 x2 x3 x4 x5
      · simp [hlen2]
      · simp [hcap2]
    · simp only [State.charge_cost, State.setW_cost]
      have : st2.cost ≤ st.cost + 1 + 27 := by simpa using hcost2
      omega
  · intro hx
    have hi0 : i = 0 := by by_contra h; simp [Nat.pos_of_ne_zero h] at hx
    subst hi0
    have hn : ord.length - 1 - 0 = rest.length := by
      simp only [hrest_def, List.length_reverse, List.length_tail]; omega
    rw [hn, List.drop_length, List.take_length, List.nil_append] at hR
    refine ⟨hR.frame rfl rfl, hF.charge 1, by simpa using hri, ?_⟩
    simp only [State.charge_cost]; omega


/-! ## The root merge (end of one tree) -/

/-- Root merge: if no group was reported in this tree, the root's accumulator becomes a new piece; otherwise it is
merged into the last reported group (its top is replaced by the root, the root's tail is prepended). -/
def finBlk : Stmt :=
  .seq (.wset "pt.r" (.load "fp.TV" (.var "pt.b"))) <|
  .ite (.eq (.var "pt.np") (.var "pt.np0"))
    (.seq (.wstore "pt.PT" (.var "pt.np") (.var "pt.r")) <|
     .seq (.wstore "pt.PF" (.var "pt.np") (.load "pt.af" (.var "pt.r"))) <|
     .seq (.wstore "pt.PL" (.var "pt.np") (.load "pt.al" (.var "pt.r"))) <|
     .seq (.wstore "pt.PN" (.var "pt.np") (.load "pt.an" (.var "pt.r")))
          (.wset "pt.np" (.add (.var "pt.np") (.lit 1))))
    (.seq (.wset "pt.g" (.sub (.var "pt.np") (.lit 1))) <|
     .ite (.eq (.load "pt.an" (.var "pt.r")) (.lit 0))
       (.wstore "pt.PT" (.var "pt.g") (.var "pt.r"))
       (.seq (.wstore "pt.nx" (.load "pt.al" (.var "pt.r")) (.load "pt.PF" (.var "pt.g"))) <|
        .seq (.wstore "pt.PF" (.var "pt.g") (.load "pt.af" (.var "pt.r"))) <|
        .seq (.wstore "pt.PT" (.var "pt.g") (.var "pt.r"))
             (.wstore "pt.PN" (.var "pt.g") (.add (.load "pt.an" (.var "pt.r")) (.load "pt.PN" (.var "pt.g"))))))

section FinRAM

variable {st : State V} {b r np : ℕ}

theorem finBlk_none (hb : st.w "pt.b" = b) (hbl : b < st.wlen "fp.TV") (hr : st.wa "fp.TV" b = r)
    (hnp : st.w "pt.np" = np) (hnp0 : st.w "pt.np0" = np) (hcap : np + 1 < st.cap)
    (hrl : r < st.wlen "pt.an" ∧ r < st.wlen "pt.af" ∧ r < st.wlen "pt.al")
    (hPl : np < st.wlen "pt.PT" ∧ np < st.wlen "pt.PF" ∧ np < st.wlen "pt.PL" ∧ np < st.wlen "pt.PN") :
    Runs ops finBlk st (fun st' =>
      st'.wa "pt.PT" np = r ∧ st'.wa "pt.PF" np = st.wa "pt.af" r ∧ st'.wa "pt.PL" np = st.wa "pt.al" r ∧
      st'.wa "pt.PN" np = st.wa "pt.an" r ∧ st'.w "pt.np" = np + 1 ∧
      (∀ arr j, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PL" ∨ arr = "pt.PN") → j ≠ np →
        st'.wa arr j = st.wa arr j) ∧
      (∀ arr j, arr ≠ "pt.PT" → arr ≠ "pt.PF" → arr ≠ "pt.PL" → arr ≠ "pt.PN" → st'.wa arr j = st.wa arr j) ∧
      (∀ x, x ≠ "pt.r" → x ≠ "pt.np" → st'.w x = st.w x) ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
      st'.cost ≤ st.cost + 12) := by
  obtain ⟨hr1, hr2, hr3⟩ := hrl
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hPl
  apply wp_sound
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt (by omega)
  have hfitnp : fit st.cap (np + 1) = some (np + 1) := fit_of_lt hcap
  simp only [finBlk, wp, evalW_load', evalW_add', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
    State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap,
    State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost, State.setW_cost,
    State.storeW_cost, hb, hbl, hr, hnp, hnp0, ite_true, hfit1, hfitnp, Option.bind_some, hr1, hr2, hr3, hP1, hP2,
    hP3, hP4, String.reduceEq, ne_eq, one_ne_zero, not_false_eq_true, true_implies, true_and, and_true,
    false_and, ite_false, eq_self_iff_true, not_true_eq_false, false_implies]
  refine ⟨?_, ?_, ?_, by omega⟩
  · intro arr j harr hj
    rcases harr with rfl | rfl | rfl | rfl <;> simp [hj]
  · intro arr j h1 h2 h3 h4; simp [h1, h2, h3, h4]
  · intro x h1 h2; simp [h1, h2]

end FinRAM


section FinRAM2

variable {st : State V} {b r np np0 : ℕ}

/-- Root merge into the last group when the root's tail is empty: only the top changes. -/
theorem finBlk_empty (hb : st.w "pt.b" = b) (hbl : b < st.wlen "fp.TV") (hr : st.wa "fp.TV" b = r)
    (hnp : st.w "pt.np" = np) (hnp0 : st.w "pt.np0" = np0) (hne : np ≠ np0) (hcap : 1 < st.cap)
    (hrl : r < st.wlen "pt.an") (han : st.wa "pt.an" r = 0) (hPl : np - 1 < st.wlen "pt.PT") :
    Runs ops finBlk st (fun st' =>
      st'.wa "pt.PT" (np - 1) = r ∧
      (∀ j, j ≠ np - 1 → st'.wa "pt.PT" j = st.wa "pt.PT" j) ∧
      (∀ arr j, arr ≠ "pt.PT" → st'.wa arr j = st.wa arr j) ∧
      (∀ x, x ≠ "pt.r" → x ≠ "pt.g" → st'.w x = st.w x) ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
      st'.cost ≤ st.cost + 12) := by
  apply wp_sound
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap
  have hne' : (np = np0) = False := by simp [hne]
  simp only [finBlk, wp, evalW_load', evalW_add', evalW_sub', evalW_var, evalW_lit', evalW_eq', State.setW_w,
    State.charge_w, State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen,
    State.setW_cap, State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost,
    State.setW_cost, State.storeW_cost, hb, hbl, hr, hnp, hnp0, hne', ite_true, ite_false, hfit0, hfit1,
    Option.bind_some, hrl, han, hPl, String.reduceEq, ne_eq, one_ne_zero, not_false_eq_true, true_implies,
    true_and, and_true, false_and, eq_self_iff_true, not_true_eq_false, false_implies]
  refine ⟨?_, ?_, ?_, by omega⟩
  · intro j hj; simp [hj]
  · intro arr j h1; simp [h1]
  · intro x h1 h2; simp [h1, h2]

/-- Root merge into the last group when the root's tail is nonempty: link `last T_root → head(tail G)`, the new
record is `root :: (T_root ++ tail G)`. -/
theorem finBlk_merge (hb : st.w "pt.b" = b) (hbl : b < st.wlen "fp.TV") (hr : st.wa "fp.TV" b = r)
    (hnp : st.w "pt.np" = np) (hnp0 : st.w "pt.np0" = np0) (hne : np ≠ np0) (hcap : 1 < st.cap)
    (hrl : r < st.wlen "pt.an" ∧ r < st.wlen "pt.af" ∧ r < st.wlen "pt.al") (han : st.wa "pt.an" r ≠ 0)
    (hsum : st.wa "pt.an" r + st.wa "pt.PN" (np - 1) < st.cap)
    (hnxl : st.wa "pt.al" r < st.wlen "pt.nx")
    (hPl : np - 1 < st.wlen "pt.PT" ∧ np - 1 < st.wlen "pt.PF" ∧ np - 1 < st.wlen "pt.PN") :
    Runs ops finBlk st (fun st' =>
      st'.wa "pt.nx" (st.wa "pt.al" r) = st.wa "pt.PF" (np - 1) ∧
      st'.wa "pt.PF" (np - 1) = st.wa "pt.af" r ∧ st'.wa "pt.PT" (np - 1) = r ∧
      st'.wa "pt.PN" (np - 1) = st.wa "pt.an" r + st.wa "pt.PN" (np - 1) ∧
      (∀ j, j ≠ st.wa "pt.al" r → st'.wa "pt.nx" j = st.wa "pt.nx" j) ∧
      (∀ arr j, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PN") → j ≠ np - 1 → st'.wa arr j = st.wa arr j) ∧
      (∀ arr j, arr ≠ "pt.PT" → arr ≠ "pt.PF" → arr ≠ "pt.PN" → arr ≠ "pt.nx" → st'.wa arr j = st.wa arr j) ∧
      (∀ x, x ≠ "pt.r" → x ≠ "pt.g" → st'.w x = st.w x) ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
      st'.cost ≤ st.cost + 16) := by
  obtain ⟨hr1, hr2, hr3⟩ := hrl
  obtain ⟨hP1, hP2, hP4⟩ := hPl
  apply wp_sound
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap
  have hfitS : fit st.cap (st.wa "pt.an" r + st.wa "pt.PN" (np - 1)) =
      some (st.wa "pt.an" r + st.wa "pt.PN" (np - 1)) := fit_of_lt hsum
  have hne' : (np = np0) = False := by simp [hne]
  have han' : (st.wa "pt.an" r = 0) = False := by simp [han]
  simp only [finBlk, wp, evalW_load', evalW_add', evalW_sub', evalW_var, evalW_lit', evalW_eq', State.setW_w,
    State.charge_w, State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen,
    State.setW_cap, State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost,
    State.setW_cost, State.storeW_cost, hb, hbl, hr, hnp, hnp0, hne', han', ite_true, ite_false, hfit0, hfit1,
    hfitS, Option.bind_some, hr1, hr2, hr3, hP1, hP2, hP4, hnxl, String.reduceEq, ne_eq, one_ne_zero,
    not_false_eq_true, true_implies, true_and, and_true, false_and, eq_self_iff_true, not_true_eq_false,
    false_implies]
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · intro j hj; simp [hj]
  · intro arr j harr hj
    rcases harr with rfl | rfl | rfl <;> simp [hj]
  · intro arr j h1 h2 h3 h4; simp [h1, h2, h3, h4]
  · intro x h1 h2; simp [h1, h2]

end FinRAM2

/-! ## The pieces of one tree -/

/-- The list of pieces `L` is stored at records `np0, np0 + 1, …`. -/
def PiecesRep (st : State V) (np0 : ℕ) (L : List (List ℕ)) : Prop :=
  ∀ g (h : g < L.length), PieceRep st (np0 + g) L[g]

section FinStep

variable {s : ℕ} {par : ℕ → ℕ} {root : ℕ} {rest : List ℕ}

/-- Frame facts of the root merge that the forest loop needs. -/
def FinFrame (st st' : State V) (np0 : ℕ) (loc : List ℕ) : Prop :=
  (∀ j, j ∉ loc → st'.wa "pt.nx" j = st.wa "pt.nx" j) ∧
  (∀ arr g, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PL" ∨ arr = "pt.PN") → g < np0 → st'.wa arr g = st.wa arr g) ∧
  (∀ arr j, arr ∉ ["pt.nx", "pt.PT", "pt.PF", "pt.PL", "pt.PN"] → st'.wa arr j = st.wa arr j) ∧
  (∀ x, x ≠ "pt.r" → x ≠ "pt.g" → x ≠ "pt.np" → st'.w x = st.w x) ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap

/-- **Root merge** refines `Partition.pieces`: after the loop only the root's accumulator is active; the RAM
stores all pieces of the tree at records `np0, …`. -/
theorem fin_step (hs : 2 ≤ s) (ht : TreeOrder par rest root) {st : State V} {np0 b : ℕ}
    (hR : Rep st np0 [root] (run s par rest))
    (hb : st.w "pt.b" = b) (hbl : b < st.wlen "fp.TV") (hr : st.wa "fp.TV" b = root)
    (hnp0 : st.w "pt.np0" = np0)
    (hN : ∀ x ∈ rest ++ [root], x < st.wlen "pt.an" ∧ x < st.wlen "pt.af" ∧ x < st.wlen "pt.al" ∧
      x < st.wlen "pt.nx")
    (hP : np0 + rest.length + 1 ≤ st.wlen "pt.PT" ∧ np0 + rest.length + 1 ≤ st.wlen "pt.PF" ∧
      np0 + rest.length + 1 ≤ st.wlen "pt.PL" ∧ np0 + rest.length + 1 ≤ st.wlen "pt.PN")
    (hcap : np0 + rest.length + 2 < st.cap) :
    Runs ops finBlk st (fun st' =>
      PiecesRep st' np0 (pieces s par rest root) ∧
      st'.w "pt.np" = np0 + (pieces s par rest root).length ∧
      FinFrame st st' np0 (rest ++ [root]) ∧ st'.cost ≤ st.cost + 16) := by
  have hI := inv_run hs ht
  have hnd : rest.Nodup := ht.nodup
  have hract : root ∈ ([] : List ℕ) ++ [root] := by simp
  obtain ⟨T, hT⟩ := hI.head root hract
  have hRr := hR.acc root (by simp)
  rw [hT] at hRr
  simp only [List.tail_cons] at hRr
  have hTsub : ∀ x ∈ T, x ∈ rest := fun x hx => acc_tail_mem_pre hI hract (by rw [hT]; exact hx)
  have hTnd : T.Nodup := by have := acc_tail_nodup hI hnd hract; rwa [hT] at this
  have hgle := groups_length_le hs hI
  have hrN := hN root (by simp)
  have hTlen : T.length ≤ rest.length := by
    have := List.Subperm.length_le (List.subperm_of_subset hTnd (fun x hx => hTsub x hx)); exact this
  unfold pieces
  cases hlast : (run s par rest).groups.getLast? with
  | none =>
    have hg0 : (run s par rest).groups = [] := List.getLast?_eq_none_iff.mp hlast
    have hnp : st.w "pt.np" = np0 := by rw [hR.np, hg0]; simp
    refine Runs.mono (finBlk_none (r := root) hb hbl hr hnp (by rw [hnp0]) (by omega)
      ⟨hrN.1, hrN.2.1, hrN.2.2.1⟩ ⟨by omega, by omega, by omega, by omega⟩) ?_
    rintro st' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    refine ⟨?_, by rw [h5]; simp, ⟨?_, ?_, ?_, ?_, h9, h10⟩, by omega⟩
    · intro g hg
      simp only [List.length_singleton] at hg
      obtain rfl : g = 0 := by omega
      simp only [List.getElem_singleton, Nat.add_zero]
      rw [hT]
      refine ⟨List.cons_ne_nil _ _, by simp [h1], ?_, ?_, ?_, ?_⟩
      · simp only [List.tail_cons]; rw [h4, hRr.an]
      · intro hne; simp only [List.tail_cons]; rw [h2, hRr.af hne]
      · intro hne; simp only [List.tail_cons]; rw [h3, hRr.al hne]
      · simp only [List.tail_cons]
        exact LL.frame hRr.ll (fun j _ => h7 _ _ (by decide) (by decide) (by decide) (by decide))
    · intro j _; exact h7 _ _ (by decide) (by decide) (by decide) (by decide)
    · intro arr g harr hg; exact h6 arr g harr (by omega)
    · intro arr j harr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at harr
      exact h7 arr j harr.2.1 harr.2.2.1 harr.2.2.2.1 harr.2.2.2.2
    · intro x x1 x2 x3; exact h8 x x1 x3
  | some G =>
    have hGmem : G ∈ (run s par rest).groups := List.mem_of_getLast? hlast
    have hgne : (run s par rest).groups ≠ [] := fun h => by simp [h] at hlast
    have hglen : 0 < (run s par rest).groups.length := List.length_pos_of_ne_nil hgne
    set ng := (run s par rest).groups.length with hng
    have hnp : st.w "pt.np" = np0 + ng := hR.np
    have hGidx : (run s par rest).groups[ng - 1]'(by omega) = G := by
      have : (run s par rest).groups.getLast? = (run s par rest).groups[(run s par rest).groups.length - 1]? :=
        List.getLast?_eq_getElem?
      rw [hlast, List.getElem?_eq_getElem (by omega)] at this
      exact (Option.some.inj this).symm
    have hRG := hR.grp (ng - 1) (by omega)
    rw [hGidx] at hRG
    have hGsz := (hI.gsize G hGmem).1
    obtain ⟨g0, GT, hGeq⟩ : ∃ g0 GT, G = g0 :: GT := by
      cases G with
      | nil => exact absurd rfl (hI.gne _ hGmem)
      | cons a t => exact ⟨a, t, rfl⟩
    subst hGeq
    have hGT : GT ≠ [] := by
      intro h; rw [h] at hGsz; simp at hGsz; omega
    have hidx : np0 + (ng - 1) = np0 + ng - 1 := by omega
    have hdl : (run s par rest).groups.dropLast.length = ng - 1 := by rw [List.length_dropLast]
    have hTdisj : ∀ x ∈ T, ∀ G' ∈ (run s par rest).groups, x ∉ G'.tail := fun x hx G' hG' =>
      acc_grp_disj hI hnd hract (by rw [hT]; exact hx) hG'
    -- the other records
    have hold : ∀ st' : State V, (∀ j, j ∉ T → st'.wa "pt.nx" j = st.wa "pt.nx" j) →
        (∀ arr j, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PL" ∨ arr = "pt.PN") → j ≠ np0 + ng - 1 →
          st'.wa arr j = st.wa arr j) →
        ∀ g (hg : g < ng - 1), PieceRep st' (np0 + g) ((run s par rest).groups[g]'(by omega)) := by
      intro st' hnx hPT g hg
      have hG' : (run s par rest).groups[g]'(by omega) ∈ (run s par rest).groups := List.getElem_mem _
      refine PieceRep.frame (hR.grp g (by omega)) (hPT _ _ (Or.inl rfl) (by omega))
        (hPT _ _ (Or.inr (Or.inr (Or.inr rfl))) (by omega)) (hPT _ _ (Or.inr (Or.inl rfl)) (by omega))
        (hPT _ _ (Or.inr (Or.inr (Or.inl rfl))) (by omega)) ?_
      intro j hj
      exact hnx j (fun hjT => hTdisj j hjT _ hG' (List.dropLast_subset _ hj))
    by_cases hT0 : T = []
    · -- empty root tail: only the top of the last record changes
      subst hT0
      refine Runs.mono (finBlk_empty (r := root) (np := np0 + ng) (np0 := np0) hb hbl hr hnp hnp0 (by omega)
        (by omega) hrN.1 (by rw [hRr.an]; rfl) (by omega)) ?_
      rintro st' ⟨h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, h5, h6⟩, by omega⟩
      · intro g hg
        simp only [List.length_append, List.length_singleton, hdl] at hg
        by_cases hgl : g < ng - 1
        · rw [List.getElem_append_left (by rw [hdl]; exact hgl), List.getElem_dropLast]
          exact hold st' (fun j _ => h3 _ _ (by decide))
            (fun arr j harr hj => by
              rcases harr with rfl | rfl | rfl | rfl
              · exact h2 j hj
              all_goals exact h3 _ _ (by decide)) g hgl
        · have hgeq : g = ng - 1 := by omega
          subst hgeq
          rw [List.getElem_append_right (by rw [hdl])]
          simp only [hdl, Nat.sub_self, List.getElem_cons_zero, hT, List.singleton_append]
          simp only [List.tail_cons] at hRG ⊢
          refine ⟨List.cons_ne_nil _ _, by simp [hidx, h1], ?_, ?_, ?_, ?_⟩
          · rw [h3 _ _ (by decide)]; exact hRG.pn
          · intro hne; rw [h3 _ _ (by decide)]; exact hRG.pf hne
          · intro hne; rw [h3 _ _ (by decide)]; exact hRG.pl hne
          · exact LL.frame hRG.ll (fun j _ => h3 _ _ (by decide))
      · rw [h4 _ (by decide) (by decide)]; simp [hnp, hdl]; omega
      · intro j _; exact h3 _ _ (by decide)
      · intro arr g harr hg
        rcases harr with rfl | rfl | rfl | rfl
        · exact h2 g (by omega)
        all_goals exact h3 _ _ (by decide)
      · intro arr j harr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at harr
        exact h3 arr j harr.2.1
      · intro x x1 x2 _; exact h4 x x1 x2
    · -- nonempty root tail: splice it in front of the last record's tail
      have hlastT := List.getLast_mem hT0
      have hlT := hTsub _ hlastT
      have hlN := hN _ (List.mem_append_left _ hlT)
      refine Runs.mono (finBlk_merge (r := root) (np := np0 + ng) (np0 := np0) hb hbl hr hnp hnp0 (by omega)
        (by omega) ⟨hrN.1, hrN.2.1, hrN.2.2.1⟩ (by rw [hRr.an]; exact fun h => hT0 (List.length_eq_zero_iff.mp h))
        ?_ (by rw [hRr.al hT0]; exact hlN.2.2.2) ⟨by omega, by omega, by omega⟩) ?_
      · rw [hRr.an, ← hidx, hRG.pn]
        simp only [List.tail_cons]
        have : GT.length ≤ rest.length := by
          have hGTsub : ∀ x ∈ GT, x ∈ rest := fun x hx =>
            grp_tail_mem_pre hI hGmem (by simpa using hx)
          have hGTnd : GT.Nodup := by
            have hnd' := tails_nodup hI hnd
            have hsub : GT.Sublist ((run s par rest).groups.flatMap List.tail) := by
              have := sublist_flatMap_of_mem' List.tail hGmem
              simpa using this
            exact (hsub.nodup (List.nodup_append.mp hnd').2.1)
          exact List.Subperm.length_le (List.subperm_of_subset hGTnd hGTsub)
        have hdisjT : T.length + GT.length ≤ rest.length := by
          have hnd' := tails_nodup hI hnd
          have h1 : (T ++ GT).Nodup := by
            refine List.nodup_append.mpr ⟨hTnd, ?_, ?_⟩
            · have hsub : GT.Sublist ((run s par rest).groups.flatMap List.tail) := by
                have := sublist_flatMap_of_mem' List.tail hGmem
                simpa using this
              exact (hsub.nodup (List.nodup_append.mp hnd').2.1)
            · intro a ha b hb hab
              subst hab
              exact hTdisj a ha _ hGmem (by simpa using hb)
          have h2 : ∀ x ∈ T ++ GT, x ∈ rest := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hTsub x hx
            · exact grp_tail_mem_pre hI hGmem (by simpa using hx)
          have := List.Subperm.length_le (List.subperm_of_subset h1 h2)
          simpa using this
        omega
      rintro st' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      rw [hRr.al hT0] at h1 h5
      rw [← hidx, hRG.pf (by simpa using hGT)] at h1
      simp only [List.tail_cons] at h1
      refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, h9, h10⟩, by omega⟩
      · intro g hg
        simp only [List.length_append, List.length_singleton, hdl] at hg
        by_cases hgl : g < ng - 1
        · rw [List.getElem_append_left (by rw [hdl]; exact hgl), List.getElem_dropLast]
          exact hold st' (fun j hj => h5 j (fun h => hj (h ▸ List.getLast_mem hT0)))
            (fun arr j harr hj => by
              rcases harr with rfl | rfl | rfl | rfl
              · exact h6 _ _ (Or.inl rfl) hj
              · exact h6 _ _ (Or.inr (Or.inl rfl)) hj
              · exact h7 _ _ (by decide) (by decide) (by decide) (by decide)
              · exact h6 _ _ (Or.inr (Or.inr rfl)) hj) g hgl
        · have hgeq : g = ng - 1 := by omega
          subst hgeq
          rw [List.getElem_append_right (by rw [hdl])]
          simp only [hdl, Nat.sub_self, List.getElem_cons_zero, hT, List.cons_append]
          simp only [List.tail_cons] at hRG ⊢
          have hTGT : T ++ GT ≠ [] := by simp [hT0]
          refine ⟨List.cons_ne_nil _ _, by simp [hidx, h3], ?_, ?_, ?_, ?_⟩
          · rw [hidx, h4, hRr.an, ← hidx, hRG.pn]; simp
          · intro _; rw [hidx, h2, hRr.af hT0]; simp [List.head_append_of_ne_nil hT0]
          · intro _
            rw [h7 _ _ (by decide) (by decide) (by decide) (by decide), hRG.pl hGT]
            simp [List.getLast_append_of_right_ne_nil _ _ hGT]
          · show LL st' "pt.nx" (T ++ GT)
            refine LL.append (LL.frame hRr.ll (fun j hj => h5 j ?_)) (LL.frame hRG.ll (fun j hj => h5 j ?_))
              hT0 hGT ?_
            · intro h; rw [h] at hj
              have := List.dropLast_append_getLast hT0
              have hnd2 := hTnd; rw [← this] at hnd2
              exact (List.nodup_append.mp hnd2).2.2 _ hj _ (List.mem_singleton_self _) rfl
            · intro h
              exact hTdisj _ (List.getLast_mem hT0) _ hGmem (by simp only [List.tail_cons]; exact h ▸ List.dropLast_subset _ hj)
            · exact h1
      · rw [h8 _ (by decide) (by decide)]; simp [hnp, hdl]; omega
      · intro j hj
        exact h5 j (fun h => hj (List.mem_append_left _ (h ▸ hlT)))
      · intro arr g harr hg
        rcases harr with rfl | rfl | rfl | rfl
        · exact h6 _ _ (Or.inl rfl) (by omega)
        · exact h6 _ _ (Or.inr (Or.inl rfl)) (by omega)
        · exact h7 _ _ (by decide) (by decide) (by decide) (by decide)
        · exact h6 _ _ (Or.inr (Or.inr rfl)) (by omega)
      · intro arr j harr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at harr
        exact h7 arr j harr.2.1 harr.2.2.1 harr.2.2.2.2 harr.1
      · intro x x1 x2 _; exact h8 x x1 x2

end FinStep

end Frontier.CHD.PartitionRAM
