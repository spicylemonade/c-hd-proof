import Frontier.CHD.TreeRAM3

/-!
# Frontier.CHD.TreeRAM4 — (T2, part 2) the rest pass and the path clear of `mergeTree` (owner agent-03)

**NON-GATE** (Layer B).  After the path walk, `rpLoop` appends the search vertices off the path (`K.filter (∉ path)`,
in `K`'s order) with their search parents, and `pcLoop` walks the path again to reset `tr.inP`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- `reroot` along a duplicate-free path does not depend on the base on the path. -/
theorem reroot_base {α : Type*} [DecidableEq α] :
    ∀ (P : List α) (prev : α) (f g : α → α) (w : α), w ∈ P → P.Nodup → reroot P prev f w = reroot P prev g w
  | [], _, _, _, _, hw, _ => absurd hw List.not_mem_nil
  | a :: ps, prev, f, g, w, hw, hnd => by
    simp only [reroot]
    obtain ⟨ha, hps⟩ := List.nodup_cons.mp hnd
    by_cases hwps : w ∈ ps
    · exact reroot_base ps a _ _ w hwps hps
    · have hwa : w = a := by
        rcases List.mem_cons.mp hw with h | h
        · exact h
        · exact absurd h hwps
      subst hwa
      rw [reroot_not_mem hwps, reroot_not_mem hwps]
      simp

/-! ## The rest pass -/

/-- Append `tr.w` (off the path) with parent `fp.kp[tr.w]`. -/
def rpApp : Stmt :=
  .seq (.wstore "tr.nx" (.var "tr.pv") (.var "tr.w")) <|
  .seq (.wset "tr.pv" (.var "tr.w")) <|
  .seq (.wset "tr.a" (.load "fp.kp" (.var "tr.w"))) <|
  .seq (.wstore "fp.par" (.var "tr.w") (.var "tr.a")) <|
  .seq (.wstore "tr.tid" (.var "tr.w") (.var "tr.t"))
       (.wstore "fp.fm" (.var "tr.w") (.lit 1))

/-- One search vertex: append it unless it is on the path. -/
def rpBody : Stmt :=
  .seq (.wset "tr.w" (.load "fp.K" (.var "tr.j"))) <|
  .seq (.wset "tr.a" (.load "tr.inP" (.var "tr.w"))) <|
  .seq (.ite (.eq (.var "tr.a") (.lit 0)) rpApp .skip)
       (.wset "tr.j" (.add (.var "tr.j") (.lit 1)))

def rpLoop : Stmt := .while (.lt (.var "tr.j") (.var "fp.kl")) rpBody

/-! ## The path clear -/

/-- Reset `tr.inP` at the current path vertex, then advance as `kpath`. -/
def pcBody : Stmt := .seq (.wstore "tr.inP" (.var "tr.c") (.lit 0)) pwIte

def pcLoop : Stmt := .while (.var "tr.x") pcBody

/-- The processed chain after the rest pass has scanned `K.take j`. -/
def restL {N : ℕ} (P K : List (Fin N)) (j : ℕ) : List (Fin N) := P ++ (K.take j).filter (fun w => w ∉ P)

theorem restL_succ {N : ℕ} (P K : List (Fin N)) {j : ℕ} (hj : j < K.length) :
    restL P K (j + 1) = if K[j] ∈ P then restL P K j else restL P K j ++ [K[j]] := by
  unfold restL
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.filter_append]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem restL_nodup {N : ℕ} {P K : List (Fin N)} (hP : P.Nodup) (hK : K.Nodup) (j : ℕ) :
    (restL P K j).Nodup := by
  unfold restL
  rw [List.nodup_append]
  refine ⟨hP, (hK.sublist (List.take_sublist _ _)).filter _, fun a ha b hb => ?_⟩
  rintro rfl
  simp only [List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 ha

/-- The chain facts of the rest pass for a processed list `L ⊇ P`. -/
structure CF (st0 : State V) {N : ℕ} (kpar : Fin N → Fin N) (v : Fin N) (P : List (Fin N)) (ot t : ℕ)
    (L : List (Fin N)) (st : State V) : Prop where
  inP : ∀ i, st.wa "tr.inP" i = if i ∈ P.map Fin.val then 1 else st0.wa "tr.inP" i
  tid : ∀ i, st.wa "tr.tid" i = if i ∈ L.map Fin.val then t else st0.wa "tr.tid" i
  fm : ∀ i, st.wa "fp.fm" i = if i ∈ L.map Fin.val then 1 else st0.wa "fp.fm" i
  parP : ∀ w ∈ P, st.wa "fp.par" w.val = (reroot P v id w).val
  parR : ∀ w ∈ L, w ∉ P → st.wa "fp.par" w.val = (kpar w).val
  par' : ∀ i, i ∉ L.map Fin.val → st.wa "fp.par" i = st0.wa "fp.par" i
  ll : LL st "tr.nx" (ot :: L.map Fin.val)
  nx : ∀ i, i ∉ (ot :: L.map Fin.val).dropLast → st.wa "tr.nx" i = st0.wa "tr.nx" i
  pv : st.w "tr.pv" = lastOr (L.map Fin.val) ot
  tt : st.w "tr.t" = t
  arr : ∀ arr i, arr ≠ "tr.inP" → arr ≠ "tr.tid" → arr ≠ "fp.fm" → arr ≠ "fp.par" → arr ≠ "tr.nx" →
    st.wa arr i = st0.wa arr i
  reg : ∀ y, y ∉ trRegs → st.w y = st0.w y
  wlen : st.wlen = st0.wlen
  cap : st.cap = st0.cap

theorem CF.frame {st0 : State V} {N : ℕ} {kpar : Fin N → Fin N} {v : Fin N} {P : List (Fin N)} {ot t : ℕ}
    {L : List (Fin N)} {st st' : State V} (h : CF st0 kpar v P ot t L st) (hwa : st'.wa = st.wa)
    (hreg : ∀ y, y ≠ "tr.w" → y ≠ "tr.a" → y ≠ "tr.j" → st'.w y = st.w y)
    (hlen : st'.wlen = st.wlen) (hcap : st'.cap = st.cap) : CF st0 kpar v P ot t L st' := by
  have hreg' : ∀ y, y ∉ trRegs → st'.w y = st.w y := fun y hy =>
    hreg y (fun h => hy (by simp [trRegs, h])) (fun h => hy (by simp [trRegs, h]))
      (fun h => hy (by simp [trRegs, h]))
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun w hw => ?_, fun w hw hwP => ?_, fun i hi => ?_,
    LL.frame h.ll (fun j _ => by rw [hwa]), fun i hi => ?_, ?_, ?_, fun arr i a b c d e => ?_, fun y hy => ?_, ?_, ?_⟩
  · rw [hwa]; exact h.inP i
  · rw [hwa]; exact h.tid i
  · rw [hwa]; exact h.fm i
  · rw [hwa]; exact h.parP w hw
  · rw [hwa]; exact h.parR w hw hwP
  · rw [hwa]; exact h.par' i hi
  · rw [hwa]; exact h.nx i hi
  · rw [hreg _ (by decide) (by decide) (by decide)]; exact h.pv
  · rw [hreg _ (by decide) (by decide) (by decide)]; exact h.tt
  · rw [hwa]; exact h.arr arr i a b c d e
  · rw [hreg' y hy]; exact h.reg y hy
  · rw [hlen]; exact h.wlen
  · rw [hcap]; exact h.cap

/-- **Appending one off-path vertex.** -/
theorem rpApp_spec {st0 st : State V} {N : ℕ} {kpar : Fin N → Fin N} {v : Fin N} {P K : List (Fin N)}
    {ot t : ℕ} {L : List (Fin N)} {w : Fin N}
    (h : CF st0 kpar v P ot t L st) (hw : st.w "tr.w" = w.val) (hwL : w ∉ L) (hwK : w ∈ K) (hwP : w ∉ P)
    (hLnd : L.Nodup) (hot : ot ∉ L.map Fin.val) (hotw : ot ≠ w.val)
    (hkp : ∀ w ∈ K, st0.wa "fp.kp" w.val = (kpar w).val)
    (hlens : N ≤ st0.wlen "tr.tid" ∧ N ≤ st0.wlen "fp.fm" ∧ N ≤ st0.wlen "fp.par" ∧ N ≤ st0.wlen "tr.nx" ∧
      N ≤ st0.wlen "fp.kp") (hotN : ot < st0.wlen "tr.nx") (hcap : 1 < st0.cap) :
    Runs ops rpApp st (fun st' => CF st0 kpar v P ot t (L ++ [w]) st' ∧ st'.w "tr.j" = st.w "tr.j" ∧
      st'.cost = st.cost + 6) := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hlens
  have hwN : w.val < N := w.2
  have hcap' : 1 < st.cap := by rw [h.cap]; exact hcap
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap'
  have hkpw : st.wa "fp.kp" w.val = (kpar w).val := by
    rw [h.arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hkp w hwK
  have hpvlt : lastOr (L.map Fin.val) ot < st.wlen "tr.nx" := by
    rw [h.wlen]
    unfold lastOr
    cases hL : (L.map Fin.val).getLast? with
    | none => exact hotN
    | some a =>
      have : a ∈ L.map Fin.val := List.mem_of_getLast? hL
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp this
      simp only [Option.getD_some]
      have := u.2; omega
  apply runs_seq
  refine runs_wstore (j := lastOr (L.map Fin.val) ot) (a := w.val) (by simp [h.pv]) (by simp [hw]) hpvlt ?_
  apply runs_seq
  refine runs_wset (a := w.val) (by simp [hw]) ?_
  apply runs_seq
  refine runs_wset (a := (kpar w).val) (by simp [hw, hkpw, h.wlen]; omega) ?_
  apply runs_seq
  refine runs_wstore (j := w.val) (a := (kpar w).val) (by simp [hw]) (by simp) (by simp; rw [h.wlen]; omega) ?_
  apply runs_seq
  refine runs_wstore (j := w.val) (a := t) (by simp [hw]) (by simp [h.tt]) (by simp; rw [h.wlen]; omega) ?_
  refine runs_wstore (j := w.val) (a := 1) (by simp [hw]) (by simp [hfit1]) (by simp; rw [h.wlen]; omega) ?_
  have hmap : (L ++ [w]).map Fin.val = L.map Fin.val ++ [w.val] := by simp
  have hwnot : w.val ∉ L.map Fin.val := by
    intro hm
    obtain ⟨u, hu, huw⟩ := List.mem_map.mp hm
    exact hwL (Fin.ext huw ▸ hu)
  have hnd : (ot :: L.map Fin.val).Nodup := List.nodup_cons.mpr ⟨hot, hLnd.map Fin.val_injective⟩
  have hlast := getLast_not_mem_dropLast hnd (List.cons_ne_nil _ _)
  rw [getLast_cons_eq_lastOr] at hlast
  refine ⟨⟨fun i => ?_, fun i => ?_, fun i => ?_, fun u hu => ?_, fun u hu huP => ?_, fun i hi => ?_, ?_,
    fun i hi => ?_, ?_, ?_, fun arr i a b c d e => ?_, fun y hy => ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
    exact h.inP i
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [hmap, h.tid i]
    by_cases hiw : i = w.val
    · subst hiw; simp
    · simp [hiw]
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [hmap, h.fm i]
    by_cases hiw : i = w.val
    · subst hiw; simp
    · simp [hiw]
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    have huw : u.val ≠ w.val := fun h' => hwP (Fin.ext h' ▸ hu)
    rw [if_neg huw]
    exact h.parP u hu
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rcases List.mem_append.mp hu with hu' | hu'
    · have huw : u.val ≠ w.val := fun h' => hwL (Fin.ext h' ▸ hu')
      rw [if_neg huw]
      exact h.parR u hu' huP
    · rw [List.mem_singleton] at hu'
      subst hu'
      simp
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false, true_and]
    rw [hmap] at hi
    have hiw : i ≠ w.val := fun h' => hi (by rw [h']; simp)
    rw [if_neg hiw]
    exact h.par' i (fun h' => hi (List.mem_append_left _ h'))
  · rw [hmap, ← List.cons_append]
    refine LL.append (LL.frame h.ll (fun j hj => ?_)) LL.cons_single (List.cons_ne_nil _ _) (by simp) ?_
    · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
      rw [if_neg (by rintro ⟨-, rfl⟩; exact hlast hj)]
    · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false,
        true_and, List.head_cons]
      rw [getLast_cons_eq_lastOr]
      simp
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
    rw [hmap, ← List.cons_append, List.dropLast_concat] at hi
    have hipv : i ≠ lastOr (L.map Fin.val) ot := by
      intro h'
      apply hi
      rw [h', ← getLast_cons_eq_lastOr]
      exact List.getLast_mem _
    rw [if_neg (by rintro ⟨-, h'⟩; exact hipv h')]
    exact h.nx i (fun h' => hi (List.dropLast_subset _ h'))
  · simp only [State.charge_w, State.setW_w, State.storeW_w, String.reduceEq, if_false, if_true]
    rw [hmap, lastOr_snoc]
  · simp only [State.charge_w, State.setW_w, State.storeW_w, String.reduceEq, if_false]
    exact h.tt
  · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    rw [if_neg (by rintro ⟨h', -⟩; exact c h'), if_neg (by rintro ⟨h', -⟩; exact b h'),
      if_neg (by rintro ⟨h', -⟩; exact d h'), if_neg (by rintro ⟨h', -⟩; exact e h')]
    exact h.arr arr i a b c d e
  · have hya : y ≠ "tr.a" := fun h' => hy (by simp [trRegs, h'])
    have hypv : y ≠ "tr.pv" := fun h' => hy (by simp [trRegs, h'])
    simp only [State.charge_w, State.setW_w, State.storeW_w, if_neg hya, if_neg hypv]
    exact h.reg y hy
  · simp [h.wlen]
  · simp [h.cap]
  · simp
  · simp

/-- Invariant of the rest pass with `n` search vertices left. -/
def RPJ (st0 : State V) {N : ℕ} (kpar : Fin N → Fin N) (v : Fin N) (P K : List (Fin N)) (ot t c0 : ℕ)
    (n : ℕ) (st : State V) : Prop :=
  n ≤ K.length ∧ st.w "tr.j" = K.length - n ∧ CF st0 kpar v P ot t (restL P K (K.length - n)) st ∧
    st.cost + 13 * n ≤ c0

theorem rpLoop_spec {st0 : State V} {N : ℕ} {kpar : Fin N → Fin N} {v : Fin N} {P K : List (Fin N)}
    {ot t c0 : ℕ}
    (hK : ∀ i (h : i < K.length), st0.wa "fp.K" i = (K[i]).val) (hkl : st0.w "fp.kl" = K.length)
    (hKl : K.length ≤ st0.wlen "fp.K") (hKnd : K.Nodup) (hPnd : P.Nodup)
    (hot : ot ∉ K.map Fin.val) (hPK : ∀ w ∈ P, w ∈ K) (hinP0 : ∀ w : Fin N, st0.wa "tr.inP" w.val = 0)
    (hkp : ∀ w ∈ K, st0.wa "fp.kp" w.val = (kpar w).val)
    (hlens : N ≤ st0.wlen "tr.inP" ∧ N ≤ st0.wlen "tr.tid" ∧ N ≤ st0.wlen "fp.fm" ∧ N ≤ st0.wlen "fp.par" ∧
      N ≤ st0.wlen "tr.nx" ∧ N ≤ st0.wlen "fp.kp") (hotN : ot < st0.wlen "tr.nx")
    (hcap : N + 2 < st0.cap) :
    ∀ n st, RPJ st0 kpar v P K ot t c0 n st → Runs ops rpLoop st (fun st' => RPJ st0 kpar v P K ot t (c0 + 1) 0 st') := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := hlens
  have hKN : K.length ≤ N := by simpa using hKnd.length_le_card
  apply runs_while_nat
  rintro n st ⟨hnle, hj, hC, hcost⟩
  have hcap1 : 1 < st.cap := by rw [hC.cap]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hkl' : st.w "fp.kl" = K.length := by rw [hC.reg _ (by decide)]; exact hkl
  refine ⟨if K.length - n < K.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, hj, hkl', Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst this; simp at hx
    obtain ⟨j, hjdef⟩ : ∃ j, j = K.length - n := ⟨_, rfl⟩
    rw [← hjdef] at hj hC
    have hjl : j < K.length := by omega
    obtain ⟨w, hw⟩ : ∃ w, w = K[j] := ⟨_, rfl⟩
    have hwK : w ∈ K := by rw [hw]; exact List.getElem_mem hjl
    have hKj : st.wa "fp.K" j = w.val := by
      rw [hC.arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide), hw]; exact hK j hjl
    have hjK : j < st.wlen "fp.K" := by rw [hC.wlen]; omega
    have hwN : w.val < N := w.2
    have hinPw : st.wa "tr.inP" w.val = if w ∈ P then 1 else 0 := by
      rw [hC.inP, hinP0 w]
      by_cases hwP : w ∈ P
      · rw [if_pos (List.mem_map_of_mem hwP), if_pos hwP]
      · rw [if_neg (fun h => hwP (by obtain ⟨u, hu, huw⟩ := List.mem_map.mp h; exact Fin.ext huw ▸ hu)),
          if_neg hwP]
    have hjj : K.length - (n - 1) = j + 1 := by omega
    have hsucc := restL_succ P K hjl
    rw [← hw] at hsucc
    have hrestK : ∀ u ∈ restL P K j, u ∈ K := by
      intro u hu
      unfold restL at hu
      rcases List.mem_append.mp hu with h | h
      · exact hPK u h
      · exact List.mem_of_mem_take (List.mem_filter.mp h).1
    have hotL : ot ∉ (restL P K j).map Fin.val := by
      intro h
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
      exact hot (List.mem_map_of_mem (hrestK u hu))
    have hotw : ot ≠ w.val := fun h => hot (h ▸ List.mem_map_of_mem hwK)
    have hinPl : w.val < st.wlen "tr.inP" := by rw [hC.wlen]; omega
    apply runs_seq
    refine runs_wset (a := w.val) (by simp [hj, hjK, hKj]) ?_
    apply runs_seq
    refine runs_wset (a := if w ∈ P then 1 else 0) (by simp [hinPl, hinPw]) ?_
    generalize hs2 : ((((st.charge 1).setW "tr.w" w.val).charge 1).setW "tr.a" (if w ∈ P then 1 else 0)).charge 1
      = s2
    have hC2 : CF st0 kpar v P ot t (restL P K j) s2 := hC.frame (by rw [← hs2]; rfl)
      (fun y h1 h2 h3 => by rw [← hs2]; simp [h1, h2]) (by rw [← hs2]; rfl) (by rw [← hs2]; rfl)
    have h2w : s2.w "tr.w" = w.val := by rw [← hs2]; simp
    have h2a : s2.w "tr.a" = if w ∈ P then 1 else 0 := by rw [← hs2]; simp
    have h2j : s2.w "tr.j" = j := by rw [← hs2]; simp [hj]
    have h2cost : s2.cost = st.cost + 3 := by rw [← hs2]; simp
    have h2cap : s2.cap = st.cap := by rw [← hs2]; rfl
    have hfit1' : fit s2.cap 1 = some 1 := by rw [h2cap]; exact hfit1
    have hfit0' : fit s2.cap 0 = some 0 := by rw [h2cap]; exact hfit0
    have hfitj : fit s2.cap (j + 1) = some (j + 1) := fit_of_lt (by rw [h2cap, hC.cap]; omega)
    apply runs_seq
    by_cases hwP : w ∈ P
    · refine runs_ite_false (by simp [h2a, hwP, hfit0']) ?_
      refine runs_skip ?_
      refine runs_wset (a := j + 1) (by simp [h2j, hfit1', hfitj]) ?_
      refine ⟨n - 1, by omega, by omega, by simp; omega, ?_, ?_⟩
      · rw [hjj, hsucc, if_pos hwP]
        exact hC2.frame rfl (fun y h1 h2 h3 => by simp [h3]) (by simp) (by simp)
      · simp only [State.charge_cost, State.setW_cost]; omega
    · refine runs_ite_true (x := 1) (by simp [h2a, hwP, hfit0', hfit1']) one_ne_zero ?_
      have hwL : w ∉ restL P K j := by
        intro hm
        unfold restL at hm
        rcases List.mem_append.mp hm with h | h
        · exact hwP h
        · have hmt := (List.mem_filter.mp h).1
          obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hmt
          have hi' : i < j := by simp at hi; omega
          rw [List.getElem_take, hw] at hieq
          have := (List.Nodup.getElem_inj_iff hKnd).mp hieq
          omega
      refine Runs.mono (rpApp_spec (hC2.frame (st' := s2.charge 1) rfl (fun _ _ _ _ => rfl) rfl rfl)
        (by simpa using h2w) hwL hwK hwP (restL_nodup hPnd hKnd j) hotL hotw hkp ⟨l1, l2, l3, l4, l5⟩ hotN
        (by omega)) ?_
      rintro s3 ⟨hC3, h3j, h3cost⟩
      have h3j' : s3.w "tr.j" = j := by rw [h3j]; simpa using h2j
      have hfitj3 : fit s3.cap (j + 1) = some (j + 1) := fit_of_lt (by rw [hC3.cap]; omega)
      have hfit13 : fit s3.cap 1 = some 1 := fit_of_lt (by rw [hC3.cap]; omega)
      refine runs_wset (a := j + 1) (by simp [h3j', hfit13, hfitj3]) ?_
      refine ⟨n - 1, by omega, by omega, by simp; omega, ?_, ?_⟩
      · rw [hjj, hsucc, if_neg hwP]
        exact hC3.frame rfl (fun y h1 h2 h3 => by simp [h3]) (by simp) (by simp)
      · simp only [State.charge_cost, State.setW_cost]; rw [h3cost]; simp only [State.charge_cost]; omega
  · intro hx
    have hn : n = 0 := by
      by_contra h
      have : K.length - n < K.length := by omega
      simp [this] at hx
    subst hn
    exact ⟨Nat.zero_le _, by simpa using hj, hC.frame rfl (fun _ _ _ _ => rfl) rfl rfl, by simp; omega⟩

end Frontier.CHD.PartitionRAM
