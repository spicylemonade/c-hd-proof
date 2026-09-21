import Frontier.CHD.PartitionRAM3

/-!
# Frontier.CHD.TreeRAM — the FindPivots-HD forest at RAM level: representation and `newTree` (B-L2 T1; owner agent-03)

**NON-GATE** (Layer B).  During an invocation the forest is kept as linked chains:
* per vertex `v`: `fp.fm[v]` (tree-vertex bitmap), `tr.tid[v]` (tree index), `tr.nx[v]` (next vertex of its tree's
  parent-first order), `fp.par[v]` (parent, for non-roots);
* per tree `t`: `tr.hd[t]`, `tr.tl[t]`, `tr.ln[t]` (head, tail, length of its order); register `tr.nt` (#trees);
* `tr.inP`: a temporary bitmap (path membership in `mergeTree`), all-zero between operations.
`ForestRep st N trees` states this for Layer-A trees over `Fin N` (agent-05's `TreeRec`, `growForest`).

(T1) `newTree`: appends the tree `⟨x, K, kpar⟩` of a successful search (`K` stored at `fp.K[0, fp.kl)`, `kpar` at
`fp.kp`), in `O(|K|)`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- The RAM representation of the forest of an invocation. -/
structure ForestRep (st : State V) (N : ℕ) (trees : List (TreeRec (Fin N))) : Prop where
  nt : st.w "tr.nt" = trees.length
  ne : ∀ t (ht : t < trees.length), trees[t].ord ≠ []
  root : ∀ t (ht : t < trees.length), trees[t].ord.head? = some trees[t].root
  hd : ∀ t (ht : t < trees.length), trees[t].ord.head?.map Fin.val = some (st.wa "tr.hd" t)
  tl : ∀ t (ht : t < trees.length), trees[t].ord.getLast?.map Fin.val = some (st.wa "tr.tl" t)
  ln : ∀ t (ht : t < trees.length), st.wa "tr.ln" t = trees[t].ord.length
  ll : ∀ t (ht : t < trees.length), LL st "tr.nx" (trees[t].ord.map Fin.val)
  tid : ∀ t (ht : t < trees.length), ∀ v ∈ trees[t].ord, st.wa "tr.tid" v.val = t
  par : ∀ t (ht : t < trees.length), ∀ v ∈ trees[t].ord.tail, st.wa "fp.par" v.val = (trees[t].par v).val
  fm : ∀ v : Fin N, st.wa "fp.fm" v.val = if ∃ T ∈ trees, v ∈ T.ord then 1 else 0
  inP : ∀ v : Fin N, st.wa "tr.inP" v.val = 0
  disj : trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord)
  nodup : ∀ T ∈ trees, T.ord.Nodup
  lens : N ≤ st.wlen "fp.fm" ∧ N ≤ st.wlen "tr.tid" ∧ N ≤ st.wlen "tr.nx" ∧ N ≤ st.wlen "fp.par" ∧
    N ≤ st.wlen "tr.inP" ∧ N ≤ st.wlen "tr.hd" ∧ N ≤ st.wlen "tr.tl" ∧ N ≤ st.wlen "tr.ln"

/-- Registers written by the tree layer. -/
def trRegs : List String := ["tr.t", "tr.w", "tr.a", "tr.pv", "tr.j", "tr.nt", "tr.c", "tr.f", "tr.u", "tr.x"]

/-- Arrays written by the tree layer. -/
def trArrs : List String := ["fp.fm", "tr.tid", "tr.nx", "fp.par", "tr.inP", "tr.hd", "tr.tl", "tr.ln"]

/-! ## (T1) newTree -/

/-- Mark `tr.w` as a member of tree `tr.t` with parent `fp.kp[tr.w]`. -/
def markBlk : Stmt :=
  .seq (.wstore "fp.fm" (.var "tr.w") (.lit 1)) <|
  .seq (.wstore "tr.tid" (.var "tr.w") (.var "tr.t")) <|
  .seq (.wset "tr.a" (.load "fp.kp" (.var "tr.w")))
       (.wstore "fp.par" (.var "tr.w") (.var "tr.a"))

/-- One later member of the new tree: mark it and link it after `tr.pv`. -/
def ntBody : Stmt :=
  .seq (.wset "tr.w" (.load "fp.K" (.var "tr.j"))) <|
  .seq markBlk <|
  .seq (.wstore "tr.nx" (.var "tr.pv") (.var "tr.w")) <|
  .seq (.wset "tr.pv" (.var "tr.w"))
       (.wset "tr.j" (.add (.var "tr.j") (.lit 1)))

def ntLoop : Stmt := .while (.lt (.var "tr.j") (.var "fp.kl")) ntBody

/-- (T1) Append the tree of a successful search. -/
def newTree : Stmt :=
  .seq (.wset "tr.t" (.var "tr.nt")) <|
  .seq (.wset "tr.w" (.load "fp.K" (.lit 0))) <|
  .seq markBlk <|
  .seq (.wstore "tr.hd" (.var "tr.t") (.var "tr.w")) <|
  .seq (.wset "tr.pv" (.var "tr.w")) <|
  .seq (.wset "tr.j" (.lit 1)) <|
  .seq ntLoop <|
  .seq (.wstore "tr.tl" (.var "tr.t") (.var "tr.pv")) <|
  .seq (.wstore "tr.ln" (.var "tr.t") (.var "fp.kl"))
       (.wset "tr.nt" (.add (.var "tr.t") (.lit 1)))

/-- The effect of `markBlk` at vertex `w` of tree `t` with parent word `a`. -/
structure MarkPost (st st' : State V) (w t a : ℕ) : Prop where
  wa : ∀ arr j, st'.wa arr j =
    if arr = "fp.fm" ∧ j = w then 1 else if arr = "tr.tid" ∧ j = w then t else
      if arr = "fp.par" ∧ j = w then a else st.wa arr j
  w : ∀ y, st'.w y = if y = "tr.a" then a else st.w y
  wlen : st'.wlen = st.wlen
  cap : st'.cap = st.cap
  cost : st'.cost = st.cost + 4

theorem markBlk_spec {st : State V} {w t a : ℕ} (hw : st.w "tr.w" = w) (ht : st.w "tr.t" = t)
    (hkp : st.wa "fp.kp" w = a)
    (hl : w < st.wlen "fp.fm" ∧ w < st.wlen "tr.tid" ∧ w < st.wlen "fp.kp" ∧ w < st.wlen "fp.par")
    (hcap : 1 < st.cap) :
    Runs ops markBlk st (fun st' => MarkPost st st' w t a) := by
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap
  obtain ⟨h1, h2, h3, h4⟩ := hl
  apply runs_seq
  refine runs_wstore (j := w) (a := 1) (by simp [hw]) (by simp [hfit1]) h1 ?_
  apply runs_seq
  refine runs_wstore (j := w) (a := t) (by simp [hw]) (by simp [ht]) (by simpa using h2) ?_
  apply runs_seq
  refine runs_wset (a := a) (by simp [hw, h3, hkp]) ?_
  refine runs_wstore (j := w) (a := a) (by simp [hw]) (by simp) (by simpa using h4) ?_
  refine ⟨fun arr j => ?_, fun y => ?_, by simp, by simp, by simp⟩
  · simp only [State.charge_wa, State.storeW_wa, State.setW_wa]
    by_cases h1 : arr = "fp.par" ∧ j = w
    · obtain ⟨rfl, rfl⟩ := h1; simp
    · rw [if_neg h1]
      by_cases h2 : arr = "tr.tid" ∧ j = w
      · obtain ⟨rfl, rfl⟩ := h2; simp
      · rw [if_neg h2]
        by_cases h3 : arr = "fp.fm" ∧ j = w
        · obtain ⟨rfl, rfl⟩ := h3; simp
        · rw [if_neg h3]
          simp only [if_neg h1, if_neg h2, if_neg h3]
  · simp only [State.charge_w, State.storeW_w, State.setW_w]

theorem getLast_not_mem_dropLast {α : Type*} {L : List α} (hnd : L.Nodup) (h : L ≠ []) :
    L.getLast h ∉ L.dropLast := by
  intro hmem
  have e := List.dropLast_concat_getLast h
  rw [← e] at hnd
  obtain ⟨-, -, hd⟩ := List.nodup_append.mp hnd
  exact hd _ hmem _ (List.mem_singleton_self _) rfl

/-- Invariant of the new-tree loop after the first `|K| - n` members. -/
structure NTI (st0 : State V) {N : ℕ} (K : List (Fin N)) (t c0 n : ℕ) (st : State V) : Prop where
  n_lt : n < K.length
  j : st.w "tr.j" = K.length - n
  tt : st.w "tr.t" = t
  pv : ∀ h : K.length - n - 1 < K.length, st.w "tr.pv" = (K[K.length - n - 1]'h).val
  fm : ∀ i, st.wa "fp.fm" i = if i ∈ (K.take (K.length - n)).map Fin.val then 1 else st0.wa "fp.fm" i
  tid : ∀ i, st.wa "tr.tid" i = if i ∈ (K.take (K.length - n)).map Fin.val then t else st0.wa "tr.tid" i
  par : ∀ i, st.wa "fp.par" i =
    if i ∈ (K.take (K.length - n)).map Fin.val then st0.wa "fp.kp" i else st0.wa "fp.par" i
  ll : LL st "tr.nx" ((K.take (K.length - n)).map Fin.val)
  nx : ∀ i, i ∉ ((K.take (K.length - n)).map Fin.val).dropLast → st.wa "tr.nx" i = st0.wa "tr.nx" i
  hd : ∀ h : 0 < K.length, st.wa "tr.hd" t = (K[0]'h).val
  hd' : ∀ i, i ≠ t → st.wa "tr.hd" i = st0.wa "tr.hd" i
  arr : ∀ arr i, arr ≠ "fp.fm" → arr ≠ "tr.tid" → arr ≠ "fp.par" → arr ≠ "tr.nx" → arr ≠ "tr.hd" →
    st.wa arr i = st0.wa arr i
  reg : ∀ y, y ∉ trRegs → st.w y = st0.w y
  wlen : st.wlen = st0.wlen
  cap : st.cap = st0.cap
  cost : st.cost + 9 * n ≤ c0

theorem take_succ_map {N : ℕ} (K : List (Fin N)) {j : ℕ} (hj : j < K.length) :
    (K.take (j + 1)).map Fin.val = (K.take j).map Fin.val ++ [(K[j]).val] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append]
  rfl

theorem ntLoop_spec {st0 : State V} {N : ℕ} {K : List (Fin N)} {t c0 : ℕ}
    (hK : ∀ i (h : i < K.length), st0.wa "fp.K" i = (K[i]).val) (hkl : st0.w "fp.kl" = K.length)
    (hKl : K.length ≤ st0.wlen "fp.K") (hKnd : K.Nodup)
    (hlens : N ≤ st0.wlen "fp.fm" ∧ N ≤ st0.wlen "tr.tid" ∧ N ≤ st0.wlen "fp.kp" ∧ N ≤ st0.wlen "fp.par" ∧
      N ≤ st0.wlen "tr.nx")
    (hcap : K.length + 2 < st0.cap) :
    ∀ n st, NTI st0 K t c0 n st → Runs ops ntLoop st (fun st' => NTI st0 K t (c0 + 1) 0 st') := by
  apply runs_while_nat
  intro n st hI
  obtain ⟨hnlt, hIj, hItt, hIpv, hIfm, hItid, hIpar, hIll, hInx, hIhd, hIhd', hIarr, hIreg, hIwlen, hIcap,
    hIcost⟩ := hI
  have hcap1 : 1 < st.cap := by rw [hIcap]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hkl' : st.w "fp.kl" = K.length := by rw [hIreg _ (by decide)]; exact hkl
  refine ⟨if K.length - n < K.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, hIj, hkl', Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst this; simp at hx
    obtain ⟨j, hj⟩ : ∃ j, j = K.length - n := ⟨_, rfl⟩
    rw [← hj] at hIj hIpv hIfm hItid hIpar hIll hInx
    have hjl : j < K.length := by omega
    have hj1 : 1 ≤ j := by omega
    have hjj : K.length - (n - 1) = j + 1 := by omega
    obtain ⟨w, hw⟩ : ∃ w, w = K[j] := ⟨_, rfl⟩
    have hwK : st.wa "fp.K" j = w.val := by
      rw [hIarr _ _ (by decide) (by decide) (by decide) (by decide) (by decide), hw]; exact hK j hjl
    have hjK : j < st.wlen "fp.K" := by rw [hIwlen]; omega
    have hwN : w.val < N := w.2
    have hwl : w.val < st.wlen "fp.fm" ∧ w.val < st.wlen "tr.tid" ∧ w.val < st.wlen "fp.kp" ∧
        w.val < st.wlen "fp.par" := by
      rw [hIwlen]; exact ⟨by omega, by omega, by omega, by omega⟩
    have hkpw : st.wa "fp.kp" w.val = st0.wa "fp.kp" w.val :=
      hIarr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have hpv0 : st.w "tr.pv" = (K[j - 1]'(by omega)).val := hIpv (by omega)
    have hpvN0 : (K[j - 1]'(by omega)).val < N := (K[j - 1]'(by omega)).2
    -- `tr.w := fp.K[j]`
    apply runs_seq
    refine runs_wset (a := w.val) (by simp [hIj, hjK, hwK]) ?_
    apply runs_seq
    refine Runs.mono (markBlk_spec (ops := ops) (w := w.val) (t := t) (a := st0.wa "fp.kp" w.val)
      (by simp) (by simp [hItt]) (by simpa using hkpw) (by simpa using hwl) (by simpa using hcap1)) ?_
    intro st1 hm
    have hpv1 : st1.w "tr.pv" = (K[j - 1]'(by omega)).val := by
      rw [hm.w]; simp only [State.charge_w, State.setW_w, String.reduceEq, if_false]; exact hpv0
    have hw1 : st1.w "tr.w" = w.val := by rw [hm.w]; simp
    have hj1' : st1.w "tr.j" = j := by rw [hm.w]; simp [hIj]
    have hpvN : (K[j - 1]'(by omega)).val < st1.wlen "tr.nx" := by
      rw [hm.wlen]; simp only [State.charge_wlen, State.setW_wlen]; rw [hIwlen]; omega
    have hcap2 : 1 < st1.cap := by rw [hm.cap]; simpa using hcap1
    have hfitj : fit st1.cap (j + 1) = some (j + 1) :=
      fit_of_lt (by rw [hm.cap]; simp only [State.charge_cap, State.setW_cap]; rw [hIcap]; omega)
    apply runs_seq
    refine runs_wstore (j := (K[j - 1]'(by omega)).val) (a := w.val) (by simp [hpv1]) (by simp [hw1])
      hpvN ?_
    apply runs_seq
    refine runs_wset (a := w.val) (by simp [hw1]) ?_
    refine runs_wset (a := j + 1) (by simp [hj1', fit_of_lt hcap2, hfitj]) ?_
    -- facts for the new invariant
    have htk := take_succ_map K hjl
    rw [← hw] at htk
    have hwnot : w ∉ K.take j := by
      intro hmem
      obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hmem
      have hi' : i < j := by simp at hi; omega
      rw [List.getElem_take, hw] at hieq
      have := (List.Nodup.getElem_inj_iff hKnd).mp hieq
      omega
    have hne : (K.take j).map Fin.val ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
    have hlast : ((K.take j).map Fin.val).getLast hne = (K[j - 1]'(by omega)).val := by
      rw [List.getLast_map]
      congr 1
      rw [List.getLast_eq_getElem]
      simp only [List.length_take, List.getElem_take]
      congr 1
      omega
    have hpvnot : (K[j - 1]'(by omega)).val ∉ ((K.take j).map Fin.val).dropLast := by
      intro h
      have hnd' : ((K.take j).map Fin.val).Nodup :=
        (hKnd.sublist (List.take_sublist _ _)).map Fin.val_injective
      rw [← hlast] at h
      exact getLast_not_mem_dropLast hnd' hne h
    have hpvmem : (K[j - 1]'(by omega)).val ∈ (K.take j).map Fin.val := by
      refine List.mem_map.mpr ⟨K[j - 1]'(by omega), ?_, rfl⟩
      exact List.mem_iff_getElem.mpr ⟨j - 1, by simp; omega, by simp⟩
    refine ⟨n - 1, by omega, by omega, ?_, ?_, fun h => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_,
      fun i hi => ?_, fun h => ?_, fun i hi => ?_, fun arr i a b c d e => ?_, fun y hy => ?_, ?_, ?_, ?_⟩
    · -- j
      simp only [State.charge_w, State.setW_w, ↓reduceIte]; omega
    · -- t
      simp only [State.charge_w, State.setW_w, State.storeW_w, String.reduceEq, if_false]
      rw [hm.w]; simp [hItt]
    · -- pv
      simp only [State.charge_w, State.setW_w, State.storeW_w, String.reduceEq, if_false, if_true]
      rw [hw]
      congr 2
      omega
    · -- fm
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
      rw [hm.wa, hjj, htk]
      simp only [true_and, String.reduceEq, false_and, if_false, State.charge_wa, State.setW_wa, hIfm i,
        List.mem_append, List.mem_singleton]
      by_cases hiw : i = w.val
      · subst hiw; simp
      · simp [hiw]
    · -- tid
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
      rw [hm.wa, hjj, htk]
      simp only [true_and, String.reduceEq, false_and, if_false, State.charge_wa, State.setW_wa, hItid i,
        List.mem_append, List.mem_singleton]
      by_cases hiw : i = w.val
      · subst hiw; simp
      · simp [hiw]
    · -- par
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
      rw [hm.wa, hjj, htk]
      simp only [true_and, String.reduceEq, false_and, if_false, State.charge_wa, State.setW_wa, hIpar i,
        List.mem_append, List.mem_singleton]
      by_cases hiw : i = w.val
      · subst hiw; simp
      · simp [hiw]
    · -- the chain grows by one link
      rw [hjj, htk]
      refine LL.append (LL.frame hIll (fun i hi => ?_)) LL.cons_single hne (by simp) ?_
      · simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
        rw [if_neg (by rintro ⟨-, rfl⟩; exact hpvnot hi)]
        rw [hm.wa]
        simp only [String.reduceEq, false_and, if_false, State.charge_wa, State.setW_wa]
      · simp only [State.charge_wa, State.setW_wa, State.storeW_wa, List.head_cons]
        rw [hlast]
        simp
    · -- nx frame
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
      rw [hjj, htk, List.dropLast_concat] at hi
      rw [if_neg (by rintro ⟨-, rfl⟩; exact hi hpvmem)]
      rw [hm.wa]
      simp only [String.reduceEq, false_and, if_false, State.charge_wa, State.setW_wa]
      exact hInx i (fun h' => hi (List.dropLast_subset _ h'))
    · -- hd
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
      rw [hm.wa]
      simp only [String.reduceEq, false_and, if_false, State.charge_wa, State.setW_wa]
      exact hIhd h
    · -- hd'
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
      rw [hm.wa]
      simp only [String.reduceEq, false_and, if_false, State.charge_wa, State.setW_wa]
      exact hIhd' i hi
    · -- other arrays
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
      rw [if_neg (by rintro ⟨h, -⟩; exact d h), hm.wa, if_neg (by rintro ⟨h, -⟩; exact a h),
        if_neg (by rintro ⟨h, -⟩; exact b h), if_neg (by rintro ⟨h, -⟩; exact c h)]
      simp only [State.charge_wa, State.setW_wa]
      exact hIarr arr i a b c d e
    · -- registers
      have hyj : y ≠ "tr.j" := fun h => hy (by simp [trRegs, h])
      have hypv : y ≠ "tr.pv" := fun h => hy (by simp [trRegs, h])
      have hya : y ≠ "tr.a" := fun h => hy (by simp [trRegs, h])
      have hyw : y ≠ "tr.w" := fun h => hy (by simp [trRegs, h])
      simp only [State.charge_w, State.setW_w, State.storeW_w, if_neg hyj, if_neg hypv]
      rw [hm.w, if_neg hya]
      simp only [State.charge_w, State.setW_w, if_neg hyw]
      exact hIreg y hy
    · simp only [State.charge_wlen, State.setW_wlen, State.storeW_wlen]; rw [hm.wlen]
      simp [hIwlen]
    · simp only [State.charge_cap, State.setW_cap, State.storeW_cap]; rw [hm.cap]; simp [hIcap]
    · simp only [State.charge_cost, State.setW_cost, State.storeW_cost]; rw [hm.cost]
      simp only [State.charge_cost, State.setW_cost]
      omega
  · intro hx
    have hn : n = 0 := by
      by_contra h
      have : K.length - n < K.length := by omega
      simp [this] at hx
    subst hn
    refine ⟨hnlt, ?_, hItt, hIpv, hIfm, hItid, hIpar, LL.frame_charge hIll 1, hInx, hIhd, hIhd', ?_, ?_, ?_, ?_,
      ?_⟩
    · simpa using hIj
    · intro arr i a b c d e
      exact hIarr arr i a b c d e
    · intro y hy
      exact hIreg y hy
    · simp [hIwlen]
    · simp [hIcap]
    · simp only [State.charge_cost]; omega

end Frontier.CHD.PartitionRAM
