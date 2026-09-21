import Frontier.CHD.TreeRAM

/-!
# Frontier.CHD.TreeRAM2 — (T1) `newTree` refines `growForest` on a successful search (owner agent-03)

**NON-GATE** (Layer B).  `newTree_spec`: from `ForestRep st N trees` and a search `K` (stored at `fp.K[0, fp.kl)`, parents
at `fp.kp`, head the root `x`, disjoint from the forest), the program ends in `ForestRep st' N (trees ++ [⟨x, K, kpar⟩])`
(agent-05's `growForest .success`), touching only the tree-layer arrays and registers, at cost `9|K| + 20`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

theorem length_le_flatMap_length {N : ℕ} :
    ∀ {trees : List (TreeRec (Fin N))}, (∀ T ∈ trees, T.ord ≠ []) →
      trees.length ≤ (trees.flatMap (fun T => T.ord)).length
  | [], _ => by simp
  | T :: ts, hne => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := List.length_pos_of_ne_nil (hne T List.mem_cons_self)
    have h2 := length_le_flatMap_length (trees := ts) (fun U hU => hne U (List.mem_cons_of_mem _ hU))
    omega

/-- A forest with a vertex outside it has fewer than `N` trees. -/
theorem trees_len_lt {N : ℕ} {trees : List (TreeRec (Fin N))} (hne : ∀ T ∈ trees, T.ord ≠ [])
    (hdisj : trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord)) (hnd : ∀ T ∈ trees, T.ord.Nodup)
    {w0 : Fin N} (hw0 : ∀ T ∈ trees, w0 ∉ T.ord) : trees.length < N := by
  have hF : ((trees.flatMap (fun T => T.ord)) ++ [w0]).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_flatMap.mpr ⟨hnd, hdisj.imp (fun h => ?_)⟩, List.nodup_singleton _, ?_⟩
    · intro w hwa hwb
      exact h w hwa hwb
    · intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      obtain ⟨T, hT, haT⟩ := List.mem_flatMap.mp ha
      intro h
      exact hw0 T hT (h ▸ haT)
  have hlen := hF.length_le_card
  simp only [List.length_append, List.length_singleton, Fintype.card_fin] at hlen
  have := length_le_flatMap_length hne
  omega

theorem ForestRep.ne_mem {st : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} (hF : ForestRep st N trees) :
    ∀ T ∈ trees, T.ord ≠ [] := by
  intro T hT
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hT
  exact hF.ne t ht

theorem getElem_snoc {α : Type*} {l : List α} {a : α} {t : ℕ} (ht : t < (l ++ [a]).length) :
    (l ++ [a])[t] = if h : t < l.length then l[t] else a := by
  split_ifs with h
  · exact List.getElem_append_left h
  · rw [List.getElem_append_right (by omega)]
    simp

/-- **(T1) `newTree` refines `growForest .success`.** -/
theorem newTree_spec {st0 : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} {K : List (Fin N)}
    {kpar : Fin N → Fin N} {x : Fin N}
    (hF : ForestRep st0 N trees) (hKne : K ≠ []) (hKx : K.head? = some x) (hKnd : K.Nodup)
    (hKtv : ∀ w ∈ K, ∀ T ∈ trees, w ∉ T.ord)
    (hK : ∀ i (h : i < K.length), st0.wa "fp.K" i = (K[i]).val) (hkl : st0.w "fp.kl" = K.length)
    (hKl : K.length ≤ st0.wlen "fp.K")
    (hkp : ∀ w ∈ K, st0.wa "fp.kp" w.val = (kpar w).val) (hkpl : N ≤ st0.wlen "fp.kp")
    (hcap : N + 2 < st0.cap) :
    Runs ops newTree st0 (fun st' => ForestRep st' N (trees ++ [⟨x, K, kpar⟩]) ∧
      (∀ arr i, arr ∉ trArrs → st'.wa arr i = st0.wa arr i) ∧ (∀ y, y ∉ trRegs → st'.w y = st0.w y) ∧
      st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧ st'.cost ≤ st0.cost + 9 * K.length + 20) := by
  classical
  obtain ⟨hlF1, hlF2, hlF3, hlF4, hlF5, hlF6, hlF7, hlF8⟩ := hF.lens
  have hK0 : 0 < K.length := List.length_pos_of_ne_nil hKne
  have hKN : K.length ≤ N := by
    have := hKnd.length_le_card
    simpa using this
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 = K[0] := ⟨_, rfl⟩
  have hk0K : k0 ∈ K := by rw [hk0]; exact List.getElem_mem hK0
  have hlt : trees.length < N := trees_len_lt hF.ne_mem hF.disj hF.nodup (hKtv k0 hk0K)
  have hcap1 : 1 < st0.cap := by omega
  have hfit0 : fit st0.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st0.cap 1 = some 1 := fit_of_lt hcap1
  -- `tr.t := tr.nt`
  apply runs_seq
  refine runs_wset (a := trees.length) (by simp [hF.nt]) ?_
  -- `tr.w := fp.K[0]`
  apply runs_seq
  refine runs_wset (a := k0.val) (by simp [hfit0, show 0 < st0.wlen "fp.K" by omega, hK 0 hK0, hk0]) ?_
  generalize hs2 : ((((st0.setW "tr.t" trees.length).charge 1).setW "tr.w" k0.val).charge 1) = s2
  have h2w : ∀ y, s2.w y = if y = "tr.w" then k0.val else if y = "tr.t" then trees.length else st0.w y := by
    intro y; rw [← hs2]; simp only [State.charge_w, State.setW_w]
  have h2wa : s2.wa = st0.wa := by rw [← hs2]; rfl
  have h2len : s2.wlen = st0.wlen := by rw [← hs2]; rfl
  have h2cap : s2.cap = st0.cap := by rw [← hs2]; rfl
  have h2cost : s2.cost = st0.cost + 2 := by rw [← hs2]; simp
  -- mark the root
  apply runs_seq
  refine Runs.mono (markBlk_spec (ops := ops) (st := s2) (w := k0.val) (t := trees.length)
    (a := st0.wa "fp.kp" k0.val) (by simp [h2w]) (by simp [h2w]) (by rw [h2wa])
    (by rw [h2len]; exact ⟨by have := k0.2; omega, by have := k0.2; omega, by have := k0.2; omega,
      by have := k0.2; omega⟩) (by rw [h2cap]; exact hcap1)) ?_
  intro s3 hm3
  -- `tr.hd[t] := tr.w; tr.pv := tr.w; tr.j := 1`
  have h3w : ∀ y, s3.w y = if y = "tr.a" then st0.wa "fp.kp" k0.val else s2.w y := hm3.w
  have h3len : s3.wlen = st0.wlen := by rw [hm3.wlen, h2len]
  have h3cap : s3.cap = st0.cap := by rw [hm3.cap, h2cap]
  apply runs_seq
  refine runs_wstore (j := trees.length) (a := k0.val) (by simp [h3w, h2w]) (by simp [h3w, h2w])
    (by rw [h3len]; omega) ?_
  apply runs_seq
  refine runs_wset (a := k0.val) (by simp [h3w, h2w]) ?_
  apply runs_seq
  refine runs_wset (a := 1) (by simp [h3cap, hfit1]) ?_
  generalize hs6 : (((((s3.storeW "tr.hd" trees.length k0.val).charge 1).setW "tr.pv" k0.val).charge 1).setW
    "tr.j" 1).charge 1 = s6
  have h6w : ∀ y, s6.w y = if y = "tr.j" then 1 else if y = "tr.pv" then k0.val else s3.w y := by
    intro y; rw [← hs6]; simp only [State.charge_w, State.setW_w, State.storeW_w]
  have h6wa : ∀ arr i, s6.wa arr i = if arr = "tr.hd" ∧ i = trees.length then k0.val else s3.wa arr i := by
    intro arr i; rw [← hs6]; simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
  have h6len : s6.wlen = st0.wlen := by rw [← hs6]; simp [h3len]
  have h6cap : s6.cap = st0.cap := by rw [← hs6]; simp [h3cap]
  have h6cost : s6.cost = st0.cost + 9 := by rw [← hs6]; simp [hm3.cost, h2cost]
  -- the list facts
  have hK1 : (K.take (K.length - (K.length - 1))).map Fin.val = [k0.val] := by
    rw [show K.length - (K.length - 1) = 1 by omega]
    cases K with
    | nil => exact absurd rfl hKne
    | cons a t => simp [hk0]
  -- the loop
  apply runs_seq
  refine Runs.mono (ntLoop_spec (ops := ops) (st0 := st0) (K := K) (t := trees.length)
    (c0 := s6.cost + 9 * (K.length - 1)) hK hkl hKl hKnd ⟨hlF1, hlF2, hkpl, hlF4, hlF3⟩ (by omega)
    (K.length - 1) s6 ⟨by omega, ?_, ?_, fun h => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, fun i hi => ?_,
      fun h => ?_, fun i hi => ?_, fun arr i a b c d e => ?_, fun y hy => ?_, h6len, h6cap, le_rfl⟩) ?_
  · rw [h6w]; simp; omega
  · rw [h6w, h3w, h2w]; simp
  · rw [h6w]; simp only [String.reduceEq, if_false, if_true]
    rw [hk0]; congr 2; omega
  · rw [h6wa, hm3.wa, hK1, h2wa]
    simp only [List.mem_singleton, String.reduceEq, false_and, if_false, true_and]
  · rw [h6wa, hm3.wa, hK1, h2wa]
    simp only [List.mem_singleton, String.reduceEq, false_and, if_false, true_and]
    try (by_cases hi : i = k0.val <;> simp [hi])
  · rw [h6wa, hm3.wa, hK1, h2wa]
    simp only [List.mem_singleton, String.reduceEq, false_and, if_false, true_and]
    try (by_cases hi : i = k0.val <;> simp [hi])
  · rw [hK1]; trivial
  · rw [h6wa, hm3.wa, h2wa]
    simp only [String.reduceEq, false_and, if_false]
  · rw [h6wa]; simp only [true_and, if_true]; rw [hk0]
  · rw [h6wa, if_neg (by rintro ⟨-, h⟩; exact hi h), hm3.wa, h2wa]
    simp only [String.reduceEq, false_and, if_false]
  · rw [h6wa, if_neg (by rintro ⟨h, -⟩; exact e h), hm3.wa, if_neg (by rintro ⟨h, -⟩; exact a h),
      if_neg (by rintro ⟨h, -⟩; exact b h), if_neg (by rintro ⟨h, -⟩; exact c h), h2wa]
  · have hyj : y ≠ "tr.j" := fun h => hy (by simp [trRegs, h])
    have hypv : y ≠ "tr.pv" := fun h => hy (by simp [trRegs, h])
    have hya : y ≠ "tr.a" := fun h => hy (by simp [trRegs, h])
    have hyw : y ≠ "tr.w" := fun h => hy (by simp [trRegs, h])
    have hyt : y ≠ "tr.t" := fun h => hy (by simp [trRegs, h])
    rw [h6w, if_neg hyj, if_neg hypv, h3w, if_neg hya, h2w, if_neg hyw, if_neg hyt]
  · intro s7 hI7
    obtain ⟨-, h7j, h7t, h7pv, h7fm, h7tid, h7par, h7ll, h7nx, h7hd, h7hd', h7arr, h7reg, h7len, h7cap,
      h7cost⟩ := hI7
    have hKK : K.take (K.length - 0) = K := by simp
    rw [hKK] at h7fm h7tid h7par h7ll h7nx
    have h7pv' : s7.w "tr.pv" = (K.getLast hKne).val := by
      rw [h7pv (by omega), List.getLast_eq_getElem]
      congr 2
    have h7kl : s7.w "fp.kl" = K.length := by rw [h7reg _ (by decide)]; exact hkl
    have hcap7 : 1 < s7.cap := by rw [h7cap]; omega
    have hfitT : fit s7.cap (trees.length + 1) = some (trees.length + 1) := fit_of_lt (by rw [h7cap]; omega)
    -- `tr.tl[t] := tr.pv; tr.ln[t] := fp.kl; tr.nt := tr.t + 1`
    apply runs_seq
    refine runs_wstore (j := trees.length) (a := (K.getLast hKne).val) (by simp [h7t]) (by simp [h7pv'])
      (by rw [h7len]; omega) ?_
    apply runs_seq
    refine runs_wstore (j := trees.length) (a := K.length) (by simp [h7t]) (by simp [h7kl])
      (by simp; rw [h7len]; omega) ?_
    refine runs_wset (a := trees.length + 1) (by simp [h7t, fit_of_lt hcap7, hfitT]) ?_
    generalize hs10 : ((((((s7.storeW "tr.tl" trees.length (K.getLast hKne).val).charge 1).storeW "tr.ln"
      trees.length K.length).charge 1).setW "tr.nt" (trees.length + 1)).charge 1) = s10
    have h10w : ∀ y, s10.w y = if y = "tr.nt" then trees.length + 1 else s7.w y := by
      intro y; rw [← hs10]; simp only [State.charge_w, State.setW_w, State.storeW_w]
    have h10wa : ∀ arr i, s10.wa arr i = if arr = "tr.ln" ∧ i = trees.length then K.length else
        if arr = "tr.tl" ∧ i = trees.length then (K.getLast hKne).val else s7.wa arr i := by
      intro arr i; rw [← hs10]; simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    have h10len : s10.wlen = st0.wlen := by rw [← hs10]; simp [h7len]
    have h10cap : s10.cap = st0.cap := by rw [← hs10]; simp [h7cap]
    have h10cost : s10.cost = s7.cost + 3 := by rw [← hs10]; simp
    -- membership facts
    have hmemK : ∀ v : Fin N, v.val ∈ K.map Fin.val ↔ v ∈ K := fun v =>
      ⟨fun h => by obtain ⟨u, hu, huv⟩ := List.mem_map.mp h; exact Fin.ext huv ▸ hu,
       fun h => List.mem_map_of_mem h⟩
    have hold : ∀ t (ht : t < trees.length), ∀ v ∈ trees[t].ord, v.val ∉ K.map Fin.val := by
      intro t ht v hv hvK
      exact hKtv v ((hmemK v).mp hvK) trees[t] (List.getElem_mem ht) hv
    -- the array updates, seen at old vertices
    have hfm10 : ∀ i, s10.wa "fp.fm" i = if i ∈ K.map Fin.val then 1 else st0.wa "fp.fm" i := by
      intro i; rw [h10wa]; simp only [String.reduceEq, false_and, if_false]; exact h7fm i
    have htid10 : ∀ i, s10.wa "tr.tid" i = if i ∈ K.map Fin.val then trees.length else st0.wa "tr.tid" i := by
      intro i; rw [h10wa]; simp only [String.reduceEq, false_and, if_false]; exact h7tid i
    have hpar10 : ∀ i, s10.wa "fp.par" i = if i ∈ K.map Fin.val then st0.wa "fp.kp" i else st0.wa "fp.par" i := by
      intro i; rw [h10wa]; simp only [String.reduceEq, false_and, if_false]; exact h7par i
    have hnx10 : ∀ i, s10.wa "tr.nx" i = s7.wa "tr.nx" i := by
      intro i; rw [h10wa]; simp only [String.reduceEq, false_and, if_false]
    have hll10 : LL s10 "tr.nx" (K.map Fin.val) := LL.frame h7ll (fun i _ => hnx10 i)
    refine ⟨⟨?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
      fun t ht => ?_, fun t ht => ?_, fun v => ?_, fun v => ?_, ?_, ?_, ?_⟩, fun arr i harr => ?_,
      fun y hy => ?_, h10len, h10cap, ?_⟩
    · rw [h10w]; simp
    · rw [getElem_snoc]; split_ifs with h
      · exact hF.ne t h
      · exact hKne
    · rw [getElem_snoc]; split_ifs with h
      · exact hF.root t h
      · exact hKx
    · rw [getElem_snoc]; split_ifs with h
      · rw [h10wa, if_neg (by rintro ⟨h', -⟩; exact absurd h' (by decide)),
          if_neg (by rintro ⟨h', -⟩; exact absurd h' (by decide)), h7hd' t (by omega)]
        exact hF.hd t h
      · have htt : t = trees.length := by simp at ht; omega
        subst htt
        rw [h10wa]
        simp only [String.reduceEq, false_and, if_false]
        rw [h7hd hK0]
        cases K with
        | nil => exact absurd rfl hKne
        | cons a l => simp
    · rw [getElem_snoc]; split_ifs with h
      · rw [h10wa, if_neg (by rintro ⟨-, h'⟩; omega), if_neg (by rintro ⟨-, h'⟩; omega),
          h7arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hF.tl t h
      · have htt : t = trees.length := by simp at ht; omega
        subst htt
        rw [h10wa]
        simp only [String.reduceEq, false_and, if_false, true_and, if_true]
        rw [List.getLast?_eq_getLast hKne]
        rfl
    · rw [getElem_snoc]; split_ifs with h
      · rw [h10wa, if_neg (by rintro ⟨-, h'⟩; omega),
          h7arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hF.ln t h
      · have htt : t = trees.length := by simp at ht; omega
        subst htt
        rw [h10wa]
        simp
    · rw [getElem_snoc]; split_ifs with h
      · refine LL.frame (hF.ll t h) (fun i hi => ?_)
        rw [hnx10]
        refine h7nx i (fun hK' => ?_)
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.dropLast_subset _ hi)
        exact hold t h v hv (List.dropLast_subset _ hK')
      · exact hll10
    · rw [getElem_snoc]; split_ifs with h
      · intro v hv
        rw [htid10, if_neg (hold t h v hv)]
        exact hF.tid t h v hv
      · intro v hv
        rw [htid10, if_pos ((hmemK v).mpr hv)]
        simp at ht; omega
    · rw [getElem_snoc]; split_ifs with h
      · intro v hv
        rw [hpar10, if_neg (hold t h v (List.mem_of_mem_tail hv))]
        exact hF.par t h v hv
      · intro v hv
        have hvK : v ∈ K := List.mem_of_mem_tail hv
        rw [hpar10, if_pos ((hmemK v).mpr hvK)]
        exact hkp v hvK
    · rw [hfm10]
      by_cases hvK : v ∈ K
      · rw [if_pos ((hmemK v).mpr hvK), if_pos ⟨⟨x, K, kpar⟩, List.mem_append_right _ (List.mem_singleton_self _), hvK⟩]
      · rw [if_neg (fun h => hvK ((hmemK v).mp h)), hF.fm v]
        congr 1
        apply propext
        constructor
        · rintro ⟨T, hT, hvT⟩; exact ⟨T, List.mem_append_left _ hT, hvT⟩
        · rintro ⟨T, hT, hvT⟩
          rcases List.mem_append.mp hT with h | h
          · exact ⟨T, h, hvT⟩
          · rw [List.mem_singleton] at h; subst h; exact absurd hvT hvK
    · rw [h10wa]
      simp only [String.reduceEq, false_and, if_false]
      rw [h7arr _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hF.inP v
    · rw [List.pairwise_append]
      refine ⟨hF.disj, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      intro w hwa hwK
      exact hKtv w hwK a ha hwa
    · intro T hT
      rcases List.mem_append.mp hT with h | h
      · exact hF.nodup T h
      · rw [List.mem_singleton] at h; subst h; exact hKnd
    · rw [h10len]; exact hF.lens
    · have h1 : arr ≠ "tr.ln" := fun h => harr (by simp [trArrs, h])
      have h2 : arr ≠ "tr.tl" := fun h => harr (by simp [trArrs, h])
      have h3 : arr ≠ "fp.fm" := fun h => harr (by simp [trArrs, h])
      have h4 : arr ≠ "tr.tid" := fun h => harr (by simp [trArrs, h])
      have h5 : arr ≠ "fp.par" := fun h => harr (by simp [trArrs, h])
      have h6 : arr ≠ "tr.nx" := fun h => harr (by simp [trArrs, h])
      have h7 : arr ≠ "tr.hd" := fun h => harr (by simp [trArrs, h])
      rw [h10wa, if_neg (by rintro ⟨h, -⟩; exact h1 h), if_neg (by rintro ⟨h, -⟩; exact h2 h)]
      exact h7arr arr i h3 h4 h5 h6 h7
    · have hnt : y ≠ "tr.nt" := fun h => hy (by simp [trRegs, h])
      rw [h10w, if_neg hnt]
      exact h7reg y hy
    · rw [h10cost]
      have := h7cost
      rw [h6cost] at this
      omega

end Frontier.CHD.PartitionRAM
