import Frontier.CHD.RamSpine
import Frontier.CHD.BMCost

/-!
# SpineLink — the Layer-A meaning of the RAM expansion (agent-08, B-L4, NON-GATE)

For a group table `GrpRep st l n p P piv` of a Layer-A loop state `σ` (the families lifted to `ℕ`
by `liftP` / `liftPiv`), the child row produced by `RamSpine.expand_spec` from the pulled keys
`ks` is duplicate-free, fits the row, has exactly the members of `BM.expand σ ks.toFinset Bi`, and
its scan work is the expansion term `∑ j ∈ pulledGroups σ S0, |P j|` of `BMLazy.iterCostD`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.CHD.RamLevel

section grpFacts

variable {V : Type} {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}

theorem mlist_nodup (hG : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) :
    (mlist st l n j).Nodup := by
  unfold mlist
  refine List.Nodup.map_on ?_ List.nodup_range
  intro q hq q' hq' h
  rw [List.mem_range] at hq hq'
  have e1 := hG.pos j hj q hq
  have e2 := hG.pos j hj q' hq'
  rw [h] at e1
  omega

theorem mem_mlist (hG : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) {v : ℕ} :
    v ∈ mlist st l n j ↔ v ∈ P j := by
  rw [hG.img j hj]; simp [mlist]

theorem grpOf_of_mem (hG : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) {x : ℕ} (hx : x ∈ P j) :
    grpOf st l n x = j := by
  have := ((hG.mem_iff hj).1 hx).2
  simp [grpOf, this]

theorem isPiv_iff (hG : GrpRep st l n p P piv) {x : ℕ} (hx : x < n) :
    isPiv st l n x ↔ ∃ j < p, x ∈ P j ∧ piv j = x := by
  constructor
  · rintro ⟨h0, hp⟩
    rcases hG.nomemb x hx with h | ⟨j, hj, -, hxP⟩
    · exact absurd h h0
    · refine ⟨j, hj, hxP, ?_⟩
      rw [← hG.pivs j hj, ← grpOf_of_mem hG hj hxP]; exact hp
  · rintro ⟨j, hj, hxP, hpv⟩
    refine ⟨by rw [((hG.mem_iff hj).1 hxP).2]; omega, ?_⟩
    rw [grpOf_of_mem hG hj hxP, hG.pivs j hj, hpv]

theorem gl_eq_card (hG : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) :
    gl st l n j = (P j).card := by
  rw [← mlist_length, ← List.toFinset_card_of_nodup (mlist_nodup hG hj)]
  congr 1
  ext v
  rw [List.mem_toFinset, mem_mlist hG hj]

theorem mem_extOf (hG : GrpRep st l n p P piv) {lt mk : ℕ → Prop} [DecidablePred lt]
    [DecidablePred mk] {x : ℕ} (hx : x < n) {v : ℕ} :
    v ∈ extOf st l n lt mk x ↔ ∃ j < p, x ∈ P j ∧ piv j = x ∧ v ∈ P j ∧ lt v ∧ ¬ mk v := by
  unfold extOf
  split_ifs with hp
  · obtain ⟨j, hj, hxP, hpv⟩ := (isPiv_iff hG hx).1 hp
    rw [grpOf_of_mem hG hj hxP, List.mem_filter, mem_mlist hG hj]
    constructor
    · rintro ⟨hv, hb⟩
      simp only [decide_eq_true_eq] at hb
      exact ⟨j, hj, hxP, hpv, hv, hb⟩
    · rintro ⟨j', hj', hxP', -, hv, hb⟩
      have e : j' = j := by
        have := grpOf_of_mem hG hj' hxP'; rw [grpOf_of_mem hG hj hxP] at this; exact this.symm
      subst e
      exact ⟨hv, by simpa using hb⟩
  · simp only [List.not_mem_nil, false_iff]
    rintro ⟨j, hj, hxP, hpv, -⟩
    exact hp ((isPiv_iff hG hx).2 ⟨j, hj, hxP, hpv⟩)

theorem mem_expList (hG : GrpRep st l n p P piv) {lt : ℕ → Prop} [DecidablePred lt]
    {ks : List ℕ} (hks : ∀ x ∈ ks, x < n) (v : ℕ) :
    v ∈ ks ++ ks.flatMap (extOf st l n lt (fun x => x ∈ ks)) ↔
      v ∈ ks ∨ ∃ j < p, piv j ∈ ks ∧ piv j ∈ P j ∧ v ∈ P j ∧ lt v := by
  rw [List.mem_append, List.mem_flatMap]
  constructor
  · rintro (h | ⟨x, hx, hv⟩)
    · exact Or.inl h
    · obtain ⟨j, hj, hxP, hpv, hvP, hlt, -⟩ := (mem_extOf hG (hks x hx)).1 hv
      exact Or.inr ⟨j, hj, hpv ▸ hx, hpv ▸ hxP, hvP, hlt⟩
  · rintro (h | ⟨j, hj, hpk, hpP, hvP, hlt⟩)
    · exact Or.inl h
    · by_cases hvk : v ∈ ks
      · exact Or.inl hvk
      · exact Or.inr ⟨piv j, hpk, (mem_extOf hG (hks _ hpk)).2 ⟨j, hj, hpP, rfl, hvP, hlt, hvk⟩⟩

theorem expList_nodup (hG : GrpRep st l n p P piv) {lt : ℕ → Prop} [DecidablePred lt]
    {ks : List ℕ} (hks : ∀ x ∈ ks, x < n) (hnd : ks.Nodup) :
    (ks ++ ks.flatMap (extOf st l n lt (fun x => x ∈ ks))).Nodup := by
  rw [List.nodup_append]
  refine ⟨hnd, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun x hx => ?_, ?_⟩
    · unfold extOf
      split_ifs with hp
      · obtain ⟨j, hj, hxP, -⟩ := (isPiv_iff hG (hks x hx)).1 hp
        rw [grpOf_of_mem hG hj hxP]
        exact (mlist_nodup hG hj).filter _
      · exact List.nodup_nil
    · refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hnd
      intro v hva hvb
      obtain ⟨j, hj, -, hpa, hvP, -⟩ := (mem_extOf hG (hks a ha)).1 hva
      obtain ⟨j', hj', -, hpb, hvP', -⟩ := (mem_extOf hG (hks b hb)).1 hvb
      have e : j = j' := by
        have e1 := grpOf_of_mem hG hj hvP; rw [grpOf_of_mem hG hj' hvP'] at e1; exact e1.symm
      subst e
      exact hab (hpa.symm.trans hpb)
  · intro a ha b hb hab
    subst hab
    obtain ⟨x, hx, hv⟩ := List.mem_flatMap.1 hb
    obtain ⟨-, -, -, -, -, -, hmk⟩ := (mem_extOf hG (hks x hx)).1 hv
    exact hmk ha

theorem expList_lt (hG : GrpRep st l n p P piv) {lt : ℕ → Prop} [DecidablePred lt]
    {ks : List ℕ} (hks : ∀ x ∈ ks, x < n) :
    ∀ v ∈ ks ++ ks.flatMap (extOf st l n lt (fun x => x ∈ ks)), v < n := by
  intro v hv
  rcases List.mem_append.1 hv with h | h
  · exact hks v h
  · obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 h
    exact extOf_lt hG (hks y hy) hxy

/-- The room hypothesis of `expand_spec` holds automatically. -/
theorem expList_room (hG : GrpRep st l n p P piv) {lt : ℕ → Prop} [DecidablePred lt]
    {ks : List ℕ} (hks : ∀ x ∈ ks, x < n) (hnd : ks.Nodup) :
    ks.length + (ks.flatMap (extOf st l n lt (fun x => x ∈ ks))).length ≤ n := by
  have hnd' := expList_nodup hG (lt := lt) hks hnd
  rw [← List.length_append, ← List.toFinset_card_of_nodup hnd']
  calc _ ≤ (Finset.range n).card := Finset.card_le_card (fun v hv => by
          rw [List.mem_toFinset] at hv; simpa using expList_lt hG hks v hv)
    _ = n := Finset.card_range n

end grpFacts

/-! ### Lifting Layer-A group families to `ℕ` -/

section lift

/-- The `ℕ`-indexed group family of a Layer-A family (empty beyond `p`). -/
def liftP {N p : ℕ} (P : Fin p → Finset (Fin N)) (j : ℕ) : Finset ℕ :=
  if h : j < p then (P ⟨j, h⟩).map Fin.valEmbedding else ∅

/-- The `ℕ`-indexed pivot table of a Layer-A pivot family (`0` beyond `p`). -/
def liftPiv {N p : ℕ} (piv : Fin p → Fin N) (j : ℕ) : ℕ :=
  if h : j < p then (piv ⟨j, h⟩ : ℕ) else 0

theorem mem_liftP {N p : ℕ} (P : Fin p → Finset (Fin N)) (j : Fin p) (x : ℕ) :
    x ∈ liftP P j ↔ ∃ u ∈ P j, (u : ℕ) = x := by
  simp [liftP, j.2]

theorem liftPiv_val {N p : ℕ} (piv : Fin p → Fin N) (j : Fin p) : liftPiv piv j = piv j := by
  simp [liftPiv, j.2]

theorem val_mem_liftP {N p : ℕ} (P : Fin p → Finset (Fin N)) (j : Fin p) (u : Fin N) :
    (u : ℕ) ∈ liftP P j ↔ u ∈ P j := by
  rw [mem_liftP]
  exact ⟨fun ⟨w, hw, h⟩ => (Fin.ext h) ▸ hw, fun h => ⟨u, h, rfl⟩⟩

theorem val_mem_map {N : ℕ} (l : List (Fin N)) (u : Fin N) : (u : ℕ) ∈ l.map Fin.val ↔ u ∈ l := by
  rw [List.mem_map]
  exact ⟨fun ⟨w, hw, h⟩ => (Fin.ext h) ▸ hw, fun h => ⟨u, h, rfl⟩⟩

end lift

section link

variable {V : Type} {G : Graph} {s : Fin G.n} {p : ℕ}

open Frontier.CHD.BM

/-- **Members of the child row = `BM.expand`**. -/
theorem expand_link (σ : LState G s p) {st : State V} {l : ℕ}
    (hG : GrpRep st l G.n p (liftP σ.P) (liftPiv σ.piv)) (ksF : List (Fin G.n)) (Bi : WLab G s)
    {lt : ℕ → Prop} [DecidablePred lt] (hlt : ∀ v : Fin G.n, lt v ↔ σ.d v < Bi) (x : ℕ) :
    x ∈ ksF.map Fin.val ++ (ksF.map Fin.val).flatMap
        (extOf st l G.n lt (fun y => y ∈ ksF.map Fin.val)) ↔
      ∃ u ∈ BM.expand σ ksF.toFinset Bi, (u : ℕ) = x := by
  have hks : ∀ y ∈ ksF.map Fin.val, y < G.n := by
    intro y hy; obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; exact w.2
  rw [mem_expList hG hks x]
  simp only [BM.expand, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset]
  constructor
  · rintro (h | ⟨j, hj, hpk, hpP, hvP, hlt'⟩)
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
      exact ⟨u, Or.inl hu, rfl⟩
    · set J : Fin p := ⟨j, hj⟩
      have hpv : liftPiv σ.piv j = σ.piv J := liftPiv_val σ.piv J
      rw [hpv] at hpk hpP
      obtain ⟨u, hu, rfl⟩ := (mem_liftP σ.P J x).1 hvP
      exact ⟨u, Or.inr ⟨J, (val_mem_map ksF _).1 hpk, (val_mem_liftP σ.P J _).1 hpP, hu,
        (hlt u).1 hlt'⟩, rfl⟩
  · rintro ⟨u, (hu | ⟨J, hpk, hpP, hu, hd⟩), rfl⟩
    · exact Or.inl ((val_mem_map ksF u).2 hu)
    · refine Or.inr ⟨J, J.2, ?_, ?_, (val_mem_liftP σ.P J u).2 hu, (hlt u).2 hd⟩
      · rw [liftPiv_val]; exact (val_mem_map ksF _).2 hpk
      · rw [liftPiv_val]; exact (val_mem_liftP σ.P J _).2 hpP

/-- **The scan work is the expansion term of `iterCostD`**. -/
theorem scanW_sum (σ : LState G s p) {st : State V} {l : ℕ}
    (hG : GrpRep st l G.n p (liftP σ.P) (liftPiv σ.piv)) (ksF : List (Fin G.n)) (hnd : ksF.Nodup) :
    ((ksF.map Fin.val).map (scanW st l G.n)).sum =
      ∑ j ∈ pulledGroups σ ksF.toFinset, (σ.P j).card := by
  classical
  rw [List.map_map, ← List.sum_toFinset _ hnd]
  have hsc : ∀ u : Fin G.n, (scanW st l G.n ∘ Fin.val) u =
      if isPiv st l G.n u then gl st l G.n (grpOf st l G.n u) else 0 := fun u => rfl
  simp only [hsc]
  rw [← Finset.sum_filter]
  -- the pulled current pivots are the images of the pulled groups
  have himg : ksF.toFinset.filter (fun u : Fin G.n => isPiv st l G.n u) =
      (pulledGroups σ ksF.toFinset).image σ.piv := by
    ext u
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_image, pulledGroups,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hu, hp⟩
      obtain ⟨j, hj, huP, hpv⟩ := (isPiv_iff hG u.2).1 hp
      set J : Fin p := ⟨j, hj⟩
      have e : σ.piv J = u := Fin.ext (by rw [← liftPiv_val σ.piv J]; exact hpv)
      refine ⟨J, ⟨e ▸ hu, ?_⟩, e⟩
      rw [e]; exact (val_mem_liftP σ.P J u).1 huP
    · rintro ⟨J, ⟨hpk, hpP⟩, rfl⟩
      exact ⟨hpk, (isPiv_iff hG (σ.piv J).2).2 ⟨J, J.2, (val_mem_liftP σ.P J _).2 hpP,
        liftPiv_val σ.piv J⟩⟩
  rw [himg, Finset.sum_image]
  · refine Finset.sum_congr rfl (fun J hJ => ?_)
    simp only [pulledGroups, Finset.mem_filter, Finset.mem_univ, true_and] at hJ
    have hm : ((σ.piv J : Fin G.n) : ℕ) ∈ liftP σ.P J := (val_mem_liftP σ.P J _).2 hJ.2
    rw [grpOf_of_mem hG J.2 hm, gl_eq_card hG J.2]
    simp [liftP, J.2]
  · intro J hJ J' hJ' h
    simp only [pulledGroups, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hJ hJ'
    have h1 : ((σ.piv J : Fin G.n) : ℕ) ∈ liftP σ.P J := (val_mem_liftP σ.P J _).2 hJ.2
    have h2 : ((σ.piv J' : Fin G.n) : ℕ) ∈ liftP σ.P J' := (val_mem_liftP σ.P J' _).2 hJ'.2
    rw [h] at h1
    have e1 := grpOf_of_mem hG J.2 h1
    rw [grpOf_of_mem hG J'.2 h2] at e1
    exact Fin.ext e1.symm

end link

end Frontier.CHD.RamSpine
