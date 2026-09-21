import Frontier.CHD.PartitionRAM4

/-!
# Frontier.CHD.PartitionRAM5 — the whole PT program (owner agent-03)

**NON-GATE.** `ptProg` = forest loop (Algorithm 5 on every FindPivots tree) ; MakePivots ; clearing of `pt.as`.
`ptProg_spec`: from agent-09's forest layout (`ForestAt`), the `S`/`Q` bitmaps and an all-zero `pt.as`, the program
stores exactly the pivot groups `makePivots S Q (forestPieces k trees)` (`= forestGroups S Q k trees`) as compact
segments (`GrpOut`), leaves `pt.as` all-zero again, touches only its own arrays and registers, and costs at most
`170·Σ_T |T| + 10`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

theorem sum_map_affine {β : Type*} (l : List β) (f : β → ℕ) (a b : ℕ) :
    (l.map (fun x => a * f x + b)).sum = a * (l.map f).sum + b * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- Consecutive segments form the flattened list. -/
theorem segAt_flatten {st : State V} {arr : String} :
    ∀ (Gs : List (List ℕ)) (b : ℕ),
      (∀ j (h : j < Gs.length), SegAt st arr (b + ((Gs.take j).map List.length).sum) Gs[j]) →
      SegAt st arr b Gs.flatten
  | [], _, _ => fun i hi => by simp at hi
  | g :: Gs, b, h => by
    have h0 := h 0 (by simp)
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.getElem_cons_zero] at h0
    have ih := segAt_flatten Gs (b + g.length) (fun j hj => by
      have := h (j + 1) (by simp; omega)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ] at this
      rw [Nat.add_assoc]
      exact this)
    intro i hi
    simp only [List.flatten_cons, List.length_append] at hi ⊢
    by_cases hig : i < g.length
    · rw [List.getElem_append_left hig]
      exact h0 i hig
    · rw [List.getElem_append_right (by omega)]
      have := ih (i - g.length) (by omega)
      rw [show b + g.length + (i - g.length) = b + i by omega] at this
      exact this

theorem GrpOut.congr {st st' : State V} {Gs : List (List ℕ)} (h : GrpOut st Gs)
    (hng : st'.w "pt.ng" = st.w "pt.ng") (hgv : st'.w "pt.gv" = st.w "pt.gv")
    (hGO : ∀ j, st'.wa "pt.GO" j = st.wa "pt.GO" j) (hGL : ∀ j, st'.wa "pt.GL" j = st.wa "pt.GL" j)
    (hGV : ∀ j, st'.wa "pt.GV" j = st.wa "pt.GV" j) : GrpOut st' Gs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hng.trans h1, hgv.trans h2, fun j hj => ?_⟩
  obtain ⟨a, b, c⟩ := h3 j hj
  exact ⟨(hGO j).trans a, (hGL j).trans b, fun i hi => (hGV _).trans (c i hi)⟩

/-- The PT program of one FindPivots call. -/
def ptProg : Stmt :=
  .seq (.wset "pt.t" (.lit 0)) <|
  .seq (.wset "pt.np" (.lit 0)) <|
  .seq forestLoop <|
  .seq (.wset "pt.g" (.lit 0)) <|
  .seq (.wset "pt.ng" (.lit 0)) <|
  .seq (.wset "pt.gv" (.lit 0)) <|
  .seq mpLoop <|
  .seq (.wset "pt.j" (.lit 0)) clrLoop

/-- Registers written by the PT program. -/
def ptRegs : List String := forestRegs ++ mpRegs ++ ["pt.j"]

/-- Arrays written by the PT program. -/
def ptOut : List String := ptArrs ++ ["pt.as", "pt.GV", "pt.GO", "pt.GL"]

/-- **The PT program refines MakePivots over the tree partition**, with the bitmap reset and cost
`O(Σ_T |T| + 1)`. -/
theorem ptProg_spec {st0 : State V} {k N : ℕ} {trees : List (TreeRec ℕ)} {S Q : Finset ℕ} (hk : 2 ≤ k)
    (hF : ForestAt st0 trees) (hN : ∀ T ∈ trees, ∀ x ∈ T.ord, x < N)
    (hNl : N ≤ st0.wlen "fp.par" ∧ N ≤ st0.wlen "pt.an" ∧ N ≤ st0.wlen "pt.af" ∧ N ≤ st0.wlen "pt.al" ∧
      N ≤ st0.wlen "pt.nx" ∧ N ≤ st0.wlen "fp.inS" ∧ N ≤ st0.wlen "fp.inQ" ∧ N ≤ st0.wlen "pt.as")
    (hPl : (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PT" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PF" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PL" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PN")
    (hGl : 2 * (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.GV" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.GO" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.GL")
    (hcapT : ∀ t (ht : t < trees.length), st0.wa "fp.toff" t + trees[t].ord.length < st0.cap)
    (hcapK : 2 * k < st0.cap) (hcapS : 2 * (trees.map (fun T => T.ord.length)).sum + 2 < st0.cap)
    (hkm : st0.w "pt.km1" = k - 1)
    (hSb : BitRep st0 "fp.inS" S N) (hQb : BitRep st0 "fp.inQ" Q N) (hA0 : BitRep st0 "pt.as" ∅ N) :
    Runs ops ptProg st0 (fun st' =>
      GrpOut st' (makePivots S Q (forestPieces k trees)) ∧ BitRep st' "pt.as" ∅ N ∧
      (∀ arr j, arr ∉ ptOut → st'.wa arr j = st0.wa arr j) ∧
      (∀ y, y ∉ ptRegs → st'.w y = st0.w y) ∧ st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧
      st'.cost ≤ st0.cost + 170 * (trees.map (fun T => T.ord.length)).sum + 10) := by
  classical
  have hpf := hF.pf
  have hpcsl : (forestPieces k trees).length ≤ (trees.map (fun T => T.ord.length)).sum :=
    forestPieces_length_le hk trees hpf
  have hpcsT : ((forestPieces k trees).map List.length).sum ≤ 2 * (trees.map (fun T => T.ord.length)).sum :=
    forestPieces_total_le hk trees hpf
  have htl : trees.length ≤ (trees.map (fun T => T.ord.length)).sum := trees_length_le_sum hpf
  have hfit0 : fit st0.cap 0 = some 0 := fit_of_lt (by omega)
  -- `pt.t := 0; pt.np := 0`
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0]) ?_
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0]) ?_
  generalize hs1 : (((st0.setW "pt.t" 0).charge 1).setW "pt.np" 0).charge 1 = st1
  have h1wa : st1.wa = st0.wa := by rw [← hs1]; rfl
  have h1len : st1.wlen = st0.wlen := by rw [← hs1]; rfl
  have h1cap : st1.cap = st0.cap := by rw [← hs1]; rfl
  have h1cost : st1.cost = st0.cost + 2 := by rw [← hs1]; simp
  have h1w : ∀ y, y ≠ "pt.t" → y ≠ "pt.np" → st1.w y = st0.w y := by
    intro y h1 h2; rw [← hs1]; simp [h1, h2]
  have h1t : st1.w "pt.t" = 0 := by rw [← hs1]; simp
  have h1np : st1.w "pt.np" = 0 := by rw [← hs1]; simp
  have hF1 : ForestAt st1 trees :=
    ⟨by rw [h1w _ (by decide) (by decide)]; exact hF.nt, by rw [h1len]; exact hF.offl,
      by rw [h1wa, h1len]; exact hF.seg, by rw [h1wa]; exact hF.par, hF.pf, hF.disj⟩
  -- the forest loop
  apply runs_seq
  refine Runs.mono (forestLoop_spec (ops := ops) (st0 := st1) hk hF1
    (fun T hT x hx => by
      rw [h1len]; have := hN T hT x hx
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩)
    (by rw [h1len]; exact hPl) (by rw [h1wa, h1cap]; exact hcapT) (by rw [h1cap]; exact hcapK)
    (by rw [h1cap]; omega) (by rw [h1w _ (by decide) (by decide)]; exact hkm)
    (c0 := st1.cost + (trees.map (fun T => 40 * T.ord.length + 40)).sum) trees.length st1
    ⟨le_rfl, by rw [h1t, Nat.sub_self], by rw [Nat.sub_self, List.take_zero]; intro g hg; simp [forestPieces] at hg,
      by rw [h1np, Nat.sub_self, List.take_zero]; simp [forestPieces],
      fun j _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl,
      by rw [Nat.sub_self, List.drop_zero]⟩) ?_
  rintro st2 ⟨hPR2, hnp2, -, harr2, hreg2, hlen2, hcap2, hcost2⟩
  -- `pt.g := 0; pt.ng := 0; pt.gv := 0`
  have hfit0' : fit st2.cap 0 = some 0 := by rw [hcap2, h1cap]; exact hfit0
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0']) ?_
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0']) ?_
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0']) ?_
  generalize hs3 : (((((st2.setW "pt.g" 0).charge 1).setW "pt.ng" 0).charge 1).setW "pt.gv" 0).charge 1 = st3
  have h3wa : st3.wa = st2.wa := by rw [← hs3]; rfl
  have h3len : st3.wlen = st0.wlen := by rw [← hs3, ← h1len, ← hlen2]; rfl
  have h3cap : st3.cap = st0.cap := by rw [← hs3, ← h1cap, ← hcap2]; rfl
  have h3cost : st3.cost = st2.cost + 3 := by rw [← hs3]; simp
  have h3w : ∀ y, y ≠ "pt.g" → y ≠ "pt.ng" → y ≠ "pt.gv" → st3.w y = st2.w y := by
    intro y h1 h2 h3; rw [← hs3]; simp [h1, h2, h3]
  have h3g : st3.w "pt.g" = 0 := by rw [← hs3]; simp
  have h3ng : st3.w "pt.ng" = 0 := by rw [← hs3]; simp
  have h3gv : st3.w "pt.gv" = 0 := by rw [← hs3]; simp
  -- arrays outside the partition arrays are those of `st0`
  have h3out : ∀ arr j, arr ∉ ptArrs → st3.wa arr j = st0.wa arr j := by
    intro arr j h; rw [h3wa, harr2 arr j h, h1wa]
  have hSb3 : BitRep st3 "fp.inS" S N := fun x hx => by rw [h3out _ _ (by decide)]; exact hSb x hx
  have hQb3 : BitRep st3 "fp.inQ" Q N := fun x hx => by rw [h3out _ _ (by decide)]; exact hQb x hx
  have hA3 : BitRep st3 "pt.as" ∅ N := fun x hx => by rw [h3out _ _ (by decide)]; exact hA0 x hx
  have hnd : ∀ F ∈ forestPieces k trees, F.Nodup := forestPieces_nodup hk hpf
  have hNp : ∀ F ∈ forestPieces k trees, ∀ x ∈ F, x < N := by
    intro F hF x hx
    obtain ⟨T, hT, hxT⟩ := forestPieces_mem hpf F hF x hx
    exact hN T hT x hxT
  -- MakePivots
  apply runs_seq
  refine Runs.mono (mpLoop_spec (ops := ops) (st0 := st3) (S := S) (Q := Q) (N := N)
    (PiecesRep.frame_wa hPR2 h3wa) hnd hNp
    (by rw [h3w _ (by decide) (by decide) (by decide)]; exact hnp2)
    (by rw [h3len]; exact ⟨by omega, by omega, by omega⟩) hSb3 hQb3
    (by rw [h3len]; exact ⟨hNl.2.2.2.2.2.1, hNl.2.2.2.2.2.2.1, hNl.2.2.2.2.2.2.2, hNl.2.2.2.2.1⟩)
    (by rw [h3len]; omega) (by rw [h3len]; exact ⟨by omega, by omega⟩) (by rw [h3cap]; exact ⟨by omega, by omega⟩)
    (c0 := st3.cost + ((forestPieces k trees).map (fun F => 16 * F.length + 42)).sum)
    (forestPieces k trees).length st3
    ⟨le_rfl, by rw [h3g, Nat.sub_self], by rw [Nat.sub_self, List.take_zero]; exact ⟨h3ng, h3gv, fun j h => by simp at h⟩,
      by rw [Nat.sub_self, List.take_zero]; exact hA3, fun _ _ _ _ _ _ => rfl, fun _ _ => rfl, rfl, rfl,
      by rw [Nat.sub_self, List.drop_zero]⟩) ?_
  rintro st4 ⟨hG4, hA4, harr4, hreg4, hlen4, hcap4, hcost4⟩
  -- `pt.j := 0`
  have hfit0'' : fit st4.cap 0 = some 0 := by rw [hcap4, h3cap]; exact hfit0
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0'']) ?_
  generalize hs5 : (st4.setW "pt.j" 0).charge 1 = st5
  have h5wa : st5.wa = st4.wa := by rw [← hs5]; rfl
  have h5len : st5.wlen = st0.wlen := by rw [← hs5, ← h3len, ← hlen4]; rfl
  have h5cap : st5.cap = st0.cap := by rw [← hs5, ← h3cap, ← hcap4]; rfl
  have h5cost : st5.cost = st4.cost + 1 := by rw [← hs5]; simp
  have h5w : ∀ y, y ≠ "pt.j" → st5.w y = st4.w y := by intro y h; rw [← hs5]; simp [h]
  have h5j : st5.w "pt.j" = 0 := by rw [← hs5]; simp
  -- the grouped vertices
  set Gs := makePivots S Q (forestPieces k trees) with hGs
  have hG5 : GrpOut st5 Gs := GrpOut.congr hG4 (h5w _ (by decide)) (h5w _ (by decide))
    (fun j => by rw [h5wa]) (fun j => by rw [h5wa]) (fun j => by rw [h5wa])
  have hLlen : Gs.flatten.length = (Gs.map List.length).sum := List.length_flatten
  have hGtot : (Gs.map List.length).sum ≤ ((forestPieces k trees).map List.length).sum :=
    mp_total_le S Q (forestPieces k trees)
  have hseg5 : SegAt st5 "pt.GV" 0 Gs.flatten :=
    segAt_flatten Gs 0 (fun j hj => by rw [Nat.zero_add]; exact (hG5.2.2 j hj).2.2)
  have hLN : ∀ x ∈ Gs.flatten, x < N := by
    intro x hx
    obtain ⟨g, hg, hxg⟩ := List.mem_flatten.mp hx
    obtain ⟨-, -, -, hsmall, -⟩ := makePivots_spec (S := S) (Q := Q) (forestPieces k trees)
    obtain ⟨F, hF, hgF⟩ := hsmall g hg
    exact hNp F hF x (hgF x hxg)
  -- the assigned set is the set of grouped vertices
  have hAeq : (forestPieces k trees).foldl (mpStep S Q) ([], ∅) =
      (Gs, ((forestPieces k trees).foldl (mpStep S Q) ([], ∅)).2) := rfl
  have hAsub : ((forestPieces k trees).foldl (mpStep S Q) ([], ∅)).2 \ Gs.flatten.toFinset = ∅ := by
    ext x
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.notMem_empty, iff_false, not_and, not_not]
    intro hx
    obtain ⟨g, hg, hxg⟩ := ((mpInv_fold S Q (forestPieces k trees)).assigned x).mp hx
    exact List.mem_flatten.mpr ⟨g, hg, hxg⟩
  -- the clearing loop
  refine Runs.mono (clrLoop_spec (ops := ops) (st0 := st5) (L := Gs.flatten)
    (A := ((forestPieces k trees).foldl (mpStep S Q) ([], ∅)).2) (N := N)
    hseg5 (by rw [h5w _ (by decide), hG4.2.1, hLlen]) (by rw [h5len, hLlen]; omega) hLN
    (by rw [h5len]; exact hNl.2.2.2.2.2.2.2) (by rw [h5cap, hLlen]; omega)
    (c0 := st5.cost + 4 * Gs.flatten.length) Gs.flatten.length st5
    ⟨le_rfl, by rw [h5j, Nat.sub_self], by
      rw [Nat.sub_self, List.take_zero, List.toFinset_nil, Finset.sdiff_empty]
      intro x hx; rw [h5wa]; exact hA4 x hx,
      fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, le_rfl⟩) ?_
  rintro st6 ⟨hA6, harr6, hreg6, hlen6, hcap6, hcost6⟩
  rw [hAsub] at hA6
  refine ⟨GrpOut.congr hG5 (hreg6 _ (by decide) (by decide)) (hreg6 _ (by decide) (by decide))
      (fun j => harr6 _ _ (by decide)) (fun j => harr6 _ _ (by decide)) (fun j => harr6 _ _ (by decide)),
    hA6, ?_, ?_, by rw [hlen6, h5len], by rw [hcap6, h5cap], ?_⟩
  · intro arr j harr
    have h1 : arr ∉ ptArrs := fun h => harr (List.mem_append_left _ h)
    have h2 : arr ≠ "pt.as" := fun h => harr (List.mem_append_right _ (by simp [h]))
    have h3 : arr ≠ "pt.GV" := fun h => harr (List.mem_append_right _ (by simp [h]))
    have h4 : arr ≠ "pt.GO" := fun h => harr (List.mem_append_right _ (by simp [h]))
    have h5 : arr ≠ "pt.GL" := fun h => harr (List.mem_append_right _ (by simp [h]))
    rw [harr6 arr j h2, h5wa, harr4 arr j h2 h3 h4 h5, h3out arr j h1]
  · intro y hy
    have hyF : y ∉ forestRegs := fun h => hy (List.mem_append_left _ (List.mem_append_left _ h))
    have hyM : y ∉ mpRegs := fun h => hy (List.mem_append_left _ (List.mem_append_right _ h))
    have hyj : y ≠ "pt.j" := fun h => hy (List.mem_append_right _ (by simp [h]))
    have hyx : y ≠ "pt.x" := fun h => hyM (by simp [mpRegs, h])
    have hyg : y ≠ "pt.g" := fun h => hyM (by simp [mpRegs, h])
    have hyng : y ≠ "pt.ng" := fun h => hyM (by simp [mpRegs, h])
    have hygv : y ≠ "pt.gv" := fun h => hyM (by simp [mpRegs, h])
    have hyt : y ≠ "pt.t" := fun h => hyF (by simp [forestRegs, h])
    have hynp : y ≠ "pt.np" := fun h => hyF (by simp [forestRegs, treeRegs, h])
    rw [hreg6 y hyx hyj, h5w y hyj, hreg4 y hyM, h3w y hyg hyng hygv, hreg2 y hyF, h1w y hyt hynp]
  · have e1 := sum_map_affine trees (fun T => T.ord.length) 40 40
    have e2 := sum_map_affine (forestPieces k trees) List.length 16 42
    omega

end Frontier.CHD.PartitionRAM
