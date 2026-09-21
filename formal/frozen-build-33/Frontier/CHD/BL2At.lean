import Frontier.CHD.BL2CallInst
import Frontier.CHD.BL2Phi
import Frontier.CHD.SpineLoop

/-!
# Frontier.CHD.BL2At — B-L2: the FindPivots-HD call of the level-`lvl` spine procedure
(owner agent-09, NON-GATE)

`fpAt = fpPrep ; fpCallC`: `fp.B := slot B[lvl]` (agent-02's `loadSlot`), `fp.sb := lvl·n`,
`fp.sn := S.len[lvl]`, then the complete FindPivots-HD call (computable form).  `fpAt_spec` is
stated over the facts of agent-08's `CallIn` (label table, slot `B[l]`, `S` row `l`, B-L2's
`phiR`) and ends in an outcome of agent-05's `fpC` for the out-lists `L6.outL G`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2Inst

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.BL2
  Frontier.CHD.PartitionRAM Frontier.CHD.RamLevel Frontier.CHD.LabIInst Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- Preparation of the level-`lvl` FindPivots call. -/
def fpPrep : Stmt :=
  seq (wset "sl.i" (mul (lit 4) (var "lvl")))
  (seq (loadSlot (slotBlk "fp.B") (slotF "fp.B"))
  (seq (wset "fp.sb" (mul (var "lvl") (var "n")))
       (wset "fp.sn" (load "S.len" (var "lvl")))))

/-- **The FindPivots-HD call of the level-`lvl` spine procedure** (closed, computable). -/
def fpAt : Stmt := seq fpPrep fpCallC

/-- Registers written by `fpPrep`. -/
def fpPrepWR : List String :=
  ((["sl.i"] ++ (slotF "fp.B" :: (slotBlk "fp.B").ws)) ++ ["fp.sb"]) ++ ["fp.sn"]
def fpPrepVR : List String := (([] ++ [(slotBlk "fp.B").l]) ++ []) ++ []

/-- A row of vertex ids with members `S` is a duplicate-free list of vertices enumerating `S`. -/
theorem row_vertices {xs : List ℕ} {S : Finset (Fin G.n)}
    (hmem : ∀ x : ℕ, x ∈ xs ↔ ∃ u ∈ S, (u : ℕ) = x) (hnd : xs.Nodup) :
    ∃ SL : List (Fin G.n), SL.map Fin.val = xs ∧ SL.Nodup ∧ ∀ u, u ∈ SL ↔ u ∈ S := by
  have hlt : ∀ x ∈ xs, x < G.n := fun x hx => by
    obtain ⟨u, _, rfl⟩ := (hmem x).mp hx; exact u.2
  refine ⟨xs.pmap (fun x h => (⟨x, h⟩ : Fin G.n)) hlt, ?_, ?_, ?_⟩
  · rw [List.map_pmap]; simp [List.pmap_eq_map]
  · exact hnd.pmap (fun a _ b _ h => by simpa using congrArg Fin.val h)
  · intro u
    rw [List.mem_pmap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, hv, hvx⟩ := (hmem x).mp hx
      have : v = ⟨x, hlt x hx⟩ := Fin.ext hvx
      rw [← this]; exact hv
    · intro hu; exact ⟨u.val, (hmem u.val).mpr ⟨u, hu, rfl⟩, rfl⟩

/-- **The level-`lvl` FindPivots-HD call refines agent-05's `fpC`** over the facts of the spine's
call entry: label table `d0` (`LabAt`, clock origin `c0`), slot `B[l]`, the `S` row `l`, and the
clean FindPivots state `phiR` with deleted edges `Din`. -/
theorem fpAt_spec {c0 k hins hext l : ℕ} (hk2 : 2 ≤ k) (hhext : k ≤ hext)
    (hsort : ∀ u, (L6.outL G u).Pairwise (SortedRel G s))
    {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} (hpre : CallPre B S d0)
    {Din : Finset (Fin G.m)} {H : Fin G.n → ℕ → List (Fin G.m)} {st₀ : State ℝ≥0}
    (hlab : LabAt (s := s) st₀ d0 H c0) (hgr : GraphAt st₀ G) (hmcap : G.m + 2 ≤ st₀.cap)
    (hB : SlotHolds st₀ (RamBaseCase.slotB l) H (vc st₀) B)
    (hBL : SlotLens st₀ (RamBaseCase.slotB l))
    (hS : RamSpine.SetRow st₀ "S" "S.len" l S) (hC : phiR G s k hins hext st₀ Din)
    (hl : st₀.w "lvl" = l) (hn : st₀.w "n" = G.n) (hWlen : l < st₀.wlen "W.len")
    (hrow : (l + 1) * G.n ≤ st₀.wlen "W")
    (hbud : ∀ d1 Dout Q W trees cost,
      FindPivotsC (L6.outL G) k hins hext B S d0 Din d1 Dout Q W trees cost →
      st₀.cost + 9 + CFC (labI (G := G) (s := s) c0) (labX c0) +
        KC (labI (G := G) (s := s) c0) (labX c0) * cost ≤ c0 + st₀.cap)
    (hcap4 : 4 * l + 4 < st₀.cap)
    (hcap : (2 * l + 5) * G.n + st₀.w "fp.ob" + 2 * k + 4 < st₀.cap) :
    Runs realOps fpAt st₀ (fun st' =>
      ∃ (ι' : IState G s) (cost : ℕ) (H' : Fin G.n → ℕ → List (Fin G.m)) (wl : List (Fin G.n)),
        (∀ l' Blow, fpC G s (L6.outL G) k hins hext l' Blow B S d0 Din ι'.d
          (forestGroups S ι'.Q k ι'.trees).length
          (fun j => ((forestGroups S ι'.Q k ι'.trees).get j).toFinset) ι'.Q ι'.W ι'.D
          ⟨lxOf B S d0, ι'.trees, Din, ι'.D⟩ cost) ∧
        LabAt (s := s) st' ι'.d H' c0 ∧ HExt H (vc st₀) H' (vc st') ∧ GraphAt st' G ∧
        WalkInv ι'.d ∧ (∀ v, ι'.d v ≤ d0 v) ∧
        phiR G s k hins hext st' ι'.D ∧
        GrpOut st' ((forestGroups S ι'.Q k ι'.trees).map (List.map Fin.val)) ∧
        wl.Nodup ∧ wl.toFinset = ι'.W ∧ RowRep st' "W" "W.len" G.n l (wl.map Fin.val) ∧
        (∀ j, j ≠ l → st'.wa "W.len" j = st₀.wa "W.len" j) ∧
        (∀ j, (j < l * G.n ∨ (l + 1) * G.n ≤ j) → st'.wa "W" j = st₀.wa "W" j) ∧
        Unchanged st₀ st' ([] ++ fcWA (labI (G := G) (s := s) c0) "S" "fp.LX")
          ([] ++ fcVA (labI (G := G) (s := s) c0) "fp.LX")
          (fpPrepWR ++ fcWR (labI (G := G) (s := s) c0) (labX c0) "fp.LX")
          (fpPrepVR ++ fcVR (labI (G := G) (s := s) c0) (labX c0) "fp.LX") ∧
        st₀.cost ≤ st'.cost ∧
        st'.cost ≤ st₀.cost + 9 + CFC (labI (G := G) (s := s) c0) (labX c0) +
          KC (labI (G := G) (s := s) c0) (labX c0) * cost) := by
  classical
  obtain ⟨xs, hR, hxnd, hxmem⟩ := hS
  obtain ⟨SL, rfl, hSLnd, hSL⟩ := row_vertices hxmem hxnd
  obtain ⟨hRl, hRw, hRlen, hRS, hRarr⟩ := hR
  have hn1 : 1 ≤ G.n := Nat.one_le_iff_ne_zero.mpr (fun h => by have := s.2; omega)
  have hlm : l * G.n ≤ (2 * l + 5) * G.n := Nat.mul_le_mul_right _ (by omega)
  have hsm : (l + 1) * G.n = l * G.n + G.n := Nat.succ_mul l G.n
  have hsm2 : (2 * l + 5) * G.n = 2 * (l * G.n) + 5 * G.n := by ring
  have hSLn : SL.length ≤ G.n := by simpa using hRl
  unfold fpAt fpPrep
  rw [← fpCall_eq_C (G := G) (s := s) c0]
  refine runs_seq ?_
  -- sl.i := 4 lvl
  refine runs_seq (runs_wset (a := 4 * l) (by
    simp only [evalW_mul', evalW_lit', evalW_var, hl, fit_of_lt (show 4 < st₀.cap by omega),
      Option.bind_some, fit_of_lt (show 4 * l < st₀.cap by omega)]) ?_)
  generalize hs1 : (st₀.setW "sl.i" (4 * l)).charge 1 = s1
  have hu1 : Unchanged st₀ s1 [] [] ["sl.i"] [] := by
    rw [← hs1]; exact ((unch_setW st₀ "sl.i" _).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hi1 : s1.w "sl.i" = RamBaseCase.slotB l := by rw [← hs1]; simp [RamBaseCase.slotB]
  have hBL1 : SlotLens s1 (RamBaseCase.slotB l) := by
    rw [← hs1]; exact ⟨hBL.l, hBL.h, hBL.v, hBL.e, hBL.r, hBL.f⟩
  have hB1 : SlotHolds s1 (RamBaseCase.slotB l) H (vc st₀) B := by rw [← hs1]; exact hB
  -- fp.B := slot B[l]
  refine runs_seq ((loadSlot_spec (slotBlk "fp.B") (slotF "fp.B") ⟨by decide⟩ s1 hi1 hBL1
    hB1).mono ?_)
  rintro s2 ⟨hW2, hu2, hc2⟩
  have hu12 := hu1.cat hu2
  have hcap2 : s2.cap = st₀.cap := hu12.cap
  have hlv2 : s2.w "lvl" = l := by rw [hu12.wreg _ (by decide)]; exact hl
  have hn2 : s2.w "n" = G.n := by rw [hu12.wreg _ (by decide)]; exact hn
  -- fp.sb := lvl * n
  refine runs_seq (runs_wset (a := l * G.n) (by
    simp only [evalW_mul', evalW_var, hlv2, hn2, Option.bind_some,
      fit_of_lt (show l * G.n < s2.cap by rw [hcap2]; omega)]) ?_)
  generalize hs3 : (s2.setW "fp.sb" (l * G.n)).charge 1 = s3
  have hu3 : Unchanged s2 s3 [] [] ["fp.sb"] [] := by
    rw [← hs3]; exact ((unch_setW s2 "fp.sb" _).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hu13 := hu12.cat hu3
  have hSlen3 := hu13.warr "S.len" (by decide)
  have hlv3 : s3.w "lvl" = l := by rw [hu13.wreg _ (by decide)]; exact hl
  -- fp.sn := S.len[lvl]
  refine runs_wset (a := SL.length) (by
    simp only [evalW_load', evalW_var, hlv3, Option.bind_some, hSlen3.2, hRlen, if_true,
      hSlen3.1]
    simp [hRS]) ?_
  generalize hs4 : (s3.setW "fp.sn" SL.length).charge 1 = s4
  have hu4 : Unchanged s3 s4 [] [] ["fp.sn"] [] := by
    rw [← hs4]; exact ((unch_setW s3 "fp.sn" _).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hu04 := hu13.cat hu4
  have hcap4' : s4.cap = st₀.cap := hu04.cap
  have hc4 : s4.cost = st₀.cost + 9 := by
    rw [← hs4]; simp only [State.charge_cost, State.setW_cost]; rw [← hs3]
    simp only [State.charge_cost, State.setW_cost]; rw [hc2, ← hs1]; simp
  have hsb4 : s4.w "fp.sb" = l * G.n := by
    rw [← hs4]; simp only [State.charge_w, State.setW_w]; simp; rw [← hs3]; simp
  have hsn4 : s4.w "fp.sn" = SL.length := by rw [← hs4]; simp
  -- the label layer and the clean state at s4
  have hLT4 : (labI (G := G) (s := s) c0).LT s4 d0 (H, vc st₀) :=
    LTp_frame (show LTp c0 st₀ d0 (H, vc st₀) from ⟨hlab, rfl, hgr, hmcap⟩) hu04
      (Disj.nil_left _) (Disj.nil_left _) (by omega)
  have hB4 : (labI (G := G) (s := s) c0).LS s4 "fp.B" B (H, vc st₀) :=
    LSp_frame (show LSp s2 "fp.B" B (H, vc st₀) from hW2) (hu3.cat hu4) (by decide) (by decide)
  have hC4 : FPClean (pinCtx (L6.outL G) k hins hext B (lxOf B S d0)) d0 Din s4 :=
    (phiR_toClean hC (by simpa using hgr.head.1) (fun q => by simpa using hgr.head.2 q q.2) d0).frame
      hu04 (Disj.nil_left _) (by decide)
  have hA4 : ∀ a, a ∈ ["S", "W", "W.len"] → s4.wa a = st₀.wa a ∧ s4.wlen a = st₀.wlen a :=
    fun a ha => hu04.warr a (by simp)
  have hS4 := hA4 "S" (by simp)
  have hWl4 := hA4 "W" (by simp)
  have hWL4 := hA4 "W.len" (by simp)
  have hob4 : s4.w "fp.ob" = st₀.w "fp.ob" := hu04.wreg _ (by decide)
  refine (fpCall_spec (LI := labI (G := G) (s := s) c0) (X := labX c0) (out := L6.outL G) (l := l)
    (fun u e => L6.outL_mem) hsort (fun u => L6.outL_nodup u) (namesL_inst c0) (namesI_inst c0)
    (namesTail_inst c0) (namesCall_inst c0) hk2 hhext hpre hSLnd hSL hLT4 hB4 hC4
    (fun j hj => by
      rw [hS4.1, hsb4]; have := hRarr j (by simpa using hj); rw [this, List.getElem_map])
    (by rw [hsb4, hS4.2]; omega) hsn4
    (by rw [hu04.wreg _ (by decide)]; exact hl) (by rw [hu04.wreg _ (by decide)]; exact hn)
    (by rw [hWL4.2]; exact hWlen) (by rw [hWl4.2]; exact hrow)
    (fun d1 Dout Q W trees cost h => by
      have := hbud _ _ _ _ _ _ h
      have hc0 : (labI (G := G) (s := s) c0).c0 = c0 := rfl
      rw [hc4, hcap4', hc0]; omega)
    (by rw [hsb4, hob4, hcap4']; omega)).mono ?_
  rintro st' ⟨ι', cost, g', wl, hfpC, hLab, hgext, hwalk, hle, hCl, hG, hwnd, hwset, hWR, hoL,
    hoW, hU, hc0', hc'⟩
  obtain ⟨⟨hLA, hvc, hgr', _⟩, _, _⟩ := hLab
  refine ⟨ι', cost, g'.1, wl, hfpC, hLA, ?_, hgr', hwalk, hle, phiR_of_clean hCl, hG, hwnd,
    hwset, hWR, fun j hj => by rw [hoL j hj, hWL4.1], fun j hj => by rw [hoW j hj, hWl4.1],
    (hu04.cat hU).mono (by simp) (by simp) ?_ ?_, by omega, by omega⟩
  · have : vc st' = g'.2 := hvc
    rw [this]; exact hgext
  · intro z hz; simpa [fpPrepWR, List.mem_append, or_assoc] using hz
  · intro z hz; simpa [fpPrepVR, List.mem_append, or_assoc] using hz

end Frontier.CHD.BL2Inst
