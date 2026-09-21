import Frontier.CHD.LabTests

/-!
# LtBiTest — the expansion test `sp.lt := [d px < B_i]` (BM.12; agent-02, NON-GATE)

`ltBi Kb kbf := headLtB "px" spY Kb "sp.yf" kbf "sp.c1" "sp.c2" "sp.lt"`, the bound `B_i` in the
block `Kb`.  `ltBi_spec` is the precise-footprint `Runs` spec (read-only on the label table,
writes `ltW` and the value register `sp.yl`); it instantiates agent-08's `RamSpine.LtI` once
that interface carries a value-register list.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.LabTab Frontier.CHD.MLab
  WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The scratch label block of the expansion test. -/
def spY : LReg := ⟨"sp.yl", "sp.yh", "sp.yv", "sp.ye", "sp.yr"⟩

/-- Word registers written by `ltBi`. -/
def ltW : List String := ["sp.yf", "sp.yh", "sp.yv", "sp.ye", "sp.yr", "sp.c1", "sp.c2", "sp.lt"]

/-- `sp.lt := [d px < B_i]`. -/
def ltBi (Kb : LReg) (kbf : String) : Stmt :=
  headLtB "px" spY Kb "sp.yf" kbf "sp.c1" "sp.c2" "sp.lt"

/-- Register hygiene of the bound block of `ltBi`. -/
structure LtHyg (K : LReg) (kf : String) : Prop where
  w : ∀ a ∈ K.ws ++ [kf], a ∉ ltW ++ ["px"]
  l : K.l ≠ "sp.yl"

open Classical in
/-- **The expansion test.** -/
theorem ltBi_spec {K : LReg} {kf : String} (hK : LtHyg K kf)
    (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (hL : LabAt st d H c0) (v : Fin G.n) (hv : st.w "px" = v) (Bl : WLab G s)
    (hKh : WHolds st K kf H (vc st) Bl) (hcap : 1 < st.cap) :
    Runs realOps (ltBi K kf) st (fun r =>
      r.w "sp.lt" = (if d v < Bl then 1 else 0) ∧ Unchanged st r [] [] ltW ["sp.yl"] ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 22 ∧ LabAt r d H c0 ∧ WHolds r K kf H (vc r) Bl) := by
  have hKw : ∀ a ∈ K.ws, a ∉ "sp.yf" :: spY.ws := fun a ha hm => hK.w a (by simp [ha]) (by
      simp only [spY, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [ltW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have hkf : kf ∉ "sp.yf" :: spY.ws := fun hm => hK.w kf (by simp) (by
      simp only [spY, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [ltW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have hCF : CmpFresh spY K "sp.c1" "sp.c2" :=
    ⟨by decide, by decide, by decide, fun hm => hK.w "sp.c1" (by simp [hm]) (by decide),
      fun hm => hK.w "sp.c2" (by simp [hm]) (by decide)⟩
  have hwp := headLtB_wp "px" spY K "sp.yf" kf "sp.c1" "sp.c2" "sp.lt" ⟨by decide, by decide⟩
    hCF hKw (fun hm => hK.l (by simpa [spY] using hm)) hkf st d H c0 hL v hv Bl hKh hcap
  refine (Frontier.CHD.LabIInst.Runs.cost_ge (wp_sound (ops := realOps) _ _ _ hwp)).mono ?_
  rintro r ⟨⟨h1, h2, h3⟩, h4⟩
  have hU : Unchanged st r [] [] ltW ["sp.yl"] :=
    h2.mono (by simp) (by simp) (by decide) (by simp [spY])
  have hvc : vc (G := G) r = vc st := vc_of_unchanged hU (by simp)
  refine ⟨h1, hU, h4, h3, hL.of_unchanged hU (by simp) (by simp) h4, ?_⟩
  rw [hvc]
  exact hKh.of_unchanged hU (fun a ha hm => hK.w a (by simp [ha]) (List.mem_append_left _ hm))
    (by simpa using hK.l) (fun hm => hK.w kf (by simp) (List.mem_append_left _ hm))

end Frontier.CHD.WinScan
