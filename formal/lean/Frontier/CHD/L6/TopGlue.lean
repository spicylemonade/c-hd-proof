import Frontier.CHD.L6.SpineTop
import Frontier.CHD.SpineLoop
import Frontier.CHD.SynFrame

/-!
# The top-level call from agent-08's level contract (agent-10)

`TopInOf DLf PIf body ps`: the top-call invariant is agent-08's `RamSpine.CallIn` at level `LF`
with the top-level arguments (`Blow = initLabels src src`, `B = ⊤`, `S = {src}`,
`d = initLabels src`, no deleted edges, the empty global `D` state), plus the procedure table.

`callSpec_of_ramSpine`: agent-08's `RamSpine.CallSpec … (LF cn cm)` (the level-induction result at
the top level) gives the top-level `L6.CallSpec`, provided no statement of the program text writes
L6's `gKeep`/`gRep` or `coreTop`'s saved `core.*` registers (the footprint conditions `hfoot`,
decidable on the concrete program; the frame itself comes from `Runs.frame`).
NON-GATE (composition).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

/-- The per-level parameter of `dlOps` (ignored by it). -/
def Tz : ℕ → ℕ := fun _ => 0

/-- **The top-call invariant** from agent-08's `CallIn` at level `LF`. -/
def TopInOf (DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz)
    (PIf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.PhiI (Finset (Fin H.m)))
    (body : Stmt) (ps : List Stmt) : TopInv :=
  fun H src cn cm c0 r => r.procs = ps ∧ MasterIn H src cn cm ∧ (DLf H src cn cm).use r ≤ 2 ∧
    ∃ Ds : ℕ → BM.DStrM H src,
    RamSpine.CallIn (DLf H src cn cm) (PIf H src cn cm).PhiR (CostSkeleton.LF cn cm) body
      (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm)) r (CostSkeleton.LF cn cm)
      (BM.initLabels src src) ⊤ {src} (BM.initLabels src) ∅ BM.DGl.init Ds (H0 (G := H)) c0

/-- The footprint conditions of the spine program (decidable on the concrete text). -/
structure SpineFoot (ps : List Stmt) : Prop where
  keep : "gKeep" ∉ fWA ps (call pBmssp)
  rep : "gRep" ∉ fWA ps (call pBmssp)
  n : "core.n" ∉ fWR ps (call pBmssp)
  s : "core.s" ∉ fWR ps (call pBmssp)
  m : "core.m" ∉ fWR ps (call pBmssp)

/-- **The top-level `CallSpec` from agent-08's level contract at `LF`.** -/
theorem callSpec_of_ramSpine {P : ℕ → ℕ → CostPar}
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {PIf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.PhiI (Finset (Fin H.m))}
    {body : Stmt} {ps : List Stmt} {K Kpol Dp : ℕ} {Slf : ℕ → ℕ → ℕ} {Sbf : ℕ → ℕ → ℕ → ℕ}
    (Km : ℝ) (hSb : ∀ cn cm, 1 ≤ Sbf cn cm (CostSkeleton.LF cn cm))
    (hSl : ∀ n m, Slf n m ≤ Kpol * (n + m + 2) ^ Dp)
    (hucap : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      2 + 2 * (Km * GateCCalc.Tchd cn cm) ≤ ((DLf H src cn cm).ucap : ℝ))
    (hcall : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIf H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) (CostSkeleton.LF cn cm))
    (hfoot : SpineFoot ps) :
    CallSpec P (TopInOf DLf PIf body ps) K 0 Kpol Km Dp := by
  intro H src cn cm c0 r hTop hbud hmas
  obtain ⟨hps, hMI, hUse0, Ds, hIn⟩ := hTop
  have hS : ∀ x ∈ ({src} : Finset (Fin H.n)), BM.initLabels src src ≤ dis (s := src) x := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact le_of_eq BM.initLabels_source
  have hKI : DB.KeyInj (BM.DGl.init (G := H) (s := src)).L (BM.kof H src) := by
    intro v i a h; simp [BM.DGl.init] at h
  have hL : ∀ v i a, (BM.DGl.init (G := H) (s := src)).L v = some (i, a) → (⊤ : WLab H src) ≤ a := by
    intro v i a h; simp [BM.DGl.init] at h
  have hbudN : ∀ res φ' g' lg, BM.BMSSPD H src (BM.dlOps H src)
      (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb Tz
      (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
      (BM.initLabels src src) ⊤ {src} (BM.initLabels src) ∅ BM.DGl.init res φ' g' lg →
      r.cost + K * lg.cost + Slf cn cm ≤ c0 + r.cap := by
    intro res φ' g' lg hrel
    have h := hbud Tz (BM.initLabels src src) le_rfl res φ' g' lg hrel
    have hS : ((Slf cn cm : ℕ) : ℝ) ≤ (Kpol : ℝ) * ((cn : ℝ) + cm + 2) ^ Dp := by
      exact_mod_cast hSl cn cm
    have h' : ((r.cost + K * lg.cost + Slf cn cm : ℕ) : ℝ) ≤ ((c0 + r.cap : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  have huseN : ∀ res φ' g' lg, BM.BMSSPD H src (BM.dlOps H src)
      (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb Tz
      (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
      (BM.initLabels src src) ⊤ {src} (BM.initLabels src) ∅ BM.DGl.init res φ' g' lg →
      (DLf H src cn cm).use r + 2 * lg.cost ≤ (DLf H src cn cm).ucap := by
    intro res φ' g' lg hrel
    have hm := hmas Tz (BM.initLabels src src) le_rfl res φ' g' lg hrel
    have hu := hucap H src cn cm hMI
    have hu0 : ((DLf H src cn cm).use r : ℝ) ≤ 2 := by exact_mod_cast hUse0
    have h' : (((DLf H src cn cm).use r + 2 * lg.cost : ℕ) : ℝ) ≤ ((DLf H src cn cm).ucap : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  refine ((hcall H src cn cm hMI r (BM.initLabels src src) ⊤ {src} (BM.initLabels src) ∅
    BM.DGl.init Ds (H0 (G := H)) c0 BM.callPre_top (delInv_empty H src) hS le_top hKI hL
    (by rw [Finset.card_singleton]; exact hSb cn cm) hIn hbudN huseN).frame hps).mono ?_
  rintro r' ⟨⟨res, φ', g', lg, H', hrel, -, hOut, -, hc2, -⟩, hU⟩
  refine ⟨Tz, BM.initLabels src src, res, φ', g', lg, H', c0, le_rfl, hrel, hOut.lab, ?_, ?_⟩
  · exact ⟨hU.warr _ hfoot.keep, hU.warr _ hfoot.rep, hU.wreg _ hfoot.n, hU.wreg _ hfoot.s,
      hU.wreg _ hfoot.m, hU.cap⟩
  · have h : ((r'.cost : ℕ) : ℝ) ≤ ((r.cost + K * lg.cost : ℕ) : ℝ) := by exact_mod_cast hc2
    push_cast at h
    linarith

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.callSpec_of_ramSpine
