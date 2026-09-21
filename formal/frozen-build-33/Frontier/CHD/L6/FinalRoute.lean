import Frontier.CHD.L6.ProFinal
import Frontier.CHD.L6.Route

/-!
# The C-HD route with the concrete prologue (agent-10)

`chdTarget_of_spineParts`: the frozen Gate-C target `CHDTarget F` follows from
* agent-08's level contract at the top level (`RamSpine.CallSpec … (LF cn cm)`, the level
  induction over `BMSSPD`), with an `|S|` bound `Sbf` admitting `|{src}| = 1`;
* the two allocation hooks of the prologue (`HookSpec`: B-L2's FindPivots state `PhiR ∅`, B-L3's
  `D` layer `DR` at `LF + 1`) and their footprint compatibilities;
* the procedure table (`ps[P_bmssp] = body`, `SpineFoot ps`), admissible cost parameters `GoodP`,
  and a word exponent `e ≥ 32` large enough for the constants.
Everything else (dispatch, L6, the core wrapper, the prologue `spinePro`, exactness, the master
cost theorem, budgets) is proved.  NON-GATE (composition; the listed hypotheses are open).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

theorem chdTarget_of_spineParts (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (body : Stmt)
    (hps : ps[RamSpine.P_bmssp]? = some body) (hfoot : SpineFoot ps)
    {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {PIf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.PhiI (Finset (Fin H.m))}
    {fpPro dPro : Stmt} {fwa fva fwr fvr dwa dva dwr dvr : List String} {Kf Kd : ℕ}
    (hFP : HookSpec e ps fpPro (fun H src cn cm r => (PIf H src cn cm).PhiR r ∅) fwa fva fwr fvr Kf)
    (hD : HookSpec e ps dPro (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
        (DLf H src cn cm).DR r (H0 (G := H)) BM.DGl.init Ds (CostSkeleton.LF cn cm + 1)) ∧
        (DLf H src cn cm).use r ≤ 2)
        dwa dva dwr dvr Kd)
    (hPd : ∀ H src cn cm, (∀ a ∈ (PIf H src cn cm).pWA, a ∉ dwa) ∧
      (∀ a ∈ (PIf H src cn cm).pWR, a ∉ dwr))
    (hPb : ∀ H src cn cm, (∀ a ∈ (PIf H src cn cm).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (PIf H src cn cm).pWR, a ∉ blowWR ++ ["lvl"]))
    {K Kpol : ℕ} {Slf : ℕ → ℕ → ℕ} {Sbf : ℕ → ℕ → ℕ → ℕ} {Dp : ℕ} (hDp : 2 ≤ Dp)
    (hSb : ∀ cn cm, 1 ≤ Sbf cn cm (CostSkeleton.LF cn cm))
    (hSl : ∀ n m, Slf n m ≤ Kpol * (n + m + 2) ^ Dp)
    (hucap : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      2 + 2 * (kmaster ch ce cb * GateCCalc.Tchd cn cm) ≤ ((DLf H src cn cm).ucap : ℝ))
    (hcall : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIf H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) (CostSkeleton.LF cn cm))
    (hbig : 12 + ((K : ℝ) + (13000 + 34 * ((Kf : ℝ) + Kd)) + 0) * (kmaster ch ce cb + 1) +
      |(0 : ℝ)| + |(Kpol : ℝ)| ≤ (4 : ℝ) ^ (e + 1 - Dp)) :
    GateCTarget.CHDTarget GateCCalc.F :=
  chdTarget_of_parts e he ps (spinePro fpPro dPro) hP (TopIn := TopInOf DLf PIf body ps)
    (Kp := 13000 + 34 * ((Kf : ℝ) + Kd)) (K := (K : ℝ)) (K0 := 0) (Kpol := (Kpol : ℝ))
    (Dp := Dp) hDp (by positivity) (Nat.cast_nonneg _) le_rfl hbig
    (proSpec_spinePro he hps hFP hD hPd hPb)
    (callSpec_of_ramSpine (kmaster ch ce cb) hSb hSl hucap hcall hfoot)

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.chdTarget_of_spineParts
