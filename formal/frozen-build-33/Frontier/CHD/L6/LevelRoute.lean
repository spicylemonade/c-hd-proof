import Frontier.CHD.L6.FinalRoute
import Frontier.CHD.L6.FPHook
import Frontier.CHD.L6.NamedWitness

/-!
# The C-HD route by levels (agent-10)

`callSpec_of_levels`: agent-08's level contract at every level `l ≤ LF` follows from the base case
(`CallSpec … 0`, agent-03) and the level step (`CallSpec … l → CallSpec … (l+1)` for `l < LF`,
agent-01's level body with agent-08/06's iteration), by induction on the level.

`chdTarget_of_levels`: the frozen Gate-C target from the base case, the level step, B-L3's
`D`-layer hook, and the decidable side conditions.  The FindPivots hook is discharged
(`fpHook`, agent-09's `fpAlloc_phiR`) with `PIf := PIfOf P`.  NON-GATE (composition).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

theorem callSpec_of_levels {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ Ω : Type}
    {DL : RamSpine.DLayer G s T} {PhiR : State ℝ≥0 → Φ → Prop} {Inv : Φ → Prop}
    {FPC : BM.FPRelC G s Φ Ω} {DCb : BM.DCost} {Mf τ : ℕ → ℕ} {LF : ℕ} {body : Stmt}
    {K Sl : ℕ} {Sb : ℕ → ℕ}
    (h0 : RamSpine.CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb 0)
    (hs : ∀ l, l < LF → RamSpine.CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb l →
      RamSpine.CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb (l + 1)) :
    ∀ l ≤ LF, RamSpine.CallSpec DL PhiR Inv FPC DCb Mf τ LF body K Sl Sb l := by
  intro l
  induction l with
  | zero => intro _; exact h0
  | succ l ih => intro hl; exact hs l (by omega) (ih (by omega))

/-- **The C-HD target by levels.** -/
theorem chdTarget_of_levels (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (body : Stmt)
    (hps : ps[RamSpine.P_bmssp]? = some body) (hfoot : SpineFoot ps)
    {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {dPro : Stmt} {dwa dva dwr dvr : List String} {Kd : ℕ}
    (hD : HookSpec e ps dPro (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
        (DLf H src cn cm).DR r (H0 (G := H)) BM.DGl.init Ds (CostSkeleton.LF cn cm + 1)) ∧
        (DLf H src cn cm).use r ≤ 2)
        dwa dva dwr dvr Kd)
    (hPd : ∀ H src cn cm, (∀ a ∈ (PIfOf P H src cn cm).pWA, a ∉ dwa) ∧
      (∀ a ∈ (PIfOf P H src cn cm).pWR, a ∉ dwr))
    (hPb : ∀ H src cn cm, (∀ a ∈ (PIfOf P H src cn cm).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (PIfOf P H src cn cm).pWR, a ∉ blowWR ++ ["lvl"]))
    {K Kpol : ℕ} {Slf : ℕ → ℕ → ℕ} {Sbf : ℕ → ℕ → ℕ → ℕ} {Dp : ℕ} (hDp : 2 ≤ Dp)
    (hSb : ∀ cn cm, 1 ≤ Sbf cn cm (CostSkeleton.LF cn cm))
    (hSl : ∀ n m, Slf n m ≤ Kpol * (n + m + 2) ^ Dp)
    (hucap : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      2 + 2 * (kmaster ch ce cb * GateCCalc.Tchd cn cm) ≤ ((DLf H src cn cm).ucap : ℝ))
    (h0 : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) 0)
    (hs : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) l →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) (l + 1))
    (hbig : 12 + ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster ch ce cb + 1) +
      |(0 : ℝ)| + |(Kpol : ℝ)| ≤ (4 : ℝ) ^ (e + 1 - Dp)) :
    GateCTarget.CHDTarget GateCCalc.F :=
  chdTarget_of_spineParts e he ps body hps hfoot hP (PIf := PIfOf P) (fpHook e he ps P) hD hPd hPb
    hDp hSb hSl hucap (fun H src cn cm hMI => callSpec_of_levels (h0 H src cn cm hMI) (hs H src cn cm hMI)
      (CostSkeleton.LF cn cm) le_rfl) hbig

/-- **Gate C from the level contracts** (the shape of the final theorem `chd_gateC`). -/
theorem gateC_of_levels (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (body : Stmt)
    (hps : ps[RamSpine.P_bmssp]? = some body) (hfoot : SpineFoot ps)
    {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {dPro : Stmt} {dwa dva dwr dvr : List String} {Kd : ℕ}
    (hD : HookSpec e ps dPro (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
        (DLf H src cn cm).DR r (H0 (G := H)) BM.DGl.init Ds (CostSkeleton.LF cn cm + 1)) ∧
        (DLf H src cn cm).use r ≤ 2)
        dwa dva dwr dvr Kd)
    (hPd : ∀ H src cn cm, (∀ a ∈ (PIfOf P H src cn cm).pWA, a ∉ dwa) ∧
      (∀ a ∈ (PIfOf P H src cn cm).pWR, a ∉ dwr))
    (hPb : ∀ H src cn cm, (∀ a ∈ (PIfOf P H src cn cm).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (PIfOf P H src cn cm).pWR, a ∉ blowWR ++ ["lvl"]))
    {K Kpol : ℕ} {Slf : ℕ → ℕ → ℕ} {Sbf : ℕ → ℕ → ℕ → ℕ} {Dp : ℕ} (hDp : 2 ≤ Dp)
    (hSb : ∀ cn cm, 1 ≤ Sbf cn cm (CostSkeleton.LF cn cm))
    (hSl : ∀ n m, Slf n m ≤ Kpol * (n + m + 2) ^ Dp)
    (hucap : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      2 + 2 * (kmaster ch ce cb * GateCCalc.Tchd cn cm) ≤ ((DLf H src cn cm).ucap : ℝ))
    (h0 : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) 0)
    (hs : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) l →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) (l + 1))
    (hbig : 12 + ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster ch ce cb + 1) +
      |(0 : ℝ)| + |(Kpol : ℝ)| ≤ (4 : ℝ) ^ (e + 1 - Dp)) :
    Frontier.GateC :=
  GateCTarget.chdTarget_F_imp_gateC
    (chdTarget_of_levels e he ps body hps hfoot hP hD hPd hPb hDp hSb hSl hucap h0 hs hbig)

/-- **The named C-HD witness, by levels**: the explicit program
`chdProg e ps (coreTop (spineOf (spinePro BL2.fpAlloc dPro)))` is exact and runs within a constant
times `Tdisp F n m`, from the same hypotheses as `chdTarget_of_levels`. -/
theorem chdProg_of_levels (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (body : Stmt)
    (hps : ps[RamSpine.P_bmssp]? = some body) (hfoot : SpineFoot ps)
    {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb)
    {DLf : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), RamSpine.DLayer H src Tz}
    {dPro : Stmt} {dwa dva dwr dvr : List String} {Kd : ℕ}
    (hD : HookSpec e ps dPro (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
        (DLf H src cn cm).DR r (H0 (G := H)) BM.DGl.init Ds (CostSkeleton.LF cn cm + 1)) ∧
        (DLf H src cn cm).use r ≤ 2)
        dwa dva dwr dvr Kd)
    (hPd : ∀ H src cn cm, (∀ a ∈ (PIfOf P H src cn cm).pWA, a ∉ dwa) ∧
      (∀ a ∈ (PIfOf P H src cn cm).pWR, a ∉ dwr))
    (hPb : ∀ H src cn cm, (∀ a ∈ (PIfOf P H src cn cm).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (PIfOf P H src cn cm).pWR, a ∉ blowWR ++ ["lvl"]))
    {K Kpol : ℕ} {Slf : ℕ → ℕ → ℕ} {Sbf : ℕ → ℕ → ℕ → ℕ} {Dp : ℕ} (hDp : 2 ≤ Dp)
    (hSb : ∀ cn cm, 1 ≤ Sbf cn cm (CostSkeleton.LF cn cm))
    (hSl : ∀ n m, Slf n m ≤ Kpol * (n + m + 2) ^ Dp)
    (hucap : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      2 + 2 * (kmaster ch ce cb * GateCCalc.Tchd cn cm) ≤ ((DLf H src cn cm).ucap : ℝ))
    (h0 : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) 0)
    (hs : ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
      ∀ l : ℕ, l < CostSkeleton.LF cn cm →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) l →
      RamSpine.CallSpec (DLf H src cn cm) (PIfOf P H src cn cm).PhiR (DelInv H src)
        (fpC H src (outL H) (CostSkeleton.kF cn cm) (P cn cm).hins (P cn cm).hext) (P cn cm).DCb
        (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm)) (CostSkeleton.LF cn cm)
        body K (Slf cn cm) (Sbf cn cm) (l + 1))
    (hbig : 12 + ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster ch ce cb + 1) +
      |(0 : ℝ)| + |(Kpol : ℝ)| ≤ (4 : ℝ) ^ (e + 1 - Dp)) :
    let core := coreTop (spineOf (spinePro BL2.fpAlloc dPro))
    let Kc : ℝ := ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) * (kmaster ch ce cb + 1) + 250
    (chdProg e ps core).Exact ∧ ∀ (G : Graph) (s : Fin G.n),
      (chdProg e ps core).RunsWithin G s
        ((bodyC Kc + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m) := by
  intro core Kc
  have hKs : (0 : ℝ) ≤ (K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0 := by positivity
  have hsp := spineSpec_of_parts (e := e) (ps := ps) (pro := spinePro BL2.fpAlloc dPro) (P := P)
    (Kp := 13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) (K := (K : ℝ)) (K0 := 0) (Kpol := (Kpol : ℝ))
    (Km := kmaster ch ce cb) (by positivity) (Nat.cast_nonneg _) le_rfl
    (proSpec_spinePro he hps (fpHook e he ps P) hD hPd hPb)
    (callSpec_of_ramSpine (kmaster ch ce cb) hSb hSl hucap (fun H src cn cm hMI => callSpec_of_levels
      (h0 H src cn cm hMI) (hs H src cn cm hMI) (CostSkeleton.LF cn cm) le_rfl) hfoot)
  have hcore := coreSpec_of_spine e he ps (spineOf (spinePro BL2.fpAlloc dPro)) P
    ((K : ℝ) + (13000 + 34 * ((100 : ℕ) + (Kd : ℝ))) + 0) 0 (Kpol : ℝ) (kmaster ch ce cb) Dp hDp hKs
    (kmaster_nonneg ch ce cb) hbig hsp (masterSpec_of_good hP)
  exact chdProg_exact_within e (by omega) ps core Kc
    (by have := mul_nonneg hKs (show (0 : ℝ) ≤ kmaster ch ce cb + 1 by
      have := kmaster_nonneg ch ce cb; linarith); linarith) hcore

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.chdTarget_of_levels
#print axioms Frontier.CHD.L6.chdProg_of_levels
#print axioms Frontier.CHD.L6.gateC_of_levels
