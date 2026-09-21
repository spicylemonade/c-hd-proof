import Frontier.CHD.DLayerInst
import Frontier.CHD.L6.ProFinal
import Frontier.CHD.SelectRAM
import Frontier.CHD.EntLess

/-!
# `dPro` — the D-layer allocation hook of the spine prologue (owner agent-09, NON-GATE)

`dPro Cw` allocates, once, every array of agent-04's D layer (`DLayerInst.DRI`), sized from the
prologue registers `pr.tn = Tnat cn cm`, `cp.L = LF cn cm`, `n = |V|`:
* use capacity `ucap = Cw · Tnat + 2`, entry pool / block records / stack `ecap = bcap = ucap + 2`;
* level tables of `LF + 2` cells (levels `0..top`, `top = LF + 1`);
* the top-level structure `newC 0 ⊤` at level `top` (`newTopS`, one block id);
* the live-key lists `lk.n / lk.p` (`n + top + 1` self-loops: every list empty);
* the per-level bound arrays `dsl.b*` (flag `0` = bound `⊤`) and `dsl.M` (`M = 0`);
* the select scratch `sel.w` of `6 ecap + 60` cells (agent-05's `pullS_spec`, `hwc` / `swc`).

`dProSpec`: `dPro Cw` is an `L6.HookSpec` whose post is `DRI (dPar Cw cn cm) r H0 DGl.init Ds (LF+1)`
plus `use r = 1`, the procedure-table fact `procs[1] = selBody entLess 1` and the `sel.w` size,
with footprint `dProWA / dProVA / dProWR / []` and cost `≤ (23 Cw + 300)(Tnat + 1)`.
The only numeric condition is `64 Cw + 128 ≤ 4^(e-1)` (word size vs. the literal `Cw`).
-/

open scoped ENNReal NNReal

namespace Frontier.RAM

variable {V : Type}

/-- the text contains no procedure call (allocations allowed) -/
def NoCallT : Stmt → Prop
  | .call _ => False
  | .seq a b => NoCallT a ∧ NoCallT b
  | .ite _ a b => NoCallT a ∧ NoCallT b
  | .while _ b => NoCallT b
  | _ => True

/-- **Syntactic frame of a call-free run**: nothing outside the text's own write targets
changes (allocations included), for every procedure table. -/
theorem exec_cframe (ops : VOps V) : ∀ (f : ℕ) (c : Stmt) (s r : State V), NoCallT c →
    exec ops f c s = some r → Unchanged s r (sWA c) (sVA c) (sWR c) (sVR c) := by
  intro f
  induction f with
  | zero => intro c s r _ h; simp [exec] at h
  | succ f ih =>
    intro c s r hnc h
    cases c with
    | skip =>
      simp only [exec, Option.some.injEq] at h
      subst h; exact Unchanged.charge s 1 _ _ _ _
    | wset x e =>
      simp only [exec] at h
      cases he : evalW s e with
      | none => simp [he] at h
      | some a =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_setW_iff (by simp [sWR])]
        exact Unchanged.refl _ _ _ _ _
    | vset x e =>
      simp only [exec] at h
      cases he : evalV ops s e with
      | none => simp [he] at h
      | some a =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_setV_iff (by simp [sVR])]
        exact Unchanged.refl _ _ _ _ _
    | vle x a b =>
      simp only [exec] at h
      cases ha : evalV ops s a with
      | none => simp [ha] at h
      | some p =>
        cases hb : evalV ops s b with
        | none => simp [ha, hb] at h
        | some q =>
          cases hf : fit s.cap (if ops.le p q then 1 else 0) with
          | none => simp [ha, hb, hf] at h
          | some bit =>
            simp [ha, hb, hf] at h
            subst h
            rw [unchanged_charge_iff, unchanged_setW_iff (by simp [sWR])]
            exact Unchanged.refl _ _ _ _ _
    | wstore arr i e =>
      simp only [exec] at h
      cases hi : evalW s i with
      | none => simp [hi] at h
      | some j =>
        cases he : evalW s e with
        | none => simp [hi, he] at h
        | some a =>
          simp [hi, he] at h
          obtain ⟨-, h⟩ := h
          subst h
          rw [unchanged_charge_iff, unchanged_storeW_iff (by simp [sWA])]
          exact Unchanged.refl _ _ _ _ _
    | vstore arr i e =>
      simp only [exec] at h
      cases hi : evalW s i with
      | none => simp [hi] at h
      | some j =>
        cases he : evalV ops s e with
        | none => simp [hi, he] at h
        | some a =>
          simp [hi, he] at h
          obtain ⟨-, h⟩ := h
          subst h
          rw [unchanged_charge_iff, unchanged_storeV_iff (by simp [sVA])]
          exact Unchanged.refl _ _ _ _ _
    | walloc arr e =>
      simp only [exec] at h
      cases he : evalW s e with
      | none => simp [he] at h
      | some k =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_allocW_iff (by simp [sWA])]
        exact Unchanged.refl _ _ _ _ _
    | valloc arr e =>
      simp only [exec] at h
      cases he : evalW s e with
      | none => simp [he] at h
      | some k =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_allocV_iff (by simp [sVA])]
        exact Unchanged.refl _ _ _ _ _
    | seq a b =>
      simp only [exec] at h
      cases h1 : exec ops f a s with
      | none => simp [h1] at h
      | some s' =>
        simp only [h1, Option.bind_some] at h
        have hA := ih a s s' hnc.1 h1
        have hB := ih b s' r hnc.2 h
        refine (hA.mono ?_ ?_ ?_ ?_).trans (hB.mono ?_ ?_ ?_ ?_) <;>
          intro x hx <;> simp only [sWA, sVA, sWR, sVR, List.mem_append] at hx ⊢ <;> tauto
    | ite c a b =>
      simp only [exec] at h
      cases hc : evalW s c with
      | none => simp [hc] at h
      | some x =>
        have h0 : Unchanged s (s.charge 1) (sWA (.ite c a b)) (sVA (.ite c a b))
            (sWR (.ite c a b)) (sVR (.ite c a b)) := Unchanged.charge s 1 _ _ _ _
        by_cases hx : x = 0
        · simp [hc, hx] at h
          have hB := ih b (s.charge 1) r hnc.2 h
          refine h0.trans (hB.mono ?_ ?_ ?_ ?_) <;>
            intro y hy <;> simp only [sWA, sVA, sWR, sVR, List.mem_append] at hy ⊢ <;> tauto
        · simp [hc, hx] at h
          have hA := ih a (s.charge 1) r hnc.1 h
          refine h0.trans (hA.mono ?_ ?_ ?_ ?_) <;>
            intro y hy <;> simp only [sWA, sVA, sWR, sVR, List.mem_append] at hy ⊢ <;> tauto
    | «while» c b =>
      simp only [exec] at h
      cases hc : evalW s c with
      | none => simp [hc] at h
      | some x =>
        by_cases hx : x = 0
        · simp [hc, hx] at h
          subst h; exact Unchanged.charge s 1 _ _ _ _
        · cases h1 : exec ops f b (s.charge 1) with
          | none => simp [hc, hx, h1] at h
          | some s' =>
            have h' : exec ops f (.while c b) s' = some r := by simpa [hc, hx, h1] using h
            have hB := ih b (s.charge 1) s' (show NoCallT b from hnc) h1
            have hW := ih (.while c b) s' r hnc h'
            have h0 : Unchanged s (s.charge 1) (sWA (.while c b)) (sVA (.while c b))
                (sWR (.while c b)) (sVR (.while c b)) := Unchanged.charge s 1 _ _ _ _
            refine (h0.trans (hB.mono ?_ ?_ ?_ ?_)).trans hW <;>
              intro y hy <;> simp only [sWA, sVA, sWR, sVR, List.mem_append] at hy ⊢ <;> tauto
    | call p => exact (show False from hnc).elim

/-- **Attach the call-free syntactic frame to a `Runs` postcondition.** -/
theorem Runs.cframe {ops : VOps V} {c : Stmt} {s : State V} {Q : State V → Prop}
    (h : Runs ops c s Q) (hc : NoCallT c) :
    Runs ops c s (fun r => Q r ∧ Unchanged s r (sWA c) (sVA c) (sWR c) (sVR c)) := by
  obtain ⟨f, r, hex, hQ⟩ := h
  exact ⟨f, r, hex, hQ, exec_cframe ops f c s r hc hex⟩

end Frontier.RAM

namespace Frontier.CHD.DPro

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.DB Frontier.CHD.DGlob
  Frontier.CHD.DLI Frontier.CHD.L6 Frontier.CHD.BM
open Frontier.RAM.WExpr Frontier.RAM.Stmt

/-! ## The text -/

/-- the sizes: `ad.u = Cw · Tnat + 2`, `ad.ec = ad.bc = ad.sc = ad.u + 2`, `ad.lc = LF + 2`, the top
level `nw.lv = LF + 1`, and the key-list length `kl.len = n + LF + 2` -/
def dSizes (Cw : ℕ) : Stmt :=
  seq (wset "ad.u" (add (mul (lit Cw) (var "pr.tn")) (lit 2)))
  (seq (wset "ad.ec" (add (var "ad.u") (lit 2)))
  (seq (wset "ad.bc" (var "ad.ec"))
  (seq (wset "ad.sc" (var "ad.ec"))
  (seq (wset "ad.lc" (add (var "cp.L") (lit 2)))
  (seq (wset "nw.lv" (add (var "cp.L") (lit 1)))
       (wset "kl.len" (add (var "n") (var "ad.lc"))))))))

/-- the per-level parameter / bound arrays (all zero: `M = 0`, bound flag `0` = `⊤`) and the
select scratch `sel.w` -/
def dLvl : Stmt :=
  seq (walloc "dsl.M" (var "ad.lc"))
  (seq (walloc "dsl.bf" (var "ad.lc"))
  (seq (walloc "dsl.bh" (var "ad.lc"))
  (seq (walloc "dsl.bv" (var "ad.lc"))
  (seq (walloc "dsl.be" (var "ad.lc"))
  (seq (walloc "dsl.br" (var "ad.lc"))
  (seq (valloc "dsl.bl" (var "ad.lc"))
       (walloc "sel.w" (add (mul (lit 6) (var "ad.ec")) (lit 60)))))))))

/-- **The D-layer allocation hook.** -/
def dPro (Cw : ℕ) : Stmt :=
  seq (dSizes Cw) (seq allocD (seq newTopS (seq KL.klAlloc dLvl)))

/-- the use capacity -/
def dUcap (Cw cn cm : ℕ) : ℕ := Cw * CostSkeleton.Tnat cn cm + 2

/-- **The D-layer parameters** of the spine: top level `LF + 1`, `ecap = bcap = ucap + 2`, the
selection routine `selBody entLess 1` at procedure index `1`. -/
def dPar (Cw cn cm : ℕ) : DPar :=
  ⟨CostSkeleton.LF cn cm + 1, dUcap Cw cn cm + 2, dUcap Cw cn cm + 2, dUcap Cw cn cm, 1,
    SelectRAM.selBody SelectRAM.entLess 1⟩

/-- the hook constant -/
def dKd (Cw : ℕ) : ℕ := 23 * Cw + 300

/-- word arrays `dPro` writes -/
def dProWA : List String :=
  ["live", "ent.key", "ent.nxt", "ent.h", "ent.v", "ent.e", "ent.r", "blk.hd", "blk.tl", "blk.cnt",
    "blk.bot", "blk.h", "blk.v", "blk.e", "blk.r", "dsl.stk", "dsl.sz", "dsl.base", "dsl.base",
    "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz", "lk.n", "lk.p", "lk.n", "lk.p",
    "dsl.M", "dsl.bf", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "sel.w"]
/-- value arrays `dPro` writes -/
def dProVA : List String := ["ent.len", "blk.len", "dsl.bl"]
/-- word registers `dPro` writes -/
def dProWR : List String :=
  ["ad.u", "ad.ec", "ad.bc", "ad.sc", "ad.lc", "nw.lv", "kl.len", "ds.fresh", "blk.fresh", "nw.id",
    "blk.fresh", "kl.j", "kl.j"]

theorem sWA_dPro (Cw : ℕ) : sWA (dPro Cw) = dProWA := rfl
theorem sVA_dPro (Cw : ℕ) : sVA (dPro Cw) = dProVA := rfl
theorem sWR_dPro (Cw : ℕ) : sWR (dPro Cw) = dProWR := rfl
theorem sVR_dPro (Cw : ℕ) : sVR (dPro Cw) = [] := rfl

theorem dPro_nocall (Cw : ℕ) : NoCallT (dPro Cw) := by
  simp [NoCallT, dPro, dSizes, dLvl, allocD, newTopS, KL.klAlloc, KL.klFillLoop, KL.klFillBody]

/-! ## The pieces -/

theorem dSizes_spec {ops : VOps ℝ≥0} (Cw : ℕ) (st : State ℝ≥0) (T L N : ℕ)
    (htn : st.w "pr.tn" = T) (hL : st.w "cp.L" = L) (hn : st.w "n" = N) (hT : 1 ≤ T)
    (hc : Cw * T + N + L + 8 < st.cap) :
    Runs ops (dSizes Cw) st (fun r => r.w "ad.u" = Cw * T + 2 ∧ r.w "ad.ec" = Cw * T + 2 + 2 ∧
      r.w "ad.bc" = Cw * T + 2 + 2 ∧ r.w "ad.sc" = Cw * T + 2 + 2 ∧ r.w "ad.lc" = L + 2 ∧
      r.w "nw.lv" = L + 1 ∧ r.w "kl.len" = N + (L + 2) ∧ r.cost = st.cost + 7) := by
  have hCw : Cw ≤ Cw * T := Nat.le_mul_of_pos_right Cw hT
  apply wp_sound
  simp [dSizes, wp, htn, hL, hn, fit, show Cw < st.cap by omega, show Cw * T < st.cap by omega,
    show Cw * T + 2 < st.cap by omega, show Cw * T + 2 + 2 < st.cap by omega,
    show 2 < st.cap by omega, show L + 2 < st.cap by omega, show 1 < st.cap by omega,
    show L + 1 < st.cap by omega, show N + (L + 2) < st.cap by omega]

/-- the exact entry-pool lengths after `allocD` (for `DLens.ent`) -/
theorem allocD_len {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (N ecap bcap scap lcap : ℕ)
    (hn : st0.w "n" = N) (hec : st0.w "ad.ec" = ecap) (hbc : st0.w "ad.bc" = bcap)
    (hsc : st0.w "ad.sc" = scap) (hlc : st0.w "ad.lc" = lcap) (hcap : 1 < st0.cap) :
    Runs ops allocD st0 (fun r => (r.wlen "ent.nxt" = ecap ∧ r.wlen "ent.key" = ecap ∧
      r.vlen "ent.len" = ecap ∧ r.wlen "ent.h" = ecap ∧ r.wlen "ent.v" = ecap ∧
      r.wlen "ent.e" = ecap ∧ r.wlen "ent.r" = ecap) ∧ (∀ i, r.wa "ent.key" i = 0) ∧
      r.wlen "dsl.stk" = scap ∧ r.wlen "dsl.sz" = lcap ∧ r.wlen "live" = N) := by
  apply wp_sound
  simp [allocD, wp, hn, hec, hbc, hsc, hlc, fit, show 0 < st0.cap by omega]

/-- `newTopS` on the empty layer uses exactly one block id -/
theorem newTopS_bf {ops : VOps ℝ≥0} (st0 : State ℝ≥0) (hi : ℕ) (hlv : st0.w "nw.lv" = hi)
    (hbf : st0.w "blk.fresh" = 0) (h1 : hi < st0.wlen "dsl.base") (h2 : 0 < st0.wlen "blk.hd")
    (h3 : 0 < st0.wlen "blk.tl") (h4 : 0 < st0.wlen "blk.cnt") (h5 : 0 < st0.wlen "blk.bot")
    (h6 : 0 < st0.wlen "dsl.stk") (h7 : hi < st0.wlen "dsl.sz") (hcap : 2 < st0.cap) :
    Runs ops newTopS st0 (fun r => r.w "blk.fresh" = 1) := by
  apply wp_sound
  simp [newTopS, wp, hlv, hbf, fit, show 0 < st0.cap by omega, show 1 < st0.cap by omega, h1, h2,
    h3, h4, h5, h6, h7]

theorem dLvl_spec {ops : VOps ℝ≥0} (st : State ℝ≥0) (lc ec : ℕ) (hlc : st.w "ad.lc" = lc)
    (hec : st.w "ad.ec" = ec) (hc : 6 * ec + 60 < st.cap) :
    Runs ops dLvl st (fun r => r.wlen "dsl.M" = lc ∧ r.wlen "dsl.bf" = lc ∧ r.wlen "dsl.bh" = lc ∧
      r.wlen "dsl.bv" = lc ∧ r.wlen "dsl.be" = lc ∧ r.wlen "dsl.br" = lc ∧ r.vlen "dsl.bl" = lc ∧
      r.wlen "sel.w" = 6 * ec + 60 ∧ (∀ j, r.wa "dsl.M" j = 0) ∧ (∀ j, r.wa "dsl.bf" j = 0) ∧
      r.cost = st.cost + 7 * (lc + 1) + (6 * ec + 61)) := by
  apply wp_sound
  simp [dLvl, wp, hlc, hec, fit, show 6 < st.cap by omega, show 6 * ec < st.cap by omega,
    show 60 < st.cap by omega, show 6 * ec + 60 < st.cap by omega]
  ring


/-! ## Everything `dPro` establishes -/

/-- the raw facts after `dPro` -/
structure DAlloc (Cw cn cm : ℕ) (H : Graph) (src : Fin H.n) (r : State ℝ≥0) : Prop where
  dl : DLRep (G := H) (s := src) r H0 (vc (G := H) r) (dUcap Cw cn cm + 2) (dUcap Cw cn cm + 2)
    (fun _ => none) 0 (fun _ => newC 0 ⊤) (CostSkeleton.LF cn cm + 1) 0
  ent : r.wlen "ent.nxt" = dUcap Cw cn cm + 2 ∧ r.wlen "ent.key" = dUcap Cw cn cm + 2 ∧
    r.vlen "ent.len" = dUcap Cw cn cm + 2 ∧ r.wlen "ent.h" = dUcap Cw cn cm + 2 ∧
    r.wlen "ent.v" = dUcap Cw cn cm + 2 ∧ r.wlen "ent.e" = dUcap Cw cn cm + 2 ∧
    r.wlen "ent.r" = dUcap Cw cn cm + 2
  /-- every pool slot holds a key `< n` (zero-initialised) -/
  key0 : ∀ i, r.wa "ent.key" i = 0
  stk : r.wlen "dsl.stk" = dUcap Cw cn cm + 2
  sz : r.wlen "dsl.sz" = CostSkeleton.LF cn cm + 2
  live : r.wlen "live" = H.n
  lvl : r.wlen "dsl.M" = CostSkeleton.LF cn cm + 2 ∧ r.wlen "dsl.bf" = CostSkeleton.LF cn cm + 2 ∧
    r.wlen "dsl.bh" = CostSkeleton.LF cn cm + 2 ∧ r.wlen "dsl.bv" = CostSkeleton.LF cn cm + 2 ∧
    r.wlen "dsl.be" = CostSkeleton.LF cn cm + 2 ∧ r.wlen "dsl.br" = CostSkeleton.LF cn cm + 2 ∧
    r.vlen "dsl.bl" = CostSkeleton.LF cn cm + 2
  M0 : ∀ j, r.wa "dsl.M" j = 0
  bf0 : ∀ j, r.wa "dsl.bf" j = 0
  lk : ∀ i < H.n + (CostSkeleton.LF cn cm + 1) + 1, r.wa "lk.n" i = i ∧ r.wa "lk.p" i = i
  lkl : r.wlen "lk.n" = H.n + (CostSkeleton.LF cn cm + 2) ∧
    r.wlen "lk.p" = H.n + (CostSkeleton.LF cn cm + 2)
  selw : r.wlen "sel.w" = 6 * (dUcap Cw cn cm + 2) + 60
  dsf : r.w "ds.fresh" = 0
  bkf : r.w "blk.fresh" = 1
  cap : (CostSkeleton.LF cn cm + 1 + 2) * (H.n + 2) + 8 * (dUcap Cw cn cm + 2) + 2 * H.n +
    4 * (CostSkeleton.LF cn cm + 1) + 400 < r.cap

theorem sWA_dLvl : sWA dLvl = ["dsl.M", "dsl.bf", "dsl.bh", "dsl.bv", "dsl.be", "dsl.br", "sel.w"] :=
  rfl
theorem sVA_dLvl : sVA dLvl = ["dsl.bl"] := rfl
theorem sWR_dLvl : sWR dLvl = [] := rfl
theorem sVR_dLvl : sVR dLvl = [] := rfl
theorem sWA_newTopS :
    sWA newTopS = ["dsl.base", "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "dsl.stk", "dsl.sz"] := rfl
theorem sVA_newTopS : sVA newTopS = [] := rfl
theorem sWR_newTopS : sWR newTopS = ["nw.id", "blk.fresh"] := rfl
theorem sVR_newTopS : sVR newTopS = [] := rfl
theorem sWA_allocD : sWA allocD = ["live", "ent.key", "ent.nxt", "ent.h", "ent.v", "ent.e", "ent.r",
    "blk.hd", "blk.tl", "blk.cnt", "blk.bot", "blk.h", "blk.v", "blk.e", "blk.r", "dsl.stk",
    "dsl.sz", "dsl.base"] := rfl
theorem sVA_allocD : sVA allocD = ["ent.len", "blk.len"] := rfl
theorem sWR_allocD : sWR allocD = ["ds.fresh", "blk.fresh"] := rfl
theorem sVR_allocD : sVR allocD = [] := rfl
theorem sWA_dSizes (Cw : ℕ) : sWA (dSizes Cw) = [] := rfl
theorem sVA_dSizes (Cw : ℕ) : sVA (dSizes Cw) = [] := rfl
theorem sWR_dSizes (Cw : ℕ) :
    sWR (dSizes Cw) = ["ad.u", "ad.ec", "ad.bc", "ad.sc", "ad.lc", "nw.lv", "kl.len"] := rfl
theorem sVR_dSizes (Cw : ℕ) : sVR (dSizes Cw) = [] := rfl

/-- the capacity arithmetic: `64 Cw + 128 ≤ 4^(e-1)` and `CoreIn.cap` pay every word and
allocation of `dPro` -/
theorem dPro_cap {e cn cm N cap Cw : ℕ} (he : 2 ≤ e) (hCw : 64 * Cw + 128 ≤ 4 ^ (e - 1))
    (hcn : 1 ≤ cn) (hcm : 1 ≤ cm) (hN : N ≤ 2 * cn) (hcap : (cn + cm + 2) ^ (e + 1) ≤ cap) :
    (CostSkeleton.LF cn cm + 1 + 2) * (N + 2) + 8 * (dUcap Cw cn cm + 2) + 2 * N +
      4 * (CostSkeleton.LF cn cm + 1) + 400 < cap := by
  have hX : 4 ≤ cn + cm + 2 := by omega
  have hcapX : (64 * Cw + 128) * (cn + cm + 2) ^ 2 ≤ cap := by
    have h1 : (cn + cm + 2) ^ (e + 1) = (cn + cm + 2) ^ (e - 1) * (cn + cm + 2) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have h2 : 4 ^ (e - 1) ≤ (cn + cm + 2) ^ (e - 1) := Nat.pow_le_pow_left hX _
    calc (64 * Cw + 128) * (cn + cm + 2) ^ 2 ≤ 4 ^ (e - 1) * (cn + cm + 2) ^ 2 :=
          Nat.mul_le_mul_right _ hCw
      _ ≤ (cn + cm + 2) ^ (e - 1) * (cn + cm + 2) ^ 2 := Nat.mul_le_mul_right _ h2
      _ = (cn + cm + 2) ^ (e + 1) := h1.symm
      _ ≤ cap := hcap
  have hT := Tnat_le_sq cn cm hcn
  have hL := LF_le cn cm hcn
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (cn + cm + 2) ^ 2 := ⟨_, rfl⟩
  rw [← hY] at hcapX hT
  have hY16 : 16 ≤ Y := by rw [hY]; nlinarith
  have hYc : 4 * cn + 4 ≤ Y := by rw [hY]; nlinarith
  have hrow : (CostSkeleton.LF cn cm + 1 + 2) * (N + 2) ≤ 2 * Y := by
    have h1 : (CostSkeleton.LF cn cm + 1 + 2) * (N + 2) ≤ (cn + 4) * (2 * cn + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (cn + 4) * (2 * cn + 2) ≤ 2 * Y := by rw [hY]; nlinarith
    omega
  have hCT : Cw * CostSkeleton.Tnat cn cm ≤ Cw * (8 * Y) := Nat.mul_le_mul_left Cw (by omega)
  have e1 : Cw * (8 * Y) = 8 * (Cw * Y) := by ring
  have e2 : (64 * Cw + 128) * Y = 64 * (Cw * Y) + 128 * Y := by ring
  unfold dUcap
  omega

set_option maxHeartbeats 16000000 in
/-- **The run of `dPro`** from a hook state: the raw facts, the footprint, the cost. -/
theorem dPro_runs (e : ℕ) (he : 2 ≤ e) (ps : List Stmt) (Cw : ℕ)
    (hCw : 64 * Cw + 128 ≤ 4 ^ (e - 1)) (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ)
    (st : State ℝ≥0) (hIn : HookIn e ps H src cn cm c0 st) :
    Runs realOps (dPro Cw) st (fun r => DAlloc Cw cn cm H src r ∧
      Unchanged st r dProWA dProVA dProWR [] ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + dKd Cw * (CostSkeleton.Tnat cn cm + 1)) := by
  have hc := hIn.pre.core
  have hcn1 := hc.cn_pos
  have hcm1 := hc.cm_pos
  have hN := hc.sizeN
  have hnpos : 0 < H.n := Fin.pos src
  have hbig := dPro_cap (N := H.n) (Cw := Cw) he hCw hcn1 hcm1 hN hc.cap
  have hLle := LF_le cn cm hcn1
  have hTge : cn ≤ CostSkeleton.Tnat cn cm := by unfold CostSkeleton.Tnat; omega
  have hUc : dUcap Cw cn cm = Cw * CostSkeleton.Tnat cn cm + 2 := rfl
  have hCT : Cw ≤ Cw * CostSkeleton.Tnat cn cm := Nat.le_mul_of_pos_right Cw (by omega)
  suffices hmain : Runs realOps (dPro Cw) st (fun r => DAlloc Cw cn cm H src r ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + dKd Cw * (CostSkeleton.Tnat cn cm + 1)) by
    refine (Runs.cframe hmain (dPro_nocall Cw)).mono ?_
    rintro r ⟨⟨hA, hc1, hc2⟩, hU⟩
    rw [sWA_dPro, sVA_dPro, sWR_dPro, sVR_dPro] at hU
    exact ⟨hA, hU, hc1, hc2⟩
  unfold dPro
  -- 1. the sizes
  refine runs_seq ((Runs.cframe (dSizes_spec (ops := realOps) Cw st (CostSkeleton.Tnat cn cm)
    (CostSkeleton.LF cn cm) H.n hIn.tn hIn.pre.L hIn.n (by omega) (by omega))
    (by simp [NoCallT, dSizes])).mono ?_)
  rintro t1 ⟨⟨h1u, h1ec, h1bc, h1sc, h1lc, h1lv, h1kl, h1c⟩, hU1⟩
  rw [sWA_dSizes, sVA_dSizes, sWR_dSizes, sVR_dSizes] at hU1
  rw [← hUc] at h1ec h1bc h1sc
  have hcap1 : t1.cap = st.cap := hU1.cap
  have hn1 : t1.w "n" = H.n := by rw [hU1.wreg "n" (by simp)]; exact hIn.n
  -- 2. allocD
  refine runs_seq ((Runs.cframe (runs_and
    (allocD_spec (ops := realOps) (G := H) (s := src) t1 H0 (vc (G := H) st) (dUcap Cw cn cm + 2)
      (dUcap Cw cn cm + 2) (dUcap Cw cn cm + 2) (CostSkeleton.LF cn cm + 2) hn1 h1ec h1bc h1sc
      h1lc (by omega) (by omega))
    (allocD_len (ops := realOps) t1 H.n (dUcap Cw cn cm + 2) (dUcap Cw cn cm + 2)
      (dUcap Cw cn cm + 2) (CostSkeleton.LF cn cm + 2) hn1 h1ec h1bc h1sc h1lc (by omega)))
    (by simp [NoCallT, allocD])).mono ?_)
  rintro t2 ⟨⟨⟨hE2, hc2⟩, hent2, hkey2, hstk2, hsz2, hlive2⟩, hU2⟩
  rw [sWA_allocD, sVA_allocD, sWR_allocD, sVR_allocD] at hU2
  have hcap2 : t2.cap = st.cap := hU2.cap.trans hcap1
  have hlv2 : t2.w "nw.lv" = CostSkeleton.LF cn cm + 1 := by
    rw [hU2.wreg "nw.lv" (by simp)]; exact h1lv
  have hba := hE2.barr
  -- 3. the top structure
  refine runs_seq ((Runs.cframe (Runs.keep_len (runs_and
    (newTopDL (ops := realOps) (G := H) (s := src) t2 H0 (vc (G := H) st) (dUcap Cw cn cm + 2)
      (dUcap Cw cn cm + 2) (dUcap Cw cn cm + 2) (CostSkeleton.LF cn cm + 2) (fun _ => newC 0 ⊤)
      (CostSkeleton.LF cn cm + 1) 0 ⊤ hE2 hlv2 (by omega) (by omega) (by omega) (by omega))
    (newTopS_bf (ops := realOps) t2 (CostSkeleton.LF cn cm + 1) hlv2 hE2.bf
      (by have := hE2.basel; omega) (by have := hba.1; omega) (by have := hba.2.1; omega)
      (by have := hba.2.2.1; omega) (by have := hba.2.2.2.1; omega) (by have := hE2.stkl; omega)
      (by have := hE2.szl; omega) (by omega)))
    (by simp [NoAlloc, newTopS])) (by simp [NoCallT, newTopS])).mono ?_)
  rintro t3 ⟨⟨⟨⟨hDL3, hc3⟩, hbf3⟩, hwl3, hvl3⟩, hU3⟩
  rw [sWA_newTopS, sVA_newTopS, sWR_newTopS, sVR_newTopS] at hU3
  have hcap3 : t3.cap = st.cap := hU3.cap.trans hcap2
  have hkl3 : t3.w "kl.len" = H.n + (CostSkeleton.LF cn cm + 2) := by
    rw [hU3.wreg "kl.len" (by simp), hU2.wreg "kl.len" (by simp)]; exact h1kl
  -- 4. the key lists
  refine runs_seq ((KL.klAlloc_spec (ops := realOps) t3 (H.n + (CostSkeleton.LF cn cm + 2)) hkl3
    (by omega)).mono ?_)
  rintro t4 ⟨hself4, hln4, hlp4, hU4, hc4⟩
  have hcap4 : t4.cap = st.cap := hU4.cap.trans hcap3
  have hlc4 : t4.w "ad.lc" = CostSkeleton.LF cn cm + 2 := by
    rw [hU4.wreg "ad.lc" (by simp), hU3.wreg "ad.lc" (by simp), hU2.wreg "ad.lc" (by simp)]
    exact h1lc
  have hec4 : t4.w "ad.ec" = dUcap Cw cn cm + 2 := by
    rw [hU4.wreg "ad.ec" (by simp), hU3.wreg "ad.ec" (by simp), hU2.wreg "ad.ec" (by simp)]
    exact h1ec
  -- 5. the level arrays and the select scratch
  refine (Runs.cframe (dLvl_spec (ops := realOps) t4 (CostSkeleton.LF cn cm + 2)
    (dUcap Cw cn cm + 2) hlc4 hec4 (by omega)) (by simp [NoCallT, dLvl])).mono ?_
  rintro r ⟨⟨hM, hbf, hbh, hbv, hbe, hbr, hbl, hsel, hM0, hbf0, hc5⟩, hU5⟩
  rw [sWA_dLvl, sVA_dLvl, sWR_dLvl, sVR_dLvl] at hU5
  have hcapr : r.cap = st.cap := hU5.cap.trans hcap4
  have hU45 : Unchanged t3 r ["lk.n", "lk.p", "dsl.M", "dsl.bf", "dsl.bh", "dsl.bv", "dsl.be",
      "dsl.br", "sel.w"] ["dsl.bl"] ["kl.j"] [] :=
    (hU4.mono (by intro x hx; simp at hx ⊢; tauto) (List.nil_subset _) (List.Subset.refl _)
      (List.Subset.refl _)).trans
    (hU5.mono (by intro x hx; simp at hx ⊢; tauto) (List.Subset.refl _) (List.nil_subset _)
      (List.Subset.refl _))
  have hvc : vc (G := H) r = vc (G := H) st := by
    funext v
    simp only [vc]
    rw [(hU45.warr "vcnt" (by simp)).1, (hU3.warr "vcnt" (by simp)).1,
      (hU2.warr "vcnt" (by simp)).1, (hU1.warr "vcnt" (by simp)).1]
  have hDLr := DLRep.of_unch hDL3 hU45 (by decide) (by decide) (by decide)
  have hupd : Function.update (fun _ : ℕ => newC (G := H) (s := src) 0 ⊤) (CostSkeleton.LF cn cm + 1)
      (⟨0, ⊤, [⟨⊥, []⟩]⟩ : DStr (Fin H.n) (WLab H src)) = fun _ => newC 0 ⊤ := by
    funext j; rw [Function.update_apply]; split_ifs <;> rfl
  rw [hupd, ← hvc] at hDLr
  have hnot : ∀ a ∈ ["ent.nxt", "ent.key", "ent.h", "ent.v", "ent.e", "ent.r", "dsl.stk",
      "dsl.sz", "live"], a ∉ ["lk.n", "lk.p", "dsl.M", "dsl.bf", "dsl.bh", "dsl.bv", "dsl.be",
      "dsl.br", "sel.w"] := by decide
  have hwl : ∀ a ∈ ["ent.nxt", "ent.key", "ent.h", "ent.v", "ent.e", "ent.r", "dsl.stk",
      "dsl.sz", "live"], r.wlen a = t2.wlen a := by
    intro a ha
    rw [(hU45.warr a (hnot a ha)).2, hwl3]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hent2
  refine ⟨⟨hDLr, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨hM, hbf, hbh, hbv, hbe, hbr, hbl⟩,
    hM0, hbf0, ?_, ?_, hsel, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hwl "ent.nxt" (by simp)]; exact a1
  · rw [hwl "ent.key" (by simp)]; exact a2
  · rw [(hU45.varr "ent.len" (by simp)).2, hvl3]; exact a3
  · rw [hwl "ent.h" (by simp)]; exact a4
  · rw [hwl "ent.v" (by simp)]; exact a5
  · rw [hwl "ent.e" (by simp)]; exact a6
  · rw [hwl "ent.r" (by simp)]; exact a7
  · intro i
    rw [(hU45.warr "ent.key" (by simp)).1, (hU3.warr "ent.key" (by simp)).1]; exact hkey2 i
  · rw [hwl "dsl.stk" (by simp)]; exact hstk2
  · rw [hwl "dsl.sz" (by simp)]; exact hsz2
  · rw [hwl "live" (by simp)]; exact hlive2
  · intro i hi
    rw [(hU5.warr "lk.n" (by simp)).1, (hU5.warr "lk.p" (by simp)).1]
    exact hself4 i (by omega)
  · rw [(hU5.warr "lk.n" (by simp)).2, (hU5.warr "lk.p" (by simp)).2]; exact ⟨hln4, hlp4⟩
  · rw [hU45.wreg "ds.fresh" (by simp), hU3.wreg "ds.fresh" (by simp)]; exact hE2.pool.1
  · rw [hU45.wreg "blk.fresh" (by simp)]; exact hbf3
  · rw [hcapr]; exact hbig
  · rw [hc5, hc4, hc3, hc2, h1c]; omega
  · have hexp : dKd Cw * (CostSkeleton.Tnat cn cm + 1) =
        23 * (Cw * CostSkeleton.Tnat cn cm) + 23 * Cw + 300 * CostSkeleton.Tnat cn cm + 300 := by
      unfold dKd; ring
    rw [hc5, hc4, hc3, hc2, h1c, hexp]
    omega

/-- **The `DRI` of agent-04 at level `LF + 1`** from the raw facts. -/
theorem dri_of_alloc {Cw cn cm : ℕ} {H : Graph} {src : Fin H.n} {r : State ℝ≥0}
    (hA : DAlloc Cw cn cm H src r)
    (hp : r.procs[1]? = some (SelectRAM.selBody SelectRAM.entLess 1)) :
    DRI (G := H) (s := src) (dPar Cw cn cm) r (H0 (G := H)) BM.DGl.init (fun _ => newC 0 ⊤)
      (CostSkeleton.LF cn cm + 1) := by
  have hU1 : 1 ≤ dUcap Cw cn cm := by unfold dUcap; omega
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hA.lvl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hA.ent
  have hcap := hA.cap
  have hlkn := hA.lkl.1
  have hlkp := hA.lkl.2
  have hnpos : 0 < H.n := Fin.pos src
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp, ?_, ?_⟩
  · show DLRep (G := H) (s := src) r H0 (vc (G := H) r) (dUcap Cw cn cm + 2) (dUcap Cw cn cm + 2)
      (fun _ => none) 0 (fun _ => newC 0 ⊤) (CostSkeleton.LF cn cm + 1)
      ((CostSkeleton.LF cn cm + 1) - (CostSkeleton.LF cn cm + 1))
    rw [Nat.sub_self]; exact hA.dl
  · intro j _ _
    exact ⟨⟨fun _ => rfl, fun _ => hA.bf0 j⟩, fun q hq => absurd hq WithTop.top_ne_coe⟩
  · intro j _ _; exact hA.M0 j
  · exact ⟨fun _ => [], KL.LL_alloc hA.lk, fun j _ _ v =>
      ⟨fun h => absurd h List.not_mem_nil, fun h => absurd h (hasKey_newC _ 0 ⊤ v)⟩⟩
  · intro j _ _; exact wf_newC _ 0 ⊤
  · intro j _ _; exact freshOK_newC 0 0 ⊤
  · intro u i a h; simp [BM.DGl.init] at h
  · show r.w "ds.fresh" + r.w "blk.fresh" ≤ dUcap Cw cn cm
    rw [hA.dsf, hA.bkf]; omega
  · exact {
      bf := by show CostSkeleton.LF cn cm + 1 < r.wlen "dsl.bf"; omega
      bl := by show CostSkeleton.LF cn cm + 1 < r.vlen "dsl.bl"; omega
      bh := by show CostSkeleton.LF cn cm + 1 < r.wlen "dsl.bh"; omega
      bv := by show CostSkeleton.LF cn cm + 1 < r.wlen "dsl.bv"; omega
      be := by show CostSkeleton.LF cn cm + 1 < r.wlen "dsl.be"; omega
      br := by show CostSkeleton.LF cn cm + 1 < r.wlen "dsl.br"; omega
      M := by show CostSkeleton.LF cn cm + 1 < r.wlen "dsl.M"; omega
      lkn := by show H.n + (CostSkeleton.LF cn cm + 1) < r.wlen "lk.n"; omega
      lkp := by show H.n + (CostSkeleton.LF cn cm + 1) < r.wlen "lk.p"; omega
      sz := by show CostSkeleton.LF cn cm + 1 < r.wlen "dsl.sz"; rw [hA.sz]; omega
      ent := ⟨e1, e2, e3, e4, e5, e6, e7⟩
      stk := by show dUcap Cw cn cm + 2 ≤ r.wlen "dsl.stk"; rw [hA.stk]
      live := by show H.n ≤ r.wlen "live"; rw [hA.live]
      ue := by show dUcap Cw cn cm + 2 ≤ dUcap Cw cn cm + 2; exact le_rfl
      ub := by show dUcap Cw cn cm + 2 ≤ dUcap Cw cn cm + 2; exact le_rfl
      cap := by
        show 4 * (dUcap Cw cn cm + 2) + 2 * (dUcap Cw cn cm + 2) + 2 * H.n +
          4 * (CostSkeleton.LF cn cm + 1) + 300 < r.cap
        omega
      rowcap := by
        show (CostSkeleton.LF cn cm + 1 + 2) * (H.n + 2) + 2 * (dUcap Cw cn cm + 2) + 300 < r.cap
        omega
      stkl := by show r.wlen "dsl.stk" = dUcap Cw cn cm + 2; exact hA.stk
      selw := by show 6 * (dUcap Cw cn cm + 2) + 60 ≤ r.wlen "sel.w"; rw [hA.selw]
      selc := by rw [hA.selw]; omega }
  · intro j _
    show 1 ≤ dUcap Cw cn cm
    exact hU1
  · intro i _
    rw [hA.key0 i]; exact hnpos
  · intro j _ _
    show 2 * 0 + 2 < r.cap
    omega

/-- **The D-layer allocation hook** (`L6.HookSpec`), full form: agent-04's `DRI` at level `LF + 1`
(the empty D layer, one top structure), `use = 1`, all raw facts (`DAlloc`: pool keys `< n`, the
`sel.w` scratch, exact lengths, the combined capacity sum) and the procedure-table fact. -/
theorem dProSpec_full (e : ℕ) (he : 2 ≤ e) (ps : List Stmt) (Cw : ℕ)
    (hCw : 64 * Cw + 128 ≤ 4 ^ (e - 1))
    (hsel : ps[1]? = some (SelectRAM.selBody SelectRAM.entLess 1)) :
    HookSpec e ps (dPro Cw)
      (fun H src cn cm r => DRI (G := H) (s := src) (dPar Cw cn cm) r (H0 (G := H)) BM.DGl.init
          (fun _ => newC 0 ⊤) (CostSkeleton.LF cn cm + 1) ∧
        r.w "ds.fresh" + r.w "blk.fresh" = 1 ∧ DAlloc Cw cn cm H src r ∧
        r.procs[1]? = some (SelectRAM.selBody SelectRAM.entLess 1))
      dProWA dProVA dProWR [] (dKd Cw) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro H src cn cm c0 st hIn
  refine (dPro_runs e he ps Cw hCw H src cn cm c0 st hIn).mono ?_
  rintro r ⟨hA, hU, hc1, hc2⟩
  have hp : r.procs[1]? = some (SelectRAM.selBody SelectRAM.entLess 1) := by
    rw [hU.procs, hIn.pre.core.procs]; exact hsel
  exact ⟨⟨dri_of_alloc hA hp, by rw [hA.dsf, hA.bkf], hA, hp⟩, hU, hc1, hc2⟩

/-- **The D-layer allocation hook** in the route's shape (`L6.LevelRoute` / `FinalRoute` `hD` for a
D layer with `DR = DRI (dPar Cw cn cm)` and `use = ds.fresh + blk.fresh`, e.g. agent-04's `mkDL`). -/
theorem dProSpec (e : ℕ) (he : 2 ≤ e) (ps : List Stmt) (Cw : ℕ)
    (hCw : 64 * Cw + 128 ≤ 4 ^ (e - 1))
    (hsel : ps[1]? = some (SelectRAM.selBody SelectRAM.entLess 1)) :
    HookSpec e ps (dPro Cw)
      (fun H src cn cm r => (∃ Ds : ℕ → BM.DStrM H src,
          DRI (G := H) (s := src) (dPar Cw cn cm) r (H0 (G := H)) BM.DGl.init Ds
            (CostSkeleton.LF cn cm + 1)) ∧ r.w "ds.fresh" + r.w "blk.fresh" ≤ 2)
      dProWA dProVA dProWR [] (dKd Cw) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro H src cn cm c0 st hIn
  refine (dPro_runs e he ps Cw hCw H src cn cm c0 st hIn).mono ?_
  rintro r ⟨hA, hU, hc1, hc2⟩
  have hp : r.procs[1]? = some (SelectRAM.selBody SelectRAM.entLess 1) := by
    rw [hU.procs, hIn.pre.core.procs]; exact hsel
  exact ⟨⟨⟨_, dri_of_alloc hA hp⟩, by rw [hA.dsf, hA.bkf]; omega⟩, hU, hc1, hc2⟩

end Frontier.CHD.DPro

#print axioms Frontier.CHD.DPro.dProSpec
#print axioms Frontier.CHD.DPro.dProSpec_full
#print axioms Frontier.CHD.DPro.dPro
