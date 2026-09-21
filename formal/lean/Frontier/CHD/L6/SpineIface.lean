import Frontier.CHD.L6.CoreTop
import Frontier.CHD.L6.Params
import Frontier.CHD.L6.LevelTab

/-!
# The interface between the core wrapper and the spine / master theorems (agent-10, COORD G2-8)

`CoreSpec` (L6.Body) is the only remaining hypothesis of `chdTarget_of_core`.  It is split as

* `SpineSpec` — the **RAM spine** (agent-08 with 01/02/04/05/06/09/03): started on a state
  `SpineIn` (all of `CoreIn`, the C-HD parameter registers `cp.*`, the per-level tables
  `cp.tau` / `cp.M` and the initialized label table), the program `spine` ends in a state whose
  label table represents the labels `res.2.2.2` of a Layer-A top-level run `TopRun` (agent-01's
  `BMSSPD` over `dlOps` and `fpC (outL H)` with the parameters `tF/kF/LF (cn, cm)`); its cost is
  at most `Ks (lg.cost + Tchd cn cm)` above the start;
* `MasterSpec` — the **Layer-A master cost theorem** (agent-06): every such top-level run has
  `lg.cost ≤ Km Tchd cn cm`.

`coreTop spine` = save `n, s, m`; `paramsProg`; `levelTab`; `initLab`; `spine` (skipped if
`gM = 0`); restore.  The
theorem `coreSpec_of_spine` (L6.CoreSpecProof) derives `CoreSpec e ps (coreTop spine) Kc` from the
two.  The cost parameters `P cn cm` (FindPivots' charges `hins/hext` and the base-case heap costs
`DCb`) are chosen by the spine and must be the same in both specifications.
NON-GATE (interface definitions only).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

/-- The Layer-A cost parameters chosen by the RAM spine. -/
structure CostPar where
  /-- FindPivots' charge per heap insertion (`fpC … hins hext`) -/
  hins : ℕ
  /-- FindPivots' charge per heap extraction -/
  hext : ℕ
  /-- the base-case heap costs (`BaseDH`) -/
  DCb : BM.DCost

/-- **The Layer-A top-level run** of the C-HD core on `H` from `src`, with the parameters of
`(cn, cm)`: source frontier `{src}`, bound `⊤`, level `LF cn cm`, no deleted edges. -/
def TopRun (H : Graph) (src : Fin H.n) (cn cm : ℕ) (P : CostPar) (T : ℕ → ℕ) (Blow : WLab H src)
    (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
    (lg : BM.Log H src (FPData H src)) : Prop :=
  BM.BMSSPD H src (BM.dlOps H src) (fpC H src (outL H) (CostSkeleton.kF cn cm) P.hins P.hext)
    P.DCb T (BM.chdM (CostSkeleton.tF cn cm)) (BM.chdTau (CostSkeleton.tF cn cm))
    (CostSkeleton.LF cn cm) Blow ⊤ {src} (BM.initLabels src) ∅ BM.DGl.init res φ' gE lg

/-- The graph facts available to the master cost theorem (all derived from `CoreIn`). -/
structure MasterIn (H : Graph) (src : Fin H.n) (cn cm : ℕ) : Prop where
  sizeN : H.n ≤ 2 * cn
  sizeM : H.m ≤ 2 * cm
  cn_le : cn ≤ cm + 1
  cm_pos : 1 ≤ cm
  cn_pos : 1 ≤ cn
  mpos : 0 < H.m
  deg : ∀ u : Fin H.n, (BM.Eout H {u}).card ≤ 5 * CostSkeleton.dd cn cm
  dens : CostSkeleton.dd cn cm ≤ GateCCalc.F cn + 1
  sorted : ∀ x : Fin H.n, (outL H x).Pairwise (SortedRel H src)
  simple : ∀ x : Fin H.n, ((outL H x).map H.dst).Nodup

/-- **The Layer-A master cost theorem** (agent-06) for the cost parameters `P`. -/
def MasterSpec (P : ℕ → ℕ → CostPar) (Km : ℝ) : Prop :=
  ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm →
    ∀ (T : ℕ → ℕ) (Blow : WLab H src), Blow ≤ BM.initLabels src src →
    ∀ (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
      (lg : BM.Log H src (FPData H src)), TopRun H src cn cm (P cn cm) T Blow res φ' gE lg →
      (lg.cost : ℝ) ≤ Km * GateCCalc.Tchd cn cm

/-- **The state after the prefix `corePre`**: `CoreIn`, the parameter registers of `paramsProg`,
the per-level tables of `levelTab`, and the label table of `initLab` (clock origin `c0`). -/
structure PreIn (e : ℕ) (ps : List Stmt) (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ)
    (t : State ℝ≥0) : Prop where
  core : CoreIn e ps H src cn cm t
  lg : t.w "cp.lg" = CostSkeleton.lgN cn
  dd : t.w "cp.dd" = CostSkeleton.dd cn cm
  tt : t.w "cp.t" = CostSkeleton.tF cn cm
  k : t.w "cp.k" = CostSkeleton.kF cn cm
  L : t.w "cp.L" = CostSkeleton.LF cn cm
  tau : ∀ l ≤ CostSkeleton.LF cn cm, t.wa "cp.tau" l = BM.chdTau (CostSkeleton.tF cn cm) l
  M : ∀ l ≤ CostSkeleton.LF cn cm + 1, t.wa "cp.M" l = BM.chdM (CostSkeleton.tF cn cm) l
  tauLen : t.wlen "cp.tau" = CostSkeleton.LF cn cm + 1
  MLen : t.wlen "cp.M" = CostSkeleton.LF cn cm + 2
  /-- the label table of `initLab`; `c0` is the **clock origin** of the label counters (the
  budget `hbud` of `SpineSpec` is measured from it) -/
  lab : LabAt (s := src) t (BM.initLabels src) (H0 (G := H)) c0

/-- **The state at the spine's entry**: `PreIn`, and the reduced graph has an edge (`coreTop`
answers `gM = 0` itself: then only `src` is reachable and `initLab`'s table is already exact). -/
structure SpineIn (e : ℕ) (ps : List Stmt) (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ)
    (t : State ℝ≥0) : Prop extends PreIn e ps H src cn cm c0 t where
  mpos : 0 < H.m

/-- What the spine must not touch: the output arrays `gKeep` / `gRep` of L6, the registers where
`coreTop` saved `n, s, m`, and the word capacity. -/
structure SpineFrame (t r : State ℝ≥0) : Prop where
  keep : r.wa "gKeep" = t.wa "gKeep" ∧ r.wlen "gKeep" = t.wlen "gKeep"
  rep : r.wa "gRep" = t.wa "gRep" ∧ r.wlen "gRep" = t.wlen "gRep"
  n : r.w "core.n" = t.w "core.n"
  s : r.w "core.s" = t.w "core.s"
  m : r.w "core.m" = t.w "core.m"
  cap : r.cap = t.cap

/-- The per-instance master bound (`MasterSpec`'s conclusion for one instance), handed to the
spine so that it can size its allocations (e.g. the D-layer pool `Cw · Tnat`, agent-07/10's
option A) with its own constants. -/
def MasterBound (H : Graph) (src : Fin H.n) (cn cm : ℕ) (P : CostPar) (Km : ℝ) : Prop :=
  ∀ (T : ℕ → ℕ) (Blow : WLab H src), Blow ≤ BM.initLabels src src →
    ∀ (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
      (lg : BM.Log H src (FPData H src)), TopRun H src cn cm P T Blow res φ' gE lg →
      (lg.cost : ℝ) ≤ Km * GateCCalc.Tchd cn cm

/-- **The RAM spine specification** (agent-08's target) for the cost parameters `P`.  The spine
may assume
* the **budget** `hbud` (agent-07, Objection 3): every Layer-A top-level outcome fits, with its RAM
  overhead `Ks (lg.cost + Tchd) + Kb`, under the clock origin plus the word capacity (what the
  `RefinesB`-style fragment specs need for the label counters);
* the **master bound** `MasterBound … Km` (every outcome has `lg.cost ≤ Km Tchd`), from which the
  spine sizes its allocations (with `CostSkeleton.Tchd_le_Tnat`).
`coreSpec_of_spine` discharges both from `MasterSpec P Km` and a large word exponent. -/
def SpineSpec (e : ℕ) (ps : List Stmt) (spine : Stmt) (P : ℕ → ℕ → CostPar) (Ks Kb Kpol Km : ℝ)
    (Dp : ℕ) : Prop :=
  ∀ (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ) (t : State ℝ≥0), SpineIn e ps H src cn cm c0 t →
    (∀ (T : ℕ → ℕ) (Blow : WLab H src), Blow ≤ BM.initLabels src src →
      ∀ (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
        (lg : BM.Log H src (FPData H src)), TopRun H src cn cm (P cn cm) T Blow res φ' gE lg →
        (t.cost : ℝ) + Ks * ((lg.cost : ℝ) + GateCCalc.Tchd cn cm) + Kb +
          Kpol * ((cn : ℝ) + cm + 2) ^ Dp ≤ c0 + t.cap) →
    MasterBound H src cn cm (P cn cm) Km →
    Runs realOps spine t (fun r => ∃ (T : ℕ → ℕ) (Blow : WLab H src) (res : BM.ResultD H src)
      (φ' : Finset (Fin H.m)) (gE : BM.DGl H src) (lg : BM.Log H src (FPData H src))
      (Hh : Fin H.n → ℕ → List (Fin H.m)) (c1 : ℕ),
      Blow ≤ BM.initLabels src src ∧ TopRun H src cn cm (P cn cm) T Blow res φ' gE lg ∧
      LabAt (s := src) r res.2.2.2 Hh c1 ∧ SpineFrame t r ∧
      (r.cost : ℝ) ≤ t.cost + Ks * ((lg.cost : ℝ) + GateCCalc.Tchd cn cm))

/-- The prefix of the core: save `n, s, m`; parameters; per-level tables; label table. -/
def corePre : Stmt :=
  seq (wset "core.n" (var "n")) (seq (wset "core.s" (var "s")) (seq (wset "core.m" (var "m"))
  (seq paramsProg (seq levelTab initLab))))

/-- The postfix of the core: restore `n, s, m`. -/
def corePost : Stmt :=
  seq (wset "n" (var "core.n")) (seq (wset "s" (var "core.s")) (wset "m" (var "core.m")))

/-- **The core wrapper.**  If the reduced graph has no edge (`gM = 0`), the table of `initLab` is
already the answer. -/
def coreTop (spine : Stmt) : Stmt :=
  seq corePre (seq (ite (eq (var "gM") (lit 0)) skip spine) corePost)

end Frontier.CHD.L6
