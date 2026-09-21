import Frontier.CHD.BL2Scan

/-!
# Frontier.CHD.BL2Loop — B-L2: the scan loop invariant and its preservation (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

variable (LI : LabI V ops G s)

/-! ## The scan loop invariant -/

/-- Registers read by the scan invariant. -/
def footRegs : List String :=
  ["gM", "fp.kl", "fp.k", "fp.hsz", "fp.p", "fp.pp", "fp.u", "fp.res", "fp.go"]

/-- Maximal machine cost of one loop iteration (test included). -/
def Kit : ℕ := LI.Ccand + LI.Ccmp + LI.Crel + 30

/-- Write sets of the whole scan. -/
def scanWA : List String := myArrs ++ LI.relWA
def scanVA : List String := LI.relVA
def scanWR : List String := myRegs ++ [LI.ru, LI.re, LI.rv] ++ LI.candWR ++ LI.cmpWR ++ LI.relWR
def scanVR : List String := LI.candVR ++ LI.cmpVR ++ LI.relVR

variable (c : FPCtx G s) (T : Finset (Fin G.n)) (slB slX : String) (u : Fin G.n)

/-- The machine part of a running scan state. -/
structure Core (σ : SSt G s) (Lrem : List (Fin G.m)) (g : LI.Gh) (st : State V) : Prop where
  lab : LabRep LI c slB slX σ.d g st
  my : MyRep c T σ st
  cur : Cursor st c σ.D u Lrem
  ureg : st.w "fp.u" = u
  res : st.w "fp.res" = 0
  go : st.w "fp.go" = if st.w "fp.p" < G.m then 1 else 0

/-- Result code of a finished scan. -/
def ResCode (st : State V) (r : ScanRes) (σ : SSt G s) : Prop :=
  (r = .cont ∧ (st.w "fp.res" = 0 ∨ st.w "fp.res" = 1)) ∨
  (r = .contact ∧ st.w "fp.res" = 2 ∧ ∃ a b : Fin G.n, σ.hit = some (a, b) ∧
      st.w "fp.cu" = a ∧ st.w "fp.cv" = b) ∨
  (r = .full ∧ st.w "fp.res" = 3)

/-- Bookkeeping relative to the scan's start state `st₀`. -/
structure Book (st₀ st : State V) (n : ℕ) : Prop where
  unch : Unchanged st₀ st (scanWA LI) (scanVA LI) (scanWR LI) (scanVR LI)
  cost0 : st₀.cost ≤ st.cost
  cost : st.cost ≤ st₀.cost + 4 + Kit LI * n

/-- Running scan state: Layer A has reached `σ` with remaining list `Lrem` at cost `n`. -/
structure RunI (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V) (σ : SSt G s)
    (Lrem : List (Fin G.m)) (n : ℕ) (g : LI.Gh) (st : State V) : Prop where
  core : Core LI c T slB slX u σ Lrem g st
  fin : σ.d u ≠ ⊤
  klt : σ.K.length < c.k
  hist : LI.gext g₀ g
  cont : ∀ σ' r n', Scan c T u σ Lrem σ' r n' → Scan c T u σ₀ (c.out u) σ' r (n + n')
  book : Book LI st₀ st n

/-- Stopped scan state (after a stopping iteration). -/
structure StopI (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V) (σ' : SSt G s) (r : ScanRes)
    (n : ℕ) (g : LI.Gh) (st : State V) : Prop where
  scan : Scan c T u σ₀ (c.out u) σ' r n
  lab : LabRep LI c slB slX σ'.d g st
  my : MyRep c T σ' st
  out : OutRep st c σ'.D
  ureg : st.w "fp.u" = u
  go : st.w "fp.go" = 0
  code : ResCode st r σ'
  hist : LI.gext g₀ g
  book : Book LI st₀ st n

/-- The loop invariant indexed by the measure. -/
def LoopI (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V) (m : ℕ) (st : State V) : Prop :=
  (∃ σ Lrem n g, m = Lrem.length + 1 ∧ RunI LI c T slB slX u σ₀ g₀ st₀ σ Lrem n g st) ∨
  (m = 0 ∧ ∃ σ' r n g, StopI LI c T slB slX u σ₀ g₀ st₀ σ' r n g st)

variable {LI c T slB slX u}

/-- The machine part survives writes to registers outside its footprint. -/
theorem Core.frame_regs {σ : SSt G s} {Lrem : List (Fin G.m)} {g : LI.Gh} {st st' : State V}
    {wr vr : List String} (h : Core LI c T slB slX u σ Lrem g st)
    (hu : Unchanged st st' [] [] wr vr) (hf : Disj wr footRegs)
    (hB : Disj wr (LI.slWR slB)) (hBv : Disj vr (LI.slVR slB))
    (hX : Disj wr (LI.slWR slX)) (hXv : Disj vr (LI.slVR slX)) (hc : st.cost ≤ st'.cost) :
    Core LI c T slB slX u σ Lrem g st' := by
  have R : ∀ x ∈ footRegs, st'.w x = st.w x := fun x hx => hu.wreg x (fun h' => hf x h' hx)
  have hmy : Disj wr myRegs → MyRep c T σ st' := fun h' => h.my.frame hu (Disj.nil_left _) h'
  refine ⟨h.lab.frame hu (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
      hB hBv (Disj.nil_left _) (Disj.nil_left _) hX hXv hc, ?_, ?_, ?_, ?_, ?_⟩
  · -- MyRep reads only gM, fp.kl, fp.k, fp.hsz among registers
    have A : ∀ a, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a :=
      fun a => hu.warr a (fun h' => absurd h' List.not_mem_nil)
    obtain ⟨hl, hnd, hset, hsz, hcap, harr, hpL, hpos, hbL, hb⟩ := h.my.heap
    have rgM := R "gM" (by simp [footRegs])
    have rkl := R "fp.kl" (by simp [footRegs])
    have rk := R "fp.k" (by simp [footRegs])
    have rh := R "fp.hsz" (by simp [footRegs])
    have hw : st'.wa = st.wa := funext fun a => (A a).1
    have hwl : st'.wlen = st.wlen := funext fun a => (A a).2
    exact ⟨by rw [rgM]; exact h.my.gM, by rw [hwl]; exact h.my.headL,
      fun q => by rw [hw]; exact h.my.head q,
      ⟨hl, hnd, hset, by rw [rh]; exact hsz, by rw [hwl]; exact hcap,
        fun i hi => by rw [hw]; exact harr i hi, by rw [hwl]; exact hpL,
        fun i hi => by rw [hw]; exact hpos i hi, by rw [hwl]; exact hbL,
        fun v => by rw [hw]; exact hb v⟩,
      by rw [rkl]; exact h.my.kl, by rw [hwl]; exact h.my.kcap,
      fun i hi => by rw [hw]; exact h.my.karr i hi,
      ⟨by rw [hwl]; exact h.my.inK.1, fun v => by rw [hw]; exact h.my.inK.2 v⟩,
      ⟨by rw [hwl]; exact h.my.val.1, fun v => by rw [hw]; exact h.my.val.2 v⟩,
      ⟨by rw [hwl]; exact h.my.fm.1, fun v => by rw [hw]; exact h.my.fm.2 v⟩,
      by rw [hwl]; exact h.my.kpL, fun v hv => by rw [hw]; exact h.my.kp v hv,
      by rw [rk]; exact h.my.kreg, h.my.Knd, h.my.HK⟩
  · obtain ⟨h1, h2, Pre, hPre, hs1, hs2, h3⟩ := h.cur
    have A : ∀ a, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a :=
      fun a => hu.warr a (fun h' => absurd h' List.not_mem_nil)
    have hw : st'.wa = st.wa := funext fun a => (A a).1
    have hwl : st'.wlen = st.wlen := funext fun a => (A a).2
    have rp := R "fp.p" (by simp [footRegs])
    have rpp := R "fp.pp" (by simp [footRegs])
    refine ⟨by rw [hwl]; exact h1, fun w hw' => ?_, Pre, hPre, ?_, ?_, by rw [rpp]; exact h3⟩
    · rw [hw]; exact (h2 w hw').of_eq (by rw [hw]) (by rw [hwl])
    · rw [hw, rp]; exact hs1.of_eq (by rw [hw]) (by rw [hwl])
    · rw [rp]; exact hs2.of_eq (by rw [hw]) (by rw [hwl])
  · rw [R "fp.u" (by simp [footRegs])]; exact h.ureg
  · rw [R "fp.res" (by simp [footRegs])]; exact h.res
  · rw [R "fp.go" (by simp [footRegs]), R "fp.p" (by simp [footRegs])]; exact h.go

end Frontier.CHD.BL2
