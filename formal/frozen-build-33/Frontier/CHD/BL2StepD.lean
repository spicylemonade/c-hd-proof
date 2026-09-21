import Frontier.CHD.BL2StepC

/-!
# Frontier.CHD.BL2StepD — B-L2: precise frames and bookkeeping for the branch lemmas (agent-09, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {c : FPCtx G s} {T : Finset (Fin G.n)} {slB slX : String}
  {u : Fin G.n}

/-- Registers read by `MyRep`. -/
def myRepRegs : List String := ["gM", "fp.kl", "fp.k", "fp.hsz"]
/-- Arrays read by `MyRep`. -/
def myRepArrs : List String :=
  ["gHead", "fp.H", "fp.hp", "fp.inH", "fp.K", "fp.inK", "fp.val", "fp.fm", "fp.kp"]

theorem myRepRegs_sub : myRepRegs ⊆ myRegs := by
  intro x hx; simp [myRepRegs] at hx; simp [myRegs]; tauto
theorem myRepArrs_sub : myRepArrs ⊆ myArrs := by
  intro x hx; simp [myRepArrs] at hx; simp [myArrs]; tauto

/-- `MyRep` with its exact read set. -/
theorem MyRep.frameR {σ : SSt G s} {st st' : State V} {wa va wr vr : List String}
    (h : MyRep c T σ st) (hu : Unchanged st st' wa va wr vr)
    (hwa : Disj wa myRepArrs) (hwr : Disj wr myRepRegs) : MyRep c T σ st' := by
  have A : ∀ a ∈ myRepArrs, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a :=
    fun a ha => hu.warr a (fun h' => hwa a h' ha)
  have R : ∀ x ∈ myRepRegs, st'.w x = st.w x := fun x hx => hu.wreg x (fun h' => hwr x h' hx)
  have aH := A "gHead" (by simp [myRepArrs])
  have aHp := A "fp.H" (by simp [myRepArrs])
  have ahp := A "fp.hp" (by simp [myRepArrs])
  have ainH := A "fp.inH" (by simp [myRepArrs])
  have aK := A "fp.K" (by simp [myRepArrs])
  have ainK := A "fp.inK" (by simp [myRepArrs])
  have aval := A "fp.val" (by simp [myRepArrs])
  have afm := A "fp.fm" (by simp [myRepArrs])
  have akp := A "fp.kp" (by simp [myRepArrs])
  obtain ⟨hl, hnd, hset, hsz, hcap, harr, hpL, hpos, hbL, hb⟩ := h.heap
  exact ⟨by rw [R "gM" (by simp [myRepRegs])]; exact h.gM, by rw [aH.2]; exact h.headL,
    fun q => by rw [aH.1]; exact h.head q,
    ⟨hl, hnd, hset, by rw [R "fp.hsz" (by simp [myRepRegs])]; exact hsz, by rw [aHp.2]; exact hcap,
      fun i hi => by rw [aHp.1]; exact harr i hi, by rw [ahp.2]; exact hpL,
      fun i hi => by rw [ahp.1]; exact hpos i hi, by rw [ainH.2]; exact hbL,
      fun v => by rw [ainH.1]; exact hb v⟩,
    by rw [R "fp.kl" (by simp [myRepRegs])]; exact h.kl, by rw [aK.2]; exact h.kcap,
    fun i hi => by rw [aK.1]; exact h.karr i hi,
    ⟨by rw [ainK.2]; exact h.inK.1, fun v => by rw [ainK.1]; exact h.inK.2 v⟩,
    ⟨by rw [aval.2]; exact h.val.1, fun v => by rw [aval.1]; exact h.val.2 v⟩,
    ⟨by rw [afm.2]; exact h.fm.1, fun v => by rw [afm.1]; exact h.fm.2 v⟩,
    by rw [akp.2]; exact h.kpL, fun v hv => by rw [akp.1]; exact h.kp v hv,
    by rw [R "fp.k" (by simp [myRepRegs])]; exact h.kreg, h.Knd, h.HK⟩

/-- `MyRep` depends on the search state only through `H`, `K`, `val`, `kpar`. -/
theorem MyRep.congr_σ {σ σ' : SSt G s} {st : State V} (h : MyRep c T σ st)
    (hH : σ'.H = σ.H) (hK : σ'.K = σ.K) (hval : σ'.val = σ.val) (hkp : σ'.kpar = σ.kpar) :
    MyRep c T σ' st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, h2, h3, hH ▸ h4, hK ▸ h5, h6, hK ▸ h7, hK ▸ h8, hval ▸ h9, h10, h11, ?_, h13,
    hK ▸ h14, by rw [hH, hK]; exact h15⟩
  intro v hv; rw [hkp]; exact h12 v (hK ▸ hv)

/-- `Cursor` with its exact read set. -/
theorem Cursor.frameR {D : Finset (Fin G.m)} {Lrem : List (Fin G.m)} {st st' : State V}
    {wa va wr vr : List String} (h : Cursor st c D u Lrem) (hu : Unchanged st st' wa va wr vr)
    (hwa : Disj wa ["gHd", "gNxt"]) (hwr : Disj wr ["fp.p", "fp.pp"]) :
    Cursor st' c D u Lrem := by
  have hF := hu.warr "gHd" (fun h' => hwa _ h' (by simp))
  have hN := hu.warr "gNxt" (fun h' => hwa _ h' (by simp))
  have hp := hu.wreg "fp.p" (fun h' => hwr _ h' (by simp))
  have hpp := hu.wreg "fp.pp" (fun h' => hwr _ h' (by simp))
  obtain ⟨h1, h2, Pre, hPre, hs1, hs2, h3⟩ := h
  refine ⟨by rw [hF.2]; exact h1, fun w hw => ?_, Pre, hPre, ?_, ?_, ?_⟩
  · rw [hF.1]; exact (h2 w hw).of_eq hN.1 hN.2
  · rw [hF.1, hp]; exact hs1.of_eq hN.1 hN.2
  · rw [hp]; exact hs2.of_eq hN.1 hN.2
  · rw [hpp]; exact h3

theorem OutRep.frameR {D : Finset (Fin G.m)} {st st' : State V} {wa va wr vr : List String}
    (h : OutRep st c D) (hu : Unchanged st st' wa va wr vr) (hwa : Disj wa ["gHd", "gNxt"]) :
    OutRep st' c D := by
  have hF := hu.warr "gHd" (fun h' => hwa _ h' (by simp))
  have hN := hu.warr "gNxt" (fun h' => hwa _ h' (by simp))
  refine ⟨by rw [hF.2]; exact h.1, fun w => ?_⟩
  rw [hF.1]; exact (h.2 w).of_eq hN.1 hN.2

/-- Bookkeeping across one iteration. -/
theorem Book.step {st₀ st st' : State V} {n k : ℕ} {wa va wr vr : List String}
    (hB : Book LI st₀ st n) (hu : Unchanged st st' wa va wr vr)
    (hwa : wa ⊆ scanWA LI) (hva : va ⊆ scanVA LI) (hwr : wr ⊆ scanWR LI) (hvr : vr ⊆ scanVR LI)
    (hc0 : st.cost ≤ st'.cost) (hc : st'.cost ≤ st.cost + Kit LI) (hk : 1 ≤ k) :
    Book LI st₀ st' (n + k) := by
  refine ⟨hB.unch.trans (hu.mono hwa hva hwr hvr), hB.cost0.trans hc0, ?_⟩
  have := hB.cost
  have : Kit LI * (n + k) = Kit LI * n + Kit LI * k := Nat.mul_add _ _ _
  have : Kit LI ≤ Kit LI * k := Nat.le_mul_of_pos_right _ hk
  omega

theorem mem_scanWR_my {x : String} (hx : x ∈ myRegs) : x ∈ scanWR LI := by
  simp only [scanWR, List.mem_append]; tauto
theorem mem_scanWR_ifc {x : String} (hx : x ∈ [LI.ru, LI.re, LI.rv]) : x ∈ scanWR LI := by
  simp only [scanWR, List.mem_append]; tauto
theorem mem_scanWA_my {x : String} (hx : x ∈ myArrs) : x ∈ scanWA LI := by
  simp only [scanWA, List.mem_append]; tauto
theorem candWR_sub : LI.candWR ⊆ scanWR LI := by
  intro x hx; simp only [scanWR, List.mem_append]; tauto
theorem cmpWR_sub : LI.cmpWR ⊆ scanWR LI := by
  intro x hx; simp only [scanWR, List.mem_append]; tauto
theorem relWR_sub : LI.relWR ⊆ scanWR LI := by
  intro x hx; simp only [scanWR, List.mem_append]; tauto
theorem candVR_sub : LI.candVR ⊆ scanVR LI := by
  intro x hx; simp only [scanVR, List.mem_append]; tauto
theorem cmpVR_sub : LI.cmpVR ⊆ scanVR LI := by
  intro x hx; simp only [scanVR, List.mem_append]; tauto
theorem relVR_sub : LI.relVR ⊆ scanVR LI := by
  intro x hx; simp only [scanVR, List.mem_append]; tauto
theorem relWA_sub : LI.relWA ⊆ scanWA LI := by
  intro x hx; simp only [scanWA, List.mem_append]; tauto
theorem relVA_sub : LI.relVA ⊆ scanVA LI := fun _ h => h

/-- Closes goals `l ⊆ scanWR LI` (etc.) for concatenations of known name lists. -/
syntax "scan_sub" : tactic
macro_rules
  | `(tactic| scan_sub) => `(tactic| (simp only [List.append_subset, List.cons_subset, List.nil_subset, and_true, true_and]; all_goals (repeat' apply And.intro); all_goals (first | exact candWR_sub | exact cmpWR_sub | exact relWR_sub | exact candVR_sub | exact cmpVR_sub | exact relVR_sub | exact relWA_sub | exact relVA_sub | exact List.nil_subset _ | (apply mem_scanWR_my; decide) | (apply mem_scanWA_my; decide) | (apply mem_scanWR_ifc; simp; done))))

/-- Stopping the scan with result code `r`. -/
theorem stop_spec {st : State V} {r : ℕ} (hr : r < st.cap) (h0 : 0 < st.cap) :
    Runs ops (fpStop r) st (fun st' => st'.w "fp.res" = r ∧ st'.w "fp.go" = 0 ∧
      (∀ x, x ≠ "fp.res" → x ≠ "fp.go" → st'.w x = st.w x) ∧
      Unchanged st st' [] [] ["fp.res", "fp.go"] [] ∧ st'.cost = st.cost + 2) := by
  apply wp_sound
  simp only [fpStop, wp, evalW_lit', fit, hr, h0, ite_true, State.charge_cap, State.setW_cap]
  refine ⟨by simp, by simp, fun x h1 h2 => by simp [h1, h2], ?_, by simp⟩
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
  simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
  simp [hx.1, hx.2]

theorem sub_scanWR_my {x : String} (hx : x ∈ myRegs) : x ∈ scanWR LI := by
  simp only [scanWR, List.mem_append]; tauto

theorem sub_scanWR_ifc {x : String} (hx : x ∈ [LI.ru, LI.re, LI.rv]) : x ∈ scanWR LI := by
  simp only [scanWR, List.mem_append]; tauto

theorem sub_scanWR_cand {x : String} (hx : x ∈ LI.candWR) : x ∈ scanWR LI := by
  simp only [scanWR, List.mem_append]; tauto

theorem sub_scanWR_cmp {x : String} (hx : x ∈ LI.cmpWR) : x ∈ scanWR LI := by
  simp only [scanWR, List.mem_append]; tauto

theorem sub_scanWR_rel {x : String} (hx : x ∈ LI.relWR) : x ∈ scanWR LI := by
  simp only [scanWR, List.mem_append]; tauto

theorem sub_scanVR_cand {x : String} (hx : x ∈ LI.candVR) : x ∈ scanVR LI := by
  simp only [scanVR, List.mem_append]; tauto

theorem sub_scanVR_cmp {x : String} (hx : x ∈ LI.cmpVR) : x ∈ scanVR LI := by
  simp only [scanVR, List.mem_append]; tauto

theorem sub_scanVR_rel {x : String} (hx : x ∈ LI.relVR) : x ∈ scanVR LI := by
  simp only [scanVR, List.mem_append]; tauto

theorem sub_scanWA_my {x : String} (hx : x ∈ myArrs) : x ∈ scanWA LI := by
  simp only [scanWA, List.mem_append]; tauto

end Frontier.CHD.BL2
