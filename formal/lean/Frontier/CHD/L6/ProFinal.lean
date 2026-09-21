import Frontier.CHD.L6.ProMain
import Frontier.CHD.DGlobal
import Frontier.CHD.L6.TauCap

/-!
# `ProSpec` for the spine prologue (agent-10)

`proSpec_spinePro`: `spinePro fpPro dPro` establishes agent-08's `CallIn` at level `LF` with the
top-level arguments (`TopInOf`), keeps the spine frame, and costs `≤ (13000 + 34 (Kf + Kd)) Tchd`,
given the two allocation hooks (`HookSpec`) and the footprint compatibilities of `PhiR`.
NON-GATE (Layer B, spine prologue).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

/-! ## The base-case heap arrays -/

def heapProg : Stmt :=
  seq (walloc "hp_A" (var "n")) (seq (walloc "hp_P" (var "n")) (wset "hp_n" (lit 0)))

theorem heapProg_runs {V : Type} {ops : VOps V} (st : State V) (N : ℕ) (hn : st.w "n" = N)
    (hcap : 1 < st.cap) :
    Runs ops heapProg st (fun r => r.w "hp_n" = 0 ∧ r.wlen "hp_A" = N ∧ r.wlen "hp_P" = N ∧
      (∀ v, r.wa "hp_P" v = 0) ∧ Unchanged st r ["hp_A", "hp_P"] [] ["hp_n"] [] ∧
      r.cost = st.cost + 2 * N + 3) := by
  unfold heapProg
  refine runs_seq (runs_walloc (k := N) (by simp [hn]) ?_)
  refine runs_seq (runs_walloc (k := N) (by simp [hn]) ?_)
  refine runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_
  refine ⟨by simp, by simp [State.allocW], by simp [State.allocW], fun v => by simp [State.allocW],
    ?_, by simp [State.allocW]; ring⟩
  rw [unchanged_charge_iff, unchanged_setW_iff (by simp), unchanged_charge_iff,
    unchanged_allocW_iff (by simp), unchanged_charge_iff, unchanged_allocW_iff (by simp)]
  exact Unchanged.refl _ _ _ _ _

/-- **The spine prologue.** -/
def spinePro (fpPro dPro : Stmt) : Stmt :=
  seq partA (seq heapProg (seq fpPro (seq dPro (seq blowProg frameProg))))

/-! ## The hook contracts -/

/-- Word arrays the prologue relies on after the hooks. -/
def protWA : List String :=
  ["gSt", "gHead", "gHd", "gNxt", "cp.tau", "cp.M", "gKeep", "gRep", "hp_A", "hp_P", "sp.xm",
    "sp.ptr"] ++ labW ++ RamSpine.rowArrs ++ RamSpine.lenArrs ++ slotW
/-- Value arrays the prologue relies on after the hooks. -/
def protVA : List String := ["gW", "sl.l"] ++ labV
/-- Word registers the prologue relies on after the hooks. -/
def protWR : List String :=
  ["gS", "gN", "gM", "cn", "cm", "gD", "cp.lg", "cp.dd", "cp.t", "cp.k", "cp.L", "n", "pr.tn",
    "core.n", "core.s", "core.m", "hp_n"]

/-- The state at a hook: `PreIn`, `n = |V|`, `pr.tn = Tnat`. -/
structure HookIn (e : ℕ) (ps : List Stmt) (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ)
    (st : State ℝ≥0) : Prop where
  pre : PreIn e ps H src cn cm c0 st
  n : st.w "n" = H.n
  tn : st.w "pr.tn" = CostSkeleton.Tnat cn cm

/-- **An allocation hook**: from `HookIn`, `prog` establishes `Post`, writes only `wa va wr vr`
(which avoid the protected names), at cost `≤ Kh (Tnat + 1)`. -/
def HookSpec (e : ℕ) (ps : List Stmt) (prog : Stmt)
    (Post : ∀ (H : Graph) (_src : Fin H.n) (_cn _cm : ℕ), State ℝ≥0 → Prop)
    (wa va wr vr : List String) (Kh : ℕ) : Prop :=
  (∀ a ∈ wa, a ∉ protWA) ∧ (∀ a ∈ va, a ∉ protVA) ∧ (∀ a ∈ wr, a ∉ protWR) ∧
  ∀ (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ) (st : State ℝ≥0), HookIn e ps H src cn cm c0 st →
    Runs realOps prog st (fun r => Post H src cn cm r ∧ Unchanged st r wa va wr vr ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + Kh * (CostSkeleton.Tnat cn cm + 1))

/-! ## `PreIn` under frames -/

theorem PreIn.of_unchanged {e : ℕ} {ps : List Stmt} {H : Graph} {src : Fin H.n} {cn cm c0 : ℕ}
    {t r : State ℝ≥0} {wa va wr vr : List String} (h : PreIn e ps H src cn cm c0 t)
    (hu : Unchanged t r wa va wr vr) (hwa : ∀ a ∈ wa, a ∉ protWA) (hva : ∀ a ∈ va, a ∉ protVA)
    (hwr : ∀ a ∈ wr, a ∉ protWR) (hc : t.cost ≤ r.cost) : PreIn e ps H src cn cm c0 r where
  core := h.core.of_unchanged hu (fun hm => hwa _ hm (by simp [protWA]))
    (fun hm => hwa _ hm (by simp [protWA])) (fun hm => hwa _ hm (by simp [protWA]))
    (fun hm => hwa _ hm (by simp [protWA])) (fun hm => hva _ hm (by simp [protVA]))
    (fun hm => hwr _ hm (by simp [protWR])) (fun hm => hwr _ hm (by simp [protWR]))
    (fun hm => hwr _ hm (by simp [protWR])) (fun hm => hwr _ hm (by simp [protWR]))
    (fun hm => hwr _ hm (by simp [protWR])) (fun hm => hwr _ hm (by simp [protWR]))
  lg := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [protWR]))]; exact h.lg
  dd := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [protWR]))]; exact h.dd
  tt := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [protWR]))]; exact h.tt
  k := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [protWR]))]; exact h.k
  L := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [protWR]))]; exact h.L
  tau l hl := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [protWA]))).1]; exact h.tau l hl
  M l hl := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [protWA]))).1]; exact h.M l hl
  tauLen := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [protWA]))).2]; exact h.tauLen
  MLen := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [protWA]))).2]; exact h.MLen
  lab := h.lab.of_unchanged hu (fun a ha hm => hwa _ hm (by simp [protWA, ha]))
    (fun hm => hva _ hm (by simp [protVA, labV])) hc


/-- Word arrays `PreIn` relies on. -/
def pinWA : List String := ["gSt", "gHead", "gHd", "gNxt", "cp.tau", "cp.M"] ++ labW
/-- Value arrays `PreIn` relies on. -/
def pinVA : List String := ["gW"] ++ labV
/-- Word registers `PreIn` relies on. -/
def pinWR : List String := ["gS", "gN", "gM", "cn", "cm", "gD", "cp.lg", "cp.dd", "cp.t", "cp.k",
  "cp.L"]

theorem PreIn.of_unchanged' {e : ℕ} {ps : List Stmt} {H : Graph} {src : Fin H.n} {cn cm c0 : ℕ}
    {t r : State ℝ≥0} {wa va wr vr : List String} (h : PreIn e ps H src cn cm c0 t)
    (hu : Unchanged t r wa va wr vr) (hwa : ∀ a ∈ wa, a ∉ pinWA) (hva : ∀ a ∈ va, a ∉ pinVA)
    (hwr : ∀ a ∈ wr, a ∉ pinWR) (hc : t.cost ≤ r.cost) : PreIn e ps H src cn cm c0 r where
  core := h.core.of_unchanged hu (fun hm => hwa _ hm (by simp [pinWA]))
    (fun hm => hwa _ hm (by simp [pinWA])) (fun hm => hwa _ hm (by simp [pinWA]))
    (fun hm => hwa _ hm (by simp [pinWA])) (fun hm => hva _ hm (by simp [pinVA]))
    (fun hm => hwr _ hm (by simp [pinWR])) (fun hm => hwr _ hm (by simp [pinWR]))
    (fun hm => hwr _ hm (by simp [pinWR])) (fun hm => hwr _ hm (by simp [pinWR]))
    (fun hm => hwr _ hm (by simp [pinWR])) (fun hm => hwr _ hm (by simp [pinWR]))
  lg := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [pinWR]))]; exact h.lg
  dd := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [pinWR]))]; exact h.dd
  tt := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [pinWR]))]; exact h.tt
  k := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [pinWR]))]; exact h.k
  L := by rw [hu.wreg _ (fun hm => hwr _ hm (by simp [pinWR]))]; exact h.L
  tau l hl := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [pinWA]))).1]; exact h.tau l hl
  M l hl := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [pinWA]))).1]; exact h.M l hl
  tauLen := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [pinWA]))).2]; exact h.tauLen
  MLen := by rw [(hu.warr _ (fun hm => hwa _ hm (by simp [pinWA]))).2]; exact h.MLen
  lab := h.lab.of_unchanged hu (fun a ha hm => hwa _ hm (by simp [pinWA, ha]))
    (fun hm => hva _ hm (by simp [pinVA, labV])) hc

theorem pre_sub_prot : (∀ a ∈ pinWA, a ∈ protWA) ∧ (∀ a ∈ pinVA, a ∈ protVA) ∧
    (∀ a ∈ pinWR, a ∈ protWR) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro a ha <;> simp [pinWA, pinVA, pinWR, protWA, protVA, protWR, labW, labV] at ha ⊢ <;>
    tauto

theorem blowProg_noalloc : DGlob.NoAlloc blowProg := by
  simp [blowProg, storeSlot, DGlob.NoAlloc]

theorem frameProg_noalloc : DGlob.NoAlloc frameProg := by
  simp [frameProg, DGlob.NoAlloc]

/-! ## Capacity facts for the prologue -/

theorem capBig {e : ℕ} (he : 32 ≤ e) {ps : List Stmt} {H : Graph} {src : Fin H.n} {cn cm : ℕ}
    {t : State ℝ≥0} (hc : CoreIn e ps H src cn cm t) :
    (CostSkeleton.LF cn cm + 3) * (H.n + 1) + H.m + 8 + 4 * CostSkeleton.LF cn cm + 6 +
      (CostSkeleton.LF cn cm + 3) * (H.n + H.m + 8) < t.cap := by
  have hcn1 := hc.cn_pos
  have hcm1 := hc.cm_pos
  have hX4 : 4 ≤ cn + cm + 2 := by omega
  have h6 := X_pow_ge hcn1 hcm1 he hc.cap
  have hsq := sq_lt_pow6 (cn + cm + 2) hX4
  have hL := LF_le cn cm hcn1
  have hN := hc.sizeN
  have hM := hc.sizeM
  have : (CostSkeleton.LF cn cm + 3) * (H.n + 1) + H.m + 8 + 4 * CostSkeleton.LF cn cm + 6 +
      (CostSkeleton.LF cn cm + 3) * (H.n + H.m + 8) ≤ 64 * (cn + cm + 2) ^ 2 := by nlinarith
  omega

/-! ## The prologue specification -/

set_option maxHeartbeats 4000000 in
theorem proSpec_spinePro {e : ℕ} (he : 32 ≤ e) {ps : List Stmt} {body : Stmt}
    (hps : ps[RamSpine.P_bmssp]? = some body)
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
      (∀ a ∈ (PIf H src cn cm).pWR, a ∉ blowWR ++ ["lvl"])) :
    ProSpec e ps (spinePro fpPro dPro) (TopInOf DLf PIf body ps)
      (13000 + 34 * ((Kf : ℝ) + Kd)) := by
  intro H src cn cm c0 t hS
  have hP : PreIn e ps H src cn cm c0 t := hS.toPreIn
  have hc := hP.core
  have hcn1 := hc.cn_pos
  have hcm1 := hc.cm_pos
  have hcapB := capBig he hc
  have hsub := pre_sub_prot
  obtain ⟨L, hLdef⟩ : ∃ L, L = CostSkeleton.LF cn cm := ⟨_, rfl⟩
  have hnpos : 0 < H.n := Fin.pos src
  unfold spinePro
  -- part A
  refine runs_seq ((partA_runs he hP).cost_mono.mono ?_)
  rintro t1 ⟨hA, hm1⟩
  have hA_pin : ∀ a ∈ spAllocW.map Prod.fst, a ∉ pinWA := by decide
  have hP1 : PreIn e ps H src cn cm c0 t1 :=
    hP.of_unchanged' hA.U hA_pin (by decide) (by decide) hm1
  have hcap1 : t1.cap = t.cap := hA.U.cap
  -- heap arrays
  refine runs_seq ((heapProg_runs (ops := realOps) t1 H.n hA.n (by omega)).mono ?_)
  rintro t2 ⟨h2n0, h2A, h2P, h2Pz, hU2, hc2⟩
  have hP2 : PreIn e ps H src cn cm c0 t2 :=
    hP1.of_unchanged' hU2 (by decide) (by decide) (by decide) (by omega)
  have h2n : t2.w "n" = H.n := by rw [hU2.wreg _ (by decide)]; exact hA.n
  have h2tn : t2.w "pr.tn" = CostSkeleton.Tnat cn cm := by rw [hU2.wreg _ (by decide)]; exact hA.tn
  -- the FindPivots hook
  obtain ⟨hFwa, hFva, hFwr, hFrun⟩ := hFP
  refine runs_seq ((hFrun H src cn cm c0 t2 ⟨hP2, h2n, h2tn⟩).mono ?_)
  rintro t3 ⟨hPhi3, hU3, hm3, hc3⟩
  have pin_of : ∀ {l : List String}, (∀ a ∈ l, a ∉ protWA) → ∀ a ∈ l, a ∉ pinWA :=
    fun h a ha hp => h a ha (hsub.1 a hp)
  have pinV_of : ∀ {l : List String}, (∀ a ∈ l, a ∉ protVA) → ∀ a ∈ l, a ∉ pinVA :=
    fun h a ha hp => h a ha (hsub.2.1 a hp)
  have pinR_of : ∀ {l : List String}, (∀ a ∈ l, a ∉ protWR) → ∀ a ∈ l, a ∉ pinWR :=
    fun h a ha hp => h a ha (hsub.2.2 a hp)
  have hP3 : PreIn e ps H src cn cm c0 t3 :=
    hP2.of_unchanged' hU3 (pin_of hFwa) (pinV_of hFva) (pinR_of hFwr) hm3
  have h3n : t3.w "n" = H.n := by rw [hU3.wreg _ (fun hm => hFwr _ hm (by decide))]; exact h2n
  have h3tn : t3.w "pr.tn" = CostSkeleton.Tnat cn cm := by
    rw [hU3.wreg _ (fun hm => hFwr _ hm (by decide))]; exact h2tn
  -- the D-layer hook
  obtain ⟨hDwa, hDva, hDwr, hDrun⟩ := hD
  refine runs_seq ((hDrun H src cn cm c0 t3 ⟨hP3, h3n, h3tn⟩).mono ?_)
  rintro t4 ⟨⟨⟨Ds, hDR4⟩, hUse4⟩, hU4, hm4, hc4⟩
  have hP4 : PreIn e ps H src cn cm c0 t4 :=
    hP3.of_unchanged' hU4 (pin_of hDwa) (pinV_of hDva) (pinR_of hDwr) hm4
  have hPhi4 : (PIf H src cn cm).PhiR t4 ∅ :=
    (PIf H src cn cm).frame t3 t4 ∅ dwa dva dwr dvr hPhi3 hU4 (hPd H src cn cm).1
      (hPd H src cn cm).2
  -- frames of the arrays allocated in part A, from t1 to t4
  have prot14 : ∀ a ∈ protWA, a ∉ ["hp_A", "hp_P"] → t4.wa a = t1.wa a ∧ t4.wlen a = t1.wlen a := by
    intro a ha hnh
    have e2 := hU2.warr a hnh
    have e3 := hU3.warr a (fun hm => hFwa _ hm ha)
    have e4 := hU4.warr a (fun hm => hDwa _ hm ha)
    exact ⟨by rw [e4.1, e3.1, e2.1], by rw [e4.2, e3.2, e2.2]⟩
  have protV14 : ∀ a ∈ protVA, t4.va a = t1.va a ∧ t4.vlen a = t1.vlen a := by
    intro a ha
    have e2 := hU2.varr a (by simp)
    have e3 := hU3.varr a (fun hm => hFva _ hm ha)
    have e4 := hU4.varr a (fun hm => hDva _ hm ha)
    exact ⟨by rw [e4.1, e3.1, e2.1], by rw [e4.2, e3.2, e2.2]⟩
  have hL4 : t4.w "cp.L" = L := by rw [hLdef]; exact hP4.L
  have hS4 : t4.w "gS" = src := hP4.core.gS
  have hn4 : t4.w "n" = H.n := by rw [hU4.wreg _ (fun hm => hDwr _ hm (by decide))]; exact h3n
  have hcap4 : t4.cap = t.cap := by rw [hU4.cap, hU3.cap, hU2.cap, hcap1]
  have hslen4 : ∀ i < 4 * (L + 2), SlotLens t4 i := by
    intro i hi
    have hv := (protV14 "sl.l" (by simp [protVA])).2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv, hA.slotv.1, ← hLdef]; exact hi
    all_goals
      first
      | (rw [(prot14 "sl.h" (by simp [protWA, slotW]) (by decide)).2,
          (hA.slotw "sl.h" (by simp [slotW])).1, ← hLdef]; exact hi)
      | (rw [(prot14 "sl.v" (by simp [protWA, slotW]) (by decide)).2,
          (hA.slotw "sl.v" (by simp [slotW])).1, ← hLdef]; exact hi)
      | (rw [(prot14 "sl.e" (by simp [protWA, slotW]) (by decide)).2,
          (hA.slotw "sl.e" (by simp [slotW])).1, ← hLdef]; exact hi)
      | (rw [(prot14 "sl.r" (by simp [protWA, slotW]) (by decide)).2,
          (hA.slotw "sl.r" (by simp [slotW])).1, ← hLdef]; exact hi)
      | (rw [(prot14 "sl.f" (by simp [protWA, slotW]) (by decide)).2,
          (hA.slotw "sl.f" (by simp [slotW])).1, ← hLdef]; exact hi)
  -- the Blow slot
  refine runs_seq ((DGlob.Runs.keep_len (blowProg_runs src t4 L hS4 hL4 (hslen4 _ (by omega))
    (by rw [hcap4, hLdef]; omega)) blowProg_noalloc).mono ?_)
  rintro t5 ⟨⟨hBlow, hSoth5, hU5, hc5⟩, hwl5, hvl5⟩
  have hP5 : PreIn e ps H src cn cm c0 t5 :=
    hP4.of_unchanged' hU5 (by decide) (by decide) (by decide) (by omega)
  have hn5 : t5.w "n" = H.n := by rw [hU5.wreg _ (by decide)]; exact hn4
  have hL5 : t5.w "cp.L" = L := by rw [hU5.wreg _ (by decide)]; exact hL4
  have hS5 : t5.w "gS" = src := hP5.core.gS
  have hcap5 : t5.cap = t.cap := by rw [hU5.cap, hcap4]
  have hrowA : ∀ a ∈ RamSpine.rowArrs, t5.wlen a = (L + 2) * H.n ∧ t5.wa a = t1.wa a ∨
      a ∈ slotW := by
    intro a ha
    left
    have hp : a ∈ protWA := by simp [protWA, ha]
    have hnh : a ∉ ["hp_A", "hp_P"] := by
      intro h; simp [RamSpine.rowArrs] at ha; simp at h; rcases h with rfl | rfl <;> simp at ha
    have hns : a ∉ slotW := by
      intro h; simp [RamSpine.rowArrs] at ha; simp [slotW] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp at ha
    have e14 := prot14 a hp hnh
    refine ⟨by rw [hwl5 a, e14.2, (hA.rows a ha).1, ← hLdef], ?_⟩
    rw [(hU5.warr a hns).1, e14.1]
  have hSlen5 : (L + 1) * H.n ≤ t5.wlen "S" := by
    rcases hrowA "S" (by simp [RamSpine.rowArrs]) with ⟨h1, -⟩ | h
    · rw [h1]; exact Nat.mul_le_mul_right _ (by omega)
    · simp [slotW] at h
  have hSLlen5 : L < t5.wlen "S.len" := by
    have hp : "S.len" ∈ protWA := by simp [protWA, RamSpine.lenArrs]
    rw [hwl5, (prot14 "S.len" hp (by decide)).2, (hA.lens "S.len" (by simp [RamSpine.lenArrs])).1,
      ← hLdef]
    omega
  refine (DGlob.Runs.keep_len (frameProg_runs (ops := realOps) t5 H.n L src hn5 hL5 hS5 hnpos
    hSlen5 hSLlen5 (by rw [hcap5, hLdef]; nlinarith)) frameProg_noalloc).mono ?_
  rintro r ⟨⟨hSr, hSothr, hSLr, hSLothr, hlvl, hU6, hc6⟩, hwl6, hvl6⟩
  have hPr : PreIn e ps H src cn cm c0 r :=
    hP5.of_unchanged' hU6 (by decide) (by decide) (by decide) (by omega)
  have hcapr : r.cap = t.cap := by rw [hU6.cap, hcap5]
  -- composed frames
  have hU46 : Unchanged t4 r (slotW ++ ["S", "S.len"]) ["sl.l"] (blowWR ++ ["lvl"]) blowVR :=
    (hU5.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hU6.mono (by simp) (by simp) (by simp) (by simp))
  have hvc : vc (G := H) r = vc (G := H) t4 := by
    funext v; show r.wa "vcnt" v = t4.wa "vcnt" v
    rw [(hU46.warr "vcnt" (by decide)).1]
  -- arrays of part A at r
  have arrA : ∀ a ∈ protWA, a ∉ ["hp_A", "hp_P"] → a ∉ slotW ++ ["S", "S.len"] →
      r.wa a = t1.wa a ∧ r.wlen a = t1.wlen a := by
    intro a hp hnh hns
    have e14 := prot14 a hp hnh
    exact ⟨by rw [(hU46.warr a hns).1, e14.1], by rw [(hU46.warr a hns).2, e14.2]⟩
  have lenA : ∀ a ∈ protWA, a ∉ ["hp_A", "hp_P"] → r.wlen a = t1.wlen a := by
    intro a hp hnh
    rw [hwl6, hwl5, (prot14 a hp hnh).2]
  have rowP : ∀ a ∈ RamSpine.rowArrs, a ∈ protWA := fun a ha => by simp [protWA, ha]
  have rowH : ∀ a ∈ RamSpine.rowArrs, a ∉ ["hp_A", "hp_P"] := by decide
  have rowS : ∀ a ∈ RamSpine.rowArrs, a ∉ slotW ++ ["S", "S.len"] → True := fun _ _ _ => trivial
  have lenP : ∀ a ∈ RamSpine.lenArrs, a ∈ protWA := fun a ha => by simp [protWA, ha]
  have lenH : ∀ a ∈ RamSpine.lenArrs, a ∉ ["hp_A", "hp_P"] := by decide
  have hTopArgs : RamSpine.CallIn (DLf H src cn cm) (PIf H src cn cm).PhiR (CostSkeleton.LF cn cm)
      body (BM.chdTau (CostSkeleton.tF cn cm)) (BM.chdM (CostSkeleton.tF cn cm)) r
      (CostSkeleton.LF cn cm) (BM.initLabels src src) ⊤ {src} (BM.initLabels src) ∅ BM.DGl.init Ds
      (H0 (G := H)) c0 := by
    subst hLdef
    refine ⟨hlvl, le_rfl, ?_, hPr.lab, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Static
      refine ⟨?_, hPr.core.gN, hPr.core.graph, hPr.core.csr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hPr.tau, hPr.M, ?_, ?_, ?_, ?_⟩
      · rw [hU6.wreg _ (by decide)]; exact hn5
      · rw [hPr.core.procs]; exact hps
      · intro a ha; rw [lenA a (rowP a ha) (rowH a ha), (hA.rows a ha).1]
      · intro a ha; rw [lenA a (lenP a ha) (lenH a ha), (hA.lens a ha).1]
      · intro i hi
        have h4 := hslen4 i (by have hi' : i < 4 * (CostSkeleton.LF cn cm + 2) := hi; exact hi')
        exact ⟨by rw [hvl6, hvl5]; exact h4.l, by rw [hwl6, hwl5]; exact h4.h,
          by rw [hwl6, hwl5]; exact h4.v, by rw [hwl6, hwl5]; exact h4.e,
          by rw [hwl6, hwl5]; exact h4.r, by rw [hwl6, hwl5]; exact h4.f⟩
      · rw [lenA "sp.xm" (by simp [protWA]) (by decide), hA.xm.1]
      · rw [lenA "sp.ptr" (by simp [protWA]) (by decide), hA.ptr]
      · rw [hPr.tauLen]
      · rw [hPr.MLen]
      · refine ⟨?_, ?_, ?_, fun v _ => ?_⟩
        · rw [hU6.wreg _ (by decide), hU5.wreg _ (by decide),
            hU4.wreg _ (fun hm => hDwr _ hm (by decide)),
            hU3.wreg _ (fun hm => hFwr _ hm (by decide))]
          exact h2n0
        · rw [hwl6, hwl5, (hU4.warr _ (fun hm => hDwa _ hm (by decide))).2,
            (hU3.warr _ (fun hm => hFwa _ hm (by decide))).2]
          exact h2A
        · rw [hwl6, hwl5, (hU4.warr _ (fun hm => hDwa _ hm (by decide))).2,
            (hU3.warr _ (fun hm => hFwa _ hm (by decide))).2]
          exact h2P
        · rw [(hU46.warr "hp_P" (by decide)).1, (hU4.warr _ (fun hm => hDwa _ hm (by decide))).1,
            (hU3.warr _ (fun hm => hFwa _ hm (by decide))).1]
          exact h2Pz v
      · rw [hcapr]; omega
      · intro l hl; rw [hcapr]; exact (tau_M_cap cn cm e t.cap hcn1 hcm1 he hc.cap).1 l hl
      · intro l hl; rw [hcapr]; exact chdM_two_cap cn cm e t.cap hcn1 hcm1 he hc.cap l hl
    · -- the D layer
      refine (DLf H src cn cm).frame t4 r (H0 (G := H)) (H0 (G := H)) BM.DGl.init Ds
        (CostSkeleton.LF cn cm + 1) _ _ _ _ hDR4 hU46 ?_ ?_ ?_ (by rw [hvc]; exact HExt.refl _ _)
      · intro a ha hm
        exact (DLf H src cn cm).dWA_ok a ha
          ((by decide : ∀ b ∈ slotW ++ ["S", "S.len"], b ∈ RamSpine.spArrs) a hm)
      · intro a ha hm
        exact (DLf H src cn cm).dVA_ok a ha (by simp at hm; simp [hm])
      · intro a ha hm
        exact (DLf H src cn cm).dWR_ok a ha
          ((by decide : ∀ b ∈ blowWR ++ ["lvl"], b ∈ RamSpine.spRegs) a hm)
    · exact (PIf H src cn cm).frame t4 r ∅ _ _ _ _ hPhi4 hU46 (hPb H src cn cm).1
        (hPb H src cn cm).2
    · -- the S row
      refine ⟨[(src : ℕ)], ⟨by simp; omega, by rw [hwl6]; exact hSlen5, by rw [hwl6]; exact hSLlen5,
        by rw [hSLr]; rfl, fun i hi => ?_⟩, by simp, fun x => ?_⟩
      · simp at hi; subst hi; simp; exact hSr
      · simp [eq_comm]
    · -- slot B[LF] = ⊤
      refine ⟨?_, fun q hq => absurd hq WithTop.top_ne_coe⟩
      simp only [iff_true]
      show r.wa "sl.f" (4 * CostSkeleton.LF cn cm) = 0
      rw [(hU6.warr "sl.f" (by decide)).1, (hSoth5 _ (by omega)).2 "sl.f" (by simp [slotW]),
        (prot14 "sl.f" (by simp [protWA, slotW]) (by decide)).1,
        (hA.slotw "sl.f" (by simp [slotW])).2]
    · -- slot Blow[LF]
      have h := hBlow.of_unchanged hU6 (by decide) (by simp)
      rw [hvc]; exact h
    · -- Clear
      refine ⟨fun l' _ x _ => ?_, fun l' _ x _ => ?_, fun x _ => ?_⟩
      · rw [(arrA "sp.g" (by simp [protWA, RamSpine.rowArrs]) (by decide) (by decide)).1,
          (hA.rows "sp.g" (by simp [RamSpine.rowArrs])).2]
      · rw [(arrA "sp.inU" (by simp [protWA, RamSpine.rowArrs]) (by decide) (by decide)).1,
          (hA.rows "sp.inU" (by simp [RamSpine.rowArrs])).2]
      · rw [(arrA "sp.xm" (by simp [protWA]) (by decide) (by decide)).1, hA.xm.2]
  have huseR : (DLf H src cn cm).use r ≤ 2 := by
    rw [(DLf H src cn cm).use_frame t4 r _ _ _ _ hU46 (fun a ha hm => (DLf H src cn cm).dWR_ok a ha
      ((by decide : ∀ b ∈ blowWR ++ ["lvl"], b ∈ RamSpine.spRegs) a hm))]
    exact hUse4
  refine ⟨⟨hPr.core.procs, masterIn_of_coreIn hc hS.mpos, huseR, Ds, hTopArgs⟩, ?_, ?_⟩
  · -- the spine frame
    have kp : ∀ a ∈ ["gKeep", "gRep"], r.wa a = t.wa a ∧ r.wlen a = t.wlen a := by
      intro a ha
      have e1 := arrA a (by simp at ha; rcases ha with rfl | rfl <;> simp [protWA])
        (by simp at ha; rcases ha with rfl | rfl <;> decide)
        (by simp at ha; rcases ha with rfl | rfl <;> decide)
      have e0 := hA.U.warr a (by simp at ha; rcases ha with rfl | rfl <;> decide)
      exact ⟨by rw [e1.1, e0.1], by rw [e1.2, e0.2]⟩
    have rg : ∀ x ∈ ["core.n", "core.s", "core.m"], r.w x = t.w x := by
      intro x hx
      have h1 : x ∉ ["lvl"] := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
      have h2 : x ∉ blowWR := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
      have h3 : x ∈ protWR := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
      have h4 : x ∉ ["hp_n"] := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
      have h5 : x ∉ sizeWR ++ tnWR := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
      rw [hU6.wreg _ h1, hU5.wreg _ h2, hU4.wreg _ (fun hm => hDwr _ hm h3),
        hU3.wreg _ (fun hm => hFwr _ hm h3), hU2.wreg _ h4, hA.U.wreg _ h5]
    exact ⟨kp "gKeep" (by simp), kp "gRep" (by simp), rg "core.n" (by simp),
      rg "core.s" (by simp), rg "core.m" (by simp), hcapr⟩
  · -- cost
    have hcA := hA.c
    have hnat : r.cost ≤ t.cost + 50 * ((CostSkeleton.LF cn cm + 2) * (H.n + 1)) +
        3 * Nat.log 2 (CostSkeleton.dd cn cm + 1) + 2 * H.n + 119 +
        Kf * (CostSkeleton.Tnat cn cm + 1) + Kd * (CostSkeleton.Tnat cn cm + 1) := by
      omega
    have hR : (r.cost : ℝ) ≤ t.cost + 50 * (((CostSkeleton.LF cn cm : ℝ) + 2) * ((H.n : ℝ) + 1)) +
        3 * (Nat.log 2 (CostSkeleton.dd cn cm + 1) : ℝ) + 2 * (H.n : ℝ) + 119 +
        Kf * ((CostSkeleton.Tnat cn cm : ℝ) + 1) + Kd * ((CostSkeleton.Tnat cn cm : ℝ) + 1) := by
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this; linarith
    have hT1 : (cn : ℝ) ≤ GateCCalc.Tchd cn cm := CostSkeleton.n_le_Tchd cn cm
    have hcnR : (1 : ℝ) ≤ cn := by exact_mod_cast hcn1
    have hcmR : (1 : ℝ) ≤ cm := by exact_mod_cast hcm1
    have hnle : (H.n : ℝ) ≤ 2 * cn := by exact_mod_cast hc.sizeN
    have hnm : cn ≤ cm + 1 := hc.cn_le
    have hLk := CostSkeleton.term_nLkF cn cm hcn1 hcm1 hnm
    have hk2 : (2 : ℝ) ≤ CostSkeleton.kF cn cm := by exact_mod_cast CostSkeleton.two_le_kF cn cm
    have hL0 : (0 : ℝ) ≤ CostSkeleton.LF cn cm := Nat.cast_nonneg _
    have hcL : (cn : ℝ) * CostSkeleton.LF cn cm ≤ 80 * GateCCalc.Tchd cn cm := by
      have : (cn : ℝ) * CostSkeleton.LF cn cm * 2 ≤ (cn : ℝ) * CostSkeleton.LF cn cm * CostSkeleton.kF cn cm :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
      linarith
    have hprod : ((CostSkeleton.LF cn cm : ℝ) + 2) * ((H.n : ℝ) + 1) ≤ 246 * GateCCalc.Tchd cn cm := by
      have h1 : (H.n : ℝ) + 1 ≤ 3 * cn := by linarith
      have h2 : ((CostSkeleton.LF cn cm : ℝ) + 2) * ((H.n : ℝ) + 1) ≤
          ((CostSkeleton.LF cn cm : ℝ) + 2) * (3 * cn) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      nlinarith
    have hTn := CostSkeleton.Tnat_le_Tchd cn cm hcn1
    have hlgT : (Nat.log 2 (CostSkeleton.dd cn cm + 1) : ℝ) ≤ CostSkeleton.Tnat cn cm := by
      have : Nat.log 2 (CostSkeleton.dd cn cm + 1) ≤ CostSkeleton.Tnat cn cm := by
        unfold CostSkeleton.Tnat; nlinarith
      exact_mod_cast this
    have hKf : (Kf : ℝ) * ((CostSkeleton.Tnat cn cm : ℝ) + 1) ≤ Kf * (34 * GateCCalc.Tchd cn cm) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have hKd : (Kd : ℝ) * ((CostSkeleton.Tnat cn cm : ℝ) + 1) ≤ Kd * (34 * GateCCalc.Tchd cn cm) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    nlinarith

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.proSpec_spinePro
