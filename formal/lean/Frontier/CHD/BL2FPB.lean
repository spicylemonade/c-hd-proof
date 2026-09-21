import Frontier.CHD.BL2At
import Frontier.CHD.RamBody
import Frontier.CHD.RamBodyF
import Frontier.CHD.FPBridge2
import Frontier.CHD.DGlobal
import Frontier.CHD.SynFrame

/-!
# Frontier.CHD.BL2FPB — B-L2 plugged into the spine: `PhiI` and agent-01's `FPB` (owner agent-09, NON-GATE)

* `phiI k hins hext : RamSpine.PhiI (Finset (Fin G.m))`: B-L2's persistent state `phiR`
  (`FPClean` for `outL G`, cap `k`) with its footprint and the disjoint-footprint frame;
* `fpAt_noalloc`: the FindPivots call allocates nothing (decided by evaluation), so all array lengths
  are kept (`DGlobal.Runs.keep_len`);
* `fpB_inst`: **`RamBody.FPB DL (phiI …) Inv (fpC (outL G) k hins hext) LF body fpAt τf Mf 524 351 l`**
  for every D layer whose names avoid the FindPivots write sets.  The word capacity FindPivots needs
  at every level `l ≤ LF` is part of B-L2's persistent state (`phiI … LF`: the cap never changes).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2Inst

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.BL2
  Frontier.CHD.PartitionRAM Frontier.CHD.RamLevel Frontier.CHD.LabIInst Frontier.CHD.LabTab
  Frontier.CHD.RamSpine Frontier.CHD.DGlob Frontier.CHD.Partition WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-! ## No allocation -/

/-- Boolean `NoAlloc`. -/
def noAllocB : Stmt → Bool
  | .walloc _ _ => false
  | .valloc _ _ => false
  | .call _ => false
  | .seq a b => noAllocB a && noAllocB b
  | .ite _ a b => noAllocB a && noAllocB b
  | .while _ b => noAllocB b
  | _ => true

theorem noAlloc_of_B : ∀ c : Stmt, noAllocB c = true → NoAlloc c
  | .skip, _ => trivial
  | .wset _ _, _ => trivial
  | .vset _ _, _ => trivial
  | .vle _ _ _, _ => trivial
  | .wstore _ _ _, _ => trivial
  | .vstore _ _ _, _ => trivial
  | .walloc _ _, h => by simp [noAllocB] at h
  | .valloc _ _, h => by simp [noAllocB] at h
  | .call _, h => by simp [noAllocB] at h
  | .seq a b, h => by
    simp only [noAllocB, Bool.and_eq_true] at h
    exact ⟨noAlloc_of_B a h.1, noAlloc_of_B b h.2⟩
  | .ite _ a b, h => by
    simp only [noAllocB, Bool.and_eq_true] at h
    exact ⟨noAlloc_of_B a h.1, noAlloc_of_B b h.2⟩
  | .while _ b, h => noAlloc_of_B b h

/-- **The FindPivots call allocates nothing and calls no procedure.** -/
theorem fpAt_noalloc : NoAlloc fpAt := noAlloc_of_B _ (by decide)

/-- **Call-free syntactic frame** for word arrays: a run of an allocation- and call-free
statement changes no word array outside the text's store targets `sWA c`. -/
theorem exec_wa_frame {V : Type} (ops : VOps V) :
    ∀ (f : ℕ) (c : Stmt) (st r : State V), NoAlloc c → exec ops f c st = some r →
      ∀ a, a ∉ sWA c → r.wa a = st.wa a := by
  intro f
  induction f with
  | zero => intro c st r _ h; simp [exec] at h
  | succ f ih =>
    intro c st r hc h a ha
    cases c with
    | skip => simp [exec] at h; subst h; rfl
    | wset x e =>
      cases he : evalW st e with
      | none => simp [exec, he] at h
      | some v => simp [exec, he] at h; subst h; rfl
    | vset x e =>
      cases he : evalV ops st e with
      | none => simp [exec, he] at h
      | some v => simp [exec, he] at h; subst h; rfl
    | vle x p q =>
      cases h1 : evalV ops st p with
      | none => simp [exec, h1] at h
      | some u =>
        cases h2 : evalV ops st q with
        | none => simp [exec, h1, h2] at h
        | some w =>
          cases h3 : fit st.cap (if ops.le u w then 1 else 0) with
          | none => simp [exec, h1, h2, h3] at h
          | some bit => simp [exec, h1, h2, h3] at h; subst h; rfl
    | wstore arr i e =>
      have hne : a ≠ arr := by simpa [sWA] using ha
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalW st e with
        | none => simp [exec, h1, h2] at h
        | some v =>
          by_cases hj : j < st.wlen arr
          · simp [exec, h1, h2, hj] at h; subst h; funext k; simp [hne]
          · simp [exec, h1, h2, hj] at h
    | vstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalV ops st e with
        | none => simp [exec, h1, h2] at h
        | some v =>
          by_cases hj : j < st.vlen arr
          · simp [exec, h1, h2, hj] at h; subst h; rfl
          · simp [exec, h1, h2, hj] at h
    | walloc arr e => exact absurd hc (by simp [NoAlloc])
    | valloc arr e => exact absurd hc (by simp [NoAlloc])
    | call p => exact absurd hc (by simp [NoAlloc])
    | seq p q =>
      simp only [sWA, List.mem_append, not_or] at ha
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      exact (ih q s' r hc.2 h2 a ha.2).trans (ih p st s' hc.1 h1 a ha.1)
    | ite e p q =>
      simp only [sWA, List.mem_append, not_or] at ha
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · exact (ih p _ r hc.1 h2 a ha.1).trans rfl
      · exact (ih q _ r hc.2 h2 a ha.2).trans rfl
    | «while» e b =>
      have hab : a ∉ sWA b := by simpa [sWA] using ha
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        exact (ih _ s' r hc h4 a ha).trans ((ih b _ s' hc h3 a hab).trans rfl)
      · simp at h2; subst h2; rfl

/-- `Runs` of an allocation- and call-free statement keeps the word arrays outside `sWA c`. -/
theorem Runs.keep_wa {V : Type} {ops : VOps V} {c : Stmt} {st : State V} {Q : State V → Prop}
    (h : Runs ops c st Q) (hc : NoAlloc c) :
    Runs ops c st (fun r => Q r ∧ ∀ a, a ∉ sWA c → r.wa a = st.wa a) := by
  obtain ⟨f, r, h1, h2⟩ := h
  exact ⟨f, r, h1, h2, exec_wa_frame ops f c st r hc h1⟩

set_option maxRecDepth 100000 in
/-- The FindPivots call never stores to the static arrays. -/
theorem fpAt_static : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], a ∉ sWA fpAt := by
  decide

set_option maxRecDepth 100000 in
theorem fpAt_static' : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "hp_P"], a ∉ sWA fpAt := by
  decide

/-! ## `PhiI` -/

variable (G s) in
/-- **B-L2's persistent state for the spine** (`SpineLoop.PhiI`). -/
def phiI (k hins hext LF : ℕ) : PhiI (Finset (Fin G.m)) where
  PhiR st D := phiR G s k hins hext st D ∧ (2 * LF + 5) * G.n + 4 * LF + 2 * k + 8 < st.cap
  pWA := phWA
  pWR := phWR
  frame _ _ _ _ _ _ _ h hu hwa hwr :=
    ⟨phiR_frame h.1 hu (fun a haw hap => hwa a hap haw) (fun a haw hap => hwr a hap haw),
      by rw [hu.cap]; exact h.2⟩
  pWA_ok := by decide
  pWR_ok := by decide

/-! ## The FindPivots call as agent-01's `FPB` -/

/-- Write sets of `fpAt` (the clock origin is irrelevant: the lists are `rfl`-equal for every
`c0`). -/
noncomputable def fpAtWA : List String := [] ++ fcWA (labI (G := G) (s := s) 0) "S" "fp.LX"
noncomputable def fpAtVA : List String := [] ++ fcVA (labI (G := G) (s := s) 0) "fp.LX"
noncomputable def fpAtWR : List String := fpPrepWR ++ fcWR (labI (G := G) (s := s) 0) (labX 0) "fp.LX"
noncomputable def fpAtVR : List String := fpPrepVR ++ fcVR (labI (G := G) (s := s) 0) (labX 0) "fp.LX"

set_option maxRecDepth 20000 in
theorem CFC_labI (c0 : ℕ) : CFC (labI (G := G) (s := s) c0) (labX c0) = 342 := by
  simp only [BL2.CFC, BL2.KI, BL2.KS, BL2.Kit, labI, labX, treeImpl]

set_option maxRecDepth 20000 in
theorem KC_labI (c0 : ℕ) : KC (labI (G := G) (s := s) c0) (labX c0) = 524 := by
  simp only [BL2.KC, BL2.CLX, BL2.KI, BL2.KS, BL2.Kit, labI, labX, treeImpl]

/-- Arrays the spine reads across the FindPivots call. -/
def fpKeepA : List String :=
  ["gSt", "S", "S.len", "U", "U.len", "sp.gm", "sp.gs", "sp.gl", "sp.gp", "sp.gpos", "sp.g",
   "sp.inU", "sp.mk", "sp.np", "sp.mk.len", "sl.h", "sl.v", "sl.e", "sl.r", "sl.f", "sp.xm",
   "sp.ptr", "cp.tau", "cp.M", "gW", "hp_A", "hp_P", "Wp", "Wp.len"]
/-- Registers the spine reads across the FindPivots call. -/
def fpKeepR : List String := ["lvl", "n", "gN", "hp_n"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **Names the FindPivots call never writes** (decided by evaluation). -/
theorem fpAt_keep :
    (∀ a ∈ fpKeepR, a ∉ fpAtWR (G := G) (s := s)) ∧ (∀ a ∈ fpKeepA, a ∉ fpAtWA (G := G) (s := s)) ∧
    ("sl.l" ∉ fpAtVA (G := G) (s := s)) ∧ ("gW" ∉ fpAtVA (G := G) (s := s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact of_decide_eq_true rfl

/-- Nonempty, duplicate-free, pairwise disjoint groups of vertices: total size and count `≤ n`. -/
theorem groups_sizes {Gs : List (List (Fin G.n))} (hne : ∀ g ∈ Gs, g ≠ [])
    (hnd : ∀ g ∈ Gs, g.Nodup) (hdisj : Gs.Pairwise (fun g g' => ∀ x ∈ g, x ∉ g')) :
    (Gs.map List.length).sum ≤ G.n ∧ Gs.length ≤ G.n := by
  have hflat : Gs.flatten.Nodup :=
    List.nodup_flatten.mpr ⟨hnd, hdisj.imp (fun h a ha hb => h a ha hb)⟩
  have h1 : Gs.flatten.length ≤ G.n := by simpa using hflat.length_le_card
  have hlen : Gs.flatten.length = (Gs.map List.length).sum := List.length_flatten
  have h2 : ∀ L : List (List (Fin G.n)), (∀ g ∈ L, g ≠ []) → L.length ≤ (L.map List.length).sum := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons g L ih =>
      intro h
      have hg : 1 ≤ g.length := List.length_pos_iff.mpr (h g List.mem_cons_self)
      have := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  have := h2 Gs hne
  omega

/-- **The FindPivots-HD call is agent-01's `FPB`**, for every D layer whose names avoid the
FindPivots write sets. -/
theorem fpB_inst {T : ℕ → ℕ} (DL : DLayer G s T) (Inv : Finset (Fin G.m) → Prop)
    {k hins hext LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ} {l : ℕ}
    (hk2 : 2 ≤ k) (hhext : k ≤ hext) (hsort : ∀ u, (L6.outL G u).Pairwise (SortedRel G s))
    (hDLA : ∀ a ∈ DL.dWA, a ∉ fpAtWA (G := G) (s := s))
    (hDLV : ∀ a ∈ DL.dVA, a ∉ fpAtVA (G := G) (s := s))
    (hDLR : ∀ a ∈ DL.dWR, a ∉ fpAtWR (G := G) (s := s)) :
    RamBody.FPB DL (phiI G s k hins hext LF) Inv (fpC G s (L6.outL G) k hins hext) LF body fpAt
      τf Mf 524 351 l := by
  intro st Blow B S d0 φ g Ds H c0 hIn hpre _ _ hbudB
  have hlF := hIn.lvl_le
  have hSt := hIn.stat
  have hcF := hIn.phi.2
  have hob : st.w "fp.ob" = 0 := hIn.phi.1.ob0
  have hmcap : G.m + 2 ≤ st.cap := by have := hSt.cap; nlinarith
  have hBL : SlotLens st (RamBaseCase.slotB l) :=
    hSt.slots _ (by simp only [RamBaseCase.slotB]; omega)
  have hWlen : l < st.wlen "W.len" := by
    have := hSt.lens "W.len" (by decide); omega
  have hrow : (l + 1) * G.n ≤ st.wlen "W" :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) (hSt.rows "W" (by decide))
  have hbud : ∀ d1 Dout Q W trees cost,
      FindPivotsC (L6.outL G) k hins hext B S d0 φ d1 Dout Q W trees cost →
      st.cost + 9 + CFC (labI (G := G) (s := s) c0) (labX c0) +
        KC (labI (G := G) (s := s) c0) (labX c0) * cost ≤ c0 + st.cap := by
    intro d1 Dout Q W trees cost h
    have := hbudB _ _ _ _ _ _ _ _ (fpC_of_findPivotsC (lv := l) (Blow := Blow) h)
    rw [CFC_labI, KC_labI]; omega
  have h2l : (2 * l + 5) * G.n ≤ (2 * LF + 5) * G.n := Nat.mul_le_mul_right _ (by omega)
  refine (Runs.keep_wa (Runs.keep_len (fpAt_spec (c0 := c0) hk2 hhext hsort hpre hIn.lab hSt.graph
    hmcap hIn.sB hBL hIn.S hIn.phi.1 hIn.lvl hSt.n hWlen hrow hbud (by omega) (by rw [hob]; omega))
    fpAt_noalloc) fpAt_noalloc).mono ?_
  rintro r ⟨⟨⟨ι', cost, H', wl, hfpC, hLA, hHE, hgr, hwalk, hle, hphi, hG, hwnd, hwset, hWR, hoL,
    hoW, hU, hc0', hc'⟩, hwlen, hvlen⟩, hsyn⟩
  have hU' : Unchanged st r (fpAtWA (G := G) (s := s)) (fpAtVA (G := G) (s := s))
      (fpAtWR (G := G) (s := s)) (fpAtVR (G := G) (s := s)) := hU
  obtain ⟨kR, kA, kV, kW⟩ := fpAt_keep (G := G) (s := s)
  have wR : ∀ x ∈ fpKeepR, r.w x = st.w x := fun x hx => hU'.wreg x (kR x hx)
  have e : ∀ a ∈ fpKeepA, r.wa a = st.wa a := fun a ha => (hU'.warr a (kA a ha)).1
  have vS : r.va "sl.l" = st.va "sl.l" := (hU'.varr _ kV).1
  have hcap' : r.cap = st.cap := hU'.cap
  have sSlot : slotW ⊆ fpKeepA := by decide
  have sRow : rowArrs.erase "W" ⊆ fpKeepA := by decide
  have sLen : lenArrs.erase "W.len" ⊆ fpKeepA := by decide
  have sTab : ["cp.tau", "cp.M", "sp.np", "U.len", "U", "sp.gp"] ⊆ fpKeepA := by decide
  -- the groups
  obtain ⟨SL', ι'', -, hSL', hrun, -, -, hQ, -, htr, -⟩ := (hfpC l Blow).1
  have hF'' : FInv (pinCtx (L6.outL G) k hins hext B (lxOf B S d0)) ι'' :=
    Invoke.forest (c := pinCtx (L6.outL G) k hins hext B (lxOf B S d0))
      (fun u e => L6.outL_mem) hsort hpre hrun (fun x hx => (hSL' x).mp hx) hpre.walk
      (fun _ => le_rfl) ⟨fun T hT => absurd hT List.not_mem_nil,
        fun T hT => absurd hT List.not_mem_nil, fun v => by simp, List.Pairwise.nil⟩
  refine ⟨ι'.d, _, _, ι'.Q, ι'.W, ι'.D, _, cost, forestGroups S ι'.Q k ι'.trees, wl, H',
    hfpC l Blow, rfl, fun j hj => rfl, fun j hj => ?_, hG, ?_, hWR, hwnd, hwset, hLA, hHE,
    ⟨hphi, by rw [hcap']; exact hcF⟩,
    DL.frame st r H H' g Ds (l + 1) _ _ _ _ hIn.D hU' (fun a ha h => hDLA a ha h)
      (fun a ha h => hDLV a ha h) (fun a ha h => hDLR a ha h) hHE, ?_, by omega, ?_⟩
  · have hmem : (forestGroups S ι'.Q k ι'.trees)[j] ∈
        forestGroups S ι''.Q (pinCtx (L6.outL G) k hins hext B (lxOf B S d0)).k ι''.trees := by
      show _ ∈ forestGroups S ι''.Q k ι''.trees
      rw [← hQ, ← htr]; exact List.getElem_mem hj
    exact (forestGroups_facts hF'' hk2 S ι''.Q _ hmem).2.1
  · -- the group table has room
    obtain ⟨hgs, hdis, -⟩ := forest_groups_spec S ι''.Q hk2 ι''.trees hF''.pf hF''.size
    have hsz := groups_sizes (Gs := forestGroups S ι''.Q k ι''.trees)
      (fun g hg => (hgs g hg).1) (fun g hg => (hgs g hg).2.1) hdis
    rw [← hQ, ← htr] at hsz
    obtain ⟨hs1, hs2⟩ := hsz
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, lGV, lGO, lGL, -⟩ := hphi.pta.len
    exact ⟨le_trans hs1 (by omega), le_trans hs2 lGO, le_trans hs2 lGL⟩
  · -- the FindPivots frame
    have hslots : ∀ i, r.va "sl.l" i = st.va "sl.l" i ∧ ∀ a ∈ slotW, r.wa a i = st.wa a i :=
      fun i => ⟨by rw [vS], fun a ha => by rw [e a (sSlot ha)]⟩
    have hstat : Static r G LF body τf Mf :=
      RamBody.static_frame hSt (fun a _ => hwlen a) (hvlen _) (fun a ha => hsyn a (fpAt_static' a ha))
        (hU'.varr _ kW).1 (hvlen _) (wR "n" (by decide)) (wR "gN" (by decide)) (wR "hp_n" (by decide))
        hU'.procs hcap'
    have hS : SetRow r "S" "S.len" l S := by
      obtain ⟨xs, hR, hnd, hmem⟩ := hIn.S
      exact ⟨xs, hR.of_eq (hwlen _) (hwlen _) (by rw [e "S.len" (by decide)])
        (fun i _ => by rw [e "S" (by decide)]), hnd, hmem⟩
    have hclr : Clear r G.n l :=
      ⟨fun l' hl' x hx => by rw [e "sp.g" (by decide)]; exact hIn.clr.g l' hl' x hx,
        fun l' hl' x hx => by rw [e "sp.inU" (by decide)]; exact hIn.clr.inU l' hl' x hx,
        fun x hx => by rw [e "sp.xm" (by decide)]; exact hIn.clr.xm x hx⟩
    have habove : Above st r G.n l := by
      refine ⟨fun a ha i hi => ?_, fun a ha j hj => ?_, fun i _ => hslots i, funext hwlen,
        funext hvlen⟩
      · by_cases hW : a = "W"
        · subst hW; exact hoW i (Or.inr hi)
        · rw [e a (sRow ((List.mem_erase_of_ne hW).mpr ha))]
      · by_cases hW : a = "W.len"
        · subst hW; exact hoL j (by omega)
        · rw [e a (sLen ((List.mem_erase_of_ne hW).mpr ha))]
    exact ⟨by rw [wR "lvl" (by decide)]; exact hIn.lvl, hstat, hS, hslots, hclr, habove,
      fun x => by rw [e "sp.ptr" (by decide)], fun a ha i => by rw [e a (sTab ha)],
      fun a ha => hsyn a (fpAt_static a ha)⟩
  · exact ⟨by rw [CFC_labI, KC_labI] at hc'; omega,
      DL.use_frame st r _ _ _ _ hU' (fun a ha h => hDLR a ha h)⟩

end Frontier.CHD.BL2Inst
