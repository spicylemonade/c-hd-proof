import Frontier.CHD.BL2Alloc
import Frontier.CHD.L6.Final

/-!
# Frontier.CHD.BL2Phi — B-L2: the persistent FindPivots state as seen by the spine (owner agent-09,
NON-GATE)

The spine's `PhiI` (agent-08, `SpineLoop`) asks B-L2 for a representation `PhiR st D` of the
persistent FindPivots state (C-HD: the deleted-edge set `D`), with a footprint and a frame.
`phiR` is `FPClean` for the fixed out-lists `outL G` and cap `k`: by `FPClean.congr` it is the
clean state of EVERY call (any `B`, `L_X`); `FPClean.frame` is the disjoint-footprint frame
(footprint `fpcWA` / `fpcWR`).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM Frontier.CHD.PartitionRAM

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- Arrays read by `FPClean`. -/
def fpcWA : List String := ((myArrs ++ frWA0) ++ ptaArrs) ++ ["fp.inW", "fp.W", "fp.Q"]
/-- Registers read by `FPClean`. -/
def fpcWR : List String := myRegs ++ ["fp.ob"]

/-- **The clean FindPivots state survives every write outside its footprint.** -/
theorem FPClean.frame {c : FPCtx G s} {d : Labels G s} {D : Finset (Fin G.m)} {st r : State V}
    {wa va wr vr : List String} (h : FPClean c d D st) (hu : Unchanged st r wa va wr vr)
    (hwa : Disj wa fpcWA) (hwr : Disj wr fpcWR) : FPClean c d D r := by
  have A : ∀ a ∈ fpcWA, r.wa a = st.wa a ∧ r.wlen a = st.wlen a :=
    fun a ha => hu.warr a (fun h' => hwa a h' ha)
  have R : ∀ x ∈ fpcWR, r.w x = st.w x := fun x hx => hu.wreg x (fun h' => hwr x h' hx)
  have sMy : myArrs ⊆ fpcWA := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx))
  have sFr : frWA0 ⊆ fpcWA := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))
  have sPt : ptaArrs ⊆ fpcWA := fun x hx => List.mem_append_left _ (List.mem_append_right _ hx)
  have sEx : ["fp.inW", "fp.W", "fp.Q"] ⊆ fpcWA := fun x hx => List.mem_append_right _ hx
  have hI := A "fp.inW" (sEx (by simp))
  have hW := A "fp.W" (sEx (by simp))
  have hQ := A "fp.Q" (sEx (by simp))
  have hob := R "fp.ob" (List.mem_append_right _ (by simp))
  exact ⟨h.my.frame hu (hwa.mono_right sMy) (hwr.mono_right (List.subset_append_left _ _)),
    h.out.frame hu (hwa.mono_right sMy), TA0.frame h.ta (fun a ha => A a (sFr ha)),
    h.pta.frame (fun a ha => A a (sPt ha)),
    ⟨by rw [hI.2]; exact h.inW.1, fun v => by rw [hI.1]; exact h.inW.2 v⟩,
    by rw [hob, hW.2]; exact h.wlen, by rw [hob, hQ.2]; exact h.qlen, by rw [hob]; exact h.ob0⟩

/-! ## The persistent state without the graph heads

`gHead` is the spine's read-only graph array (`GraphAt`, part of the spine's `Static`), so the
persistent FindPivots state handed to the spine does not include it; `toClean` re-attaches it. -/

/-- `FPClean` without the graph heads, with the empty search state spelled out. -/
structure FPCleanNH (c : FPCtx G s) (D : Finset (Fin G.m)) (st : State V) : Prop where
  gM : st.w "gM" = G.m
  hsz : st.w "fp.hsz" = 0
  hL : c.k ≤ st.wlen "fp.H"
  hpL : st.wlen "fp.hp" = G.n
  inH : Bits (G := G) st "fp.inH" ∅
  kl : st.w "fp.kl" = 0
  kcap : c.k ≤ st.wlen "fp.K"
  inK : Bits (G := G) st "fp.inK" ∅
  val : Bits (G := G) st "fp.val" ∅
  fm : Bits (G := G) st "fp.fm" ∅
  kpL : st.wlen "fp.kp" = G.n
  kreg : st.w "fp.k" = c.k
  out : OutRep st c D
  ta : TA0 G.n st
  pta : PTA G.n st
  inW : Bits (G := G) st "fp.inW" ∅
  wlen : st.w "fp.ob" + G.n ≤ st.wlen "fp.W"
  qlen : st.w "fp.ob" + G.n ≤ st.wlen "fp.Q"
  ob0 : st.w "fp.ob" = 0

theorem FPClean.toNH {c : FPCtx G s} {d : Labels G s} {D : Finset (Fin G.m)} {st : State V}
    (h : FPClean c d D st) : FPCleanNH c D st := by
  obtain ⟨hl, _, hset, hsz, hHL, _, hpL, _, hinH⟩ := h.my.heap
  have hl0 : hl = [] := by simpa [emptySt] using hset
  subst hl0
  exact ⟨h.my.gM, by simpa using hsz, hHL, hpL, by simpa [emptySt] using hinH,
    by simpa [emptySt] using h.my.kl, h.my.kcap, by simpa [emptySt] using h.my.inK,
    by simpa [emptySt] using h.my.val, h.my.fm, h.my.kpL, h.my.kreg, h.out, h.ta, h.pta, h.inW,
    h.wlen, h.qlen, h.ob0⟩

theorem FPCleanNH.toClean {c : FPCtx G s} {D : Finset (Fin G.m)} {st : State V}
    (h : FPCleanNH c D st) (hL : G.m ≤ st.wlen "gHead")
    (hH : ∀ q : Fin G.m, st.wa "gHead" q = G.dst q) (d : Labels G s) : FPClean c d D st :=
  ⟨⟨h.gM, hL, hH, ⟨[], List.nodup_nil, by simp [emptySt], by simpa using h.hsz, h.hL,
      fun i hi => absurd hi (by simp), h.hpL, fun i hi => absurd hi (by simp),
      by simpa [emptySt] using h.inH⟩,
    by simpa [emptySt] using h.kl, h.kcap, fun i hi => absurd hi (by simp [emptySt]),
    by simpa [emptySt] using h.inK, by simpa [emptySt] using h.val, h.fm, h.kpL,
    fun v hv => absurd hv (by simp [emptySt]), h.kreg, List.nodup_nil, by simp [emptySt]⟩,
    h.out, h.ta, h.pta, h.inW, h.wlen, h.qlen, h.ob0⟩

theorem Bits.of_arr {st st' : State V} {arr : String} {S : Finset (Fin G.n)} (h : Bits st arr S)
    (he : st'.wa arr = st.wa arr ∧ st'.wlen arr = st.wlen arr) : Bits st' arr S :=
  ⟨by rw [he.2]; exact h.1, fun v => by rw [he.1]; exact h.2 v⟩

/-- The footprint of the persistent state (the graph heads excluded). -/
def phWA : List String := (((myArrs.erase "gHead") ++ frWA0) ++ ptaArrs) ++ ["fp.inW", "fp.W", "fp.Q"]
def phWR : List String := myRegs ++ ["fp.ob"]

/-- **The persistent FindPivots state survives every write outside its footprint.** -/
theorem FPCleanNH.frame {c : FPCtx G s} {D : Finset (Fin G.m)} {st r : State V}
    {wa va wr vr : List String} (h : FPCleanNH c D st) (hu : Unchanged st r wa va wr vr)
    (hwa : Disj wa phWA) (hwr : Disj wr phWR) : FPCleanNH c D r := by
  have A : ∀ a ∈ phWA, r.wa a = st.wa a ∧ r.wlen a = st.wlen a :=
    fun a ha => hu.warr a (fun h' => hwa a h' ha)
  have R : ∀ x ∈ phWR, r.w x = st.w x := fun x hx => hu.wreg x (fun h' => hwr x h' hx)
  have sFr : frWA0 ⊆ phWA := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))
  have sPt : ptaArrs ⊆ phWA := fun x hx => List.mem_append_left _ (List.mem_append_right _ hx)
  have hOut : OutRep r c D := by
    have hF := A "gHd" (by decide)
    have hN := A "gNxt" (by decide)
    obtain ⟨o1, o2⟩ := h.out
    exact ⟨by rw [hF.2]; exact o1, fun w => by rw [hF.1]; exact (o2 w).of_eq hN.1 hN.2⟩
  exact ⟨by rw [R "gM" (by decide)]; exact h.gM, by rw [R "fp.hsz" (by decide)]; exact h.hsz,
    by rw [(A "fp.H" (by decide)).2]; exact h.hL, by rw [(A "fp.hp" (by decide)).2]; exact h.hpL,
    h.inH.of_arr (A "fp.inH" (by decide)), by rw [R "fp.kl" (by decide)]; exact h.kl,
    by rw [(A "fp.K" (by decide)).2]; exact h.kcap, h.inK.of_arr (A "fp.inK" (by decide)),
    h.val.of_arr (A "fp.val" (by decide)), h.fm.of_arr (A "fp.fm" (by decide)),
    by rw [(A "fp.kp" (by decide)).2]; exact h.kpL, by rw [R "fp.k" (by decide)]; exact h.kreg,
    hOut, TA0.frame h.ta (fun a ha => A a (sFr ha)), h.pta.frame (fun a ha => A a (sPt ha)),
    h.inW.of_arr (A "fp.inW" (by decide)),
    by rw [R "fp.ob" (by decide), (A "fp.W" (by decide)).2]; exact h.wlen,
    by rw [R "fp.ob" (by decide), (A "fp.Q" (by decide)).2]; exact h.qlen,
    by rw [R "fp.ob" (by decide)]; exact h.ob0⟩

variable (G s) in
/-- **The persistent FindPivots state for the spine** (`PhiI.PhiR`): the clean FindPivots state
for the out-lists `outL G` and cap `k`, with deleted edges `D`, without the graph heads. -/
def phiR (k hins hext : ℕ) (st : State V) (D : Finset (Fin G.m)) : Prop :=
  FPCleanNH (pinCtx (G := G) (s := s) (L6.outL G) k hins hext ⊤ ⊤) D st

/-- `phiR` plus the graph heads is the clean state of every call with the same out-lists and cap. -/
theorem phiR_toClean {k hins hext : ℕ} {st : State V} {D : Finset (Fin G.m)} {B Lx : WLab G s}
    (h : phiR G s k hins hext st D) (hL : G.m ≤ st.wlen "gHead")
    (hH : ∀ q : Fin G.m, st.wa "gHead" q = G.dst q) (d : Labels G s) :
    FPClean (pinCtx (L6.outL G) k hins hext B Lx) d D st :=
  (h.toClean hL hH d).congr rfl rfl

theorem phiR_of_clean {k hins hext : ℕ} {st : State V} {D : Finset (Fin G.m)} {B Lx : WLab G s}
    {d : Labels G s} (h : FPClean (pinCtx (L6.outL G) k hins hext B Lx) d D st) :
    phiR G s k hins hext st D :=
  (FPClean.congr (c' := pinCtx (G := G) (s := s) (L6.outL G) k hins hext ⊤ ⊤) (d' := fun _ => ⊤) h
    rfl rfl).toNH

/-- The frame of `phiR` (the `PhiI.frame` field, disjoint-footprint form). -/
theorem phiR_frame {k hins hext : ℕ} {st r : State V} {D : Finset (Fin G.m)}
    {wa va wr vr : List String} (h : phiR G s k hins hext st D) (hu : Unchanged st r wa va wr vr)
    (hwa : Disj wa phWA) (hwr : Disj wr phWR) : phiR G s k hins hext r D :=
  FPCleanNH.frame h hu hwa hwr

end Frontier.CHD.BL2
