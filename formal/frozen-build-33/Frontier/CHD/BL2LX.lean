import Frontier.CHD.BL2InvLoop

/-!
# Frontier.CHD.BL2LX — B-L2: FH.1, the threshold `L_X = d_B[S] = B ⊓ inf_{x ∈ S} d[x]`
(owner agent-09, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

variable (LI : LabI V ops G s)

/-- FH.1: `fp.LX := B`, then `fp.LX := min(fp.LX, d[x])` over the roots. -/
def fpLX (sA slB slX : String) : Stmt :=
  seq (LI.copySS slB slX)
  (seq (wset "fp.j" (lit 0))
  (Stmt.while (lt (var "fp.j") (var "fp.sn"))
    (seq (wset LI.rv (load sA (add (var "fp.sb") (var "fp.j"))))
    (seq (LI.cmpTS slX)
    (seq (ite (var LI.bit) (LI.loadTS slX) skip)
         (wset "fp.j" (add (var "fp.j") (lit 1))))))))

/-- Name hygiene of FH.1. -/
structure NamesL (sA slB slX : String) : Prop where
  xB_A : Disj (LI.slWA slX) (LI.slWA slB)
  xB_V : Disj (LI.slVA slX) (LI.slVA slB)
  xB_R : Disj (LI.slWR slX ++ LI.cpWR) (LI.slWR slB)
  xB_VR : Disj (LI.slVR slX ++ LI.cpVR) (LI.slVR slB)
  x_tab : Disj (LI.slWA slX) LI.tabWA
  x_tabV : Disj (LI.slVA slX) LI.tabVA
  x_regs : Disj (LI.slWR slX ++ LI.cpWR) ["fp.j", "fp.sb", "fp.sn"]
  x_sA : sA ∉ LI.slWA slX
  cmp_regs : Disj LI.cmpWR ["fp.j", "fp.sb", "fp.sn"]
  cmp_x : Disj LI.cmpWR (LI.slWR slX)
  cmpV_x : Disj LI.cmpVR (LI.slVR slX)
  cmp_B : Disj LI.cmpWR (LI.slWR slB)
  cmpV_B : Disj LI.cmpVR (LI.slVR slB)
  rv_regs : LI.rv ∉ ["fp.j", "fp.sb", "fp.sn"]
  rv_x : LI.rv ∉ LI.slWR slX
  rv_B : LI.rv ∉ LI.slWR slB
  rv_cmp : LI.rv ∉ LI.cmpWR
  j_x : "fp.j" ∉ LI.slWR slX
  j_B : "fp.j" ∉ LI.slWR slB

/-- Register write set of FH.1. -/
def lxWR (slX : String) : List String := LI.slWR slX ++ LI.cpWR ++ ["fp.j", LI.rv] ++ LI.cmpWR
/-- Value-register write set of FH.1. -/
def lxVR (slX : String) : List String := LI.slVR slX ++ LI.cpVR ++ LI.cmpVR

/-- Cost of FH.1. -/
def CLX : ℕ := LI.Ccmp + LI.Ccopy + 8

variable {LI}

theorem inf_take_succ {d : Labels G s} {B : WLab G s} {SL : List (Fin G.n)} {j : ℕ}
    (hj : j < SL.length) :
    B ⊓ (SL.take (j + 1)).toFinset.inf d = (B ⊓ (SL.take j).toFinset.inf d) ⊓ d SL[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
    insert_empty_eq, Finset.inf_union, Finset.inf_singleton]
  rw [inf_assoc]

theorem ite_lt_eq_inf {a b : WLab G s} : (if b < a then b else a) = a ⊓ b := by
  split_ifs with h
  · exact (inf_eq_right.mpr h.le).symm
  · exact (inf_eq_left.mpr (not_lt.mp h)).symm

/-- **FH.1**: the slot `slX` receives `B ⊓ inf_{x ∈ SL} d x` (= `lxOf B S d` for `SL` listing `S`). -/
theorem lx_spec (hNL : NamesL LI sA slB slX) {st : State V} {d : Labels G s} {g : LI.Gh}
    {B : WLab G s} {SL : List (Fin G.n)}
    (hLT : LI.LT st d g) (hB : LI.LS st slB B g)
    (hroots : ∀ j (h : j < SL.length), st.wa sA (st.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st.w "fp.sb" + SL.length ≤ st.wlen sA) (hsn : st.w "fp.sn" = SL.length)
    (hcapS : st.w "fp.sb" + SL.length + 1 < st.cap)
    (hbud : st.cost + LI.Ccopy + 3 + CLX LI * SL.length ≤ LI.c0 + st.cap) :
    Runs ops (fpLX LI sA slB slX) st (fun st' => LI.LS st' slX (B ⊓ SL.toFinset.inf d) g ∧
      LI.LT st' d g ∧ LI.LS st' slB B g ∧
      Unchanged st st' (LI.slWA slX) (LI.slVA slX) (lxWR LI slX) (lxVR LI slX) ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + LI.Ccopy + 3 + CLX LI * SL.length) := by
  have hCLX : CLX LI = LI.Ccmp + LI.Ccopy + 8 := rfl
  unfold fpLX
  -- L := B
  refine runs_seq ((LI.copySS_spec (src := slB) (dst := slX) hB (by omega)).mono ?_)
  rintro st1 ⟨hX1, hu1, hc01, hc1⟩
  have hLT1 : LI.LT st1 d g := LI.LT_frame hLT hu1 hNL.x_tab hNL.x_tabV hc01
  have hB1 : LI.LS st1 slB B g := LI.LS_frame hB hu1 hNL.xB_A hNL.xB_V hNL.xB_R hNL.xB_VR
  have hcap1 : st1.cap = st.cap := hu1.cap
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap1]; omega)) ?_)
  generalize hs2 : (st1.setW "fp.j" 0).charge 1 = st2
  have hu2 : Unchanged st1 st2 [] [] ["fp.j"] [] := by
    rw [← hs2]; exact ((unch_setW st1 "fp.j" 0).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hc2 : st2.cost = st1.cost + 1 := by rw [← hs2]; simp
  have hj2 : st2.w "fp.j" = 0 := by rw [← hs2]; simp
  have hWRsb : ∀ r ∈ ["fp.sb", "fp.sn"], r ∉ lxWR LI slX := fun r hr h => by
    simp only [lxWR, List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact hNL.x_regs r (List.mem_append_left _ h) (by simp at hr ⊢; tauto)
    · exact hNL.x_regs r (List.mem_append_right _ h) (by simp at hr ⊢; tauto)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h hr
      rcases h with rfl | rfl
      · rcases hr with h' | h' <;> exact absurd h' (by decide)
      · exact hNL.rv_regs (by simp at hr ⊢; tauto)
    · exact hNL.cmp_regs r h (by simp at hr ⊢; tauto)
  have hsAW : sA ∉ LI.slWA slX := hNL.x_sA
  let K : ℕ → State V → Prop := fun m s' => ∃ j, m = SL.length - j ∧ j ≤ SL.length ∧
    s'.w "fp.j" = j ∧ LI.LS s' slX (B ⊓ (SL.take j).toFinset.inf d) g ∧ LI.LT s' d g ∧
    LI.LS s' slB B g ∧ Unchanged st s' (LI.slWA slX) (LI.slVA slX) (lxWR LI slX) (lxVR LI slX) ∧
    st.cost ≤ s'.cost ∧ s'.cost ≤ st.cost + LI.Ccopy + 2 + CLX LI * j
  have hu02 : Unchanged st st2 (LI.slWA slX) (LI.slVA slX) (lxWR LI slX) (lxVR LI slX) :=
    (hu1.cat hu2).mono (by simp) (by simp) (fun z hz => by
      simp only [List.mem_append, List.append_nil] at hz
      simp only [lxWR, List.mem_append]
      rcases hz with hz | hz
      · rcases hz with hz | hz
        · left; left; left; exact hz
        · left; left; right; exact hz
      · simp at hz; subst hz; left; right; simp) (fun z hz => by
      simp only [List.mem_append, List.append_nil] at hz
      simp only [lxVR, List.mem_append]
      rcases hz with hz | hz
      · left; left; exact hz
      · left; right; exact hz)
  have hK0 : K SL.length st2 := ⟨0, by simp, by omega, hj2,
    (by simpa using (LI.LS_frame hX1 hu2 (Disj.nil_left _) (Disj.nil_left _)
      (Disj.singleton hNL.j_x) (Disj.nil_left _))),
    LI.LT_frame hLT1 hu2 (Disj.nil_left _) (Disj.nil_left _) (by omega),
    LI.LS_frame hB1 hu2 (Disj.nil_left _) (Disj.nil_left _) (Disj.singleton hNL.j_B)
      (Disj.nil_left _), hu02, by omega, by omega⟩
  refine runs_while_nat K _ ?_ SL.length st2 hK0
  intro m s' ⟨j, hm, hjle, hj, hLX, hLT', hB', hu', hc0', hc'⟩
  have hsb' : s'.w "fp.sb" = st.w "fp.sb" := hu'.wreg _ (hWRsb "fp.sb" (by simp))
  have hsn' : s'.w "fp.sn" = SL.length := by rw [hu'.wreg _ (hWRsb "fp.sn" (by simp))]; exact hsn
  have hsA' := hu'.warr sA hsAW
  have hcap' : s'.cap = st.cap := hu'.cap
  refine ⟨if j < SL.length then 1 else 0,
    by rw [evalW_lt_of (x := j) (y := SL.length) (by simp [hj]) (by simp [hsn']) (by omega)],
    fun hne => ?_, fun h0 => ?_⟩
  · have hjl : j < SL.length := by by_contra h; simp [h] at hne
    -- rv := S[j]
    have hidx : evalW (s'.charge 1) (add (var "fp.sb") (var "fp.j")) = some (st.w "fp.sb" + j) :=
      evalW_add_of (by simp [hsb']) (by simp [hj]) (by simp [hcap']; omega)
    refine runs_seq (runs_wset (a := SL[j]) (by
      rw [evalW_load_of hidx (by simp [hsA'.2]; omega)]; simp [hsA'.1, hroots j hjl]) ?_)
    generalize hs3 : ((s'.charge 1).setW LI.rv (SL[j] : ℕ)).charge 1 = s3
    have hu3 : Unchanged s' s3 [] [] [LI.rv] [] := by
      rw [← hs3]; exact ((Unchanged.charge s' 1 [] [] [] []).cat ((unch_setW _ LI.rv _).cat
        (unch_charge' _ 1))).mono (by simp) (by simp) (by simp) (by simp)
    have hc3 : s3.cost = s'.cost + 2 := by rw [← hs3]; simp
    have hrv3 : s3.w LI.rv = SL[j] := by rw [← hs3]; simp
    have hLT3 : LI.LT s3 d g := LI.LT_frame hLT' hu3 (Disj.nil_left _) (Disj.nil_left _) (by omega)
    have hLX3 : LI.LS s3 slX (B ⊓ (SL.take j).toFinset.inf d) g :=
      LI.LS_frame hLX hu3 (Disj.nil_left _) (Disj.nil_left _) (Disj.singleton hNL.rv_x)
        (Disj.nil_left _)
    have hB3 : LI.LS s3 slB B g := LI.LS_frame hB' hu3 (Disj.nil_left _) (Disj.nil_left _)
      (Disj.singleton hNL.rv_B) (Disj.nil_left _)
    have hcap3 : s3.cap = st.cap := by rw [hu3.cap, hcap']
    have hbj : st.cost + LI.Ccopy + 3 + CLX LI * (j + 1) ≤ LI.c0 + st.cap := by
      have : CLX LI * (j + 1) ≤ CLX LI * SL.length := Nat.mul_le_mul_left _ (by omega)
      omega
    have hCj : CLX LI * (j + 1) = CLX LI * j + CLX LI := by ring
    refine runs_seq ((LI.cmpTS_spec hLT3 hLX3 hrv3 (by rw [hcap3]; omega)).mono ?_)
    rintro s4 ⟨hbit4, hu4, hc04, hc4⟩
    have hLT4 : LI.LT s4 d g := LI.LT_frame hLT3 hu4 (Disj.nil_left _) (Disj.nil_left _) hc04
    have hB4 : LI.LS s4 slB B g := LI.LS_frame hB3 hu4 (Disj.nil_left _) (Disj.nil_left _)
      hNL.cmp_B hNL.cmpV_B
    have hLX4 : LI.LS s4 slX (B ⊓ (SL.take j).toFinset.inf d) g :=
      LI.LS_frame hLX3 hu4 (Disj.nil_left _) (Disj.nil_left _) hNL.cmp_x hNL.cmpV_x
    have hrv4 : s4.w LI.rv = SL[j] := by rw [hu4.wreg _ hNL.rv_cmp]; exact hrv3
    have hj4 : s4.w "fp.j" = j := by
      rw [hu4.wreg _ (fun h => hNL.cmp_regs _ h (by simp)), hu3.wreg _ (by
        simp only [List.mem_singleton]; intro h; exact hNL.rv_regs (by rw [← h]; simp))]; exact hj
    have hcap4 : s4.cap = st.cap := by rw [hu4.cap, hcap3]
    -- the final `j := j + 1` from a state holding the new minimum
    have hfin : ∀ (s5 : State V) (L' : WLab G s), LI.LS s5 slX L' g → LI.LT s5 d g →
        LI.LS s5 slB B g → s5.w "fp.j" = j → s5.cap = st.cap →
        Unchanged s4 s5 (LI.slWA slX) (LI.slVA slX) (LI.slWR slX ++ LI.cpWR)
          (LI.slVR slX ++ LI.cpVR) → s4.cost ≤ s5.cost → s5.cost ≤ s4.cost + LI.Ccopy + 2 →
        L' = B ⊓ (SL.take (j + 1)).toFinset.inf d →
        Runs ops (wset "fp.j" (add (var "fp.j") (lit 1))) s5
          (fun s'' => ∃ m', m' < m ∧ K m' s'') := by
      intro s5 L' hX5 hLT5 hB5 hj5 hcap5 hu5 hc05 hc5 hL'
      refine runs_wset (a := j + 1) (evalW_add_of (by simp [hj5]) (evalW_lit_of (by omega))
        (by rw [hcap5]; omega)) ?_
      have hu6 : Unchanged s5 ((s5.setW "fp.j" (j + 1)).charge 1) [] [] ["fp.j"] [] :=
        ((unch_setW s5 "fp.j" _).cat (unch_charge' _ 1)).mono (by simp) (by simp) (by simp)
          (by simp)
      refine ⟨SL.length - (j + 1), by omega, j + 1, rfl, by omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hL']; exact LI.LS_frame hX5 hu6 (Disj.nil_left _) (Disj.nil_left _)
          (Disj.singleton hNL.j_x) (Disj.nil_left _)
      · exact LI.LT_frame hLT5 hu6 (Disj.nil_left _) (Disj.nil_left _) (by simp)
      · exact LI.LS_frame hB5 hu6 (Disj.nil_left _) (Disj.nil_left _) (Disj.singleton hNL.j_B)
          (Disj.nil_left _)
      · refine (((hu'.trans (hu3.mono (by simp) (by simp) ?_ (by simp))).trans
          (hu4.mono (by simp) (by simp) ?_ ?_)).trans (hu5.mono (fun _ h => h) (fun _ h => h)
            ?_ ?_)).trans (hu6.mono (by simp) (by simp) ?_ (by simp))
        · intro z hz; simp at hz; subst hz; simp only [lxWR, List.mem_append]; left; right; simp
        · intro z hz; simp only [lxWR, List.mem_append]; right; exact hz
        · intro z hz; simp only [lxVR, List.mem_append]; right; exact hz
        · intro z hz; simp only [lxWR, List.mem_append]; left; left; exact List.mem_append.mp hz
        · intro z hz; simp only [lxVR, List.mem_append]; left; exact List.mem_append.mp hz
        · intro z hz; simp at hz; subst hz; simp only [lxWR, List.mem_append]; left; right; simp
      · simp; omega
      · simp; omega
    have hch4 : Unchanged s4 (s4.charge 1) [] [] [] [] := Unchanged.charge s4 1 _ _ _ _
    have hLT4c : LI.LT (s4.charge 1) d g :=
      LI.LT_frame hLT4 hch4 (Disj.nil_left _) (Disj.nil_left _) (by simp)
    have hsucc := inf_take_succ (d := d) (B := B) hjl
    by_cases hlt : d SL[j] < B ⊓ (SL.take j).toFinset.inf d
    · rw [if_pos hlt] at hbit4
      refine runs_seq (runs_ite_true (x := 1) (by simp [hbit4]) one_ne_zero ?_)
      refine (LI.loadTS_spec (dst := slX) (v := SL[j]) hLT4c (by simpa using hrv4)
        (by simp [hcap4]; omega)).mono ?_
      rintro s5 ⟨hX5, hu5, hc05, hc5⟩
      have hu45 : Unchanged s4 s5 (LI.slWA slX) (LI.slVA slX) (LI.slWR slX ++ LI.cpWR)
          (LI.slVR slX ++ LI.cpVR) :=
        (hch4.mono (by simp) (by simp) (by simp) (by simp)).trans hu5
      refine hfin s5 (d SL[j]) hX5 (LI.LT_frame hLT4 hu45 hNL.x_tab hNL.x_tabV (by simp at hc05; omega))
        (LI.LS_frame hB4 hu45 hNL.xB_A hNL.xB_V hNL.xB_R hNL.xB_VR) ?_ (by rw [hu45.cap, hcap4])
        hu45 (by simp at hc05; omega) (by simp at hc5; omega) ?_
      · rw [hu45.wreg _ (fun h => hNL.x_regs _ h (by simp))]; exact hj4
      · rw [hsucc]; exact (inf_eq_right.mpr hlt.le).symm
    · rw [if_neg hlt] at hbit4
      refine runs_seq (runs_ite_false (by simp [hbit4]) (runs_skip ?_))
      have hu45 : Unchanged s4 ((s4.charge 1).charge 1) (LI.slWA slX) (LI.slVA slX)
          (LI.slWR slX ++ LI.cpWR) (LI.slVR slX ++ LI.cpVR) :=
        ((hch4.trans (Unchanged.charge _ 1 _ _ _ _)).mono (by simp) (by simp) (by simp) (by simp))
      have hc45 : ((s4.charge 1).charge 1).cost = s4.cost + 2 := by
        simp only [State.charge_cost]
      refine hfin _ _ (LI.LS_frame hLX4 (hch4.trans (Unchanged.charge _ 1 _ _ _ _))
            (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _))
        (LI.LT_frame hLT4 (hch4.trans (Unchanged.charge _ 1 _ _ _ _)) (Disj.nil_left _)
          (Disj.nil_left _) (by omega))
        (LI.LS_frame hB4 (hch4.trans (Unchanged.charge _ 1 _ _ _ _)) (Disj.nil_left _)
          (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _))
        (by simpa using hj4) (by simp [hcap4]) hu45 (by omega) (by omega) ?_
      rw [hsucc]; exact (inf_eq_left.mpr (not_lt.mp hlt)).symm
  · have hjeq : j = SL.length := by by_contra h; simp [show j < SL.length by omega] at h0
    subst hjeq
    rw [List.take_length] at hLX
    have hch : Unchanged s' (s'.charge 1) [] [] [] [] := Unchanged.charge s' 1 _ _ _ _
    exact ⟨LI.LS_frame hLX hch (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _),
      LI.LT_frame hLT' hch (Disj.nil_left _) (Disj.nil_left _) (by simp),
      LI.LS_frame hB' hch (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _),
      hu'.trans (hch.mono (by simp) (by simp) (by simp) (by simp)), by simp; omega, by simp; omega⟩

end Frontier.CHD.BL2
