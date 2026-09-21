import Frontier.CHD.BL2StepF

/-!
# Frontier.CHD.BL2StepG — B-L2: the member branches of a scan iteration (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {c : FPCtx G s} {T : Finset (Fin G.n)} {slB slX : String}
  {u : Fin G.n}

open Classical in
/-- Common part of the member branches: run `relaxC` from the state after the three tests and
hand the updated labels, slots and FindPivots data to a continuation. -/
theorem relax_then (hN : Names LI slB slX) {σ : SSt G s} {g : LI.Gh} {st7 : State V}
    {Lrem : List (Fin G.m)} {e : Fin G.m} (hsrc : G.src e = u)
    (hC7 : Core LI c T slB slX u σ Lrem g st7) (hLC7 : LI.LC st7 σ.d g e)
    (hrv7 : st7.w LI.rv = G.dst e) (hroom : st7.cost + 3 + LI.Crel ≤ LI.c0 + st7.cap)
    {Y : Stmt} {Q : State V → Prop}
    (hY : ∀ st9 g', LI.gext g g' → LI.LT st9 (relaxL σ.d u e) g' →
      LI.LS st9 slB c.B g' → LI.LS st9 slX c.Lx g' →
      st9.w LI.ok = (if Ok σ.d u e then 1 else 0) → MyRep c T σ st9 →
      Cursor st9 c σ.D u Lrem → (∀ x ∈ myRegs, st9.w x = st7.w x) →
      Unchanged st7 st9 LI.relWA LI.relVA LI.relWR LI.relVR →
      st7.cost + 3 ≤ st9.cost → st9.cost ≤ st7.cost + 3 + LI.Crel → st9.cap = st7.cap →
      Runs ops Y st9 Q) :
    Runs ops (seq LI.relaxC Y) (((st7.charge 1).charge 1).charge 1) Q := by
  have hu78 : Unchanged st7 (((st7.charge 1).charge 1).charge 1) [] [] [] [] :=
    ((Unchanged.charge st7 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)).trans
      (Unchanged.charge _ 1 _ _ _ _)
  have hk8 : (((st7.charge 1).charge 1).charge 1).cost = st7.cost + 3 := by simp
  have hLC8 : LI.LC (((st7.charge 1).charge 1).charge 1) σ.d g e :=
    LI.LC_frame hLC7 hu78 (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
      (Disj.nil_left _) (by omega)
  have hrv8 : (((st7.charge 1).charge 1).charge 1).w LI.rv = G.dst e := by simpa using hrv7
  have hroom8 : (((st7.charge 1).charge 1).charge 1).cost + LI.Crel ≤
      LI.c0 + (((st7.charge 1).charge 1).charge 1).cap := by
    simp only [State.charge_cost, State.charge_cap]; omega
  refine runs_seq ((LI.relaxC_spec hLC8 hrv8 hroom8).mono ?_)
  rintro st9 ⟨g', hgg', hLT9, hok9, hu9, hc9a, hc9b⟩
  rw [hk8] at hc9a hc9b
  rw [hsrc] at hLT9 hok9
  have hrelA : Disj LI.relWA myRepArrs := hN.relA_my.mono_right myRepArrs_sub
  have hrelR : Disj LI.relWR myRepRegs := hN.rel_my.mono_right myRepRegs_sub
  refine hY st9 g' hgg' hLT9 ?_ ?_ hok9 ?_ ?_ ?_ ?_ (by omega) (by omega) (by rw [hu9.cap]; simp)
  · exact LI.LS_ext (LI.LS_frame (LI.LS_frame hC7.lab.sB hu78 (Disj.nil_left _) (Disj.nil_left _)
      (Disj.nil_left _) (Disj.nil_left _)) hu9 hN.relA_slB hN.relAV_slB hN.rel_slB hN.relV_slB) hgg'
  · exact LI.LS_ext (LI.LS_frame (LI.LS_frame hC7.lab.sX hu78 (Disj.nil_left _) (Disj.nil_left _)
      (Disj.nil_left _) (Disj.nil_left _)) hu9 hN.relA_slX hN.relAV_slX hN.rel_slX hN.relV_slX) hgg'
  · exact (hC7.my.frameR hu78 (Disj.nil_left _) (Disj.nil_left _)).frameR hu9 hrelA hrelR
  · exact (hC7.cur.frameR hu78 (Disj.nil_left _) (Disj.nil_left _)).frameR hu9
      (hN.relA_my.mono_right (by simp [myArrs])) (hN.rel_my.mono_right (by simp [myRegs]))
  · intro x hx; rw [hu9.wreg x (fun h => hN.rel_my x h hx)]; rfl
  · exact (Unchanged.trans' hu78 hu9).mono (by simp) (by simp) (by simp) (by simp)

open Classical in
/-- FH.20–FH.22: an existing member (Layer A `inK`). -/
theorem old_tail (hN : Names LI slB slX) {σ₀ σ : SSt G s} {g₀ g : LI.Gh} {st₀ st st7 : State V}
    {n : ℕ} {Ld L'' : List (Fin G.m)} {e : Fin G.m} {W7 V7 : List String}
    (hbook : Book LI st₀ st n)
    (hcont : ∀ σ' r n', Scan c T u σ (Ld ++ e :: L'') σ' r n' →
      Scan c T u σ₀ (c.out u) σ' r (n + n'))
    (hLd : ∀ x ∈ Ld, x ∈ σ.D) (he : e ∉ σ.D) (hB : ext (σ.d u) e < c.B)
    (hX : ¬ σ.d (G.dst e) < c.Lx) (hT : G.dst e ∉ T) (hK : G.dst e ∈ σ.K)
    (hfin : σ.d u ≠ ⊤) (hklt : σ.K.length < c.k) (hhist : LI.gext g₀ g) (hsrc : G.src e = u)
    (hC7 : Core LI c T slB slX u σ (Ld ++ e :: L'') g st7) (hLC7 : LI.LC st7 σ.d g e)
    (hv7 : st7.w "fp.v" = G.dst e) (hrv7 : st7.w LI.rv = G.dst e) (hp7 : st7.w "fp.p" = e)
    (hu7 : Unchanged st st7 [] [] W7 V7) (hW7 : W7 ⊆ scanWR LI) (hV7 : V7 ⊆ scanVR LI)
    (hc7 : st.cost ≤ st7.cost) (hc7' : st7.cost + 3 + LI.Crel + 10 ≤ st.cost + Kit LI)
    (hroom : st7.cost + 3 + LI.Crel ≤ LI.c0 + st7.cap) (hcapk : c.k + 4 < st7.cap) :
    Runs ops (fpOld LI) (((st7.charge 1).charge 1).charge 1)
      (fun st' => ∃ m', m' < (Ld ++ e :: L'').length + 1 ∧
        LoopI LI c T slB slX u σ₀ g₀ st₀ m' st') := by
  unfold fpOld
  refine relax_then hN hsrc hC7 hLC7 hrv7 hroom ?_
  intro st9 g' hgg' hLT9 hB9 hX9 hok9 hM9 hcur9 hreg9 hu9 hc9a hc9b hcap9
  have hv9 : st9.w "fp.v" = G.dst e := by rw [hreg9 "fp.v" (by simp [myRegs])]; exact hv7
  refine runs_seq ((okPart_spec (b := Ok σ.d u e) hM9 hv9 hok9 hK hklt.le (by omega)).mono ?_)
  rintro st10 ⟨hM10, hu10, hc10a, hc10b⟩
  have hcur10 : Cursor st10 c σ.D u (Ld ++ e :: L'') := hcur9.frameR hu10 (by decide) (by decide)
  have hp10 : st10.w "fp.p" = e := by
    rw [hu10.wreg "fp.p" (by decide), hreg9 "fp.p" (by simp [myRegs])]; exact hp7
  have hgM10 : st10.w "gM" = G.m := by
    rw [hu10.wreg "gM" (by decide), hreg9 "gM" (by simp [myRegs])]; exact hC7.my.gM
  have hcap10 : st10.cap = st7.cap := by rw [hu10.cap, hcap9]
  refine (advance_spec hcur10 hLd he hp10 hgM10 (by omega)).mono ?_
  rintro st11 ⟨hcur11, hgo11, hu11, hc11⟩
  have hu1011 : Unchanged st9 st11 (["fp.val", "fp.H", "fp.hp", "fp.inH"] ++ [])
      ([] ++ []) (["fp.hsz"] ++ ["fp.pp", "fp.p", "fp.go"]) ([] ++ []) := Unchanged.trans' hu10 hu11
  have hreg11 : ∀ x, x ∉ ["fp.hsz", "fp.pp", "fp.p", "fp.go"] → st11.w x = st9.w x :=
    fun x hx => hu1011.wreg x (by simpa using hx)
  refine ⟨L''.length + 1, by simp, Or.inl ⟨improve σ u e, L'', n + (scanC + okCost c σ.d u e), g',
    rfl, ⟨⟨⟨?_, ?_, ?_⟩, ?_, by rw [improve_D']; exact hcur11, ?_, ?_, hgo11⟩, ?_, ?_,
      LI.gext_trans hhist hgg', ?_, ?_⟩⟩⟩
  · rw [improve_d]
    exact LI.LT_frame hLT9 hu1011 (hN.myW_tab.mono_left (by simp [myWArrs])) (Disj.nil_left _)
      (by omega)
  · exact LI.LS_frame hB9 hu1011 (hN.myA_slB.mono_left (by simp [myArrs])) (Disj.nil_left _)
      (hN.myR_slB.mono_left (by simp [myRegs])) (Disj.nil_left _)
  · exact LI.LS_frame hX9 hu1011 (hN.myA_slX.mono_left (by simp [myArrs])) (Disj.nil_left _)
      (hN.myR_slX.mono_left (by simp [myRegs])) (Disj.nil_left _)
  · exact (hM10.frameR hu11 (Disj.nil_left _) (by decide)).congr_σ (improve_H σ u e)
      (improve_K σ u e) (improve_val σ u e) (improve_kpar σ u e)
  · rw [hreg11 "fp.u" (by decide), hreg9 "fp.u" (by simp [myRegs])]; exact hC7.ureg
  · rw [hreg11 "fp.res" (by decide), hreg9 "fp.res" (by simp [myRegs])]; exact hC7.res
  · rw [improve_d]; exact relaxL_ne_top hfin
  · rw [improve_K]; exact hklt
  · exact cont_extend hcont hLd (fun σ' r n' h' => by
      have := Scan.inK σ σ' e L'' r n' he hB hX hT hK h'
      rwa [Nat.add_assoc] at this)
  · have hall := Unchanged.trans' (Unchanged.trans' hu7 hu9) hu1011
    refine Book.step hbook hall ?_ ?_ ?_ ?_ (by omega) (by omega) (by simp only [scanC]; omega)
    all_goals (simp only [List.nil_append, List.append_nil, List.append_subset]; (repeat' apply And.intro) <;> first | exact relWA_sub | exact relVA_sub | exact relWR_sub | exact relVR_sub | exact hW7 | exact hV7 | scan_sub)

open Classical in
/-- FH.15–FH.19: a new member (Layer A `newCont` / `newFull`). -/
theorem new_tail (hN : Names LI slB slX) {σ₀ σ : SSt G s} {g₀ g : LI.Gh} {st₀ st st7 : State V}
    {n : ℕ} {Ld L'' : List (Fin G.m)} {e : Fin G.m} {W7 V7 : List String}
    (hbook : Book LI st₀ st n)
    (hcont : ∀ σ' r n', Scan c T u σ (Ld ++ e :: L'') σ' r n' →
      Scan c T u σ₀ (c.out u) σ' r (n + n'))
    (hLd : ∀ x ∈ Ld, x ∈ σ.D) (he : e ∉ σ.D) (hB : ext (σ.d u) e < c.B)
    (hX : ¬ σ.d (G.dst e) < c.Lx) (hT : G.dst e ∉ T) (hK : G.dst e ∉ σ.K)
    (hfin : σ.d u ≠ ⊤) (hklt : σ.K.length < c.k) (hhist : LI.gext g₀ g) (hsrc : G.src e = u)
    (hC7 : Core LI c T slB slX u σ (Ld ++ e :: L'') g st7) (hLC7 : LI.LC st7 σ.d g e)
    (hv7 : st7.w "fp.v" = G.dst e) (hrv7 : st7.w LI.rv = G.dst e) (hp7 : st7.w "fp.p" = e)
    (hu7 : Unchanged st st7 [] [] W7 V7) (hW7 : W7 ⊆ scanWR LI) (hV7 : V7 ⊆ scanVR LI)
    (hc7 : st.cost ≤ st7.cost) (hc7' : st7.cost + 3 + LI.Crel + 16 ≤ st.cost + Kit LI)
    (hroom : st7.cost + 3 + LI.Crel ≤ LI.c0 + st7.cap) (hcapk : c.k + 4 < st7.cap) :
    Runs ops (fpNew LI) (((st7.charge 1).charge 1).charge 1)
      (fun st' => ∃ m', m' < (Ld ++ e :: L'').length + 1 ∧
        LoopI LI c T slB slX u σ₀ g₀ st₀ m' st') := by
  unfold fpNew
  refine relax_then hN hsrc hC7 hLC7 hrv7 hroom ?_
  intro st9 g' hgg' hLT9 hB9 hX9 hok9 hM9 hcur9 hreg9 hu9 hc9a hc9b hcap9
  have hv9 : st9.w "fp.v" = G.dst e := by rw [hreg9 "fp.v" (by simp [myRegs])]; exact hv7
  have hu9u : st9.w "fp.u" = u := by rw [hreg9 "fp.u" (by simp [myRegs])]; exact hC7.ureg
  -- FH.16: append the new member
  refine runs_seq ((memAdd_spec hM9 hv9 hu9u hK hklt (by omega)).mono ?_)
  rintro st10 ⟨hM10, hu10, hc10⟩
  have hok10 : st10.w LI.ok = (if Ok σ.d u e then 1 else 0) := by
    rw [hu10.wreg LI.ok (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => hN.rel_my LI.ok LI.ok_relWR (h ▸ by simp [myRegs]))]
    exact hok9
  have hv10 : st10.w "fp.v" = G.dst e := by rw [hu10.wreg "fp.v" (by decide)]; exact hv9
  -- FH.17: valid part and heap
  refine runs_seq ((okPart_spec (b := Ok σ.d u e) hM10 hv10 hok10 (by simp) (by simp; omega)
    (by rw [hu10.cap, hcap9]; omega)).mono ?_)
  rintro st11 ⟨hM11, hu11, hc11a, hc11b⟩
  have hu911 : Unchanged st9 st11 (["fp.K", "fp.inK", "fp.kp"] ++ ["fp.val", "fp.H", "fp.hp", "fp.inH"])
      ([] ++ []) (["fp.kl"] ++ ["fp.hsz"]) ([] ++ []) := Unchanged.trans' hu10 hu11
  have hreg11 : ∀ x, x ∉ ["fp.kl", "fp.hsz"] → st11.w x = st9.w x :=
    fun x hx => hu911.wreg x (by simpa using hx)
  have hcur11 : Cursor st11 c σ.D u (Ld ++ e :: L'') := hcur9.frameR hu911 (by decide) (by decide)
  have hcap11 : st11.cap = st7.cap := by rw [hu911.cap, hcap9]
  have hkl11 : st11.w "fp.kl" = σ.K.length + 1 := by rw [hM11.kl]; simp
  have hk11 : st11.w "fp.k" = c.k := hM11.kreg
  -- the new state in Layer A
  have hLT11 : LI.LT st11 (addNew σ u e).d g' := by
    rw [addNew_d]
    exact LI.LT_frame hLT9 hu911 (hN.myW_tab.mono_left (by simp [myWArrs])) (Disj.nil_left _)
      (by omega)
  have hB11 : LI.LS st11 slB c.B g' := LI.LS_frame hB9 hu911
    (hN.myA_slB.mono_left (by simp [myArrs])) (Disj.nil_left _)
    (hN.myR_slB.mono_left (by simp [myRegs])) (Disj.nil_left _)
  have hX11 : LI.LS st11 slX c.Lx g' := LI.LS_frame hX9 hu911
    (hN.myA_slX.mono_left (by simp [myArrs])) (Disj.nil_left _)
    (hN.myR_slX.mono_left (by simp [myRegs])) (Disj.nil_left _)
  have hM11' : MyRep c T (addNew σ u e) st11 :=
    hM11.congr_σ (addNew_H σ u e) (addNew_K σ u e) (addNew_val σ u e) (addNew_kpar σ u e)
  have hlenK : (addNew σ u e).K.length = σ.K.length + 1 := by rw [addNew_K]; simp
  have hall9 := Unchanged.trans' (Unchanged.trans' hu7 hu9) hu911
  by_cases hfull : σ.K.length + 1 < c.k
  · -- FH.19: continue (Layer A `newCont`)
    refine runs_ite_true (x := 1) (by simp [hkl11, hk11, hfull, fit]; omega) one_ne_zero ?_
    have hcurC : Cursor (st11.charge 1) c σ.D u (Ld ++ e :: L'') :=
      hcur11.frameR (Unchanged.charge st11 1 [] [] [] []) (Disj.nil_left _) (Disj.nil_left _)
    have hpC : (st11.charge 1).w "fp.p" = e := by
      simp only [State.charge_w]; rw [hreg11 "fp.p" (by decide), hreg9 "fp.p" (by simp [myRegs])]
      exact hp7
    have hgMC : (st11.charge 1).w "gM" = G.m := by
      simp only [State.charge_w]; rw [hreg11 "gM" (by decide), hreg9 "gM" (by simp [myRegs])]
      exact hC7.my.gM
    refine (advance_spec hcurC hLd he hpC hgMC (by simp; omega)).mono ?_
    rintro st12 ⟨hcur12, hgo12, hu12, hc12⟩
    simp only [State.charge_cost] at hc12
    have hu1112 : Unchanged st11 st12 [] [] ["fp.pp", "fp.p", "fp.go"] [] :=
      ((Unchanged.charge st11 1 _ _ _ _).trans hu12)
    have hreg12 : ∀ x, x ∉ ["fp.pp", "fp.p", "fp.go"] → st12.w x = st11.w x :=
      fun x hx => hu1112.wreg x hx
    refine ⟨L''.length + 1, by simp, Or.inl ⟨addNew σ u e, L'', n + (scanC + okCost c σ.d u e), g',
      rfl, ⟨⟨⟨?_, ?_, ?_⟩, ?_, by rw [addNew_D']; exact hcur12, ?_, ?_, hgo12⟩, ?_, ?_,
        LI.gext_trans hhist hgg', ?_, ?_⟩⟩⟩
    · exact LI.LT_frame hLT11 hu1112 (Disj.nil_left _) (Disj.nil_left _) (by omega)
    · exact LI.LS_frame hB11 hu1112 (Disj.nil_left _) (Disj.nil_left _)
        (hN.myR_slB.mono_left (by simp [myRegs])) (Disj.nil_left _)
    · exact LI.LS_frame hX11 hu1112 (Disj.nil_left _) (Disj.nil_left _)
        (hN.myR_slX.mono_left (by simp [myRegs])) (Disj.nil_left _)
    · exact hM11'.frameR hu1112 (Disj.nil_left _) (by decide)
    · rw [hreg12 "fp.u" (by decide), hreg11 "fp.u" (by decide)]; exact hu9u
    · rw [hreg12 "fp.res" (by decide), hreg11 "fp.res" (by decide),
        hreg9 "fp.res" (by simp [myRegs])]; exact hC7.res
    · rw [addNew_d]; exact relaxL_ne_top hfin
    · rw [hlenK]; exact hfull
    · exact cont_extend hcont hLd (fun σ' r n' h' => by
        have := Scan.newCont σ σ' e L'' r n' he hB hX hT hK (by rw [hlenK]; exact hfull) h'
        rwa [Nat.add_assoc] at this)
    · have hall := Unchanged.trans' hall9 hu1112
      refine Book.step hbook hall ?_ ?_ ?_ ?_ (by omega) (by omega)
        (by simp only [scanC]; omega)
      all_goals (simp only [List.nil_append, List.append_nil, List.append_subset]; (repeat' apply And.intro) <;> first | exact relWA_sub | exact relVA_sub | exact relWR_sub | exact relVR_sub | exact hW7 | exact hV7 | scan_sub)
  · -- FH.19: the member cap is reached (Layer A `newFull`)
    refine runs_ite_false (by simp [hkl11, hk11, hfull, fit]; omega) ?_
    refine (stop_spec (st := st11.charge 1) (r := 3) (by simp; omega) (by simp; omega)).mono ?_
    rintro st' ⟨hres, hgo', hreg, hu', hc'⟩
    simp only [State.charge_cost] at hc'
    have hu11' : Unchanged st11 st' [] [] ["fp.res", "fp.go"] [] :=
      (Unchanged.charge st11 1 _ _ _ _).trans hu'
    refine ⟨0, by omega, Or.inr ⟨rfl, addNew σ u e, .full, n + (scanC + okCost c σ.d u e), g', ?_⟩⟩
    refine ⟨cont_stop hcont hLd (Scan.newFull σ e L'' he hB hX hT hK (by rw [hlenK]; omega)),
      ⟨LI.LT_frame hLT11 hu11' (Disj.nil_left _) (Disj.nil_left _) (by omega),
        LI.LS_frame hB11 hu11' (Disj.nil_left _) (Disj.nil_left _)
          (hN.myR_slB.mono_left (by simp [myRegs])) (Disj.nil_left _),
        LI.LS_frame hX11 hu11' (Disj.nil_left _) (Disj.nil_left _)
          (hN.myR_slX.mono_left (by simp [myRegs])) (Disj.nil_left _)⟩,
      hM11'.frameR hu11' (Disj.nil_left _) (by decide),
      by rw [addNew_D']; exact (hcur11.toOutRep).frameR hu11' (Disj.nil_left _), ?_, hgo', ?_,
      LI.gext_trans hhist hgg', ?_⟩
    · rw [hreg "fp.u" (by decide) (by decide)]; simp only [State.charge_w]
      rw [hreg11 "fp.u" (by decide)]; exact hu9u
    · exact Or.inr (Or.inr ⟨rfl, hres⟩)
    · have hall := Unchanged.trans' hall9 hu11'
      refine Book.step hbook hall ?_ ?_ ?_ ?_ (by omega) (by omega)
        (by simp only [scanC]; omega)
      all_goals (simp only [List.nil_append, List.append_nil, List.append_subset]; (repeat' apply And.intro) <;> first | exact relWA_sub | exact relVA_sub | exact relWR_sub | exact relVR_sub | exact hW7 | exact hV7 | scan_sub)

end Frontier.CHD.BL2
