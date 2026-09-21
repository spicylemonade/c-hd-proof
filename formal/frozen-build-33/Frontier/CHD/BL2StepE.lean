import Frontier.CHD.BL2StepG

/-!
# Frontier.CHD.BL2StepE — B-L2: one iteration of the scan loop refines one Layer-A `Scan` step
(agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {c : FPCtx G s} {T : Finset (Fin G.n)} {slB slX : String}
  {u : Fin G.n}

theorem scan_step (hown : OutOK c) (hnd : OutNodup c) (hN : Names LI slB slX)
    (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V)
    (hbud : ∀ σ' r n', Scan c T u σ₀ (c.out u) σ' r n' →
      st₀.cost + 5 + Kit LI * n' + Kit LI ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap)
    {σ : SSt G s} {Lrem : List (Fin G.m)} {n : ℕ} {g : LI.Gh} {st : State V}
    (h : RunI LI c T slB slX u σ₀ g₀ st₀ σ Lrem n g st) (hgo : st.w "fp.go" ≠ 0) :
    Runs ops (fpScanBody LI slB slX) (st.charge 1)
      (fun st' => ∃ m', m' < Lrem.length + 1 ∧ LoopI LI c T slB slX u σ₀ g₀ st₀ m' st') := by
  obtain ⟨hC, hfin, hklt, hhist, hcont, hbook⟩ := h
  have hcap : st.cap = st₀.cap := hbook.unch.cap
  have hpM : st.w "fp.p" < G.m := by
    have := hC.go
    by_contra hh
    rw [if_neg hh] at this
    exact hgo this
  obtain ⟨Ld, e, L'', hLrem, hLd, he, hpe, hel, hsnx⟩ := hC.cur.first hpM
  subst hLrem
  have hsrc : G.src e = u := by
    obtain ⟨-, -, Pre, hPre, -⟩ := hC.cur
    exact (hown u e).mp (by rw [hPre]; simp)
  -- the budget of this iteration
  obtain ⟨σc, rc, nc, hsc⟩ := Scan.exists_run c T u (Ld ++ e :: L'') σ
  have hb := hbud _ _ _ (hcont _ _ _ hsc)
  have hroom : st.cost + Kit LI ≤ LI.c0 + st.cap := by
    have h1 := hbook.cost
    have h2 : Kit LI * n ≤ Kit LI * (n + nc) := Nat.mul_le_mul_left _ (by omega)
    rw [hcap]; omega
  have hKit : Kit LI = LI.Ccand + LI.Ccmp + LI.Crel + 30 := rfl
  unfold fpScanBody
  refine scan_prefix hN hC hfin hpe hsrc (by omega) ?_
  intro st5 hC5 hLC5 hbit5 hv5 hu5 hc5a hc5b
  by_cases hB : ext (σ.d u) e < c.B
  · rw [if_pos hB] at hbit5
    refine runs_ite_true (x := 1) (by simp [hbit5]) one_ne_zero ?_
    have hcap5 : st5.cap = st.cap := hu5.cap
    refine scan_mid hN hC5 hLC5 hv5 (by rw [hcap5]; omega) ?_
    intro st7 hC7 hLC7 hbit7 hv7 hrv7 hu7 hc7a hc7b
    have hcap7 : st7.cap = st.cap := by rw [hu7.cap]; simp [hcap5]
    have hu57 : Unchanged st st7 [] [] ((["fp.v", LI.ru, LI.re] ++ LI.candWR) ++ (LI.rv :: LI.cmpWR))
        (LI.candVR ++ LI.cmpVR) :=
      (Unchanged.trans' hu5 hu7).mono (by simp) (by simp) (fun _ h => h) (fun _ h => h)
    have hW57 : (["fp.v", LI.ru, LI.re] ++ LI.candWR) ++ (LI.rv :: LI.cmpWR) ⊆ scanWR LI := by
      simp only [List.append_subset, List.cons_subset]
      exact ⟨⟨⟨mem_scanWR_my (by simp [myRegs]), mem_scanWR_ifc (by simp),
        mem_scanWR_ifc (by simp), List.nil_subset _⟩, candWR_sub⟩, mem_scanWR_ifc (by simp),
        cmpWR_sub⟩
    have hV57 : LI.candVR ++ LI.cmpVR ⊆ scanVR LI := by
      simp only [List.append_subset]; exact ⟨candVR_sub, cmpVR_sub⟩
    have hp7 : st7.w "fp.p" = e := by
      rw [hu7.wreg "fp.p" (by
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hN.ifc_my LI.rv (by simp) (h ▸ by simp [myRegs]),
          fun h => hN.cmp_my _ h (by simp [myRegs])⟩)]
      rw [hu5.wreg "fp.p" (by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨⟨by decide, fun h => hN.ifc_my LI.ru (by simp) (h ▸ by simp [myRegs]),
          fun h => hN.ifc_my LI.re (by simp) (h ▸ by simp [myRegs])⟩,
          fun h => hN.cand_my _ h (by simp [myRegs])⟩)]
      exact hpe
    by_cases hX : σ.d (G.dst e) < c.Lx
    · -- FH.9: delete the edge (Layer A `lxdel`)
      rw [if_pos hX] at hbit7
      refine runs_ite_true (x := 1) (by simp [hbit7]) one_ne_zero ?_
      have hC7' : Cursor (st7.charge 1) c σ.D u (Ld ++ e :: L'') :=
        hC7.cur.frameR (Unchanged.charge st7 1 [] [] [] []) (Disj.nil_left _) (Disj.nil_left _)
      refine (unlink_spec (fun w e' h' => (hown w e').mp h') (hnd u) hC7' hLd he
        (by simpa using hp7) (by simpa using hC7.ureg) (by simpa using hC7.my.gM)
        (by simp; omega)).mono ?_
      rintro st' ⟨hcur', hgo', hu', hc'⟩
      refine ⟨L''.length + 1, by simp, Or.inl ⟨{ σ with D := insert e σ.D }, L'', n + scanC, g, rfl,
        ⟨⟨?_, ?_, hcur', ?_, ?_, hgo'⟩, hfin, hklt, hhist, ?_, ?_⟩⟩⟩
      · have hu7' : Unchanged st7 st' ["gHd", "gNxt"] [] ["fp.p", "fp.go"] [] :=
          (Unchanged.charge st7 1 _ _ _ _).trans hu'
        exact hC7.lab.frame hu7' (hN.myW_tab.mono_left (by simp [myWArrs])) (Disj.nil_left _)
          (hN.myA_slB.mono_left (by simp [myArrs])) (Disj.nil_left _)
          (hN.myR_slB.mono_left (by simp [myRegs])) (Disj.nil_left _)
          (hN.myA_slX.mono_left (by simp [myArrs])) (Disj.nil_left _)
          (hN.myR_slX.mono_left (by simp [myRegs])) (Disj.nil_left _) (by simp at hc'; omega)
      · have hu7' : Unchanged st7 st' ["gHd", "gNxt"] [] ["fp.p", "fp.go"] [] :=
          (Unchanged.charge st7 1 _ _ _ _).trans hu'
        exact (hC7.my.frameR hu7' (by decide) (by decide)).congr_σ rfl rfl rfl rfl
      · rw [hu'.wreg "fp.u" (by decide)]; simpa using hC7.ureg
      · rw [hu'.wreg "fp.res" (by decide)]; simpa using hC7.res
      · exact cont_extend hcont hLd (fun σ' r n' h' => Scan.lxdel σ σ' e L'' r n' he hB hX h')
      · refine Book.step hbook (Unchanged.trans' (Unchanged.trans' (Unchanged.trans' hu5 hu7)
          (Unchanged.charge st7 1 [] [] [] [])) hu') ?_ ?_ ?_ ?_ ?_ ?_ (by decide)
        · scan_sub
        · scan_sub
        · scan_sub
        · scan_sub
        · simp at hc'; omega
        · simp at hc'; omega
    · rw [if_neg hX] at hbit7
      refine runs_ite_false (by simp [hbit7]) ?_
      have hvfm : ((G.dst e : Fin G.n) : ℕ) < st7.wlen "fp.fm" := by
        rw [hC7.my.fm.1]; exact (G.dst e).isLt
      by_cases hT : G.dst e ∈ T
      · -- FH.10–FH.13: contact
        have hfm1 : st7.wa "fp.fm" (G.dst e) = 1 := by simp [hC7.my.fm.2, hT]
        refine runs_ite_true (x := 1) (by simp [hv7, hvfm, hfm1]) one_ne_zero ?_
        exact contact_tail hN hbook hcont hLd he hB hX hT hhist hsrc hC7 hLC7 hv7 hrv7 hu57 hW57 hV57
          (by omega) (by omega) (by rw [hcap7]; omega) (by rw [hcap7, hcap]; omega)
      · have hfm0 : st7.wa "fp.fm" (G.dst e) = 0 := by simp [hC7.my.fm.2, hT]
        refine runs_ite_false (by simp [hv7, hvfm, hfm0]) ?_
        have hvK : ((G.dst e : Fin G.n) : ℕ) < st7.wlen "fp.inK" := by
          rw [hC7.my.inK.1]; exact (G.dst e).isLt
        by_cases hK : G.dst e ∈ σ.K
        · -- FH.20–FH.22: an existing member
          have hk1 : st7.wa "fp.inK" (G.dst e) = 1 := by
            simp [hC7.my.inK.2, List.mem_toFinset.mpr hK]
          refine runs_ite_true (x := 1) (by simp [hv7, hvK, hk1]) one_ne_zero ?_
          exact old_tail hN hbook hcont hLd he hB hX hT hK hfin hklt hhist hsrc hC7 hLC7 hv7 hrv7
            hp7 hu57 hW57 hV57 (by omega) (by omega) (by rw [hcap7]; omega)
            (by rw [hcap7, hcap]; omega)
        · -- FH.15–FH.19: a new member
          have hk0 : st7.wa "fp.inK" (G.dst e) = 0 := by
            simp [hC7.my.inK.2, hK]
          refine runs_ite_false (by simp [hv7, hvK, hk0]) ?_
          exact new_tail hN hbook hcont hLd he hB hX hT hK hfin hklt hhist hsrc hC7 hLC7 hv7 hrv7
            hp7 hu57 hW57 hV57 (by omega) (by omega) (by rw [hcap7]; omega)
            (by rw [hcap7, hcap]; omega)
  · -- FH.8: range stop (Layer A `brk`)
    rw [if_neg hB] at hbit5
    refine runs_ite_false (by simp [hbit5]) ?_
    have hcap5 : st5.cap = st.cap := hu5.cap
    refine (stop_spec (st := st5.charge 1) (r := 1) (by simp; omega) (by simp; omega)).mono ?_
    rintro st' ⟨hres, hgo', hreg, hu', hc'⟩
    refine ⟨0, by omega, Or.inr ⟨rfl, σ, .cont, n + scanC, g, ?_⟩⟩
    have hu5' : Unchanged st5 st' [] [] ["fp.res", "fp.go"] [] :=
      (Unchanged.charge st5 1 _ _ _ _).trans hu'
    have hstopR : Disj ["fp.res", "fp.go"] myRepRegs := by decide
    refine ⟨cont_stop hcont hLd (Scan.brk σ e L'' he hB), ?_, hC5.my.frameR hu5' (Disj.nil_left _)
      hstopR, (hC5.cur.toOutRep).frameR hu5' (Disj.nil_left _), ?_, hgo', ?_, hhist, ?_⟩
    · exact hC5.lab.frame hu5' (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
        (Disj.nil_left _) (hN.myR_slB.mono_left (by simp [myRegs])) (Disj.nil_left _)
        (Disj.nil_left _) (Disj.nil_left _) (hN.myR_slX.mono_left (by simp [myRegs]))
        (Disj.nil_left _) (by simp at hc'; omega)
    · rw [hreg "fp.u" (by decide) (by decide)]; simpa using hC5.ureg
    · exact Or.inl ⟨rfl, Or.inr hres⟩
    · refine Book.step hbook (Unchanged.trans' hu5 hu5') (by simp) (by simp) ?_ ?_ ?_ ?_ (by decide)
      · intro x hx
        simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with ((rfl | rfl | rfl) | hx) | (rfl | rfl)
        · exact sub_scanWR_my (by simp [myRegs])
        · exact sub_scanWR_ifc (by simp)
        · exact sub_scanWR_ifc (by simp)
        · exact sub_scanWR_cand hx
        · exact sub_scanWR_my (by simp [myRegs])
        · exact sub_scanWR_my (by simp [myRegs])
      · intro x hx; simp only [List.append_nil] at hx; exact sub_scanVR_cand hx
      · simp at hc'; omega
      · simp at hc'; omega

end Frontier.CHD.BL2
