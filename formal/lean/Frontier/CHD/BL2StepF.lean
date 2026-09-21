import Frontier.CHD.BL2StepD

/-!
# Frontier.CHD.BL2StepF — B-L2: the contact branch of a scan iteration (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {c : FPCtx G s} {T : Finset (Fin G.n)} {slB slX : String}
  {u : Fin G.n}

/-- FH.10–FH.13: relax into the tree vertex, record the contact edge, stop with code 2. -/
theorem contact_tail (hN : Names LI slB slX) {σ₀ σ : SSt G s} {g₀ g : LI.Gh} {st₀ st st7 : State V}
    {n : ℕ} {Ld L'' : List (Fin G.m)} {e : Fin G.m} {W7 V7 : List String}
    (hbook : Book LI st₀ st n)
    (hcont : ∀ σ' r n', Scan c T u σ (Ld ++ e :: L'') σ' r n' →
      Scan c T u σ₀ (c.out u) σ' r (n + n'))
    (hLd : ∀ x ∈ Ld, x ∈ σ.D) (he : e ∉ σ.D) (hB : ext (σ.d u) e < c.B)
    (hX : ¬ σ.d (G.dst e) < c.Lx) (hT : G.dst e ∈ T) (hhist : LI.gext g₀ g) (hsrc : G.src e = u)
    (hC7 : Core LI c T slB slX u σ (Ld ++ e :: L'') g st7) (hLC7 : LI.LC st7 σ.d g e)
    (hv7 : st7.w "fp.v" = G.dst e) (hrv7 : st7.w LI.rv = G.dst e)
    (hu7 : Unchanged st st7 [] [] W7 V7) (hW7 : W7 ⊆ scanWR LI) (hV7 : V7 ⊆ scanVR LI)
    (hc7 : st.cost ≤ st7.cost) (hc7' : st7.cost + 2 + LI.Crel + 6 ≤ st.cost + Kit LI)
    (hroom : st7.cost + 2 + LI.Crel ≤ LI.c0 + st7.cap) (hcap7 : 3 < st7.cap) :
    Runs ops (fpContact LI) ((st7.charge 1).charge 1)
      (fun st' => ∃ m', m' < (Ld ++ e :: L'').length + 1 ∧
        LoopI LI c T slB slX u σ₀ g₀ st₀ m' st') := by
  have hu78 : Unchanged st7 ((st7.charge 1).charge 1) [] [] [] [] :=
    (Unchanged.charge st7 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)
  have hLC8 : LI.LC ((st7.charge 1).charge 1) σ.d g e :=
    LI.LC_frame hLC7 hu78 (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)
      (Disj.nil_left _) (by simp only [State.charge_cost]; omega)
  have hrv8 : ((st7.charge 1).charge 1).w LI.rv = G.dst e := by simpa using hrv7
  have hroom8 : ((st7.charge 1).charge 1).cost + LI.Crel ≤ LI.c0 + ((st7.charge 1).charge 1).cap := by
    simp only [State.charge_cost, State.charge_cap]; omega
  refine runs_seq ((LI.relaxC_spec hLC8 hrv8 hroom8).mono ?_)
  rintro st9 ⟨g', hgg', hLT9, hok9, hu9, hc9a, hc9b⟩
  have hk8 : ((st7.charge 1).charge 1).cost = st7.cost + 2 := by simp
  rw [hk8] at hc9a hc9b
  rw [hsrc] at hLT9
  have hrelA : Disj LI.relWA myRepArrs := hN.relA_my.mono_right myRepArrs_sub
  have hrelR : Disj LI.relWR myRepRegs := hN.rel_my.mono_right myRepRegs_sub
  have hu9R : ∀ x ∈ myRegs, st9.w x = st7.w x := fun x hx => by
    rw [hu9.wreg x (fun h => hN.rel_my x h hx)]; rfl
  have hcap9 : st9.cap = st7.cap := hu9.cap
  have hB9 : LI.LS st9 slB c.B g' := LI.LS_ext (LI.LS_frame (LI.LS_frame hC7.lab.sB hu78
    (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)) hu9
    hN.relA_slB hN.relAV_slB hN.rel_slB hN.relV_slB) hgg'
  have hX9 : LI.LS st9 slX c.Lx g' := LI.LS_ext (LI.LS_frame (LI.LS_frame hC7.lab.sX hu78
    (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _)) hu9
    hN.relA_slX hN.relAV_slX hN.rel_slX hN.relV_slX) hgg'
  have hM9 : MyRep c T σ st9 :=
    (hC7.my.frameR hu78 (Disj.nil_left _) (Disj.nil_left _)).frameR hu9 hrelA hrelR
  have hO9 : OutRep st9 c σ.D := ((hC7.cur.toOutRep).frameR hu78 (Disj.nil_left _)).frameR hu9
    (hN.relA_my.mono_right (by simp [myArrs]))
  have hu9u : st9.w "fp.u" = u := by rw [hu9R "fp.u" (by simp [myRegs])]; exact hC7.ureg
  have hu9v : st9.w "fp.v" = G.dst e := by rw [hu9R "fp.v" (by simp [myRegs])]; exact hv7
  refine runs_seq (runs_wset (a := u) (by simp [hu9u]) ?_)
  refine runs_seq (runs_wset (a := G.dst e) (by simp [hu9v]) ?_)
  generalize hst10 : (((st9.setW "fp.cu" u).charge 1).setW "fp.cv" (G.dst e)).charge 1 = st10
  have hu10 : Unchanged st9 st10 [] [] ["fp.cu", "fp.cv"] [] := by
    rw [← hst10]
    exact (Unchanged.trans' (Unchanged.trans' (Unchanged.trans' (unch_setW st9 "fp.cu" u)
      (unch_charge' _ 1)) (unch_setW _ "fp.cv" (G.dst e))) (unch_charge' _ 1)).mono
      (by simp) (by simp) (by simp) (by simp)
  have hc10 : st10.cost = st9.cost + 2 := by rw [← hst10]; simp
  have hcu10 : st10.w "fp.cu" = u := by rw [← hst10]; simp
  have hcv10 : st10.w "fp.cv" = G.dst e := by rw [← hst10]; simp
  have hcap10 : st10.cap = st7.cap := by rw [hu10.cap, hcap9]
  refine (stop_spec (st := st10) (r := 2) (by omega) (by omega)).mono ?_
  rintro st' ⟨hres, hgo', hreg, hu', hc'⟩
  have hu10' : Unchanged st9 st' [] [] (["fp.cu", "fp.cv"] ++ ["fp.res", "fp.go"]) [] :=
    (Unchanged.trans' hu10 hu').mono (by simp) (by simp) (by simp) (by simp)
  have hRd : Disj (["fp.cu", "fp.cv"] ++ ["fp.res", "fp.go"]) myRepRegs := by decide
  have hRB : Disj (["fp.cu", "fp.cv"] ++ ["fp.res", "fp.go"]) (LI.slWR slB) :=
    hN.myR_slB.mono_left (by simp [myRegs])
  have hRX : Disj (["fp.cu", "fp.cv"] ++ ["fp.res", "fp.go"]) (LI.slWR slX) :=
    hN.myR_slX.mono_left (by simp [myRegs])
  refine ⟨0, by omega, Or.inr ⟨rfl, { σ with d := relaxL σ.d u e, hit := some (u, G.dst e) },
    .contact, n + scanC, g', ?_⟩⟩
  refine ⟨cont_stop hcont hLd (Scan.contact σ e L'' he hB hX hT),
    ⟨LI.LT_frame hLT9 hu10' (Disj.nil_left _) (Disj.nil_left _) (by omega),
      LI.LS_frame hB9 hu10' (Disj.nil_left _) (Disj.nil_left _) hRB (Disj.nil_left _),
      LI.LS_frame hX9 hu10' (Disj.nil_left _) (Disj.nil_left _) hRX (Disj.nil_left _)⟩,
    (hM9.frameR hu10' (Disj.nil_left _) hRd).congr_σ rfl rfl rfl rfl,
    hO9.frameR hu10' (Disj.nil_left _), ?_, hgo', ?_, LI.gext_trans hhist hgg', ?_⟩
  · rw [hreg "fp.u" (by decide) (by decide), ← hst10]; simp [hu9u]
  · refine Or.inr (Or.inl ⟨rfl, hres, u, G.dst e, rfl, ?_, ?_⟩)
    · rw [hreg "fp.cu" (by decide) (by decide)]; exact hcu10
    · rw [hreg "fp.cv" (by decide) (by decide)]; exact hcv10
  · have hall : Unchanged st st' (([] ++ [] ++ LI.relWA) ++ []) (([] ++ [] ++ LI.relVA) ++ [])
        (((W7 ++ []) ++ LI.relWR) ++ (["fp.cu", "fp.cv"] ++ ["fp.res", "fp.go"]))
        (((V7 ++ []) ++ LI.relVR) ++ []) :=
      Unchanged.trans' (Unchanged.trans' (Unchanged.trans' hu7 hu78) hu9) hu10'
    refine Book.step hbook hall ?_ ?_ ?_ ?_ (by omega) (by omega) (by decide)
    · simp only [List.nil_append, List.append_nil]; exact relWA_sub
    · simp only [List.nil_append, List.append_nil]; exact relVA_sub
    · simp only [List.nil_append, List.append_nil, List.append_subset]
      exact ⟨⟨hW7, relWR_sub⟩, by scan_sub⟩
    · simp only [List.nil_append, List.append_nil, List.append_subset]
      exact ⟨hV7, relVR_sub⟩

end Frontier.CHD.BL2
