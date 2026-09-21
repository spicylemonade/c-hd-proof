import Frontier.CHD.BL2SearchStep

/-!
# Frontier.CHD.BL2SearchRound — B-L2: extract + scan + dispatch (one `stepCont`/`stepContact`/`stepFull`)
(agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {c : FPCtx G s} {T : Finset (Fin G.n)}
  {slB slX : String}

/-- A search from a state with a nonempty heap below the cap costs at least one round. -/
theorem Search.cost_ge_round {σ σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (h : Search c T σ σ' res n) (hK : σ.K.length < c.k) (hH : σ.H ≠ ∅) : c.hext + 1 ≤ n := by
  cases h with
  | empty _ hH' _ => exact absurd hH' hH
  | capped _ hk => omega
  | stepCont _ _ _ _ _ _ _ _ _ _ _ _ => omega
  | stepContact _ _ _ _ _ _ _ _ => omega
  | stepFull _ _ _ _ _ _ _ _ => omega

theorem HeapRep.charge' {st : State V} {k : ℕ} {H : Finset (Fin G.n)} (h : HeapRep st k H)
    (j : ℕ) : HeapRep (st.charge j) k H := h

open Classical in
theorem search_round (hown : OutOK c) (hsort : OutSorted c) (hnd : OutNodup c)
    (hN : Names LI slB slX) (hNX : NamesX LI X slB slX)
    (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V)
    (hbud : ∀ σ' res n', Search c T σ₀ σ' res n' →
      st₀.cost + 2 + KS LI X * n' + KS LI X ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) (hhext : c.k ≤ c.hext)
    {σ : SSt G s} {n : ℕ} {g : LI.Gh} {st : State V}
    (hR : SRep LI c T slB slX σ g st) (hI : SInv c σ) (hhist : LI.gext g₀ g)
    (hcont : ∀ σ'' res n', Search c T σ σ'' res n' → Search c T σ₀ σ'' res (n + n'))
    (hbook : SBook LI X st₀ st n) (hgo1 : st.w "fp.sgo" = 1)
    (hK : σ.K.length < c.k) (hH : σ.H ≠ ∅) :
    Runs ops (seq (fpExtract LI X) (seq (fpScan LI slB slX)
        (ite (lt (var "fp.res") (lit 2)) skip
          (seq (wset "fp.sres" (var "fp.res")) (wset "fp.sgo" (lit 0))))))
      (((st.charge 1).charge 1).charge 1)
      (fun st' => ∃ m', m' < G.n - σ.done.card + 1 ∧
        SLoopI LI X c T slB slX σ₀ g₀ st₀ m' st') := by
  have hcap : st.cap = st₀.cap := hbook.unch.cap
  have hKS : KS LI X = Kit LI + X.Ctt + 40 := rfl
  have hKit : Kit LI = LI.Ccand + LI.Ccmp + LI.Crel + 30 := rfl
  -- a completed round is paid for by the budget
  have hroomN : ∀ N, (∃ σ' res, Search c T σ σ' res N) →
      st.cost + KS LI X * N + KS LI X ≤ LI.c0 + st.cap := by
    rintro N ⟨σ', res, hs⟩
    have hb := hbud _ _ _ (hcont _ _ _ hs)
    have h1 := hbook.cost
    have h2 : KS LI X * (n + N) = KS LI X * n + KS LI X * N := Nat.mul_add _ _ _
    rw [hcap]; omega
  obtain ⟨σc, rc, nc, hsc⟩ := Search.exists_run hown hsort T G.n σ (by omega) hI
  have hnc := Search.cost_ge_round hsc hK hH
  have hroom := hroomN nc ⟨σc, rc, hsc⟩
  have hHk : σ.H.card ≤ c.k := by
    calc σ.H.card ≤ σ.K.toFinset.card := Finset.card_le_card hR.my.HK
      _ ≤ σ.K.length := List.toFinset_card_le _
      _ ≤ c.k := hK.le
  have hKSk : KS LI X * (c.hext + 1) ≥ (X.Ctt + 6) * c.k + 13 + 5 + Kit LI + 10 := by
    have : KS LI X * (c.hext + 1) ≥ KS LI X * (c.k + 1) := Nat.mul_le_mul_left _ (by omega)
    have : KS LI X * (c.k + 1) = KS LI X * c.k + KS LI X := by ring
    have : (X.Ctt + 6) * c.k ≤ KS LI X * c.k := Nat.mul_le_mul_right _ (by omega)
    omega
  have hKSk' : KS LI X * nc ≥ KS LI X * (c.hext + 1) := Nat.mul_le_mul_left _ hnc
  -- ExtractMin
  have hHne : σ.H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hH
  have hfinH : ∀ v ∈ σ.H, σ.d v ≠ ⊤ := fun v hv => hI.finVal v (hI.heapVal hv)
  have hu23 : Unchanged st (((st.charge 1).charge 1).charge 1) [] [] [] [] :=
    ((Unchanged.charge st 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)).trans
      (Unchanged.charge _ 1 _ _ _ _)
  have hLT2 : LI.LT (((st.charge 1).charge 1).charge 1) σ.d g :=
    LI.LT_frame hR.lab.lab hu23 (Disj.nil_left _) (Disj.nil_left _) (by simp; omega)
  have hext := extract_spec (st := ((st.charge 1).charge 1).charge 1) hNX
    ((hR.my.heap).charge' _ |>.charge' _ |>.charge' _) hHne hLT2 hfinH
    (by simp only [State.charge_cost, State.charge_cap]
        have : (X.Ctt + 6) * σ.H.card ≤ (X.Ctt + 6) * c.k := Nat.mul_le_mul_left _ hHk
        omega)
    (by simp; rw [hcap]; omega) hHk
  refine runs_seq (hext.mono ?_)
  rintro st_e ⟨u, huH, hmin, hue, hHe, hue_u, hce0, hce⟩
  simp only [State.charge_cost] at hce0 hce
  set σe : SSt G s := { σ with H := σ.H.erase u, done := insert u σ.done } with hσe
  have hu2e : Unchanged st st_e ["fp.H", "fp.hp", "fp.inH"] [] (extRegs ++ [X.ra, X.rb] ++ X.ttWR)
      X.ttVR := (hu23.cat hue_u).mono (by simp) (by simp) (by simp) (by simp)
  have hWe_tab : Disj ["fp.H", "fp.hp", "fp.inH"] LI.tabWA := hN.myW_tab.mono_left (by simp [myWArrs])
  have hWe_slB : Disj ["fp.H", "fp.hp", "fp.inH"] (LI.slWA slB) :=
    hN.myA_slB.mono_left (by simp [myArrs])
  have hWe_slX : Disj ["fp.H", "fp.hp", "fp.inH"] (LI.slWA slX) :=
    hN.myA_slX.mono_left (by simp [myArrs])
  have hRe_slB : Disj (extRegs ++ [X.ra, X.rb] ++ X.ttWR) (LI.slWR slB) :=
    Disj.append_left (Disj.append_left (hNX.sr_slB.mono_left (by simp)) hNX.ab_slB) hNX.tt_slB
  have hRe_slX : Disj (extRegs ++ [X.ra, X.rb] ++ X.ttWR) (LI.slWR slX) :=
    Disj.append_left (Disj.append_left (hNX.sr_slX.mono_left (by simp)) hNX.ab_slX) hNX.tt_slX
  have hRe_my : Disj (extRegs ++ [X.ra, X.rb] ++ X.ttWR) ["gM", "fp.kl", "fp.k"] :=
    Disj.append_left (Disj.append_left (by decide) (hNX.ab_my.mono_right (by simp [myRegs])))
      (hNX.tt_my.mono_right (by simp [myRegs]))
  have hLe : LabRep LI c slB slX σe.d g st_e :=
    hR.lab.frame hu2e hWe_tab (Disj.nil_left _) hWe_slB (Disj.nil_left _) hRe_slB
      (hNX.ttV_slB.mono_left (by simp) |> fun h => h) hWe_slX (Disj.nil_left _) hRe_slX
      hNX.ttV_slX (by omega)
  have hMe : MyRep c T σe st_e :=
    (MyRep.setHeap' (σ := σ) hR.my hHe hu2e hRe_my
      ((Finset.erase_subset _ _).trans hR.my.HK)).congr_σ rfl rfl rfl rfl
  have hOe : OutRep st_e c σe.D := hR.out.frameR hu2e (by decide)
  have hfin_u : σe.d u ≠ ⊤ := hfinH u huH
  have hcape : st_e.cap = st.cap := by rw [hu2e.cap]
  -- Layer-A facts about the extraction
  obtain ⟨hIe, hCe⟩ := inv_extract hI huH hmin
  have hudone : u ∉ σ.done := fun h => Finset.disjoint_left.mp hI.doneH h huH
  have hcard : σ.done.card + 1 ≤ G.n := by
    have := Finset.card_le_univ (insert u σ.done)
    rw [Finset.card_insert_of_notMem hudone, Fintype.card_fin] at this
    exact this
  -- the scan's budget: every scan outcome extends to a search outcome from `σ`
  have hbud_s : ∀ σ' r n', Scan c T u σe (c.out u) σ' r n' →
      st_e.cost + 5 + Kit LI * n' + Kit LI ≤ LI.c0 + st_e.cap := by
    intro σ' r n' hs
    have hN' : ∃ N, n' + c.hext + 1 ≤ N ∧ ∃ σ'' res, Search c T σ σ'' res N := by
      cases r with
      | cont =>
        obtain ⟨hI', -⟩ := Scan.inv hown hsort hs (List.suffix_refl _) hIe hCe
        obtain ⟨σ'', res, n'', hs''⟩ := Search.exists_run hown hsort T G.n σ' (by omega) hI'
        exact ⟨n' + n'' + c.hext + 1, by omega, σ'', res,
          Search.stepCont σ σ' σ'' u res n' n'' hK huH hmin hs hs''⟩
      | contact =>
        exact ⟨n' + c.hext + 1, le_rfl, σ', .contact, Search.stepContact σ σ' u n' hK huH hmin hs⟩
      | full =>
        exact ⟨n' + c.hext + 1, le_rfl, σ', .success, Search.stepFull σ σ' u n' hK huH hmin hs⟩
    obtain ⟨N, hNge, hex⟩ := hN'
    have h1 := hroomN N hex
    have h2 : KS LI X * N ≥ KS LI X * (n' + (c.hext + 1)) := Nat.mul_le_mul_left _ (by omega)
    have h3 : KS LI X * (n' + (c.hext + 1)) = KS LI X * n' + KS LI X * (c.hext + 1) :=
      Nat.mul_add _ _ _
    have h4 : Kit LI * n' ≤ KS LI X * n' := Nat.mul_le_mul_right _ (by omega)
    have h5 : (X.Ctt + 6) * σ.H.card ≤ (X.Ctt + 6) * c.k := Nat.mul_le_mul_left _ hHk
    rw [hcape]; omega
  refine runs_seq ((scan_spec hown hnd hN hLe hMe hOe hue hfin_u hK hbud_s
    (by rw [hcape, hcap]; omega)).mono ?_)
  rintro st_s ⟨σ', r, n_s, g', hscan, hLs, hMs, hOs, hus, hcode, hgg', hus_u, hcs0, hcs⟩
  have hdone' : σ'.done = insert u σ.done := Scan.done_eq hscan
  have hIs : SInv c σ' := (Scan.inv hown hsort hscan (List.suffix_refl _) hIe hCe).1
  have hmeas : G.n - σ'.done.card + 1 < G.n - σ.done.card + 1 := by
    rw [hdone', Finset.card_insert_of_notMem hudone]; omega
  -- `fp.sgo` survives extraction and scan
  have hsgo_s : st_s.w "fp.sgo" = 1 := by
    rw [hus_u.wreg "fp.sgo" (by
      intro h
      simp only [scanWR, List.mem_append] at h
      rcases h with (((h | h) | h) | h) | h
      · exact absurd h (by decide)
      · exact hNX.sg_li "fp.sgo" (by simp) (by simp only [List.mem_append]; tauto)
      · exact hNX.sg_li "fp.sgo" (by simp) (by simp only [List.mem_append]; tauto)
      · exact hNX.sg_li "fp.sgo" (by simp) (by simp only [List.mem_append]; tauto)
      · exact hNX.sg_li "fp.sgo" (by simp) (by simp only [List.mem_append]; tauto))]
    rw [hu2e.wreg "fp.sgo" (by
      intro h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact absurd h (by decide)
      · exact hNX.ab_sr _ h (by simp)
      · exact hNX.tt_sr _ h (by simp))]
    exact hgo1
  have hall : Unchanged st st_s (["fp.H", "fp.hp", "fp.inH"] ++ scanWA LI) ([] ++ scanVA LI)
      ((extRegs ++ [X.ra, X.rb] ++ X.ttWR) ++ scanWR LI) (X.ttVR ++ scanVR LI) := hu2e.cat hus_u
  have hcost_round : st_s.cost + 3 ≤ st.cost + KS LI X * (n_s + c.hext + 1) := by
    have h1 : KS LI X * (n_s + c.hext + 1) = KS LI X * n_s + KS LI X * (c.hext + 1) := by ring
    have h4 : Kit LI * n_s ≤ KS LI X * n_s := Nat.mul_le_mul_right _ (by omega)
    have h5 : (X.Ctt + 6) * σ.H.card ≤ (X.Ctt + 6) * c.k := Nat.mul_le_mul_left _ hHk
    omega
  have hWA : ["fp.H", "fp.hp", "fp.inH"] ++ scanWA LI ⊆ srchWA LI := by
    apply List.append_subset.mpr
    refine ⟨?_, fun x hx => hx⟩
    intro x hx
    apply mem_scanWA_my
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [myArrs]
  have hVA : [] ++ scanVA LI ⊆ srchVA LI := by simp [srchVA]
  have hWR : (extRegs ++ [X.ra, X.rb] ++ X.ttWR) ++ scanWR LI ⊆ srchWR LI X := by
    intro x hx; simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact extW_sub_srch (by simpa only [List.mem_append] using hx)
    · exact scanWR_sub_srch hx
  have hVR : X.ttVR ++ scanVR LI ⊆ srchVR LI X := by
    intro x hx; simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact ttV_sub_srch hx
    · exact scanVR_sub_srch hx
  have hcs : st_s.cap = st₀.cap := by rw [hus_u.cap, hcape, hcap]
  have hc1s : 1 < st_s.cap := by omega
  have hc2s : 2 < st_s.cap := by omega
  have hev : evalW st_s (lt (var "fp.res") (lit 2)) =
      some (if st_s.w "fp.res" < 2 then 1 else 0) :=
    evalW_lt_of (by simp) (evalW_lit_of hc2s) hc1s
  rcases hcode with ⟨rfl, hres⟩ | ⟨rfl, hres, a, b, hhit, hcu, hcv⟩ | ⟨rfl, hres⟩
  · -- continue (Layer A `stepCont`)
    have hlt : st_s.w "fp.res" < 2 := by rcases hres with h | h <;> omega
    refine runs_ite_true (x := 1) (by rw [hev, if_pos hlt]) one_ne_zero (runs_skip ?_)
    refine ⟨G.n - σ'.done.card + 1, hmeas, Or.inl ⟨σ', n + (n_s + c.hext + 1), g', rfl, ?_⟩⟩
    have hch : Unchanged st_s ((st_s.charge 1).charge 1) [] [] [] [] :=
      (Unchanged.charge st_s 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)
    refine ⟨⟨hLs.charge 1 |>.charge 1, hMs.charge' 1 |>.charge' 1, hOs.charge 1 |>.charge 1⟩, hIs,
      LI.gext_trans hhist hgg', fun σ'' res n' h' => ?_, ?_, by simpa using hsgo_s⟩
    · have := hcont _ _ _ (Search.stepCont σ σ' σ'' u res n_s n' hK huH hmin hscan h')
      rwa [show n + (n_s + n' + c.hext + 1) = n + (n_s + c.hext + 1) + n' by omega] at this
    · exact SBook.step hbook (hall.trans (hch.mono (by simp) (by simp) (by simp) (by simp)))
        hWA hVA hWR hVR (by simp; omega) (by simp; omega)
  · -- contact (Layer A `stepContact`)
    have hge : ¬ st_s.w "fp.res" < 2 := by omega
    refine runs_ite_false (by rw [hev, if_neg hge]) ?_
    refine (sstop_spec (a := 2) (by simp [hres]) (by simp only [State.charge_cap]; omega)).mono ?_
    rintro st' ⟨hsres, hgo', hreg', hu', hc'⟩
    simp only [State.charge_cost] at hc'
    have hu'' : Unchanged st_s st' [] [] ["fp.sres", "fp.sgo"] [] :=
      (Unchanged.charge st_s 1 _ _ _ _).trans hu'
    have hsgR : Disj ["fp.sres", "fp.sgo"] myRepRegs := by decide
    have hsgB : Disj ["fp.sres", "fp.sgo"] (LI.slWR slB) := hNX.sr_slB.mono_left (by simp [extRegs])
    have hsgX : Disj ["fp.sres", "fp.sgo"] (LI.slWR slX) := hNX.sr_slX.mono_left (by simp [extRegs])
    refine ⟨0, by omega, Or.inr ⟨rfl, σ', .contact, n + (n_s + c.hext + 1), g', ⟨?_,
      SRep.frame_regs hN ⟨hLs, hMs, hOs⟩ hu'' hsgR hsgB hsgX (by omega), hIs,
      Or.inr (Or.inl ⟨rfl, hsres⟩), fun _ => ⟨a, b, hhit, ?_, ?_⟩, LI.gext_trans hhist hgg', ?_,
      hgo'⟩⟩⟩
    · exact hcont _ _ _ (Search.stepContact σ σ' u n_s hK huH hmin hscan)
    · rw [hreg' "fp.cu" (by decide) (by decide)]; simpa using hcu
    · rw [hreg' "fp.cv" (by decide) (by decide)]; simpa using hcv
    · refine SBook.step hbook (hall.cat hu'') ?_ ?_ ?_ ?_ (by omega) (by omega)
      · simpa using hWA
      · simpa using hVA
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hWR hx
        · exact sg_sub_srch hx
      · simpa using hVR
  · -- full (Layer A `stepFull`)
    have hge : ¬ st_s.w "fp.res" < 2 := by omega
    refine runs_ite_false (by rw [hev, if_neg hge]) ?_
    refine (sstop_spec (a := 3) (by simp [hres]) (by simp only [State.charge_cap]; omega)).mono ?_
    rintro st' ⟨hsres, hgo', -, hu', hc'⟩
    simp only [State.charge_cost] at hc'
    have hu'' : Unchanged st_s st' [] [] ["fp.sres", "fp.sgo"] [] :=
      (Unchanged.charge st_s 1 _ _ _ _).trans hu'
    have hsgR : Disj ["fp.sres", "fp.sgo"] myRepRegs := by decide
    have hsgB : Disj ["fp.sres", "fp.sgo"] (LI.slWR slB) := hNX.sr_slB.mono_left (by simp [extRegs])
    have hsgX : Disj ["fp.sres", "fp.sgo"] (LI.slWR slX) := hNX.sr_slX.mono_left (by simp [extRegs])
    refine ⟨0, by omega, Or.inr ⟨rfl, σ', .success, n + (n_s + c.hext + 1), g', ⟨?_,
      SRep.frame_regs hN ⟨hLs, hMs, hOs⟩ hu'' hsgR hsgB hsgX (by omega), hIs,
      Or.inr (Or.inr ⟨rfl, hsres⟩), fun h => absurd h (by decide), LI.gext_trans hhist hgg', ?_,
      hgo'⟩⟩⟩
    · exact hcont _ _ _ (Search.stepFull σ σ' u n_s hK huH hmin hscan)
    · refine SBook.step hbook (hall.cat hu'') ?_ ?_ ?_ ?_ (by omega) (by omega)
      · simpa using hWA
      · simpa using hVA
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hWR hx
        · exact sg_sub_srch hx
      · simpa using hVR

end Frontier.CHD.BL2
