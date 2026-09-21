import Frontier.CHD.BL2SearchRound

/-!
# Frontier.CHD.BL2SearchSpec — B-L2: the RAM local search refines Layer A's `Search`
(agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {c : FPCtx G s} {T : Finset (Fin G.n)}
  {slB slX : String}

theorem search_step (hown : OutOK c) (hsort : OutSorted c) (hnd : OutNodup c)
    (hN : Names LI slB slX) (hNX : NamesX LI X slB slX)
    (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V)
    (hbud : ∀ σ' res n', Search c T σ₀ σ' res n' →
      st₀.cost + 2 + KS LI X * n' + KS LI X ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) (hhext : c.k ≤ c.hext)
    {σ : SSt G s} {n : ℕ} {g : LI.Gh} {st : State V}
    (h : SRun LI X c T slB slX σ₀ g₀ st₀ σ n g st) (hgo : st.w "fp.sgo" ≠ 0) :
    Runs ops (fpSearchBody LI X slB slX) (st.charge 1)
      (fun st' => ∃ m', m' < G.n - σ.done.card + 1 ∧
        SLoopI LI X c T slB slX σ₀ g₀ st₀ m' st') := by
  obtain ⟨hR, hI, hhist, hcont, hbook, hgo1⟩ := h
  have hcap : st.cap = st₀.cap := hbook.unch.cap
  have hKS : KS LI X = Kit LI + X.Ctt + 40 := rfl
  -- the room of this round
  obtain ⟨σc, rc, nc, hsc⟩ := Search.exists_run hown hsort T G.n σ (by omega) hI
  have hb := hbud _ _ _ (hcont _ _ _ hsc)
  have hroom : st.cost + KS LI X ≤ LI.c0 + st.cap := by
    have h1 := hbook.cost
    have h2 : KS LI X * n ≤ KS LI X * (n + nc) := Nat.mul_le_mul_left _ (by omega)
    rw [hcap]; omega
  have hkl : st.w "fp.kl" = σ.K.length := hR.my.kl
  have hk : st.w "fp.k" = c.k := hR.my.kreg
  unfold fpSearchBody
  by_cases hK : σ.K.length < c.k
  · refine runs_ite_true (x := 1) (by simp [hkl, hk, hK, fit]; omega) one_ne_zero ?_
    obtain ⟨hl, hlnd, hlset, hlsz, -⟩ := hR.my.heap
    have hlen : hl.length = σ.H.card := by rw [← hlset, List.toFinset_card_of_nodup hlnd]
    by_cases hH : σ.H = ∅
    · -- FH.5: empty heap, the search FAILS (Layer A `empty`)
      have hsz0 : (st.charge 1).w "fp.hsz" = 0 := by
        simp [hlsz, hlen, hH]
      refine runs_ite_false (by simp [hsz0]) ?_
      have hsgR : Disj ["fp.sres", "fp.sgo"] myRepRegs := by decide
      have hsgB : Disj ["fp.sres", "fp.sgo"] (LI.slWR slB) :=
        hNX.sr_slB.mono_left (by simp [extRegs])
      have hsgX : Disj ["fp.sres", "fp.sgo"] (LI.slWR slX) :=
        hNX.sr_slX.mono_left (by simp [extRegs])
      refine (sstop_spec (a := 0) (evalW_lit_of (by simp; omega)) (by simp; omega)).mono ?_
      rintro st' ⟨hres, hgo', -, hu', hc'⟩
      have hu'' : Unchanged st st' [] [] ["fp.sres", "fp.sgo"] [] :=
        (((Unchanged.charge st 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)).trans
          (Unchanged.charge _ 1 _ _ _ _)).trans hu'
      refine ⟨0, by omega, Or.inr ⟨rfl, σ, .failed, n + 1, g, ⟨hcont σ .failed 1
        (Search.empty σ hH hK), hR.frame_regs hN hu'' hsgR hsgB hsgX (by simp at hc'; omega), hI,
        Or.inl ⟨rfl, hres⟩, fun h => absurd h (by decide), hhist, ?_, hgo'⟩⟩⟩
      exact SBook.step hbook hu'' (by simp) (by simp) sg_sub_srch (by simp) (by simp at hc'; omega)
        (by simp at hc' ⊢; omega)
    · -- FH.6: extract, then scan
      have hsz1 : (st.charge 1).w "fp.hsz" ≠ 0 := by
        simp only [State.charge_w, hlsz, hlen]
        exact Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hH)
      refine runs_ite_true (x := (st.charge 1).w "fp.hsz") (by simp) hsz1 ?_
      exact search_round hown hsort hnd hN hNX σ₀ g₀ st₀ hbud hcapW hhext hR hI hhist hcont hbook
        hgo1 hK hH
  · -- FH.5: the member cap is reached, the search SUCCEEDS (Layer A `capped`)
    refine runs_ite_false (by simp [hkl, hk, hK, fit]; omega) ?_
    have hsgR : Disj ["fp.sres", "fp.sgo"] myRepRegs := by decide
    have hsgB : Disj ["fp.sres", "fp.sgo"] (LI.slWR slB) :=
      hNX.sr_slB.mono_left (by simp [extRegs])
    have hsgX : Disj ["fp.sres", "fp.sgo"] (LI.slWR slX) :=
      hNX.sr_slX.mono_left (by simp [extRegs])
    refine (sstop_spec (a := 3) (evalW_lit_of (by simp; omega)) (by simp; omega)).mono ?_
    rintro st' ⟨hres, hgo', -, hu', hc'⟩
    have hu'' : Unchanged st st' [] [] ["fp.sres", "fp.sgo"] [] :=
      ((Unchanged.charge st 1 _ _ _ _).trans (Unchanged.charge _ 1 _ _ _ _)).trans hu'
    refine ⟨0, by omega, Or.inr ⟨rfl, σ, .success, n + 1, g, ⟨hcont σ .success 1
      (Search.capped σ (not_lt.mp hK)), hR.frame_regs hN hu'' hsgR hsgB hsgX (by simp at hc'; omega),
      hI, Or.inr (Or.inr ⟨rfl, hres⟩), fun h => absurd h (by decide), hhist, ?_, hgo'⟩⟩⟩
    exact SBook.step hbook hu'' (by simp) (by simp) sg_sub_srch (by simp) (by simp at hc'; omega)
      (by simp at hc' ⊢; omega)


/-- The postcondition of the local search. -/
def SearchPost (LI : LabI V ops G s) (X : LabX LI) (c : FPCtx G s) (T : Finset (Fin G.n))
    (slB slX : String) (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ st' : State V) : Prop :=
  ∃ σ' res n g', Search c T σ₀ σ' res n ∧ SRep LI c T slB slX σ' g' st' ∧ SInv c σ' ∧
    SResCode st' res ∧
    (res = .contact → ∃ a b : Fin G.n, σ'.hit = some (a, b) ∧ st'.w "fp.cu" = a ∧
      st'.w "fp.cv" = b) ∧ LI.gext g₀ g' ∧
    Unchanged st₀ st' (srchWA LI) (srchVA LI) (srchWR LI X) (srchVR LI X) ∧
    st₀.cost ≤ st'.cost ∧ st'.cost ≤ st₀.cost + 3 + KS LI X * n

/-- **The RAM local search (FH.5–FH.22) refines Layer A's `Search`.** -/
theorem search_spec (hown : OutOK c) (hsort : OutSorted c) (hnd : OutNodup c)
    (hN : Names LI slB slX) (hNX : NamesX LI X slB slX)
    {σ₀ : SSt G s} {g₀ : LI.Gh} {st₀ : State V}
    (hR : SRep LI c T slB slX σ₀ g₀ st₀) (hI : SInv c σ₀)
    (hbud : ∀ σ' res n', Search c T σ₀ σ' res n' →
      st₀.cost + 2 + KS LI X * n' + KS LI X ≤ LI.c0 + st₀.cap)
    (hcapW : c.k + 4 < st₀.cap) (hhext : c.k ≤ c.hext) :
    Runs ops (fpSearch LI X slB slX) st₀ (SearchPost LI X c T slB slX σ₀ g₀ st₀) := by
  unfold fpSearch
  refine runs_seq (runs_wset (a := 1) (evalW_lit_of (by omega)) ?_)
  generalize hst1 : (st₀.setW "fp.sgo" 1).charge 1 = st1
  have hu1 : Unchanged st₀ st1 [] [] ["fp.sgo"] [] := by
    rw [← hst1]
    exact ((unch_setW st₀ "fp.sgo" 1).cat (unch_charge' _ 1)).mono (by simp) (by simp) (by simp)
      (by simp)
  have hc1 : st1.cost = st₀.cost + 1 := by rw [← hst1]; simp
  have hgo1 : st1.w "fp.sgo" = 1 := by rw [← hst1]; simp
  have hsgR : Disj ["fp.sgo"] myRepRegs := by decide
  have hsgB : Disj ["fp.sgo"] (LI.slWR slB) := hNX.sr_slB.mono_left (by simp [extRegs])
  have hsgX : Disj ["fp.sgo"] (LI.slWR slX) := hNX.sr_slX.mono_left (by simp [extRegs])
  have hR1 : SRep LI c T slB slX σ₀ g₀ st1 := hR.frame_regs hN hu1 hsgR hsgB hsgX (by omega)
  have hbook1 : SBook LI X st₀ st1 0 :=
    ⟨hu1.mono (by simp) (by simp) (fun x hx => sg_sub_srch (by simp at hx ⊢; right; exact hx))
      (by simp), by omega, by omega⟩
  refine runs_while_nat (SLoopI LI X c T slB slX σ₀ g₀ st₀) _ ?_ (G.n - σ₀.done.card + 1) st1
    (Or.inl ⟨σ₀, 0, g₀, rfl, ⟨hR1, hI, LI.gext_refl g₀, fun σ'' res n' h' => by simpa using h',
      hbook1, hgo1⟩⟩)
  intro m st hL
  rcases hL with ⟨σ, n, g, rfl, hSR⟩ | ⟨rfl, σ', res, n, g, hSS⟩
  · refine ⟨st.w "fp.sgo", by simp, fun hgo =>
      search_step hown hsort hnd hN hNX σ₀ g₀ st₀ hbud hcapW hhext hSR hgo, fun h0 => ?_⟩
    rw [hSR.go] at h0; exact absurd h0 one_ne_zero
  · refine ⟨st.w "fp.sgo", by simp, fun hgo => absurd hSS.go hgo, fun _ => ?_⟩
    exact ⟨σ', res, n, g, hSS.srch, ⟨hSS.rep.lab.charge 1, hSS.rep.my.charge' 1,
      hSS.rep.out.charge 1⟩, hSS.inv, by simpa [SResCode] using hSS.code,
      fun h => by simpa using hSS.hitc h, hSS.hist,
      hSS.book.unch.trans (Unchanged.charge st 1 _ _ _ _),
      by simp; exact hSS.book.cost0.trans (Nat.le_succ _), by simp; have := hSS.book.cost; omega⟩

end Frontier.CHD.BL2
