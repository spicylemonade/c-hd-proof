import Frontier.CHD.BL2HeapDel
import Frontier.CHD.BL2StepD

/-!
# Frontier.CHD.BL2Extract — B-L2: ExtractMin on the unsorted heap array (FH.6) (agent-09, NON-GATE)

A linear scan of `fp.H[0..fp.hsz)` with table-vs-table label compares (`cmpTT`, one extra
B-LAB fragment, interface `LabX`), then swap-with-last deletion.  Cost `O(|H|)` compares.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- The extra label fragment for ExtractMin: `bit := [d[ra] < d[rb]]` (both finite). -/
structure LabX (LI : LabI V ops G s) where
  ra : String
  rb : String
  cmpTT : Stmt
  Ctt : ℕ
  ttWR : List String
  ttVR : List String
  cmpTT_spec : ∀ {st : State V} {d g} {a b : Fin G.n},
    LI.LT st d g → d a ≠ ⊤ → d b ≠ ⊤ → st.w ra = a → st.w rb = b →
    st.cost + Ctt ≤ LI.c0 + st.cap →
    Runs ops cmpTT st (fun st' => st'.w LI.bit = (if d a < d b then 1 else 0) ∧
      Unchanged st st' [] [] ttWR ttVR ∧ st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + Ctt)

variable (LI : LabI V ops G s) (X : LabX LI)

/-- Registers of the extraction. -/
def extRegs : List String := ["fp.bi", "fp.i", "fp.t", "fp.u", "fp.hsz"]

/-- Name hygiene for the extraction. -/
structure NamesX (slB slX : String) : Prop where
  tt_my : Disj X.ttWR (myRegs ++ extRegs)
  tt_slB : Disj X.ttWR (LI.slWR slB)
  tt_slX : Disj X.ttWR (LI.slWR slX)
  ttV_slB : Disj X.ttVR (LI.slVR slB)
  ttV_slX : Disj X.ttVR (LI.slVR slX)
  ab_my : Disj [X.ra, X.rb] (myRegs ++ extRegs)
  ab_slB : Disj [X.ra, X.rb] (LI.slWR slB)
  ab_slX : Disj [X.ra, X.rb] (LI.slWR slX)
  ra_rb : X.ra ≠ X.rb
  bit_my : LI.bit ∉ myRegs ++ extRegs
  sr_slB : Disj (extRegs ++ ["fp.sres", "fp.sgo"]) (LI.slWR slB)
  sr_slX : Disj (extRegs ++ ["fp.sres", "fp.sgo"]) (LI.slWR slX)
  ab_sr : Disj [X.ra, X.rb] ["fp.sres", "fp.sgo"]
  tt_sr : Disj X.ttWR ["fp.sres", "fp.sgo"]
  sg_li : Disj ["fp.sres", "fp.sgo"] ([LI.ru, LI.re, LI.rv] ++ LI.candWR ++ LI.cmpWR ++ LI.relWR)

/-- One comparison step of the ExtractMin scan. -/
def fpExtStep : Stmt :=
  seq (wset X.ra (load "fp.H" (var "fp.i")))
  (seq (wset X.rb (load "fp.H" (var "fp.bi")))
  (seq X.cmpTT
  (seq (ite (var LI.bit) (wset "fp.bi" (var "fp.i")) skip)
       (wset "fp.i" (add (var "fp.i") (lit 1))))))

/-- FH.6: ExtractMin (minimum label; ties broken by the first position). -/
def fpExtract : Stmt :=
  seq (wset "fp.bi" (lit 0))
  (seq (wset "fp.i" (lit 1))
  (seq (Stmt.while (lt (var "fp.i") (var "fp.hsz")) (fpExtStep LI X))
  (seq (wset "fp.u" (load "fp.H" (var "fp.bi")))
  (seq (wset "fp.hsz" (sub (var "fp.hsz") (lit 1)))
  (seq (wset "fp.t" (load "fp.H" (var "fp.hsz")))
  (seq (wstore "fp.H" (var "fp.bi") (var "fp.t"))
  (seq (wstore "fp.hp" (var "fp.t") (var "fp.bi"))
       (wstore "fp.inH" (var "fp.u") (lit 0)))))))))

variable {LI X}

/-- One comparison step keeps `bi` an argmin of the scanned prefix. -/
theorem extStep_spec (hNX : NamesX LI X slB slX) {st : State V} {d : Labels G s} {g : LI.Gh}
    {hl : List (Fin G.n)} {i b : ℕ} {yb : Fin G.n}
    (hLT : LI.LT st d g) (harr : LArr st "fp.H" hl) (hHl : hl.length ≤ st.wlen "fp.H")
    (hfin : ∀ v ∈ hl, d v ≠ ⊤) (hi : st.w "fp.i" = i) (hb : st.w "fp.bi" = b)
    (hil : i < hl.length) (hyb : hl[b]? = some yb) (hmin : ∀ y ∈ hl.take i, d yb ≤ d y)
    (hbud : st.cost + X.Ctt + 5 ≤ LI.c0 + st.cap) (hcap : hl.length + 1 < st.cap) :
    Runs ops (fpExtStep LI X) st (fun st' => ∃ b' yb', hl[b']? = some yb' ∧
      (∀ y ∈ hl.take (i + 1), d yb' ≤ d y) ∧
      st'.w "fp.i" = i + 1 ∧ st'.w "fp.bi" = b' ∧
      Unchanged st st' [] [] (["fp.bi", "fp.i", X.ra, X.rb] ++ X.ttWR) X.ttVR ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + X.Ctt + 5) := by
  have hbl : b < hl.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hyb; exact absurd hyb (by simp)
  have hyb' : hl[b] = yb := by
    rw [List.getElem?_eq_getElem hbl] at hyb; exact Option.some.inj hyb
  have hHi : st.wa "fp.H" i = (hl[i] : ℕ) := by rw [harr i hil]; rfl
  have hHb : st.wa "fp.H" b = (yb : ℕ) := by rw [harr b hbl]; simp [hyb']
  have hiL : i < st.wlen "fp.H" := by omega
  have hbL : b < st.wlen "fp.H" := by omega
  have hra_my : ∀ x ∈ myRegs ++ extRegs, x ≠ X.ra := fun x hx h =>
    hNX.ab_my X.ra (by simp) (h ▸ hx)
  have hrb_my : ∀ x ∈ myRegs ++ extRegs, x ≠ X.rb := fun x hx h =>
    hNX.ab_my X.rb (by simp) (h ▸ hx)
  have htake : hl.take (i + 1) = hl.take i ++ [hl[i]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hil]; rfl
  unfold fpExtStep
  -- ra := H[i]
  refine runs_seq (runs_wset (a := hl[i]) (by simp [hi, hiL, hHi]) ?_)
  -- rb := H[bi]
  have hbi1 : ((st.setW X.ra hl[i]).charge 1).w "fp.bi" = b := by
    simp [hra_my "fp.bi" (by simp [extRegs]), hb]
  refine runs_seq (runs_wset (a := yb) (by simp [hbi1, hbL, hHb]) ?_)
  generalize hst2 : (((st.setW X.ra hl[i]).charge 1).setW X.rb yb).charge 1 = st2
  have hu2 : Unchanged st st2 [] [] [X.ra, X.rb] [] := by
    rw [← hst2]
    exact (Unchanged.cat (Unchanged.cat (Unchanged.cat (unch_setW st X.ra _)
      (unch_charge' _ 1)) (unch_setW _ X.rb yb)) (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hc2 : st2.cost = st.cost + 2 := by rw [← hst2]; simp
  have hcap2 : st2.cap = st.cap := by rw [← hst2]; simp
  have hra2 : st2.w X.ra = hl[i] := by rw [← hst2]; simp [hNX.ra_rb]
  have hrb2 : st2.w X.rb = yb := by rw [← hst2]; simp
  have hLT2 : LI.LT st2 d g := LI.LT_frame hLT hu2 (Disj.nil_left _) (Disj.nil_left _) (by omega)
  have hfi : d hl[i] ≠ ⊤ := hfin _ (List.getElem_mem _)
  have hfb : d yb ≠ ⊤ := hfin _ (by rw [← hyb']; exact List.getElem_mem _)
  refine runs_seq ((X.cmpTT_spec hLT2 hfi hfb hra2 hrb2 (by omega)).mono ?_)
  rintro st3 ⟨hbit3, hu3, hc3a, hc3b⟩
  have hreg3 : ∀ x ∈ myRegs ++ extRegs, st3.w x = st.w x := fun x hx => by
    rw [hu3.wreg x (fun h => hNX.tt_my x h hx), hu2.wreg x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hra_my x hx, hrb_my x hx⟩)]
  have hi3 : st3.w "fp.i" = i := by rw [hreg3 "fp.i" (by simp [extRegs])]; exact hi
  have hcap3 : st3.cap = st.cap := by rw [hu3.cap, hcap2]
  have hc3 : i + 1 < st3.cap := by rw [hcap3]; omega
  have hc3' : 1 < st3.cap := by omega
  have hu23 : Unchanged st st3 [] [] ([X.ra, X.rb] ++ X.ttWR) X.ttVR :=
    (Unchanged.cat hu2 hu3).mono (by simp) (by simp) (fun _ h => h) (by simp)
  by_cases hlt : d hl[i] < d yb
  · rw [if_pos hlt] at hbit3
    refine runs_seq (runs_ite_true (x := 1) (by simp [hbit3]) one_ne_zero
      (runs_wset (a := i) (by simp [hi3]) ?_))
    refine runs_wset (a := i + 1) (by simp [hi3, fit, hc3, hc3']) ?_
    refine ⟨i, hl[i], List.getElem?_eq_getElem hil, ?_, by simp, by simp, ?_, by simp; omega,
      by simp; omega⟩
    · intro y hy
      rw [htake, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact le_of_lt (lt_of_lt_of_le hlt (hmin y hy))
      · exact le_rfl
    · refine (Unchanged.cat (Unchanged.cat (Unchanged.cat hu23 (unch_charge' _ 1))
        (Unchanged.cat (unch_setW _ "fp.bi" i) (unch_charge' _ 1)))
        (Unchanged.cat (unch_setW _ "fp.i" (i + 1)) (unch_charge' _ 1))).mono (by simp)
        (by simp) ?_ (by simp)
      intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.nil_append, List.append_nil] at hx ⊢; tauto
  · rw [if_neg hlt] at hbit3
    refine runs_seq (runs_ite_false (by simp [hbit3]) (runs_skip ?_))
    refine runs_wset (a := i + 1) (by simp [hi3, fit, hc3, hc3']) ?_
    refine ⟨b, yb, hyb, ?_, by simp, ?_, ?_, by simp; omega, by simp; omega⟩
    · intro y hy
      rw [htake, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hmin y hy
      · exact not_lt.mp hlt
    · simp [hreg3 "fp.bi" (by simp [extRegs]), hb]
    · refine (Unchanged.cat (Unchanged.cat (Unchanged.cat hu23 (unch_charge' _ 1))
        (unch_charge' _ 1)) (Unchanged.cat (unch_setW _ "fp.i" (i + 1))
        (unch_charge' _ 1))).mono (by simp) (by simp) ?_ (by simp)
      intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.nil_append, List.append_nil] at hx ⊢; tauto

/-- **ExtractMin** (FH.6): returns in `fp.u` a vertex of minimum label, removed from the heap. -/
theorem extract_spec (hNX : NamesX LI X slB slX) {st : State V} {k : ℕ} {H : Finset (Fin G.n)}
    {d : Labels G s} {g : LI.Gh}
    (hH : HeapRep st k H) (hne : H.Nonempty) (hLT : LI.LT st d g) (hfin : ∀ v ∈ H, d v ≠ ⊤)
    (hbud : st.cost + 10 + (X.Ctt + 6) * H.card ≤ LI.c0 + st.cap) (hcap : k + 2 < st.cap)
    (hHk : H.card ≤ k) :
    Runs ops (fpExtract LI X) st (fun st' => ∃ u ∈ H, (∀ y ∈ H, d u ≤ d y) ∧ st'.w "fp.u" = u ∧
      HeapRep st' k (H.erase u) ∧
      Unchanged st st' ["fp.H", "fp.hp", "fp.inH"] [] (extRegs ++ [X.ra, X.rb] ++ X.ttWR) X.ttVR ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 10 + (X.Ctt + 6) * H.card) := by
  obtain ⟨hl, hnd, hset, hsz, hcapH, harr, hpL, hpos, hbL, hb⟩ := hH
  have hlen : hl.length = H.card := by rw [← hset, List.toFinset_card_of_nodup hnd]
  have hpos1 : 0 < hl.length := by rw [hlen]; exact Finset.card_pos.mpr hne
  have hne' : hl ≠ [] := List.ne_nil_of_length_pos hpos1
  have hfin' : ∀ v ∈ hl, d v ≠ ⊤ := fun v hv => hfin v (hset ▸ List.mem_toFinset.mpr hv)
  unfold fpExtract
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  refine runs_seq (runs_wset (a := 1) (evalW_lit_of (by simp; omega)) ?_)
  generalize hst1 : ((((st.setW "fp.bi" 0).charge 1).setW "fp.i" 1).charge 1) = st1
  have hu1 : Unchanged st st1 [] [] ["fp.bi", "fp.i"] [] := by
    rw [← hst1]
    exact (Unchanged.cat (Unchanged.cat (Unchanged.cat (unch_setW st "fp.bi" 0)
      (unch_charge' _ 1)) (unch_setW _ "fp.i" 1)) (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hc1 : st1.cost = st.cost + 2 := by rw [← hst1]; simp
  have hcap1 : st1.cap = st.cap := by rw [← hst1]; simp
  have hsz1 : st1.w "fp.hsz" = hl.length := by rw [← hst1]; simp [hsz]
  -- the comparison loop
  let I : ℕ → State V → Prop := fun m st' => ∃ i b yb, m = hl.length - i ∧ 1 ≤ i ∧ i ≤ hl.length ∧
    st'.w "fp.i" = i ∧ st'.w "fp.bi" = b ∧ hl[b]? = some yb ∧ (∀ y ∈ hl.take i, d yb ≤ d y) ∧
    Unchanged st1 st' [] [] (["fp.bi", "fp.i", X.ra, X.rb] ++ X.ttWR) X.ttVR ∧
    st1.cost ≤ st'.cost ∧ st'.cost ≤ st1.cost + (X.Ctt + 6) * (i - 1)
  have hloop : Runs ops (Stmt.while (lt (var "fp.i") (var "fp.hsz")) (fpExtStep LI X)) st1
      (fun st' => ∃ b yb, st'.w "fp.bi" = b ∧ hl[b]? = some yb ∧ (∀ y ∈ hl, d yb ≤ d y) ∧
        Unchanged st1 st' [] [] (["fp.bi", "fp.i", X.ra, X.rb] ++ X.ttWR) X.ttVR ∧
        st1.cost ≤ st'.cost ∧ st'.cost ≤ st1.cost + (X.Ctt + 6) * (hl.length - 1) + 1) := by
    have hmin0 : ∀ y ∈ hl.take 1, d hl[0] ≤ d y := by
      intro y hy
      rw [List.take_one] at hy
      simp [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos1] at hy
      rw [hy]
    refine runs_while_nat I _ ?_ (hl.length - 1) st1 ⟨1, 0, hl[0], rfl, le_rfl, hpos1,
      by rw [← hst1]; simp, by rw [← hst1]; simp, List.getElem?_eq_getElem hpos1, hmin0,
      Unchanged.refl _ _ _ _ _, le_rfl, by simp⟩
    intro m st' ⟨i, b, yb, hm, hi1, hil, hi, hb', hyb, hmin, hu', hc0', hc'⟩
    have hsz' : st'.w "fp.hsz" = hl.length := by
      rw [hu'.wreg "fp.hsz" (by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨⟨by decide, by decide, fun h => hNX.ab_my X.ra (by simp) (h ▸ by simp [extRegs]),
          fun h => hNX.ab_my X.rb (by simp) (h ▸ by simp [extRegs])⟩,
          fun h => hNX.tt_my _ h (by simp [extRegs])⟩)]
      exact hsz1
    have hcap' : st'.cap = st.cap := by rw [hu'.cap, hcap1]
    refine ⟨if i < hl.length then 1 else 0, by simp [hi, hsz', fit]; split_ifs <;> omega,
      fun hne0 => ?_, fun h0 => ?_⟩
    · have hil' : i < hl.length := by by_contra h; simp [h] at hne0
      have hLT' : LI.LT (st'.charge 1) d g := LI.LT_frame hLT ((hu1.cat hu').cat
        (unch_charge' st' 1)) (Disj.nil_left _) (Disj.nil_left _) (by simp; omega)
      have harr' : LArr (st'.charge 1) "fp.H" hl := fun j hj => by
        have := (((hu1.cat hu').cat (unch_charge' st' 1)).warr "fp.H" (by simp)).1
        rw [this]; exact harr j hj
      have hHl' : hl.length ≤ (st'.charge 1).wlen "fp.H" := by
        have := (((hu1.cat hu').cat (unch_charge' st' 1)).warr "fp.H" (by simp)).2
        rw [this, ← hsz]; exact hsz ▸ (hsz ▸ (by rw [hsz]; omega))
      refine (extStep_spec hNX hLT' harr' hHl' hfin' (by simpa using hi) (by simpa using hb')
        hil' hyb hmin ?_ (by simp; omega)).mono ?_
      · simp only [State.charge_cost, State.charge_cap]
        have : (X.Ctt + 6) * (i - 1) ≤ (X.Ctt + 6) * (H.card - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have : (X.Ctt + 6) * (H.card - 1) + (X.Ctt + 6) ≤ (X.Ctt + 6) * H.card := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      rintro st'' ⟨b', yb', hyb', hmin', hi'', hb'', hu'', hc0'', hc''⟩
      refine ⟨hl.length - (i + 1), by omega, i + 1, b', yb', rfl, by omega, by omega, hi'', hb'',
        hyb', hmin', ?_, by simp at hc0''; omega, ?_⟩
      · exact (hu'.trans ((Unchanged.charge st' 1 _ _ _ _).trans hu''))
      · simp at hc''
        have : (X.Ctt + 6) * (i + 1 - 1) = (X.Ctt + 6) * (i - 1) + (X.Ctt + 6) := by
          rw [show i + 1 - 1 = (i - 1) + 1 by omega, Nat.mul_succ]
        omega
    · have hieq : i = hl.length := by by_contra h; simp [show i < hl.length by omega] at h0
      subst hieq
      refine ⟨b, yb, by simpa using hb', hyb, fun y hy => hmin y (by rw [List.take_length]; exact hy),
        hu'.trans (Unchanged.charge st' 1 _ _ _ _), by simp; omega, by simp; omega⟩
  refine runs_seq (hloop.mono ?_)
  rintro st2 ⟨b, yb, hb2, hyb, hmin, hu2, hc2a, hc2b⟩
  have hbl : b < hl.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hyb; exact absurd hyb (by simp)
  have hyb' : hl[b] = yb := by
    rw [List.getElem?_eq_getElem hbl] at hyb; exact Option.some.inj hyb
  have hu12 := hu1.cat hu2
  have hA : ∀ a, st2.wa a = st.wa a ∧ st2.wlen a = st.wlen a := fun a => hu12.warr a (by simp)
  have hwa2 : st2.wa = st.wa := funext fun a => (hA a).1
  have hwl2 : st2.wlen = st.wlen := funext fun a => (hA a).2
  have hsz2 : st2.w "fp.hsz" = hl.length := by
    rw [hu12.wreg "fp.hsz" (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nil_append]
      refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide,
        fun h => hNX.ab_my X.ra (by simp) (h ▸ by simp [extRegs]),
        fun h => hNX.ab_my X.rb (by simp) (h ▸ by simp [extRegs])⟩,
        fun h => hNX.tt_my _ h (by simp [extRegs])⟩)]
    exact hsz
  have hcap2 : st2.cap = st.cap := by rw [hu12.cap]
  have hlastE : hl.getLast hne' = hl[hl.length - 1] := getLast_eq_getElem' hl hne'
  have hHb : st.wa "fp.H" b = (yb : ℕ) := by rw [harr b hbl]; simp [hyb']
  have hHl : st.wa "fp.H" (hl.length - 1) = ((hl.getLast hne' : Fin G.n) : ℕ) := by
    rw [harr (hl.length - 1) (by omega), hlastE]; rfl
  have hbH : b < st.wlen "fp.H" := by omega
  have hlL : hl.length - 1 < st.wlen "fp.H" := by omega
  have hlastp : ((hl.getLast hne' : Fin G.n) : ℕ) < st.wlen "fp.hp" := by
    rw [hpL]; exact (hl.getLast hne').isLt
  have hybL : (yb : ℕ) < st.wlen "fp.inH" := by rw [hbL]; exact yb.isLt
  -- the deletion, statement by statement
  have hc0 : 0 < st2.cap := by rw [hcap2]; omega
  have hc1 : 1 < st2.cap := by rw [hcap2]; omega
  refine runs_seq (runs_wset (a := yb) (by
    simp only [evalW_load', evalW_var, hb2, Option.bind_some, hwl2, hbH, if_true, hwa2, hHb]) ?_)
  generalize hsA : (st2.setW "fp.u" (yb : ℕ)).charge 1 = sA
  have hsA_w : ∀ x, x ≠ "fp.u" → sA.w x = st2.w x := fun x hx => by rw [← hsA]; simp [hx]
  have hsA_u : sA.w "fp.u" = yb := by rw [← hsA]; simp
  have hsA_wa : sA.wa = st2.wa := by rw [← hsA]; rfl
  have hsA_wl : sA.wlen = st2.wlen := by rw [← hsA]; rfl
  have hsA_cap : sA.cap = st2.cap := by rw [← hsA]; rfl
  have hsA_c : sA.cost = st2.cost + 1 := by rw [← hsA]; simp
  have hszA : sA.w "fp.hsz" = hl.length := by rw [hsA_w _ (by decide)]; exact hsz2
  refine runs_seq (runs_wset (a := hl.length - 1) (by
    simp only [evalW_sub', evalW_var, evalW_lit', hszA, fit, hsA_cap, hc1, if_true,
      Option.bind_some]) ?_)
  generalize hsB : (sA.setW "fp.hsz" (hl.length - 1)).charge 1 = sB
  have hsB_w : ∀ x, x ≠ "fp.hsz" → sB.w x = sA.w x := fun x hx => by rw [← hsB]; simp [hx]
  have hsB_hsz : sB.w "fp.hsz" = hl.length - 1 := by rw [← hsB]; simp
  have hsB_wa : sB.wa = st2.wa := by rw [← hsB, ← hsA_wa]; rfl
  have hsB_wl : sB.wlen = st2.wlen := by rw [← hsB, ← hsA_wl]; rfl
  have hsB_cap : sB.cap = st2.cap := by rw [← hsB, ← hsA_cap]; rfl
  have hsB_c : sB.cost = st2.cost + 2 := by rw [← hsB]; simp [hsA_c]
  refine runs_seq (runs_wset (a := hl.getLast hne') (by
    simp only [evalW_load', evalW_var, hsB_hsz, Option.bind_some, hsB_wl, hwl2, hlL, if_true,
      hsB_wa, hwa2, hHl]) ?_)
  generalize hsC : (sB.setW "fp.t" ((hl.getLast hne' : Fin G.n) : ℕ)).charge 1 = sC
  have hsC_w : ∀ x, x ≠ "fp.t" → sC.w x = sB.w x := fun x hx => by rw [← hsC]; simp [hx]
  have hsC_t : sC.w "fp.t" = hl.getLast hne' := by rw [← hsC]; simp
  have hsC_wa : sC.wa = st2.wa := by rw [← hsC, ← hsB_wa]; rfl
  have hsC_wl : sC.wlen = st2.wlen := by rw [← hsC, ← hsB_wl]; rfl
  have hsC_cap : sC.cap = st2.cap := by rw [← hsC, ← hsB_cap]; rfl
  have hsC_c : sC.cost = st2.cost + 3 := by rw [← hsC]; simp [hsB_c]
  have hsC_bi : sC.w "fp.bi" = b := by
    rw [hsC_w _ (by decide), hsB_w _ (by decide), hsA_w _ (by decide)]; exact hb2
  have hsC_u : sC.w "fp.u" = yb := by rw [hsC_w _ (by decide), hsB_w _ (by decide)]; exact hsA_u
  refine runs_seq (runs_wstore (j := b) (a := hl.getLast hne') (by simp [hsC_bi])
    (by simp [hsC_t]) (by rw [hsC_wl, hwl2]; exact hbH) ?_)
  have hlp' : ((hl.getLast hne' : Fin G.n) : ℕ) <
      ((sC.storeW "fp.H" b ((hl.getLast hne' : Fin G.n) : ℕ)).charge 1).wlen "fp.hp" := by
    simp only [State.charge_wlen, State.storeW_wlen]; rw [hsC_wl, hwl2]; exact hlastp
  refine runs_seq (runs_wstore (j := hl.getLast hne') (a := b) (by simp [hsC_t])
    (by simp [hsC_bi]) hlp' ?_)
  have hyp' : (yb : ℕ) < ((((sC.storeW "fp.H" b ((hl.getLast hne' : Fin G.n) : ℕ)).charge 1).storeW
      "fp.hp" ((hl.getLast hne' : Fin G.n) : ℕ) b).charge 1).wlen "fp.inH" := by
    simp only [State.charge_wlen, State.storeW_wlen]; rw [hsC_wl, hwl2]; exact hybL
  refine runs_wstore (j := yb) (a := 0) (by simp [hsC_u]) (by simp [fit, hsC_cap, hc0]) hyp' ?_
  generalize hsD : ((((((sC.storeW "fp.H" b ((hl.getLast hne' : Fin G.n) : ℕ)).charge 1).storeW
    "fp.hp" ((hl.getLast hne' : Fin G.n) : ℕ) b).charge 1).storeW "fp.inH" (yb : ℕ) 0).charge 1) = sD
  have hsD_w : sD.w = sC.w := by rw [← hsD]; rfl
  have hsD_H : ∀ j, sD.wa "fp.H" j = if j = b then ((hl.getLast hne' : Fin G.n) : ℕ)
      else st.wa "fp.H" j := fun j => by
    rw [← hsD]; simp only [State.charge_wa, State.storeW_wa]; simp [hsC_wa, hwa2]
  have hsD_hp : ∀ x, sD.wa "fp.hp" x = if x = ((hl.getLast hne' : Fin G.n) : ℕ) then b
      else st.wa "fp.hp" x := fun x => by
    rw [← hsD]; simp only [State.charge_wa, State.storeW_wa]; simp [hsC_wa, hwa2]
  have hsD_inH : ∀ x, sD.wa "fp.inH" x = if x = (yb : ℕ) then 0 else st.wa "fp.inH" x :=
    fun x => by rw [← hsD]; simp only [State.charge_wa, State.storeW_wa]; simp [hsC_wa, hwa2]
  have hsD_oth : ∀ a, a ≠ "fp.H" → a ≠ "fp.hp" → a ≠ "fp.inH" → sD.wa a = st.wa a :=
    fun a h1 h2 h3 => by
      funext j; rw [← hsD]; simp only [State.charge_wa, State.storeW_wa]; simp [h1, h2, h3, hsC_wa, hwa2]
  have hsD_wl : sD.wlen = st.wlen := by
    rw [← hsD]; simp only [State.charge_wlen, State.storeW_wlen]; rw [hsC_wl, hwl2]
  have hsD_cap : sD.cap = st.cap := by
    rw [← hsD]; simp only [State.charge_cap, State.storeW_cap]; rw [hsC_cap, hcap2]
  have hsD_c : sD.cost = st2.cost + 6 := by rw [← hsD]; simp [hsC_c]
  have hsD_procs : sD.procs = st.procs := by
    rw [← hsD]; simp only [State.charge_procs, State.storeW_procs]
    rw [← hsC, ← hsB, ← hsA]; simp only [State.charge_procs, State.setW_procs]; exact hu12.procs
  have hybH : yb ∈ H := by
    rw [← hset]; exact List.mem_toFinset.mpr (hyb' ▸ List.getElem_mem hbl)
  have hnd' := swapDel_nodup hl b hne' hbl hnd
  have hL' := swapDel_length hl b hne'
  have hlast_ne : ∀ j (hj : j < hl.length - 1), hl[j] ≠ hl.getLast hne' := by
    intro j hj h
    rw [hlastE] at h
    have := (List.Nodup.getElem_inj_iff hnd).mp h
    omega
  have hsD_va : sD.va = st2.va := by rw [← hsD, ← hsC, ← hsB, ← hsA]; rfl
  have hsD_v : sD.v = st2.v := by rw [← hsD, ← hsC, ← hsB, ← hsA]; rfl
  have hsD_vl : sD.vlen = st2.vlen := by rw [← hsD, ← hsC, ← hsB, ← hsA]; rfl
  have hsD_hsz : sD.w "fp.hsz" = hl.length - 1 := by
    rw [hsD_w, hsC_w _ (by decide)]; exact hsB_hsz
  have hsD_u : sD.w "fp.u" = yb := by rw [hsD_w]; exact hsC_u
  have hsD_reg : ∀ x, x ≠ "fp.t" → x ≠ "fp.hsz" → x ≠ "fp.u" → sD.w x = st2.w x :=
    fun x h1 h2 h3 => by rw [hsD_w, hsC_w x h1, hsB_w x h2, hsA_w x h3]
  refine ⟨yb, hybH, fun y hy => hmin y (by rw [← hset] at hy; exact List.mem_toFinset.mp hy),
    hsD_u, ⟨swapDel hl b hne', hnd', ?_, by rw [hsD_hsz, hL'], by rw [hsD_wl]; exact hcapH,
      fun j hj => ?_, by rw [hsD_wl]; exact hpL, fun j hj => ?_,
      ⟨by rw [hsD_wl]; exact hbL, fun v => ?_⟩⟩, ?_, by omega, ?_⟩
  · rw [swapDel_toFinset hl b hne' hbl hnd, hset, hyb']
  · -- the array after the swap
    have hj' : j < (swapDel hl b hne').length := hj
    have hjl : j < hl.length - 1 := by omega
    simp only [List.get_eq_getElem]
    rw [swapDel_getElem hl b hne' j hj', hsD_H j]
    by_cases hjb : j = b
    · simp [hjb]
    · simp only [hjb, if_false]; exact harr j (by omega)
  · -- positions
    have hj' : j < (swapDel hl b hne').length := hj
    have hjl : j < hl.length - 1 := by omega
    simp only [List.get_eq_getElem]
    rw [swapDel_getElem hl b hne' j hj']
    by_cases hjb : j = b
    · simp only [hjb, if_true]; rw [hsD_hp]; simp
    · have hne2 : ((hl[j]'(by omega) : Fin G.n) : ℕ) ≠ ((hl.getLast hne' : Fin G.n) : ℕ) :=
        fun h => hlast_ne j hjl (Fin.ext h)
      have hp := hpos j (by omega)
      simp only [List.get_eq_getElem] at hp
      simp only [hjb, if_false]
      rw [hsD_hp, if_neg hne2]; exact hp
  · -- membership bitmap
    rw [hsD_inH]
    by_cases hv : v = yb
    · subst hv; simp
    · have : (v : ℕ) ≠ yb := fun h => hv (Fin.ext h)
      rw [if_neg this, hb v]; simp [hv]
  · -- write sets
    refine ⟨fun a ha => ?_, fun a _ => ?_, fun x hx => ?_, fun x _ => ?_, hsD_cap, hsD_procs⟩
    · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
      exact ⟨hsD_oth a ha.1 ha.2.1 ha.2.2, by rw [hsD_wl]⟩
    · rw [hsD_va, hsD_vl]; exact hu12.varr a (by simp)
    · have hx' : x ∉ extRegs := fun h => hx (List.mem_append_left _ (List.mem_append_left _ h))
      simp only [extRegs, List.mem_cons, not_or, List.not_mem_nil, or_false] at hx'
      rw [hsD_reg x hx'.2.2.1 hx'.2.2.2.2 hx'.2.2.2.1]
      exact hu12.wreg x (by
        intro h
        simp only [List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at h
        apply hx
        simp only [List.mem_append, List.mem_cons, extRegs, List.not_mem_nil, or_false]
        tauto)
    · rw [hsD_v]; exact hu12.vreg x (by simp_all)
  · have : (X.Ctt + 6) * (hl.length - 1) + (X.Ctt + 6) ≤ (X.Ctt + 6) * H.card := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    omega

end Frontier.CHD.BL2
