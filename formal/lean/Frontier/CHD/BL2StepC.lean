import Frontier.CHD.BL2StepB

/-!
# Frontier.CHD.BL2StepC — B-L2: the label-layer part of one scan iteration (agent-09, scratch, NON-GATE)

CPS lemmas: the prefix `fp.v := gHead[p]; ru := u; re := p; candB` and the middle part
`rv := v; cmpTS`, each handing a precisely described state to the continuation.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {c : FPCtx G s} {T : Finset (Fin G.n)} {slB slX : String}
  {u : Fin G.n}

theorem Disj.cons_left {x : String} {l₁ l₂ : List String} (hx : x ∉ l₂) (h : Disj l₁ l₂) :
    Disj (x :: l₁) l₂ := by
  intro y hy; rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact h y hy

theorem Disj.append_left {l₁ l₁' l₂ : List String} (h : Disj l₁ l₂) (h' : Disj l₁' l₂) :
    Disj (l₁ ++ l₁') l₂ := by
  intro y hy; rcases List.mem_append.mp hy with hy | hy
  · exact h y hy
  · exact h' y hy

theorem footRegs_sub : footRegs ⊆ myRegs := by
  intro x hx; simp [footRegs] at hx; simp [myRegs]; tauto

/-- The prefix of an iteration: read the head, set the interface registers, form the
candidate and test it against `B` (FH.8). -/
theorem scan_prefix (hN : Names LI slB slX) {σ : SSt G s} {Lrem : List (Fin G.m)} {g : LI.Gh}
    {st : State V} (hC : Core LI c T slB slX u σ Lrem g st) (hfin : σ.d u ≠ ⊤) {e : Fin G.m}
    (hp : st.w "fp.p" = e) (hsrc : G.src e = u) (hroom : st.cost + 4 + LI.Ccand ≤ LI.c0 + st.cap)
    {X : Stmt} {Q : State V → Prop}
    (hX : ∀ st5 : State V, Core LI c T slB slX u σ Lrem g st5 → LI.LC st5 σ.d g e →
      st5.w LI.bit = (if ext (σ.d u) e < c.B then 1 else 0) → st5.w "fp.v" = G.dst e →
      Unchanged st st5 [] [] (["fp.v", LI.ru, LI.re] ++ LI.candWR) LI.candVR →
      st.cost + 4 ≤ st5.cost → st5.cost ≤ st.cost + 4 + LI.Ccand → Runs ops X st5 Q) :
    Runs ops (seq (wset "fp.v" (load "gHead" (var "fp.p")))
      (seq (wset LI.ru (var "fp.u")) (seq (wset LI.re (var "fp.p")) (seq (LI.candB slB) X))))
      (st.charge 1) Q := by
  have heL : (e : ℕ) < st.wlen "gHead" := lt_of_lt_of_le e.isLt hC.my.headL
  have hhead : st.wa "gHead" e = G.dst e := hC.my.head e
  -- the three register writes
  set st2 := ((st.charge 1).setW "fp.v" (G.dst e)).charge 1 with hst2
  set st3 := (st2.setW LI.ru u).charge 1 with hst3
  set st4 := (st3.setW LI.re e).charge 1 with hst4
  have hru_v : LI.ru ≠ "fp.v" := fun h => hN.ifc_my LI.ru (by simp) (h ▸ by simp [myRegs])
  have hre_v : LI.re ≠ "fp.v" := fun h => hN.ifc_my LI.re (by simp) (h ▸ by simp [myRegs])
  have hre_ru_u : st3.w "fp.u" = u := by
    have : ("fp.u" : String) ≠ LI.ru := fun h => hN.ifc_my LI.ru (by simp) (h ▸ by simp [myRegs])
    simp [hst3, hst2, this, hC.ureg]
  have hre_p : st3.w "fp.p" = e := by
    have : ("fp.p" : String) ≠ LI.ru := fun h => hN.ifc_my LI.ru (by simp) (h ▸ by simp [myRegs])
    simp [hst3, hst2, this, hp]
  have hu4 : Unchanged st st4 [] [] ["fp.v", LI.ru, LI.re] [] := by
    have h1 := Unchanged.trans' (Unchanged.trans' (unch_charge' st 1) (unch_setW _ "fp.v" (G.dst e)))
      (unch_charge' _ 1)
    have h2 := Unchanged.trans' (Unchanged.trans' h1 (unch_setW st2 LI.ru u)) (unch_charge' _ 1)
    have h3 := Unchanged.trans' (Unchanged.trans' h2 (unch_setW st3 LI.re e)) (unch_charge' _ 1)
    exact h3.mono (by simp) (by simp) (by intro x; simp <;> tauto) (by simp)
  have hc4 : st4.cost = st.cost + 4 := by simp [hst4, hst3, hst2]
  have hdisj4 : Disj ["fp.v", LI.ru, LI.re] footRegs := by
    refine Disj.cons_left (by simp [footRegs]) ?_
    exact (hN.ifc_my.mono_left (by intro x; simp; tauto)).mono_right footRegs_sub
  have hC4 : Core LI c T slB slX u σ Lrem g st4 :=
    hC.frame_regs hu4 hdisj4
      (Disj.cons_left (hN.myR_slB "fp.v" (by simp [myRegs])) (hN.ifc_slB.mono_left (by
        intro x; simp; tauto)))
      (Disj.nil_left _)
      (Disj.cons_left (hN.myR_slX "fp.v" (by simp [myRegs])) (hN.ifc_slX.mono_left (by
        intro x; simp; tauto)))
      (Disj.nil_left _) (by omega)
  have hv4 : st4.w "fp.v" = G.dst e := by
    have h1 : ("fp.v" : String) ≠ LI.re := fun h => hre_v h.symm
    have h2 : ("fp.v" : String) ≠ LI.ru := fun h => hru_v h.symm
    simp [hst4, hst3, hst2, h1, h2]
  have hru4 : st4.w LI.ru = G.src e := by
    simp [hst4, hst3, hN.ru_re, hsrc]
  have hre4 : st4.w LI.re = e := by simp [hst4]
  have hcap4 : st4.cap = st.cap := by simp [hst4, hst3, hst2]
  -- the candidate fragment
  have hspec := LI.candB_spec (st := st4) (sl := slB) (e := e) hC4.lab.lab hC4.lab.sB
    (by rw [hsrc]; exact hfin) hru4 hre4 (by rw [hc4, hcap4]; omega)
  -- run the program: three register writes, then candB, then X
  refine runs_seq (runs_wset (a := G.dst e) ?_ ?_)
  · simp [evalW_load', hp, heL, hhead]
  refine runs_seq (runs_wset (a := u) (by simp [hC.ureg, show ("fp.u" : String) ≠ "fp.v" by decide]) ?_)
  refine runs_seq (runs_wset (a := e) ?_ ?_)
  · have h1 : ("fp.p" : String) ≠ LI.ru := fun h => hN.ifc_my LI.ru (by simp) (h ▸ by simp [myRegs])
    simp [h1, hp, show ("fp.p" : String) ≠ "fp.v" by decide]
  refine runs_seq (hspec.mono ?_)
  rintro st5 ⟨hLC, hbit, hu5, hc5a, hc5b⟩
  have hu45 : Unchanged st st5 [] [] (["fp.v", LI.ru, LI.re] ++ LI.candWR) LI.candVR :=
    (Unchanged.trans' hu4 hu5).mono (by simp) (by simp) (by simp) (by simp)
  have hcand_foot : Disj LI.candWR footRegs := hN.cand_my.mono_right footRegs_sub
  have hC5 : Core LI c T slB slX u σ Lrem g st5 :=
    hC4.frame_regs hu5 hcand_foot hN.cand_slB hN.candV_slB hN.cand_slX hN.candV_slX hc5a
  have hv5 : st5.w "fp.v" = G.dst e := by
    rw [hu5.wreg "fp.v" (fun h => hN.cand_my _ h (by simp [myRegs]))]; exact hv4
  refine hX st5 hC5 hLC ?_ hv5 hu45 (by omega) (by omega)
  rw [hbit, hsrc]

/-- The middle of an iteration: `rv := v; cmpTS L_X` (FH.9's test `d[v] < L_X`). -/
theorem scan_mid (hN : Names LI slB slX) {σ : SSt G s} {Lrem : List (Fin G.m)} {g : LI.Gh}
    {st : State V} {e : Fin G.m} (hC : Core LI c T slB slX u σ Lrem g st) (hLC : LI.LC st σ.d g e)
    (hv : st.w "fp.v" = G.dst e) (hroom : st.cost + 2 + LI.Ccmp ≤ LI.c0 + st.cap)
    {Y : Stmt} {Q : State V → Prop}
    (hY : ∀ st7 : State V, Core LI c T slB slX u σ Lrem g st7 → LI.LC st7 σ.d g e →
      st7.w LI.bit = (if σ.d (G.dst e) < c.Lx then 1 else 0) → st7.w "fp.v" = G.dst e →
      st7.w LI.rv = G.dst e →
      Unchanged st st7 [] [] (LI.rv :: LI.cmpWR) LI.cmpVR →
      st.cost + 2 ≤ st7.cost → st7.cost ≤ st.cost + 2 + LI.Ccmp → Runs ops Y st7 Q) :
    Runs ops (seq (wset LI.rv (var "fp.v")) (seq (LI.cmpTS slX) Y)) (st.charge 1) Q := by
  set st6 := ((st.charge 1).setW LI.rv (G.dst e)).charge 1 with hst6
  have hu6 : Unchanged st st6 [] [] [LI.rv] [] :=
    (Unchanged.trans' (Unchanged.trans' (unch_charge' st 1) (unch_setW _ LI.rv (G.dst e)))
      (unch_charge' _ 1)).mono (by simp) (by simp) (by simp) (by simp)
  have hrv_foot : LI.rv ∉ footRegs := fun h => hN.ifc_my LI.rv (by simp) (footRegs_sub h)
  have hC6 : Core LI c T slB slX u σ Lrem g st6 :=
    hC.frame_regs hu6 (Disj.singleton hrv_foot) (Disj.singleton (hN.ifc_slB LI.rv (by simp)))
      (Disj.nil_left _) (Disj.singleton (hN.ifc_slX LI.rv (by simp))) (Disj.nil_left _)
      (by simp [hst6]; omega)
  have hLC6 : LI.LC st6 σ.d g e :=
    LI.LC_frame hLC hu6 (Disj.nil_left _) (Disj.nil_left _) (Disj.singleton LI.rv_cWR)
      (Disj.nil_left _) (by simp [hst6]; omega)
  have hv6 : st6.w "fp.v" = G.dst e := by
    have : ("fp.v" : String) ≠ LI.rv := fun h => hN.ifc_my LI.rv (by simp) (h ▸ by simp [myRegs])
    simp [hst6, this, hv]
  have hrv6 : st6.w LI.rv = G.dst e := by simp [hst6]
  have hc6 : st6.cost = st.cost + 2 := by simp [hst6]
  have hcap6 : st6.cap = st.cap := by simp [hst6]
  have hspec := LI.cmpTS_spec (st := st6) (sl := slX) (v := G.dst e) hC6.lab.lab hC6.lab.sX hrv6
    (by rw [hc6, hcap6]; omega)
  refine runs_seq (runs_wset (a := G.dst e) (by simp [hv]) ?_)
  refine runs_seq (hspec.mono ?_)
  rintro st7 ⟨hbit, hu7, hc7a, hc7b⟩
  have hcmp_foot : Disj LI.cmpWR footRegs := hN.cmp_my.mono_right footRegs_sub
  have hC7 := hC6.frame_regs hu7 hcmp_foot hN.cmp_slB hN.cmpV_slB hN.cmp_slX hN.cmpV_slX hc7a
  have hLC7 : LI.LC st7 σ.d g e :=
    LI.LC_frame hLC6 hu7 (Disj.nil_left _) (Disj.nil_left _) LI.cmp_cWR LI.cmp_cVR hc7a
  have hv7 : st7.w "fp.v" = G.dst e := by
    rw [hu7.wreg "fp.v" (fun h => hN.cmp_my _ h (by simp [myRegs]))]; exact hv6
  have hrv7 : st7.w LI.rv = G.dst e := by rw [hu7.wreg LI.rv hN.rv_cmp]; exact hrv6
  refine hY st7 hC7 hLC7 hbit hv7 hrv7 ?_ (by omega) (by omega)
  exact (Unchanged.trans' hu6 hu7).mono (by simp) (by simp) (by simp) (by simp)

end Frontier.CHD.BL2
