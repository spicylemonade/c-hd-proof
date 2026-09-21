import Frontier.CHD.L6.Sizes
import Frontier.CHD.Dispatch

/-!
# L6 composition (agent-10, scratch): the whole preprocessing from the body's initial state
-/

open scoped NNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt Finset

namespace L6In

/-- The input model of a graph and source (as read from the RAM input arrays). -/
noncomputable def ofGraph (G : Graph) (s : Fin G.n) : L6In where
  n := G.n
  m := G.m
  s := s
  src e := if h : e < G.m then (G.src ⟨e, h⟩ : ℕ) else 0
  dst e := if h : e < G.m then (G.dst ⟨e, h⟩ : ℕ) else 0
  wt e := if h : e < G.m then G.w ⟨e, h⟩ else 0

variable (G : Graph) (s : Fin G.n)

@[simp] theorem ofGraph_n : (ofGraph G s).n = G.n := rfl
@[simp] theorem ofGraph_m : (ofGraph G s).m = G.m := rfl
@[simp] theorem ofGraph_s : (ofGraph G s).s = s := rfl

theorem ofGraph_src (e : Fin G.m) : (ofGraph G s).src e = G.src e := by simp [ofGraph]
theorem ofGraph_dst (e : Fin G.m) : (ofGraph G s).dst e = G.dst e := by simp [ofGraph]
theorem ofGraph_wt (e : Fin G.m) : (ofGraph G s).wt e = G.w e := by simp [ofGraph]

theorem ofGraph_src_lt {e : ℕ} (he : e < G.m) : (ofGraph G s).src e < G.n := by
  simp [ofGraph, he]

theorem ofGraph_dst_lt {e : ℕ} (he : e < G.m) : (ofGraph G s).dst e < G.n := by
  simp [ofGraph, he]

end L6In

/-- Facts about the body's initial state used by L6. -/
structure InitFacts (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop where
  n : st.w "n" = G.n
  m : st.w "m" = G.m
  sreg : st.w "s" = s
  src : ∀ e < G.m, st.wa "src" e = (L6In.ofGraph G s).src e
  srcL : G.m ≤ st.wlen "src"
  dst : ∀ e < G.m, st.wa "dst" e = (L6In.ofGraph G s).dst e
  dstL : G.m ≤ st.wlen "dst"
  w : ∀ e < G.m, st.va "w" e = (L6In.ofGraph G s).wt e
  wL : G.m ≤ st.vlen "w"
  cap : (G.n + G.m + 2) ^ 4 ≤ st.cap

theorem initFacts_of_initLike {e : ℕ} (he : 3 ≤ e) {ps : List Stmt} {G : Graph} {s : Fin G.n}
    {st : State ℝ≥0} (h : Dispatch.InitLike e ps G s st) : InitFacts G s st := by
  obtain ⟨hw, -, hwa, hva, hwl, hvl, hcap, -, -⟩ := h
  have hi : ∀ x, x ∉ Dispatch.scratch → st.w x = (Dispatch.init0 e ps G s).w x := hw
  refine ⟨?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [hi _ (by simp [Dispatch.scratch])]; simp [Dispatch.init0, initState]
  · rw [hi _ (by simp [Dispatch.scratch])]; simp [Dispatch.init0, initState]
  · rw [hi _ (by simp [Dispatch.scratch])]; simp [Dispatch.init0, initState]
  · rw [hwa]; simp [Dispatch.init0, initState, L6In.ofGraph, hj]
  · rw [hwl]; simp [Dispatch.init0, initState]
  · rw [hwa]; simp [Dispatch.init0, initState, L6In.ofGraph, hj]
  · rw [hwl]; simp [Dispatch.init0, initState]
  · rw [hva]; simp [Dispatch.init0, initState, L6In.ofGraph, hj]
  · rw [hvl]; simp [Dispatch.init0, initState]
  · rw [hcap]; simp only [Dispatch.init0, initState]
    exact Nat.pow_le_pow_right (by omega) (by omega)

def L6WA : List String :=
  ["gKeep", "g_cnt", "g_pos", "g_ord", "g_mark", "g_best", "g_deg", "g_off", "g_sl", "g_kept",
   "gRep", "gOwn", "gSt", "gHd", "gSrc", "gNxt", "gHead", "ms_H"]
def L6VA : List String := ["gW", "ms_W"]
def L6WR : List String :=
  keepWR ++ paramWR ++ csortWR ++ passAWR ++ ["gN", "gM"] ++ bWR ++ ["gS"] ++ sortWR

theorem delta_ge (I : L6In) : 3 ≤ I.δ := by simp [L6In.δ, deltaF]

/-- `BPost` restarted at its own state (for the sort pass), after `g_x := 0`. -/
theorem BPost.restart {I : L6In} {st t0 : State ℝ≥0} (h : BPost I st t0) :
    BPost I ((t0.setW "g_x" 0).charge 1) ((t0.setW "g_x" 0).charge 1) where
  E := h.E.of_frame (wa := []) (va := []) (wr := ["g_x"]) (vr := []) (by simp) (by simp) (by simp)
    (by simp)
  F v hv hk := (h.F v hv hk).of_frame (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hk
    (delta_ge I)
  stN := by simpa using h.stN
  gS := by simpa using h.gS
  lSt := by simpa using h.lSt
  lHd := by simpa using h.lHd
  lNxt := by simpa using h.lNxt
  lSrc := by simpa using h.lSrc
  lHead := by simpa using h.lHead
  lW := by simpa using h.lW
  lRep := by simpa using h.lRep
  lOwn := by simpa using h.lOwn
  U := by simp
  c := by omega

/-- **The whole L6 preprocessing** from a body state with the input graph. -/
theorem l6_runs (G : Graph) (s : Fin G.n) (st : State ℝ≥0) (hI : InitFacts G s st) :
    Runs realOps (l6Prog (MergeSort.sortRange "gW" "gHead")) st (fun r =>
      ∃ t0 t, BPost (L6In.ofGraph G s) t0 t0 ∧
        SPInv (L6In.ofGraph G s) t0 ((L6In.ofGraph G s).off G.n) t ∧ r = t.charge 1 ∧
        Unchanged st r L6WA L6VA L6WR [] ∧
        r.w "cn" = min G.n (G.m + 1) ∧ r.w "cm" = G.m ∧
        r.cost ≤ st.cost + 60 * (G.n + G.m) +
          80 * ((L6In.ofGraph G s).off G.n + (L6In.ofGraph G s).sl G.n) *
            (Nat.log 2 (L6In.ofGraph G s).δ + 1) + 100) := by
  set I := L6In.ofGraph G s with hIdef
  have hδ : 3 ≤ I.δ := delta_ge I
  have hn1 : 1 ≤ G.n := by have := s.2; omega
  have hcap0 : (G.n + G.m + 2) ^ 4 ≤ st.cap := hI.cap
  have hsq : (G.n + G.m + 2) * (G.n + G.m + 2) ≤ (G.n + G.m + 2) ^ 4 := by
    have : (G.n + G.m + 2) ^ 2 ≤ (G.n + G.m + 2) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have hsq2 : (G.n + 1) * (G.m + 1) + G.n + G.m + 4 < (G.n + G.m + 2) * (G.n + G.m + 2) := by
    nlinarith
  have hcapA : (G.n + 1) * (G.m + 1) + G.n + G.m + 4 < st.cap := by omega
  have hk3 : 27 ≤ (G.n + G.m + 2) ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (G.n + G.m + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hk4 : (G.n + G.m + 2) ^ 4 = (G.n + G.m + 2) * (G.n + G.m + 2) ^ 3 := by ring
  have hcapB : 8 * (G.n + G.m) + 16 < st.cap := by nlinarith
  have hsrcb : ∀ e < G.m, I.src e < G.n := fun e he => L6In.ofGraph_src_lt G s he
  have hdstb : ∀ e < G.m, I.dst e < G.n := fun e he => L6In.ofGraph_dst_lt G s he
  unfold l6Prog
  -- (0) keep
  refine runs_seq ((keepProg_runs st G.n G.m s I.src I.dst hI.n hI.m hI.sreg s.2 hI.src hI.srcL
    hI.dst hI.dstL hdstb (by omega)).mono ?_)
  rintro s1 ⟨hK1, hU1, hc1⟩
  -- (1) params
  refine runs_seq ((paramProg_runs s1 G.n G.m (by rw [hU1.wreg _ (by simp [keepWR])]; exact hI.n)
    (by rw [hU1.wreg _ (by simp [keepWR])]; exact hI.m) hn1 (by rw [hU1.cap]; omega)).mono ?_)
  rintro s2 ⟨hD2, hcn2, hcm2, hU2, hc2⟩
  -- (2) counting sort
  have hU12 : Unchanged st s2 L6WA L6VA L6WR [] :=
    (hU1.mono (by simp [L6WA]) (by simp) (by simp [L6WR, keepWR]) (by simp)).trans
      (hU2.mono (by simp) (by simp) (by simp [L6WR, paramWR]) (by simp))
  refine runs_seq ((csort_runs s2 G.n G.m I.src (by rw [hU12.wreg _ (by simp [L6WR, keepWR, paramWR,
      csortWR, passAWR, bWR, sortWR, MergeSort.msRegs])]; exact hI.n)
    (by rw [hU12.wreg _ (by simp [L6WR, keepWR, paramWR, csortWR, passAWR, bWR, sortWR,
      MergeSort.msRegs])]; exact hI.m)
    (fun e he => by rw [(hU12.warr _ (by simp [L6WA])).1]; exact hI.src e he)
    (by rw [(hU12.warr _ (by simp [L6WA])).2]; exact hI.srcL) hsrcb
    (by rw [hU12.cap]; exact hcapA)).mono ?_)
  rintro s3 ⟨hcnt3, hord3, hordL3, hU3, hc3⟩
  have hU13 : Unchanged st s3 L6WA L6VA L6WR [] :=
    hU12.trans (hU3.mono (by simp [csortWA, L6WA]) (by simp) (by simp [L6WR, csortWR]) (by simp))
  have hregs : ∀ x ∈ ["n", "m", "s"], x ∉ L6WR := by
    simp [L6WR, keepWR, paramWR, csortWR, passAWR, bWR, sortWR, MergeSort.msRegs]
  -- environment for pass A
  have hE3 : AEnv I s3 := {
    n := by rw [hU13.wreg _ (hregs "n" (by simp))]; exact hI.n
    m := by rw [hU13.wreg _ (hregs "m" (by simp))]; exact hI.m
    gD := by rw [(hU3.wreg _ (by simp [csortWR]))]; exact hD2
    src := fun e he => by rw [(hU13.warr _ (by simp [L6WA])).1]; exact hI.src e he
    srcL := by rw [(hU13.warr _ (by simp [L6WA])).2]; exact hI.srcL
    dst := fun e he => by rw [(hU13.warr _ (by simp [L6WA])).1]; exact hI.dst e he
    dstL := by rw [(hU13.warr _ (by simp [L6WA])).2]; exact hI.dstL
    w := fun e he => by rw [(hU13.varr _ (by simp [L6VA])).1]; exact hI.w e he
    wL := by rw [(hU13.varr _ (by simp [L6VA])).2]; exact hI.wL
    hsrc := hsrcb
    hdst := hdstb
    keep := (hK1.of_unchanged hU2 (by simp)).of_unchanged hU3 (by simp [csortWA])
    cnt := hcnt3
    ord := hord3
    ordL := hordL3 }
  -- (3) pass A
  refine runs_seq ((passAProg_runs I s3 hE3 hδ
    (by rw [hU13.cap]; show 4 * (G.n + G.m) + 8 < st.cap; omega)).mono ?_)
  intro s4 hA
  have hU14 : Unchanged st s4 L6WA L6VA L6WR [] :=
    hU13.trans (hA.U.mono (by simp [passAWA, L6WA]) (by simp) (by
      intro x hx; simp only [L6WR, List.mem_append]; simp at hx ⊢; tauto) (by simp))
  have hB4 : BEnv I s4 := ⟨hA.E, hA.off, hA.sl, hA.deg, hA.kept, hA.kL, hA.gN, hA.gM⟩
  -- (4) pass B
  refine runs_seq ((passBProg_runs I s4 hB4 hδ (show (s : ℕ) < G.n from s.2)
    (by rw [hU14.wreg _ (hregs "s" (by simp))]; exact hI.sreg)
    (by rw [hU14.cap]; show 8 * (G.n + G.m) + 16 < st.cap; omega)).mono ?_)
  intro s5 hBp
  have hU15 : Unchanged st s5 L6WA L6VA L6WR [] :=
    hU14.trans (hBp.U.mono (by simp [bkWA, L6WA]) (by simp [L6VA]) (by
      intro x hx; simp only [L6WR, List.mem_append]; simp at hx ⊢; tauto) (by simp))
  -- (5) sort pass
  unfold sortPass
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hU15.cap]; omega)) ?_)
  have hR := BPost.restart hBp
  refine (sortLoop_runs I _ hR hδ (by simp [hU15.cap]; show 8 * (G.n + G.m) + 16 < st.cap; omega)
    (by simp)).mono ?_
  rintro r ⟨t, hS, rfl⟩
  have hregc : ∀ x ∈ ["cn", "cm"], (t.charge 1).w x = s2.w x := by
    intro x hx
    have h3 : s3.w x = s2.w x := hU3.wreg x (by simp at hx; rcases hx with rfl | rfl <;> simp [csortWR])
    have h4 : s4.w x = s3.w x := hA.U.wreg x (by
      simp at hx; rcases hx with rfl | rfl <;> simp [passAWR])
    have h5 : s5.w x = s4.w x := hBp.U.wreg x (by
      simp at hx; rcases hx with rfl | rfl <;> simp [bWR])
    have h6 : t.w x = ((s5.setW "g_x" 0).charge 1).w x := hS.U.wreg x (by
      simp at hx; rcases hx with rfl | rfl <;> simp [sortWR, MergeSort.msRegs])
    have hxg : x ≠ "g_x" := by simp at hx; rcases hx with rfl | rfl <;> decide
    simp [h6, hxg, h5, h4, h3]
  refine ⟨_, t, hR, hS, rfl, ?_, by rw [hregc "cn" (by simp)]; exact hcn2,
    by rw [hregc "cm" (by simp)]; exact hcm2, ?_⟩
  · have h1 : Unchanged s5 ((s5.setW "g_x" 0).charge 1) L6WA L6VA L6WR [] := by
      simp [L6WR, sortWR]
    have h2 := hS.U.mono (show ["gHead", "ms_H"] ⊆ L6WA by simp [L6WA])
      (show ["gW", "ms_W"] ⊆ L6VA by simp [L6VA])
      (show sortWR ⊆ L6WR by intro x hx; simp only [L6WR, List.mem_append]; exact Or.inr hx)
      (List.Subset.refl _)
    simpa using hU15.trans (h1.trans h2)
  · -- cost
    have hc4 := hA.c
    have hc5 := hBp.c
    have hc6 := hS.c
    have hNn := I.off_n_le_cn hδ s.2
    have hMm := I.sl_n_le hδ
    have hstN : ((s5.setW "g_x" 0).charge 1).wa "gSt" (I.off I.n) = I.sl I.n := hR.stN
    rw [hstN] at hc6
    simp only [State.charge_cost, State.setW_cost] at hc6 ⊢
    have hlog : 40 * (I.sl I.n + I.off I.n) * (Nat.log 2 I.δ + 1) ≤
        80 * (I.off I.n + I.sl I.n) * (Nat.log 2 I.δ + 1) := by
      have : 40 * (I.sl I.n + I.off I.n) ≤ 80 * (I.off I.n + I.sl I.n) := by omega
      exact Nat.mul_le_mul_right _ this
    have hN2 : I.off I.n ≤ I.off I.n * (Nat.log 2 I.δ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hM2 : I.sl I.n ≤ I.sl I.n * (Nat.log 2 I.δ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hsplit : 80 * (I.off I.n + I.sl I.n) * (Nat.log 2 I.δ + 1) =
        40 * (I.sl I.n + I.off I.n) * (Nat.log 2 I.δ + 1) +
        40 * (I.off I.n * (Nat.log 2 I.δ + 1) + I.sl I.n * (Nat.log 2 I.δ + 1)) := by ring
    simp only [I, L6In.ofGraph_n, L6In.ofGraph_m] at *
    omega

end Frontier.CHD.L6
