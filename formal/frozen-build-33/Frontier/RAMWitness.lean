import Frontier.RAMLogic

/-!
# Frontier.RAMWitness — non-vacuity of the runtime-gate model

Owner: agent-08.  A concrete `RAM.Program` (textbook Bellman–Ford: `n` rounds relaxing every edge
in index order) with kernel-checked proofs that

* `bfProgram_exact : bfProgram.Exact` — it terminates without getting stuck on EVERY graph
  (parallel edges, self loops, zero-weight cycles, unreachable vertices) and outputs exactly
  `Graph.dist`, and
* `bfProgram_runsWithin : bfProgram.RunsWithin G s (9 * ((n + 1) * (m + 1)))`.

This closes audit finding F-v2-2: `Program.Exact` is satisfiable, so the gate propositions of
`Frontier.CostModel` are not vacuously unprovable, and the output decoding / stuck conditions
are exercised by a real proof.  It is NOT a new result (Bellman–Ford, `O(nm)`).
-/

open scoped ENNReal NNReal

namespace Frontier.RAM.BF

open Frontier Graph


open Frontier Graph

variable (G : Graph)

/-- Relax edge `e` (in place). -/
noncomputable def relaxE (L : Fin G.n → ℝ≥0∞) (e : Fin G.m) : Fin G.n → ℝ≥0∞ :=
  Function.update L (G.dst e) (min (L (G.dst e)) (L (G.src e) + G.w e))

/-- Relax edges `0, …, j-1` in order. -/
noncomputable def passN (L : Fin G.n → ℝ≥0∞) : ℕ → Fin G.n → ℝ≥0∞
  | 0 => L
  | j + 1 => if h : j < G.m then relaxE G (passN L j) ⟨j, h⟩ else passN L j

/-- One full pass over all edges. -/
noncomputable def pass (L : Fin G.n → ℝ≥0∞) : Fin G.n → ℝ≥0∞ := passN G L G.m

/-- Initial labels. -/
noncomputable def L0 (s : Fin G.n) : Fin G.n → ℝ≥0∞ := fun v => if v = s then 0 else ⊤

/-- `i` full passes. -/
noncomputable def rounds (s : Fin G.n) : ℕ → Fin G.n → ℝ≥0∞
  | 0 => L0 G s
  | i + 1 => pass G (rounds s i)

variable {G}

theorem relaxE_le (L : Fin G.n → ℝ≥0∞) (e : Fin G.m) (v : Fin G.n) : relaxE G L e v ≤ L v := by
  unfold relaxE
  by_cases h : v = G.dst e
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem relaxE_dst_le (L : Fin G.n → ℝ≥0∞) (e : Fin G.m) :
    relaxE G L e (G.dst e) ≤ L (G.src e) + G.w e := by
  unfold relaxE; simp

theorem passN_succ_le (L : Fin G.n → ℝ≥0∞) (j : ℕ) (v : Fin G.n) :
    passN G L (j + 1) v ≤ passN G L j v := by
  simp only [passN]
  split_ifs with h
  · exact relaxE_le _ _ _
  · exact le_rfl

theorem passN_mono (L : Fin G.n → ℝ≥0∞) {i j : ℕ} (hij : i ≤ j) (v : Fin G.n) :
    passN G L j v ≤ passN G L i v := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact (passN_succ_le L _ v).trans ih

theorem passN_le (L : Fin G.n → ℝ≥0∞) (j : ℕ) (v : Fin G.n) : passN G L j v ≤ L v :=
  passN_mono L (Nat.zero_le j) v

theorem pass_le (L : Fin G.n → ℝ≥0∞) (v : Fin G.n) : pass G L v ≤ L v := passN_le L _ v

/-- After a pass, every edge is (Gauss–Seidel) relaxed with respect to the old labels. -/
theorem pass_edge (L : Fin G.n → ℝ≥0∞) (e : Fin G.m) :
    pass G L (G.dst e) ≤ L (G.src e) + G.w e := by
  have h1 : passN G L ((e : ℕ) + 1) (G.dst e) ≤ L (G.src e) + G.w e := by
    simp only [passN, e.isLt, dite_true]
    calc relaxE G (passN G L e) ⟨e, e.isLt⟩ (G.dst e)
        ≤ passN G L e (G.src e) + G.w e := relaxE_dst_le _ _
      _ ≤ L (G.src e) + G.w e := add_le_add (passN_le L _ _) le_rfl
  exact (passN_mono L (Nat.succ_le_of_lt e.isLt) _).trans h1

theorem rounds_succ_le (s : Fin G.n) (i : ℕ) (v : Fin G.n) :
    rounds G s (i + 1) v ≤ rounds G s i v := pass_le _ _

theorem rounds_source (s : Fin G.n) (i : ℕ) : rounds G s i s = 0 := by
  induction i with
  | zero => simp [rounds, L0]
  | succ i ih => exact le_antisymm ((rounds_succ_le s i s).trans ih.le) zero_le

/-- Soundness: labels never go below the true distance. -/
theorem relaxE_sound {s : Fin G.n} {L : Fin G.n → ℝ≥0∞} (hL : ∀ v, G.dist s v ≤ L v)
    (e : Fin G.m) (v : Fin G.n) : G.dist s v ≤ relaxE G L e v := by
  unfold relaxE
  by_cases h : v = G.dst e
  · subst h
    simp only [Function.update_self]
    exact le_min (hL _) ((dist_edge s e).trans (add_le_add (hL _) le_rfl))
  · simp [Function.update_of_ne h, hL v]

theorem passN_sound {s : Fin G.n} {L : Fin G.n → ℝ≥0∞} (hL : ∀ v, G.dist s v ≤ L v)
    (j : ℕ) (v : Fin G.n) : G.dist s v ≤ passN G L j v := by
  induction j generalizing v with
  | zero => exact hL v
  | succ j ih =>
    simp only [passN]
    split_ifs with h
    · exact relaxE_sound ih _ _
    · exact ih v

theorem rounds_sound (s : Fin G.n) (i : ℕ) (v : Fin G.n) : G.dist s v ≤ rounds G s i v := by
  induction i generalizing v with
  | zero =>
    simp only [rounds, L0]
    split_ifs with h
    · subst h; simp
    · exact le_top
  | succ i ih => exact passN_sound ih _ _

/-- After `i` rounds, labels are at most the length of every walk with at most `i` edges. -/
theorem rounds_le_walk (s : Fin G.n) :
    ∀ (i : ℕ) (v : Fin G.n) (p : List (Fin G.m)), G.IsWalk s v p → p.length ≤ i →
      rounds G s i v ≤ G.len p := by
  intro i
  induction i with
  | zero =>
    intro v p hp hl
    have : p = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst this
    rw [isWalk_nil_iff] at hp
    subst hp
    simp [rounds_source]
  | succ i ih =>
    intro v p hp hl
    rcases List.eq_nil_or_concat p with h | ⟨p', e, rfl⟩
    · subst h
      rw [isWalk_nil_iff] at hp
      subst hp
      simp [rounds_source]
    · rw [List.concat_eq_append] at hp hl ⊢
      rw [IsWalk.concat_iff] at hp
      obtain ⟨hp', rfl⟩ := hp
      have hl' : p'.length ≤ i := by simp at hl; omega
      calc rounds G s (i + 1) (G.dst e) = pass G (rounds G s i) (G.dst e) := rfl
        _ ≤ rounds G s i (G.src e) + G.w e := pass_edge _ _
        _ ≤ G.len p' + G.w e := add_le_add (ih _ _ hp' hl') le_rfl
        _ = G.len (p' ++ [e]) := by rw [len_append, len_singleton, ENNReal.coe_add]

/-- `n` rounds of Bellman–Ford give the exact distances. -/
theorem rounds_n_eq_dist (s : Fin G.n) (v : Fin G.n) : rounds G s G.n v = G.dist s v := by
  refine le_antisymm ?_ (rounds_sound s _ v)
  by_cases hr : G.Reachable s v
  · obtain ⟨p, hp, hpe, -, hlen⟩ := exists_shortest_path hr
    rw [← hpe]
    exact rounds_le_walk s _ v p hp hlen.le
  · rw [dist_eq_top_iff.mpr hr]
    exact le_top



/-! ## The program text -/

open WExpr Stmt

/-- `dist[u] + w[e]` -/
def relaxVal : VExpr := .add (.load "dist" (.var "u")) (.load "w" (.var "e"))

/-- Inner-loop body: relax edge `e`. -/
def body : Stmt :=
  seq (wset "u" (load "src" (var "e")))
  (seq (wset "v" (load "dst" (var "e")))
  (seq (ite (load "reach" (var "u"))
          (ite (eq (load "reach" (var "v")) (lit 0))
             (seq (vstore "dist" (var "v") relaxVal) (wstore "reach" (var "v") (lit 1)))
             (seq (vle "b" (.load "dist" (var "v")) relaxVal)
                  (ite (var "b") skip (vstore "dist" (var "v") relaxVal))))
          skip)
  (wset "e" (WExpr.add (var "e") (lit 1)))))

/-- One pass over all edges. -/
def inner : Stmt := .while (lt (var "e") (var "m")) body

def outerBody : Stmt := seq (wset "e" (lit 0)) (seq inner (wset "i" (WExpr.add (var "i") (lit 1))))

/-- `n` passes. -/
def outer : Stmt := .while (lt (var "i") (var "n")) outerBody

def prog : Stmt :=
  seq (walloc "reach" (var "n")) (seq (valloc "dist" (var "n"))
    (seq (wstore "reach" (var "s") (lit 1)) (seq (wset "i" (lit 0)) outer)))

/-- The Bellman–Ford program (words below `n + m + 2`). -/
def bfProgram : Program := { body := prog, wordExp := 0 }

/-! ## Invariants -/

/-- The input arrays, array lengths and word cap are as initialised. -/
structure Frame (G : Graph) (st : State ℝ≥0) : Prop where
  hn : st.w "n" = G.n
  hm : st.w "m" = G.m
  hcap : G.n + G.m + 2 ≤ st.cap
  hsrc : ∀ j (h : j < G.m), st.wa "src" j = (G.src ⟨j, h⟩ : ℕ)
  hdst : ∀ j (h : j < G.m), st.wa "dst" j = (G.dst ⟨j, h⟩ : ℕ)
  hw : ∀ j (h : j < G.m), st.va "w" j = G.w ⟨j, h⟩
  hsrcL : st.wlen "src" = G.m
  hdstL : st.wlen "dst" = G.m
  hwL : st.vlen "w" = G.m
  hreachL : st.wlen "reach" = G.n
  hdistL : st.vlen "dist" = G.n

/-- Decoded labels of a state. -/
noncomputable def lab (G : Graph) (st : State ℝ≥0) : Fin G.n → ℝ≥0∞ := fun v => st.label v

theorem lab_apply (st : State ℝ≥0) (v : Fin G.n) :
    lab G st v = if st.wa "reach" v = 0 then ⊤ else ((st.va "dist" v : ℝ≥0) : ℝ≥0∞) := rfl

theorem Frame.charge {st : State ℝ≥0} (h : Frame G st) (k : ℕ) : Frame G (st.charge k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem Frame.setW {st : State ℝ≥0} (h : Frame G st) {x : String} (hxn : x ≠ "n")
    (hxm : x ≠ "m") (a : ℕ) : Frame G (st.setW x a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨?_, ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · simp [State.setW, Ne.symm hxn, h1]
  · simp [State.setW, Ne.symm hxm, h2]

theorem Frame.storeW_reach {st : State ℝ≥0} (h : Frame G st) (j a : ℕ) :
    Frame G (st.storeW "reach" j a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_, h6, h7, h8, h9, h10, h11⟩
  · intro j' hj'; simp [State.storeW, h4 j' hj']
  · intro j' hj'; simp [State.storeW, h5 j' hj']

theorem Frame.storeV_dist {st : State ℝ≥0} (h : Frame G st) (j : ℕ) (a : ℝ≥0) :
    Frame G (st.storeV "dist" j a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, h10, h11⟩
  intro j' hj'; simp [State.storeV, h6 j' hj']

theorem lab_charge (st : State ℝ≥0) (k : ℕ) : lab G (st.charge k) = lab G st := rfl

theorem lab_setW (st : State ℝ≥0) (x : String) (a : ℕ) : lab G (st.setW x a) = lab G st := rfl

theorem relaxE_of_le {L : Fin G.n → ℝ≥0∞} {e : Fin G.m} (h : L (G.dst e) ≤ L (G.src e) + G.w e) :
    relaxE G L e = L := by
  unfold relaxE
  rw [min_eq_left h, Function.update_eq_self]

theorem relaxE_of_lt {L : Fin G.n → ℝ≥0∞} {e : Fin G.m} (h : L (G.src e) + G.w e ≤ L (G.dst e)) :
    relaxE G L e = Function.update L (G.dst e) (L (G.src e) + G.w e) := by
  unfold relaxE
  rw [min_eq_right h]

theorem eval_relaxVal {S : State ℝ≥0} {u j : ℕ} (hu : S.w "u" = u) (he : S.w "e" = j)
    (hul : u < S.vlen "dist") (hjl : j < S.vlen "w") :
    evalV realOps S relaxVal = some (S.va "dist" u + S.va "w" j) :=
  evalV_add_of (evalV_load_of (by rw [evalW_var, hu]) hul)
    (evalV_load_of (by rw [evalW_var, he]) hjl)

/-- Simulation of one inner-loop iteration: the body relaxes edge `j` on the decoded labels. -/
theorem body_runs (st : State ℝ≥0) (hF : Frame G st) (j : ℕ) (hj : j < G.m)
    (he : st.w "e" = j) :
    Runs realOps body st (fun st' => Frame G st' ∧ st'.w "e" = j + 1 ∧ st'.w "i" = st.w "i" ∧
      lab G st' = relaxE G (lab G st) ⟨j, hj⟩ ∧ st'.cost ≤ st.cost + 8) := by
  set e : Fin G.m := ⟨j, hj⟩ with he_def
  have hu : (G.src e : ℕ) < G.n := (G.src e).isLt
  have hv : (G.dst e : ℕ) < G.n := (G.dst e).isLt
  have hwj : st.va "w" j = G.w e := hF.hw j hj
  -- u := src[e]
  refine runs_seq (runs_wset (a := (G.src e : ℕ))
    (by rw [evalW_load_of (by rw [evalW_var, he]) (by rw [hF.hsrcL]; exact hj), hF.hsrc j hj]) ?_)
  set st1 := (st.setW "u" (G.src e : ℕ)).charge 1 with hst1
  have hF1 : Frame G st1 := (hF.setW (by decide) (by decide) _).charge 1
  -- v := dst[e]
  have h1e : st1.w "e" = j := by simp [hst1, State.setW, State.charge, he]
  refine runs_seq (runs_wset (a := (G.dst e : ℕ))
    (by rw [evalW_load_of (j := j) (by rw [evalW_var, h1e]) (by rw [hF1.hdstL]; exact hj),
      hF1.hdst j hj]) ?_)
  set st2 := (st1.setW "v" (G.dst e : ℕ)).charge 1 with hst2
  have hF2 : Frame G st2 := (hF1.setW (by decide) (by decide) _).charge 1
  have h2u : st2.w "u" = G.src e := by simp [hst2, hst1, State.setW, State.charge]
  have h2v : st2.w "v" = G.dst e := by simp [hst2, State.setW, State.charge]
  have h2e : st2.w "e" = j := by simp [hst2, hst1, State.setW, State.charge, he]
  have h2i : st2.w "i" = st.w "i" := by simp [hst2, hst1, State.setW, State.charge]
  have h2c : st2.cost = st.cost + 2 := by simp [hst2, hst1, State.setW, State.charge]
  have hlab2 : lab G st2 = lab G st := rfl
  have h2wa : ∀ a k, st2.wa a k = st.wa a k := fun _ _ => rfl
  have h2va : ∀ a k, st2.va a k = st.va a k := fun _ _ => rfl
  have hcap2 : G.n + G.m + 2 ≤ st2.cap := hF2.hcap
  -- the final `e := e + 1`, common to all branches
  have finish : ∀ st3 : State ℝ≥0, Frame G st3 → st3.w "e" = j → st3.w "i" = st.w "i" →
      lab G st3 = relaxE G (lab G st) e → st3.cost ≤ st.cost + 7 →
      Runs realOps (wset "e" (WExpr.add (var "e") (lit 1))) st3 (fun st' => Frame G st' ∧
        st'.w "e" = j + 1 ∧ st'.w "i" = st.w "i" ∧ lab G st' = relaxE G (lab G st) e ∧
        st'.cost ≤ st.cost + 8) := by
    intro st3 hF3 h3e h3i hl3 hc3
    refine runs_wset (a := j + 1) ?_ ?_
    · have h3cap := hF3.hcap
      exact evalW_add_of (by rw [evalW_var, h3e]) (evalW_lit_of (by omega)) (by omega)
    · refine ⟨(hF3.setW (by decide) (by decide) _).charge 1, ?_, ?_, ?_, ?_⟩
      · simp [State.setW, State.charge]
      · simp [State.setW, State.charge, h3i]
      · rw [lab_charge, lab_setW, hl3]
      · simp [State.setW, State.charge]; omega
  have hLu_def : lab G st (G.src e) =
      if st.wa "reach" (G.src e) = 0 then ⊤ else ((st.va "dist" (G.src e) : ℝ≥0) : ℝ≥0∞) :=
    lab_apply _ _
  have hLv_def : lab G st (G.dst e) =
      if st.wa "reach" (G.dst e) = 0 then ⊤ else ((st.va "dist" (G.dst e) : ℝ≥0) : ℝ≥0∞) :=
    lab_apply _ _
  refine runs_seq ?_
  have hreach2 : evalW st2 (load "reach" (var "u")) = some (st.wa "reach" (G.src e)) :=
    evalW_load_of (by rw [evalW_var, h2u]) (by rw [hF2.hreachL]; exact hu)
  by_cases hru : st.wa "reach" (G.src e) = 0
  · -- source unreached: nothing changes
    refine runs_ite_false (by rw [hreach2, hru]) (runs_skip ?_)
    refine finish _ ((hF2.charge 1).charge 1) (by simp [State.charge, h2e])
      (by simp [State.charge, h2i]) ?_ (by simp [State.charge, h2c])
    rw [lab_charge, lab_charge, hlab2, relaxE_of_le]
    rw [hLu_def]
    simp [hru]
  · refine runs_ite_true hreach2 hru ?_
    have hLu : lab G st (G.src e) = ((st.va "dist" (G.src e) : ℝ≥0) : ℝ≥0∞) := by
      rw [hLu_def]; simp [hru]
    set S3 := st2.charge 1 with hS3
    have hS3v : S3.w "v" = G.dst e := h2v
    have hS3u : S3.w "u" = G.src e := h2u
    have hS3e : S3.w "e" = j := h2e
    have hrvS3 : evalV realOps S3 relaxVal = some (st.va "dist" (G.src e) + G.w e) := by
      rw [eval_relaxVal hS3u hS3e (by rw [show S3.vlen "dist" = G.n from hF2.hdistL]; exact hu)
        (by rw [show S3.vlen "w" = G.m from hF2.hwL]; exact hj)]
      rw [show S3.va "dist" (G.src e) = st.va "dist" (G.src e) from rfl,
        show S3.va "w" j = st.va "w" j from rfl, hwj]
    have hreachv : evalW S3 (load "reach" (var "v")) = some (st.wa "reach" (G.dst e)) :=
      evalW_load_of (by rw [evalW_var, hS3v])
        (by rw [show S3.wlen "reach" = G.n from hF2.hreachL]; exact hv)
    have hcap3 : G.n + G.m + 2 ≤ S3.cap := hF2.hcap
    by_cases hrv0 : st.wa "reach" (G.dst e) = 0
    · -- target unreached: set dist[v] := dist[u] + w, reach[v] := 1
      have hc0 : (0:ℕ) < S3.cap := by omega
      have hc1 : (1:ℕ) < S3.cap := by omega
      have htest : evalW S3 (eq (load "reach" (var "v")) (lit 0)) = some 1 := by
        rw [evalW_eq_of hreachv (evalW_lit_of hc0) hc1, hrv0]; rfl
      refine runs_ite_true htest one_ne_zero ?_
      set S4 := S3.charge 1 with hS4
      refine runs_seq (runs_vstore (j := G.dst e) (by rw [evalW_var]; exact congrArg some hS3v)
        (by rw [hS4, evalV_charge]; exact hrvS3)
        (by rw [show S4.vlen "dist" = G.n from hF2.hdistL]; exact hv) ?_)
      set S5 := (S4.storeV "dist" (G.dst e) (st.va "dist" (G.src e) + G.w e)).charge 1 with hS5
      have hcap5 : G.n + G.m + 2 ≤ S5.cap := hF2.hcap
      refine runs_wstore (j := G.dst e) (a := 1) (by rw [evalW_var]; exact congrArg some hS3v)
        (evalW_lit_of (by omega))
        (by rw [show S5.wlen "reach" = G.n from hF2.hreachL]; exact hv) ?_
      refine finish _ ((((hF2.charge 1).charge 1).storeV_dist _ _).charge 1
        |>.storeW_reach _ _ |>.charge 1) (by simp [hS5, hS4, hS3, State.charge, State.storeV,
          State.storeW, h2e])
        (by simp [hS5, hS4, hS3, State.charge, State.storeV, State.storeW, h2i]) ?_
        (by simp [hS5, hS4, hS3, State.charge, State.storeV, State.storeW, h2c])
      have hne : lab G st (G.src e) + G.w e ≤ lab G st (G.dst e) := by
        rw [hLv_def]; simp [hrv0]
      rw [relaxE_of_lt hne, hLu]
      funext v'
      rw [lab_apply]
      by_cases hv' : v' = G.dst e
      · subst hv'
        simp [hS5, hS4, hS3, State.charge, State.storeV, State.storeW]
      · have hv'' : (v' : ℕ) ≠ (G.dst e : ℕ) := fun h => hv' (Fin.ext h)
        rw [Function.update_of_ne hv', lab_apply]
        simp [hS5, hS4, hS3, State.charge, State.storeV, State.storeW, hv'', h2wa, h2va]
    · -- both reached: compare
      have hLv : lab G st (G.dst e) = ((st.va "dist" (G.dst e) : ℝ≥0) : ℝ≥0∞) := by
        rw [hLv_def]; simp [hrv0]
      have hc0 : (0:ℕ) < S3.cap := by omega
      have hc1 : (1:ℕ) < S3.cap := by omega
      have htest : evalW S3 (eq (load "reach" (var "v")) (lit 0)) = some 0 := by
        rw [evalW_eq_of hreachv (evalW_lit_of hc0) hc1, if_neg hrv0]
      refine runs_ite_false htest ?_
      set S4 := S3.charge 1 with hS4
      have hdv : evalV realOps S4 (.load "dist" (var "v")) = some (st.va "dist" (G.dst e)) :=
        evalV_load_of (by rw [evalW_var]; exact congrArg some hS3v)
          (by rw [show S4.vlen "dist" = G.n from hF2.hdistL]; exact hv)
      refine runs_seq (runs_vle hdv (by rw [hS4, evalV_charge]; exact hrvS3)
        (by show 1 < st2.cap; have := hF2.hcap; omega) ?_)
      set bit := if realOps.le (st.va "dist" (G.dst e)) (st.va "dist" (G.src e) + G.w e)
        then 1 else 0 with hbit
      set S5 := (S4.setW "b" bit).charge 1 with hS5
      have hS5b : S5.w "b" = bit := by simp [hS5, State.setW, State.charge]
      by_cases hle : st.va "dist" (G.dst e) ≤ st.va "dist" (G.src e) + G.w e
      · have hbit1 : bit = 1 := by simp [hbit, realOps, hle]
        refine runs_ite_true (x := 1) (by rw [evalW_var, hS5b, hbit1]) one_ne_zero (runs_skip ?_)
        refine finish _ (((((hF2.charge 1).charge 1).setW (by decide) (by decide) _).charge 1
          |>.charge 1).charge 1) (by simp [hS5, hS4, hS3, State.charge, State.setW, h2e])
          (by simp [hS5, hS4, hS3, State.charge, State.setW, h2i]) ?_
          (by simp [hS5, hS4, hS3, State.charge, State.setW, h2c])
        rw [show lab G ((S5.charge 1).charge 1) = lab G st from rfl, relaxE_of_le]
        rw [hLu, hLv]
        exact_mod_cast hle
      · have hbit0 : bit = 0 := by simp [hbit, realOps, hle]
        refine runs_ite_false (by rw [evalW_var, hS5b, hbit0]) ?_
        set S6 := S5.charge 1 with hS6
        refine runs_vstore (j := G.dst e) (by rw [evalW_var]; simp [hS6, hS5, hS4, State.setW,
            State.charge, hS3v])
          (a := st.va "dist" (G.src e) + G.w e)
          (by
            rw [eval_relaxVal (u := G.src e) (j := j)
              (by simp [hS6, hS5, hS4, State.setW, State.charge, hS3u])
              (by simp [hS6, hS5, hS4, State.setW, State.charge, hS3e])
              (by rw [show S6.vlen "dist" = G.n from hF2.hdistL]; exact hu)
              (by rw [show S6.vlen "w" = G.m from hF2.hwL]; exact hj)]
            rw [show S6.va "dist" (G.src e) = st.va "dist" (G.src e) from rfl,
              show S6.va "w" j = st.va "w" j from rfl, hwj])
          (by rw [show S6.vlen "dist" = G.n from hF2.hdistL]; exact hv) ?_
        refine finish _ (((((((hF2.charge 1).charge 1).setW (by decide) (by decide) _).charge 1
          |>.charge 1)).storeV_dist _ _).charge 1)
          (by simp [hS6, hS5, hS4, hS3, State.charge, State.setW, State.storeV, h2e])
          (by simp [hS6, hS5, hS4, hS3, State.charge, State.setW, State.storeV, h2i]) ?_
          (by simp [hS6, hS5, hS4, hS3, State.charge, State.setW, State.storeV, h2c])
        have hlt : lab G st (G.src e) + G.w e ≤ lab G st (G.dst e) := by
          rw [hLu, hLv]
          exact_mod_cast (not_le.mp hle).le
        rw [relaxE_of_lt hlt, hLu]
        funext v'
        rw [lab_apply]
        by_cases hv' : v' = G.dst e
        · subst hv'
          simp [hS6, hS5, hS4, hS3, State.charge, State.storeV, State.setW, h2wa, hrv0]
        · have hv'' : (v' : ℕ) ≠ (G.dst e : ℕ) := fun h => hv' (Fin.ext h)
          rw [Function.update_of_ne hv', lab_apply]
          simp [hS6, hS5, hS4, hS3, State.charge, State.storeV, State.setW, h2wa, h2va, hv'']


/-- The inner loop performs one full Gauss–Seidel pass over the edges. -/
theorem inner_runs (st : State ℝ≥0) (hF : Frame G st) (he : st.w "e" = 0) :
    Runs realOps inner st (fun st' => Frame G st' ∧ st'.w "e" = G.m ∧ st'.w "i" = st.w "i" ∧
      lab G st' = pass G (lab G st) ∧ st'.cost ≤ st.cost + 9 * G.m + 1) := by
  refine runs_while (fun k st' => Frame G st' ∧ st'.w "e" = k ∧ st'.w "i" = st.w "i" ∧
      lab G st' = passN G (lab G st) k ∧ st'.cost ≤ st.cost + 9 * k) G.m _ ?_ ?_ st
    ⟨hF, he, rfl, rfl, by simp⟩
  · intro k hk st' ⟨hF', he', hi', hl', hc'⟩
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := k) (y := G.m) (by rw [evalW_var, he']) (by rw [evalW_var, hF'.hm])
        (by have := hF'.hcap; omega)]
      simp [hk]
    · refine (body_runs (st'.charge 1) (hF'.charge 1) k hk (by simp [State.charge, he'])).mono ?_
      rintro st'' ⟨hF'', he'', hi'', hl'', hc''⟩
      refine ⟨hF'', he'', ?_, ?_, ?_⟩
      · rw [hi'']; simpa [State.charge] using hi'
      · rw [hl'', lab_charge, hl']; simp [passN, hk]
      · simp [State.charge] at hc''; omega
  · intro st' ⟨hF', he', hi', hl', hc'⟩
    refine ⟨?_, hF'.charge 1, by simp [State.charge, he'], by simpa [State.charge] using hi', ?_, ?_⟩
    · rw [evalW_lt_of (x := G.m) (y := G.m) (by rw [evalW_var, he']) (by rw [evalW_var, hF'.hm])
        (by have := hF'.hcap; omega)]
      simp
    · rw [lab_charge, hl']; rfl
    · simp [State.charge]; omega

/-- The outer loop performs `n` passes. -/
theorem outer_runs (s : Fin G.n) (st : State ℝ≥0) (hF : Frame G st) (hi : st.w "i" = 0)
    (hl : lab G st = L0 G s) :
    Runs realOps outer st (fun st' => Frame G st' ∧ lab G st' = rounds G s G.n ∧
      st'.cost ≤ st.cost + (9 * G.m + 4) * G.n + 1) := by
  refine runs_while (fun i st' => Frame G st' ∧ st'.w "i" = i ∧ lab G st' = rounds G s i ∧
      st'.cost ≤ st.cost + (9 * G.m + 4) * i) G.n _ ?_ ?_ st ⟨hF, hi, hl, by simp⟩
  · intro i hi' st' ⟨hF', hi'', hl', hc'⟩
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := i) (y := G.n) (by rw [evalW_var, hi'']) (by rw [evalW_var, hF'.hn])
        (by have := hF'.hcap; omega)]
      simp [hi']
    · have hcap1 : G.n + G.m + 2 ≤ (st'.charge 1).cap := hF'.hcap
      refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
      refine runs_seq ?_
      refine (inner_runs _ (((hF'.charge 1).setW (by decide) (by decide) _).charge 1)
        (by simp [State.setW, State.charge])).mono ?_
      rintro st3 ⟨hF3, he3, hi3, hl3, hc3⟩
      have hi3' : st3.w "i" = i := by rw [hi3]; simpa [State.setW, State.charge] using hi''
      refine runs_wset (a := i + 1) (evalW_add_of (by rw [evalW_var, hi3'])
        (evalW_lit_of (by have := hF3.hcap; omega)) (by have := hF3.hcap; omega)) ?_
      refine ⟨(hF3.setW (by decide) (by decide) _).charge 1, by simp [State.setW, State.charge],
        ?_, ?_⟩
      · rw [lab_charge, lab_setW, hl3, lab_charge, lab_setW, lab_charge, hl']; rfl
      · simp [State.setW, State.charge] at hc3 ⊢
        nlinarith
  · intro st' ⟨hF', hi', hl', hc'⟩
    refine ⟨?_, hF'.charge 1, by rw [lab_charge, hl'], by simp [State.charge]; omega⟩
    rw [evalW_lt_of (x := G.n) (y := G.n) (by rw [evalW_var, hi']) (by rw [evalW_var, hF'.hn])
      (by have := hF'.hcap; omega)]
    simp

/-- The input part of a machine state: the input registers and arrays of `initState`, and a word
cap at least `n + m + 2` (any other registers and arrays are arbitrary).  Used to run the
Bellman–Ford program inside larger programs (e.g. as a dispatch fallback). -/
structure InputFrame (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop where
  hn : st.w "n" = G.n
  hm : st.w "m" = G.m
  hs : st.w "s" = s
  hcap : G.n + G.m + 2 ≤ st.cap
  hsrc : ∀ j (h : j < G.m), st.wa "src" j = (G.src ⟨j, h⟩ : ℕ)
  hdst : ∀ j (h : j < G.m), st.wa "dst" j = (G.dst ⟨j, h⟩ : ℕ)
  hw : ∀ j (h : j < G.m), st.va "w" j = G.w ⟨j, h⟩
  hsrcL : st.wlen "src" = G.m
  hdstL : st.wlen "dst" = G.m
  hwL : st.vlen "w" = G.m

theorem inputFrame_initState (P : Program) (s : Fin G.n) :
    InputFrame G s (initState P G s) := by
  refine ⟨by simp [initState], by simp [initState], by simp [initState], ?_, ?_, ?_, ?_,
    by simp [initState], by simp [initState], by simp [initState]⟩
  · simp only [initState]
    calc G.n + G.m + 2 = (G.n + G.m + 2) ^ 1 := (pow_one _).symm
      _ ≤ (G.n + G.m + 2) ^ (P.wordExp + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  · intro j h; simp [initState, h]
  · intro j h; simp [initState, h]
  · intro j h; simp [initState, h]

/-- The whole program, from any state with the input frame: initialisation followed by `n`
passes.  The cost bound is relative to the starting cost. -/
theorem prog_runs_gen (s : Fin G.n) (st0 : State ℝ≥0) (h0 : InputFrame G s st0) :
    Runs realOps prog st0 (fun st' => Frame G st' ∧
      lab G st' = rounds G s G.n ∧ st'.cost ≤ st0.cost + 2 * G.n + 4 + (9 * G.m + 4) * G.n + 1) := by
  have h0n := h0.hn
  have h0cap := h0.hcap
  refine runs_seq (runs_walloc (k := G.n) (by rw [evalW_var, h0n]) ?_)
  refine runs_seq (runs_valloc (k := G.n) (by rw [evalW_var]; simp [State.allocW,
    State.charge, h0n]) ?_)
  set st2 := ((((st0.allocW "reach" G.n).charge (G.n + 1)).allocV "dist" G.n
    realOps.zero).charge (G.n + 1)) with hst2
  have h2cap : G.n + G.m + 2 ≤ st2.cap := by
    simp only [hst2, State.allocW, State.allocV, State.charge]; omega
  refine runs_seq (runs_wstore (j := s) (a := 1)
    (by rw [evalW_var]; simp [hst2, State.allocW, State.allocV, State.charge, h0.hs])
    (evalW_lit_of (by omega))
    (by simp [hst2, State.allocW, State.allocV, State.charge]) ?_)
  set st3 := (st2.storeW "reach" s 1).charge 1 with hst3
  have h3cap : G.n + G.m + 2 ≤ st3.cap := by
    simp only [hst3, State.storeW, State.charge]; omega
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  set st4 := (st3.setW "i" 0).charge 1 with hst4
  have hF4 : Frame G st4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hn]
    · simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hm]
    · simp only [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV]; omega
    · intro j h; simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hsrc j h]
    · intro j h; simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hdst j h]
    · intro j h; simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hw j h]
    · simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hsrcL]
    · simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hdstL]
    · simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, h0.hwL]
    · simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV]
    · simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV]
  have hl4 : lab G st4 = L0 G s := by
    funext v
    rw [lab_apply]
    by_cases hv : v = s
    · subst hv
      simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, L0, realOps]
    · have hv' : (v : ℕ) ≠ (s : ℕ) := fun h => hv (Fin.ext h)
      simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
        State.allocV, L0, hv, hv']
  have hc4 : st4.cost = st0.cost + 2 * G.n + 4 := by
    simp [hst4, hst3, hst2, State.setW, State.charge, State.storeW, State.allocW,
      State.allocV]
    omega
  refine (outer_runs s st4 hF4 (by simp [hst4, State.setW, State.charge]) hl4).mono ?_
  rintro r ⟨hF, hl, hc⟩
  exact ⟨hF, hl, by omega⟩

/-- The whole program from the initial state. -/
theorem prog_runs (s : Fin G.n) :
    Runs realOps prog (initState bfProgram G s) (fun st' => Frame G st' ∧
      lab G st' = rounds G s G.n ∧ st'.cost ≤ 2 * G.n + 4 + (9 * G.m + 4) * G.n + 1) := by
  refine (prog_runs_gen s _ (inputFrame_initState bfProgram s)).mono ?_
  rintro r ⟨hF, hl, hc⟩
  exact ⟨hF, hl, by simpa [initState] using hc⟩

/-- `bfProgram` terminates on every input with the exact distances and cost at most
`9 (n + 1) (m + 1)`. -/
theorem bfProgram_runs (G : Graph) (s : Fin G.n) :
    ∃ fuel r, bfProgram.run fuel G s = some r ∧ r.Solves G s ∧
      r.cost ≤ 9 * ((G.n + 1) * (G.m + 1)) := by
  obtain ⟨fuel, r, hrun, hF, hl, hc⟩ := prog_runs (G := G) s
  refine ⟨fuel, r, hrun, ⟨hF.hreachL, hF.hdistL, fun v => ?_⟩, ?_⟩
  · calc r.label v = lab G r v := rfl
      _ = rounds G s G.n v := congrFun hl v
      _ = G.dist s v := rounds_n_eq_dist s v
  · nlinarith

/-- **Non-vacuity (F-v2-2)**: `Program.Exact` is satisfiable. -/
theorem bfProgram_exact : bfProgram.Exact := fun G s => by
  obtain ⟨fuel, r, hrun, hsolve, -⟩ := bfProgram_runs G s
  exact ⟨fuel, r, hrun, hsolve⟩

theorem bfProgram_runsWithin (G : Graph) (s : Fin G.n) :
    bfProgram.RunsWithin G s (9 * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))) := by
  obtain ⟨fuel, r, hrun, -, hc⟩ := bfProgram_runs G s
  refine ⟨fuel, r, hrun, ?_⟩
  exact_mod_cast hc

/-- The model admits an exact algorithm with an `O((n+1)(m+1))` cost bound. -/
theorem exists_exact_program :
    ∃ P : Program, P.Exact ∧ ∃ C : ℝ, ∀ (G : Graph) (s : Fin G.n),
      P.RunsWithin G s (C * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))) :=
  ⟨bfProgram, bfProgram_exact, 9, bfProgram_runsWithin⟩

end Frontier.RAM.BF
