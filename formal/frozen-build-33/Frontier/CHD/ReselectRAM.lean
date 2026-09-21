import Frontier.CHD.AppendU
import Frontier.CHD.RamPiv

/-!
# ReselectRAM — BM.23 of the recursive spine: re-selection of the marked groups (agent-06; B-L4, NON-GATE)

Program text = agent-08's `RamSpine.reselect cmpTT dsIns`.  For each marked group `j` (mark row `sp.mk`,
level `lvl`) that is still nonempty: `grpMin` (agent-01, `RamInit.grpMin_spec`) finds a key-minimal member
`b`, `sp.gp[lvl, j] := b`, `px := b`, and `dsIns` (the `D` layer's insertion, `SpineLoop.DLayer.ins`)
inserts `b` with its current label.  The loop body is `grpMin`'s statements followed by the store and the
insertion, nested differently from `seq (grpMin cmp) …`; `rsBlock_of` reassociates.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpineU

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD Frontier.CHD.RamLevel

section Block

variable {V : Type} {ops : VOps V}

/-- The re-selection of one nonempty marked group, in `grpMin` form. -/
def rsBlock (cmp dsIns : Stmt) : Stmt :=
  seq (RamInit.grpMin cmp) (seq (wstore "sp.gp" (cr (var "sp.j")) (var "sp.b")) (seq (wset "px" (var "sp.b")) dsIns))

/-- The re-selection of one nonempty marked group, as in agent-08's text. -/
def rsBlockT (cmp dsIns : Stmt) : Stmt :=
  seq (wset "sp.q" (load "sp.gs" (cr (var "sp.j"))))
  (seq (wset "sp.qe" (add (var "sp.q") (load "sp.gl" (cr (var "sp.j")))))
  (seq (wset "sp.b" (load "sp.gm" (cr (var "sp.q"))))
  (seq (incr "sp.q")
  (seq (.while (lt (var "sp.q") (var "sp.qe"))
         (seq (wset "tt.ra" (load "sp.gm" (cr (var "sp.q"))))
         (seq (wset "tt.rb" (var "sp.b"))
         (seq cmp
         (seq (ite (var "lab.bit") (wset "sp.b" (var "tt.ra")) skip)
              (incr "sp.q"))))))
  (seq (wstore "sp.gp" (cr (var "sp.j")) (var "sp.b"))
  (seq (wset "px" (var "sp.b")) dsIns))))))

def rsBody (cmp dsIns : Stmt) : Stmt :=
  seq (wset "sp.j" (load "sp.mk" (cr (var "sp.i"))))
  (seq (ite (load "sp.gl" (cr (var "sp.j"))) (rsBlockT cmp dsIns) skip)
       (incr "sp.i"))

def rsLoop (cmp dsIns : Stmt) : Stmt :=
  .while (lt (var "sp.i") (load "sp.mk.len" (var "lvl"))) (rsBody cmp dsIns)

/-- BM.23 -/
def reselect (cmp dsIns : Stmt) : Stmt := seq (wset "sp.i" (lit 0)) (rsLoop cmp dsIns)

theorem ramSpine_reselect_eq (cmp dsIns : Stmt) : RamSpine.reselect cmp dsIns = reselect cmp dsIns := rfl

/-- **Reassociation**: a run of `seq (grpMin cmp) R` is a run of agent-08's nesting. -/
theorem rsBlock_of {cmp dsIns : Stmt} {s : State V} {Q : State V → Prop}
    (h : Runs ops (rsBlock cmp dsIns) s Q) : Runs ops (rsBlockT cmp dsIns) s Q := by
  unfold rsBlock RamInit.grpMin at h
  unfold rsBlockT
  refine Runs.seq_congr (Runs.seq_assoc h) (fun t1 h1 => ?_)
  refine Runs.seq_congr (Runs.seq_assoc h1) (fun t2 h2 => ?_)
  refine Runs.seq_congr (Runs.seq_assoc h2) (fun t3 h3 => ?_)
  exact Runs.seq_congr (Runs.seq_assoc h3) (fun t4 h4 => h4)

/-- The size of a group is the length of its segment. -/
theorem GrpRep.card_eq {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) : (P j).card = gl st l n j := by
  rw [h.img j hj, Finset.card_image_of_injOn]
  · simp
  · intro q hq q' hq' e
    simp only [Finset.coe_range, Set.mem_Iio] at hq hq'
    have h1 := h.pos j hj q hq
    have h2 := h.pos j hj q' hq'
    simp only at e
    rw [e] at h1
    omega

end Block

/-! ## The loop invariant -/

section Loop

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

open Frontier.CHD.BM Frontier.CHD.RamInit

/-- registers written by `reselect` itself (besides `cmp`'s and `dsIns`'s) -/
def rsRegs : List String := ["sp.i", "sp.j", "px"] ++ gmRegs

/-- **One insertion** of the vertex in `px` with key `f px`, under a Layer-A invariant `Inv`, with its full
footprint: word arrays `IA`, value arrays `IVA`, word registers `IW`, value registers `IVR` (the shape of
`SpineLoop.DLayer.ins_spec`; agent-01's `RamPiv.DInsI` with value registers). -/
structure InsI (ops : VOps V) (dsIns : Stmt) (DR : State V → DGl G s → DStrM G s → Prop)
    (Inv : DGl G s → DStrM G s → Prop) (vok : Fin G.n → Prop) (res : State V → ℕ) (rcap : ℕ)
    (f : Fin G.n → WLab G s) (T K C : ℕ) (IA IVA IW IVR : List String) : Prop where
  run : ∀ st g D (v : Fin G.n), DR st g D → Inv g D → vok v → st.w "px" = v →
    res st + ((BM.insC (dlOps G s) T g D v (f v)).2.2 + 1) ≤ rcap →
    Runs ops dsIns st (fun r => DR r (BM.insC (dlOps G s) T g D v (f v)).1
        (BM.insC (dlOps G s) T g D v (f v)).2.1 ∧
      Unchanged st r IA IVA IW IVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * (BM.insC (dlOps G s) T g D v (f v)).2.2 + C ∧
      res r ≤ res st + ((BM.insC (dlOps G s) T g D v (f v)).2.2 + 1))
  regs : ∀ a ∈ IW, a ≠ "sp.i" ∧ a ≠ "lvl" ∧ a ≠ "n"
  arrs : ∀ a ∈ IA, a ∉ grpArrs ∧ a ≠ "sp.mk" ∧ a ≠ "sp.mk.len"
  /-- the resource counter only reads the insertion's own registers -/
  res_frame : ∀ (st r : State V) (wa va wr vr : List String), Unchanged st r wa va wr vr →
    (∀ a ∈ wr, a ∉ IW) → res r = res st

/-- Invariant of the re-selection loop after `i` marks. -/
structure RSInv {β : Type*} [LinearOrder β] (st : State V) (l n p : ℕ) (P : ℕ → Finset ℕ) (piv : ℕ → ℕ)
    (mks : List ℕ) (κ : ℕ → β) (KR : State V → Prop) (DR : State V → DGl G s → DStrM G s → Prop)
    (f : Fin G.n → WLab G s) (T : ℕ) (g : DGl G s) (D : DStrM G s) (C K Ci : ℕ)
    (IA IVA IW IVR CW CV : List String) (res : State V → ℕ) (i : ℕ) (t : State V) : Prop where
  ri : t.w "sp.i" = i
  rl : t.w "lvl" = l
  rn : t.w "n" = n
  ile : i ≤ mks.length
  ex : ∃ (piv' : ℕ → ℕ) (L : List (Fin G.n)),
    GrpRep t l n p P piv' ∧
    (∀ j ∈ mks.take i, 0 < (P j).card → piv' j ∈ P j ∧ ∀ x ∈ P j, κ (piv' j) ≤ κ x) ∧
    (∀ j, ¬ (j ∈ mks.take i ∧ 0 < (P j).card) → piv' j = piv j) ∧
    L.map Fin.val = (mks.take i).filterMap (fun j => if 0 < (P j).card then some (piv' j) else none) ∧
    DR t (insManyC (dlOps G s) T f L g D).1 (insManyC (dlOps G s) T f L g D).2.1 ∧
    t.cost ≤ st.cost + 1 + i * 8 + ((mks.take i).map (gl st l n)).sum * (C + 8) +
      K * (insManyC (dlOps G s) T f L g D).2.2 + L.length * (Ci + 3) ∧
    res t ≤ res st + (insManyC (dlOps G s) T f L g D).2.2 + L.length
  kr : KR t
  mkrow : RowRep t "sp.mk" "sp.mk.len" n l mks
  unch : Unchanged st t ("sp.gp" :: IA) IVA (rsRegs ++ CW ++ IW) (CV ++ IVR)
  gpout : ∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → t.wa "sp.gp" q = st.wa "sp.gp" q
  lo : st.cost ≤ t.cost
  wl : t.wlen = st.wlen
  vl : t.vlen = st.vlen

theorem filterMap_take_succ {α β : Type*} (l : List α) (F : α → Option β) {i : ℕ} (hi : i < l.length) :
    (l.take (i + 1)).filterMap F = (l.take i).filterMap F ++ (F l[i]).toList := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filterMap_append]
  cases h : F l[i] <;> simp [List.filterMap_cons, h]

/-- A partial choice of key-minimal pivots extends to all marked groups. -/
theorem exists_completion {β : Type*} [LinearOrder β] (P : ℕ → Finset ℕ) (κ : ℕ → β) (mks : List ℕ)
    (i : ℕ) (pv : ℕ → ℕ)
    (hpv : ∀ j ∈ mks.take i, 0 < (P j).card → pv j ∈ P j ∧ ∀ x ∈ P j, κ (pv j) ≤ κ x) :
    ∃ pf : ℕ → ℕ, (∀ j ∈ mks, 0 < (P j).card → pf j ∈ P j ∧ ∀ x ∈ P j, κ (pf j) ≤ κ x) ∧
      ∀ j ∈ mks.take i, pf j = pv j := by
  classical
  refine ⟨fun j => if j ∈ mks.take i then pv j else
    if h : (P j).Nonempty then (Finset.exists_min_image (P j) κ h).choose else pv j,
    fun j _ hc => ?_, fun j hj => by simp [hj]⟩
  by_cases hjt : j ∈ mks.take i
  · simp only [hjt, if_true]; exact hpv j hjt hc
  · have hne : (P j).Nonempty := Finset.card_pos.mp hc
    simp only [hjt, if_false, dif_pos hne]
    exact (Finset.exists_min_image (P j) κ hne).choose_spec

theorem insManyC_prefix_le (T : ℕ) (f : Fin G.n → WLab G s) :
    ∀ (L1 L2 : List (Fin G.n)) (g : DGl G s) (D : DStrM G s),
      (insManyC (dlOps G s) T f L1 g D).2.2 ≤ (insManyC (dlOps G s) T f (L1 ++ L2) g D).2.2
  | [], _, _, _ => Nat.zero_le _
  | y :: L1, L2, g, D => by
    show (BM.insC (dlOps G s) T g D y (f y)).2.2 +
        (insManyC (dlOps G s) T f L1 (BM.insC (dlOps G s) T g D y (f y)).1
          (BM.insC (dlOps G s) T g D y (f y)).2.1).2.2 ≤
      (BM.insC (dlOps G s) T g D y (f y)).2.2 +
        (insManyC (dlOps G s) T f (L1 ++ L2) (BM.insC (dlOps G s) T g D y (f y)).1
          (BM.insC (dlOps G s) T g D y (f y)).2.1).2.2
    have := insManyC_prefix_le T f L1 L2 (BM.insC (dlOps G s) T g D y (f y)).1
      (BM.insC (dlOps G s) T g D y (f y)).2.1
    omega

theorem exists_fin_list {n : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < n) :
    ∃ L : List (Fin n), L.map Fin.val = l :=
  ⟨l.pmap (fun x hx => ⟨x, hx⟩) hl, by rw [List.map_pmap]; exact List.pmap_eq_self.mpr (fun _ _ => rfl)⟩

end Loop

/-! ## Small frame helpers -/

section Frames

variable {V : Type}

theorem U_setW (r : State V) (x : String) (a : ℕ) {wa va wr vr : List String} (hx : x ∈ wr) :
    Unchanged r ((r.setW x a).charge 1) wa va wr vr :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun z hz => by
    have : z ≠ x := fun h => hz (h ▸ hx)
    simp [this], fun _ _ => rfl, rfl, rfl⟩

theorem U_storeW (r : State V) (arr : String) (j a : ℕ) {wa va wr vr : List String} (ha : arr ∈ wa) :
    Unchanged r ((r.storeW arr j a).charge 1) wa va wr vr :=
  ⟨fun b hb => ⟨by
    have : b ≠ arr := fun h => hb (h ▸ ha)
    funext i; simp [this], rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem U_charge (r : State V) {wa va wr vr : List String} : Unchanged r (r.charge 1) wa va wr vr :=
  Unchanged.charge r 1 wa va wr vr

end Frames

/-! ## Evaluation of a row entry -/

section Eval

variable {V : Type}

theorem ev_rowget {s : State V} {arr len reg : String} {l n i : ℕ} {xs : List ℕ} (hl : s.w "lvl" = l)
    (hn : s.w "n" = n) (hi : s.w reg = i) (hR : RowRep s arr len n l xs) (hix : i < xs.length)
    (hcap : (l + 1) * n < s.cap) :
    evalW s (load arr (cr (var reg))) = some xs[i] := by
  obtain ⟨h1, h2, -, -, h5⟩ := hR
  have hidx : l * n + i < (l + 1) * n := row_index_lt (by omega)
  have c1 : l * n < s.cap := by omega
  have c2 : l * n + i < s.cap := by omega
  simp only [cr, evalW_load', evalW_add', evalW_mul', evalW_var, hl, hn, hi, Option.bind_some, fit_of_lt c1,
    fit_of_lt c2]
  rw [if_pos (by omega), h5 i hix]

theorem ev_gl {s : State V} {l n j p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} (hl : s.w "lvl" = l)
    (hn : s.w "n" = n) (hj : s.w "sp.j" = j) (hjp : j < p) (hG : GrpRep s l n p P piv)
    (hcap : (l + 1) * n < s.cap) :
    evalW s (load "sp.gl" (cr (var "sp.j"))) = some (gl s l n j) := by
  have hjn : j < n := lt_of_lt_of_le hjp hG.p_le
  have hidx : l * n + j < (l + 1) * n := row_index_lt hjn
  have c1 : l * n < s.cap := by omega
  have c2 : l * n + j < s.cap := by omega
  simp only [cr, evalW_load', evalW_add', evalW_mul', evalW_var, hl, hn, hj, Option.bind_some, fit_of_lt c1,
    fit_of_lt c2]
  rw [if_pos (by have := hG.len_gl; omega)]
  rfl

end Eval

/-! ## The loop step -/

section Step

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

open Frontier.CHD.BM Frontier.CHD.RamInit

theorem sum_take_le (l : List ℕ) (f : ℕ → ℕ) (i : ℕ) : ((l.take i).map f).sum ≤ (l.map f).sum := by
  exact List.Sublist.sum_le_sum ((List.take_sublist i l).map f) (fun _ _ => Nat.zero_le _)

set_option maxHeartbeats 1000000 in
theorem rsStep {β : Type*} [LinearOrder β] {cmp dsIns : Stmt} {KR : State V → Prop} {κ : ℕ → β}
    {dom : ℕ → Prop} {C Bud : ℕ} {CW CV FA FR : List String}
    {DR : State V → DGl G s → DStrM G s → Prop} {Inv : DGl G s → DStrM G s → Prop}
    {f : Fin G.n → WLab G s} {T K Ci : ℕ} {IA IVA IW IVR : List String}
    (hI : CmpI ops cmp KR κ dom C Bud CW CV FA FR) (hFR : ∀ a ∈ gmRegs ++ CW, a ∈ FR)
    (hCWi : "sp.i" ∉ CW)
    {vok : Fin G.n → Prop} {res : State V → ℕ} {rcap : ℕ}
    (hIns : InsI ops dsIns DR Inv vok res rcap f T K Ci IA IVA IW IVR)
    (hDRf : ∀ st r g D, DR st g D → Unchanged st r ["sp.gp"] [] (rsRegs ++ CW) CV → st.cost ≤ r.cost →
      DR r g D)
    (hKRf : ∀ st r, KR st → Unchanged st r ("sp.gp" :: IA) IVA (rsRegs ++ IW) IVR → st.cost ≤ r.cost → KR r)
    (hIWr : ∀ a ∈ rsRegs ++ CW, a ∉ IW)
    {st t : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} {mks : List ℕ} {g : DGl G s}
    {D : DStrM G s} {i : ℕ}
    (hG0 : GrpRep st l n p P piv) (hnG : n = G.n) (hmnd : mks.Nodup) (hmp : ∀ j ∈ mks, j < p)
    (hdom : ∀ j ∈ mks, ∀ x ∈ P j, dom x)
    (hvok : ∀ j ∈ mks, ∀ x ∈ P j, ∀ h : x < G.n, vok ⟨x, h⟩)
    (hres : ∀ (pf : ℕ → ℕ) (Lf : List (Fin G.n)),
      (∀ j ∈ mks, 0 < (P j).card → pf j ∈ P j ∧ ∀ x ∈ P j, κ (pf j) ≤ κ x) →
      Lf.map Fin.val = mks.filterMap (fun j => if 0 < (P j).card then some (pf j) else none) →
      res st + (insManyC (dlOps G s) T f Lf g D).2.2 + Lf.length ≤ rcap)
    (hInv : ∀ L : List (Fin G.n), L.length ≤ mks.length →
      Inv (insManyC (dlOps G s) T f L g D).1 (insManyC (dlOps G s) T f L g D).2.1)
    (hcap : (l + 1) * n + 2 < st.cap)
    (hbud : ∀ L : List (Fin G.n), L.length ≤ mks.length →
      st.cost + 1 + mks.length * 8 + (mks.map (gl st l n)).sum * (C + 8) +
        K * (insManyC (dlOps G s) T f L g D).2.2 + L.length * (Ci + 3) ≤ Bud)
    (hR : RSInv st l n p P piv mks κ KR DR f T g D C K Ci IA IVA IW IVR CW CV res i t)
    (hi : i < mks.length) :
    Runs ops (rsBody cmp dsIns) (t.charge 1)
      (RSInv st l n p P piv mks κ KR DR f T g D C K Ci IA IVA IW IVR CW CV res (i + 1)) := by
  obtain ⟨piv', L, hGt, hmin, hkeep, hLf, hDt, hct, hrs⟩ := hR.ex
  have hcapt : (l + 1) * n + 2 < t.cap := by rw [hR.unch.cap]; exact hcap
  have h1 : 1 < t.cap := by omega
  have hjp : mks[i] < p := hmp _ (List.getElem_mem hi)
  have hpn := hG0.p_le
  have hjn : mks[i] < n := by omega
  have hjnot : mks[i] ∉ mks.take i := getElem_not_mem_take hmnd hi
  have hmkl : mks.length ≤ n := hR.mkrow.1
  have hnln : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos l)
  have hgaT : ∀ a ∈ grpArrs, a ≠ "sp.gp" → t.wa a = st.wa a := by
    intro a ha hne
    refine (hR.unch.warr a ?_).1
    intro hm
    rcases List.mem_cons.mp hm with h | h
    · exact hne h
    · exact (hIns.arrs a h).1 ha
  have hglT : ∀ q, gl t l n q = gl st l n q := fun q => by
    simp only [gl]; rw [hgaT "sp.gl" (by simp [grpArrs]) (by decide)]
  have hLlen : L.length ≤ i := by
    have := congrArg List.length hLf
    rw [List.length_map] at this
    rw [this]
    exact (List.length_filterMap_le _ _).trans (by simp)
  have hbudL := hbud L (by omega)
  have htakeS : ((mks.take (i + 1)).map (gl st l n)).sum =
      ((mks.take i).map (gl st l n)).sum + gl st l n mks[i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    simp only [Option.toList_some, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
  have hsumle := sum_take_le mks (gl st l n) (i + 1)
  have hmemI : ∀ y, y ∈ mks.take (i + 1) ↔ y ∈ mks.take i ∨ y = mks[i] := by
    intro y
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    simp only [List.mem_append, Option.toList_some, List.mem_singleton]
  have hFt : ∀ a, a ∈ ["sp.j", "sp.i"] → a ∈ rsRegs ++ CW := fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [rsRegs]
  have hFk : ∀ a, a ∈ ["sp.j", "sp.i"] → a ∈ rsRegs ++ IW := fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [rsRegs]
  unfold rsBody
  apply runs_seq
  refine runs_wset (a := mks[i]) (ev_rowget (s := t.charge 1) (by simpa using hR.rl) (by simpa using hR.rn)
    (by simpa using hR.ri) (RowRep.of_eq hR.mkrow rfl rfl rfl (fun _ _ => rfl)) hi (by simp; omega)) ?_
  have hGs1 : GrpRep (((t.charge 1).setW "sp.j" mks[i]).charge 1) l n p P piv' :=
    grpRep_of_eq hGt (fun _ _ => rfl) (fun _ _ => rfl)
  apply runs_seq
  by_cases hgl0 : gl st l n mks[i] = 0
  · -- empty group: skip
    have hcard0 : (P mks[i]).card = 0 := by rw [GrpRep.card_eq hG0 hjp]; exact hgl0
    refine runs_ite_false (by
        rw [ev_gl (by simp [hR.rl]) (by simp [hR.rn]) (by simp) hjp hGs1 (by simp; omega)]
        exact congrArg some ((hglT _).trans hgl0)) (runs_skip ?_)
    refine runs_wset (evalW_add_of (x := i) (y := 1) (by simp [hR.ri]) (evalW_lit_of (by simp; omega))
      (by simp; omega)) ?_
    have hUtu : Unchanged t ((((((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1).charge 1).setW "sp.i"
        (i + 1)).charge 1)) [] [] ["sp.j", "sp.i"] [] :=
      ((((U_charge t).trans (U_setW _ _ _ (by simp))).trans (U_charge _)).trans (U_charge _)).trans
        (U_setW _ _ _ (by simp))
    refine ⟨by simp, by simp [hR.rl], by simp [hR.rn], by omega,
      ⟨piv', L, grpRep_of_eq hGt (fun _ _ => rfl) (fun _ _ => rfl), fun j hj hc => ?_, fun j hj => ?_, ?_,
        hDRf _ _ _ _ hDt (hUtu.mono (by simp) (by simp) hFt (by simp)) (by simp; omega), ?_,
        by rw [hIns.res_frame _ _ _ _ _ _ hUtu (fun a ha => hIWr a (hFt a ha))]; exact hrs⟩,
      hKRf t _ hR.kr (hUtu.mono (by simp) (by simp) hFk (by simp)) (by simp; omega),
      RowRep.of_eq hR.mkrow rfl rfl rfl (fun _ _ => rfl),
      hR.unch.trans (hUtu.mono (by simp) (by simp) (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> simp [rsRegs]) (by simp)),
      fun q hq => hR.gpout q hq, by simp; have := hR.lo; omega, by simp [hR.wl], by simp [hR.vl]⟩
    · rcases (hmemI j).mp hj with hj | rfl
      · exact hmin j hj hc
      · omega
    · apply hkeep j
      rintro ⟨hj1, hj2⟩
      exact hj ⟨(hmemI j).mpr (Or.inl hj1), hj2⟩
    · rw [hLf, filterMap_take_succ _ _ hi]
      simp [hcard0]
    · simp only [State.charge_cost, State.setW_cost]
      rw [htakeS]
      nlinarith
  · -- nonempty group: argmin, pivot store, insertion
    have hgl1 : 0 < gl st l n mks[i] := Nat.pos_of_ne_zero hgl0
    have hcard1 : 0 < (P mks[i]).card := by rw [GrpRep.card_eq hG0 hjp]; exact hgl1
    refine runs_ite_true (x := gl st l n mks[i]) (by
        rw [ev_gl (by simp [hR.rl]) (by simp [hR.rn]) (by simp) hjp hGs1 (by simp; omega)]
        exact congrArg some (hglT _)) hgl0 ?_
    refine rsBlock_of ?_
    unfold rsBlock
    apply runs_seq
    have hUt1 : Unchanged t (((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1)) [] [] ["sp.j"] [] :=
      (((U_charge t).trans (U_setW _ _ _ (by simp))).trans (U_charge _))
    have hK1 : KR (((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1)) :=
      hKRf t _ hR.kr (hUt1.mono (by simp) (by simp) (fun a ha => by
        simp only [List.mem_singleton] at ha; subst ha; simp [rsRegs]) (by simp)) (by simp; omega)
    have hbudg : ((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1).cost + 4 +
        gl ((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1) l n mks[i] * (C + 8) ≤ Bud := by
      rw [show gl ((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1) l n mks[i] = gl st l n mks[i]
        from hglT _]
      simp only [State.charge_cost, State.setW_cost]
      have h2 : ((mks.take i).map (gl st l n)).sum * (C + 8) + gl st l n mks[i] * (C + 8) ≤
          (mks.map (gl st l n)).sum * (C + 8) := by
        rw [← Nat.add_mul, ← htakeS]; exact Nat.mul_le_mul_right _ hsumle
      nlinarith
    refine (grpMin_spec hI hFR _ (GrpRep.charge' hGs1 1) (by simp [hR.rl]) (by simp [hR.rn]) (by simp) hjp
      (by rw [show gl ((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1) l n mks[i] = gl st l n mks[i]
        from hglT _]; exact hgl1) (hdom _ (List.getElem_mem hi)) hK1 (by simp; omega) hbudg).mono
      (fun r1 hr1 => ?_)
    obtain ⟨hbP, hbmin, hKr1, hU1, hwl1, hc1a, hc1b⟩ := hr1
    have hbn : r1.w "sp.b" < n := ((GrpRep.mem_iff hG0 hjp).mp hbP).1
    have hreg1 : ∀ y, y ∉ gmRegs ++ CW → r1.w y = ((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1).w y :=
      fun y hy => hU1.wreg y hy
    have hnotCW : ∀ y, y = "lvl" ∨ y = "n" ∨ y = "sp.j" ∨ y = "sp.i" → y ∉ gmRegs ++ CW := by
      intro y hy hm
      rcases List.mem_append.mp hm with hm | hm
      · simp [gmRegs] at hm; rcases hy with rfl | rfl | rfl | rfl <;> simp at hm
      · rcases hy with rfl | rfl | rfl | rfl
        · exact (hI.regs _ hm).2.1 rfl
        · exact (hI.regs _ hm).2.2.1 rfl
        · exact (hI.regs _ hm).2.2.2 rfl
        · exact hCWi hm
    have hl1 : r1.w "lvl" = l := by rw [hreg1 _ (hnotCW _ (by simp))]; simp [hR.rl]
    have hn1 : r1.w "n" = n := by rw [hreg1 _ (hnotCW _ (by simp))]; simp [hR.rn]
    have hj1 : r1.w "sp.j" = mks[i] := by rw [hreg1 _ (hnotCW _ (by simp))]; simp
    have hi1 : r1.w "sp.i" = i := by rw [hreg1 _ (hnotCW _ (by simp))]; simp [hR.ri]
    have hwa1 : r1.wa = t.wa := funext fun a => (hU1.warr a (by simp)).1
    have hcap1 : r1.cap = t.cap := by rw [hU1.cap]; simp
    have hidx : l * n + mks[i] < (l + 1) * n := row_index_lt hjn
    have hgpl : l * n + mks[i] < r1.wlen "sp.gp" := by
      rw [hwl1]; simp only [State.charge_wlen, State.setW_wlen]; have := hGt.len_gp; omega
    -- the pivot store
    apply runs_seq
    refine runs_wstore (j := l * n + mks[i]) (a := r1.w "sp.b")
      (by simp [cr, evalW_add', evalW_mul', hl1, hn1, hj1, fit_of_lt (show l * n < r1.cap by rw [hcap1]; omega),
        fit_of_lt (show l * n + mks[i] < r1.cap by rw [hcap1]; omega)]) rfl hgpl ?_
    -- `px := sp.b`
    apply runs_seq
    refine runs_wset rfl ?_
    set r3 := (((r1.storeW "sp.gp" (l * n + mks[i]) (r1.w "sp.b")).charge 1).setW "px"
      (((r1.storeW "sp.gp" (l * n + mks[i]) (r1.w "sp.b")).charge 1).w "sp.b")).charge 1 with hr3
    have hbn' : r1.w "sp.b" < G.n := hnG ▸ hbn
    set v : Fin G.n := ⟨r1.w "sp.b", hbn'⟩ with hv
    have hU13 : Unchanged r1 r3 ["sp.gp"] [] ["px"] [] :=
      ((U_storeW r1 "sp.gp" _ _ (by simp)).trans (U_setW _ _ _ (by simp)))
    have hUt3 : Unchanged t r3 ["sp.gp"] [] (rsRegs ++ CW) CV := by
      refine ((hUt1.mono (by simp) (by simp) (fun a ha => hFt a (by simp at ha; simp [ha])) (by simp)).trans
        (hU1.mono (by simp) (by simp) (fun a ha => by
          rcases List.mem_append.mp ha with h | h
          · exact List.mem_append_left _ (by simp [rsRegs, h])
          · exact List.mem_append_right _ h) (List.Subset.refl _))).trans
        (hU13.mono (by simp) (by simp) (fun a ha => by simp at ha; subst ha; simp [rsRegs]) (by simp))
    have hDR3 := hDRf t r3 _ _ hDt hUt3 (by
      have e1 : r3.cost = r1.cost + 2 := by simp [hr3]
      simp only [State.charge_cost, State.setW_cost] at hc1a; omega)
    have hpx3 : r3.w "px" = (v : ℕ) := by simp [hr3, hv]
    -- the resource budget of this insertion, from a completion of the current choice
    have hres3 : res r3 = res t := hIns.res_frame t r3 _ _ _ _ hUt3 (fun a ha => hIWr a ha)
    have hpv' : ∀ j ∈ mks.take (i + 1), 0 < (P j).card →
        Function.update piv' mks[i] (r1.w "sp.b") j ∈ P j ∧
          ∀ x ∈ P j, κ (Function.update piv' mks[i] (r1.w "sp.b") j) ≤ κ x := by
      intro j hj hc
      rcases (hmemI j).mp hj with hj' | rfl
      · have hjne : j ≠ mks[i] := fun e => hjnot (e ▸ hj')
        rw [Function.update_of_ne hjne]; exact hmin j hj' hc
      · simp only [Function.update_self]; exact ⟨hbP, hbmin⟩
    have hLv : (L ++ [v]).map Fin.val = (mks.take (i + 1)).filterMap
        (fun j => if 0 < (P j).card then some (Function.update piv' mks[i] (r1.w "sp.b") j) else none) := by
      rw [List.map_append, hLf, filterMap_take_succ _ _ hi]
      congr 1
      · refine List.filterMap_congr (fun j hj => ?_)
        have hjne : j ≠ mks[i] := fun e => hjnot (e ▸ hj)
        simp [Function.update_of_ne hjne]
      · simp [hcard1, hv]
    obtain ⟨pf, hpf, hpfeq⟩ := exists_completion P κ mks (i + 1) _ hpv'
    have hLdn : ∀ x ∈ (mks.drop (i + 1)).filterMap
        (fun j => if 0 < (P j).card then some (pf j) else none), x < G.n := by
      intro x hx
      obtain ⟨j, hj, hjx⟩ := List.mem_filterMap.mp hx
      have hjm : j ∈ mks := List.mem_of_mem_drop hj
      by_cases hc : 0 < (P j).card
      · rw [if_pos hc, Option.some.injEq] at hjx
        rw [← hjx, ← hnG]
        exact ((GrpRep.mem_iff hG0 (hmp j hjm)).mp (hpf j hjm hc).1).1
      · rw [if_neg hc] at hjx; exact absurd hjx (by simp)
    obtain ⟨R, hR'⟩ := exists_fin_list _ hLdn
    have hmapf : ((L ++ [v]) ++ R).map Fin.val =
        mks.filterMap (fun j => if 0 < (P j).card then some (pf j) else none) := by
      rw [List.map_append, hLv, hR']
      conv_rhs => rw [← List.take_append_drop (i + 1) mks]
      rw [List.filterMap_append]
      congr 1
      exact List.filterMap_congr (fun j hj => by rw [hpfeq j hj])
    have hbr := hres pf _ hpf hmapf
    have hpre := insManyC_prefix_le T f (L ++ [v]) R g D
    have hLsn := insManyC_snoc T f v L g D
    have hcsn : (insManyC (dlOps G s) T f (L ++ [v]) g D).2.2 = (insManyC (dlOps G s) T f L g D).2.2 +
        (BM.insC (dlOps G s) T (insManyC (dlOps G s) T f L g D).1 (insManyC (dlOps G s) T f L g D).2.1 v
          (f v)).2.2 := by rw [hLsn]
    have hrb : res r3 + ((BM.insC (dlOps G s) T (insManyC (dlOps G s) T f L g D).1
        (insManyC (dlOps G s) T f L g D).2.1 v (f v)).2.2 + 1) ≤ rcap := by
      rw [hres3]
      simp only [List.length_append, List.length_singleton] at hbr
      omega
    refine (hIns.run r3 _ _ v hDR3 (hInv L (by omega)) (hvok _ (List.getElem_mem hi) _ hbP hbn') hpx3
      hrb).mono (fun r4 hr4 => ?_)
    obtain ⟨hD4, hU4, hwl4', hvl4', hc4a, hc4b, hres4⟩ := hr4
    have hIWn : ∀ y, y ∈ ["lvl", "n", "sp.i"] → y ∉ IW := by
      intro y hy hm
      obtain ⟨h1', h2', h3'⟩ := hIns.regs y hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact h2' rfl
      · exact h3' rfl
      · exact h1' rfl
    have hi4 : r4.w "sp.i" = i := by rw [hU4.wreg _ (hIWn _ (by simp))]; simp [hr3, hi1]
    have hcap4 : r4.cap = t.cap := by rw [hU4.cap]; simp [hr3, hcap1]
    refine runs_wset (evalW_add_of (x := i) (y := 1) (by simp [hi4]) (evalW_lit_of (by rw [hcap4]; omega))
      (by rw [hcap4]; omega)) ?_
    -- the state after `sp.i := i + 1`
    have hgpIA : "sp.gp" ∉ IA := fun h => (hIns.arrs _ h).1 (by simp [grpArrs])
    have hmkIA : "sp.mk" ∉ IA := fun h => (hIns.arrs _ h).2.1 rfl
    have hmklIA : "sp.mk.len" ∉ IA := fun h => (hIns.arrs _ h).2.2 rfl
    have hr3wa : ∀ a q, r3.wa a q = if a = "sp.gp" ∧ q = l * n + mks[i] then r1.w "sp.b" else t.wa a q := by
      intro a q; simp [hr3, hwa1]
    have hwl3 : r3.wlen = t.wlen := by
      rw [hr3]; simp only [State.charge_wlen, State.setW_wlen, State.storeW_wlen]; rw [hwl1]
      simp only [State.charge_wlen, State.setW_wlen]
    have hwa4 : ∀ a, a ∉ IA → ∀ q, r4.wa a q = r3.wa a q := fun a ha q => congrFun (hU4.warr a ha).1 q
    have hwl4 : ∀ a, a ∉ IA → r4.wlen a = t.wlen a := fun a ha => by rw [(hU4.warr a ha).2, hwl3]
    have hLsnoc := insManyC_snoc T f v L g D
    have hpiv_ne : ∀ j, j ≠ mks[i] → Function.update piv' mks[i] (r1.w "sp.b") j = piv' j :=
      fun j hj => Function.update_of_ne hj _ _
    have hUr1u : Unchanged r1 ((r4.setW "sp.i" (i + 1)).charge 1) ("sp.gp" :: IA) IVA ("px" :: IW ++ ["sp.i"])
        IVR :=
      ((hU13.mono (by simp) (by simp) (by simp) (by simp)).trans
        (hU4.mono (fun a ha => List.mem_cons_of_mem _ ha) (List.Subset.refl _)
          (fun a ha => by simp [ha]) (List.Subset.refl _))).trans (U_setW _ _ _ (by simp))
    refine ⟨by simp, ?_, ?_, by omega,
      ⟨Function.update piv' mks[i] (r1.w "sp.b"), L ++ [v], ?_, fun j hj hc => ?_, fun j hj => ?_, ?_, ?_, ?_,
        ?_⟩,
      ?_, ?_, ?_, fun q hq => ?_, ?_, ?_, ?_⟩
    · simp only [State.charge_w, State.setW_w]
      rw [if_neg (by decide), hU4.wreg _ (hIWn _ (by simp))]; simp [hr3, hl1]
    · simp only [State.charge_w, State.setW_w]
      rw [if_neg (by decide), hU4.wreg _ (hIWn _ (by simp))]; simp [hr3, hn1]
    · -- the groups with the new pivot
      refine GrpRep.of_arrays' hGt (fun a ha => ?_) (fun a ha => ?_) (fun j hj => ?_)
      · have ha' : a ∉ IA := fun h => (hIns.arrs a h).1 (by simp at ha; simp [grpArrs]; tauto)
        have hne : a ≠ "sp.gp" := by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
        funext q
        simp only [State.charge_wa, State.setW_wa]
        rw [hwa4 a ha' q, hr3wa, if_neg (by rintro ⟨h, -⟩; exact hne h)]
      · have ha' : a ∉ IA := fun h => (hIns.arrs a h).1 ha
        simp only [State.charge_wlen, State.setW_wlen]
        exact hwl4 a ha'
      · simp only [State.charge_wa, State.setW_wa]
        rw [hwa4 _ hgpIA, hr3wa]
        by_cases hjj : j = mks[i]
        · subst hjj; simp
        · rw [if_neg (by rintro ⟨-, h⟩; omega), hpiv_ne j hjj]; exact hGt.pivs j hj
    · rcases (hmemI j).mp hj with hj' | rfl
      · have hjne : j ≠ mks[i] := fun e => hjnot (e ▸ hj')
        rw [hpiv_ne j hjne]; exact hmin j hj' hc
      · simp only [Function.update_self]; exact ⟨hbP, hbmin⟩
    · have hjne : j ≠ mks[i] := fun e => hj ⟨(hmemI j).mpr (Or.inr e), e ▸ hcard1⟩
      rw [hpiv_ne j hjne]
      apply hkeep j
      rintro ⟨hj1, hj2⟩
      exact hj ⟨(hmemI j).mpr (Or.inl hj1), hj2⟩
    · rw [List.map_append, hLf, filterMap_take_succ _ _ hi]
      congr 1
      · refine List.filterMap_congr (fun j hj => ?_)
        have hjne : j ≠ mks[i] := fun e => hjnot (e ▸ hj)
        simp [hpiv_ne j hjne]
      · simp [hcard1, hv]
    · rw [hLsnoc]
      exact hDRf _ _ _ _ hD4 (U_setW _ _ _ (by exact hFt _ (by simp))) (by simp)
    · rw [hLsnoc]
      simp only [State.charge_cost, State.setW_cost, List.length_append, List.length_singleton]
      have e1 : r3.cost = r1.cost + 2 := by simp [hr3]
      have e2 : gl ((((t.charge 1).setW "sp.j" mks[i]).charge 1).charge 1) l n mks[i] = gl st l n mks[i] :=
        hglT _
      rw [e2] at hc1b
      simp only [State.charge_cost, State.setW_cost] at hc1b
      have eA : (((mks.take i).map (gl st l n)).sum + gl st l n mks[i]) * (C + 8) =
          ((mks.take i).map (gl st l n)).sum * (C + 8) + gl st l n mks[i] * (C + 8) := Nat.add_mul _ _ _
      have eB : K * ((insManyC (dlOps G s) T f L g D).2.2 + (BM.insC (dlOps G s) T (insManyC (dlOps G s) T f L g D).1
          (insManyC (dlOps G s) T f L g D).2.1 v (f v)).2.2) = K * (insManyC (dlOps G s) T f L g D).2.2 +
          K * (BM.insC (dlOps G s) T (insManyC (dlOps G s) T f L g D).1
          (insManyC (dlOps G s) T f L g D).2.1 v (f v)).2.2 := Nat.mul_add _ _ _
      have eC : (L.length + 1) * (Ci + 3) = L.length * (Ci + 3) + (Ci + 3) := by ring
      rw [htakeS, eA, eB, eC]
      omega
    · rw [hIns.res_frame _ _ _ _ _ _ (U_setW (va := []) (vr := []) (wa := []) r4 "sp.i" (i + 1)
        (wr := ["sp.i"]) (by simp)) (fun a ha => by simp at ha; subst ha; exact hIWn _ (by simp))]
      simp only [List.length_append, List.length_singleton]
      rw [hcsn]
      omega
    · exact hKRf r1 _ hKr1 (hUr1u.mono (List.Subset.refl _) (List.Subset.refl _) (fun a ha => by
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | ha | rfl
        · simp [rsRegs]
        · exact List.mem_append_right _ ha
        · simp [rsRegs]) (List.Subset.refl _)) (by
          simp only [State.charge_cost, State.setW_cost]
          have e1 : r3.cost = r1.cost + 2 := by simp [hr3]
          omega)
    · refine RowRep.of_eq hR.mkrow ?_ ?_ ?_ (fun q _ => ?_)
      · simp only [State.charge_wlen, State.setW_wlen]; exact hwl4 _ hmkIA
      · simp only [State.charge_wlen, State.setW_wlen]; exact hwl4 _ hmklIA
      · simp only [State.charge_wa, State.setW_wa]; rw [hwa4 _ hmklIA, hr3wa, if_neg (by rintro ⟨h, -⟩; exact absurd h (by decide))]
      · simp only [State.charge_wa, State.setW_wa]; rw [hwa4 _ hmkIA, hr3wa, if_neg (by rintro ⟨h, -⟩; exact absurd h (by decide))]
    · refine hR.unch.trans (((hUt1.mono (by simp) (by simp) ?_ (by simp)).trans
        (hU1.mono (by simp) (by simp) ?_ ?_)).trans (hUr1u.mono (by simp) (List.Subset.refl _) ?_ ?_))
      · intro a ha; simp at ha; subst ha; simp [rsRegs]
      · intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ (by simp [rsRegs, h]))
        · exact List.mem_append_left _ (List.mem_append_right _ h)
      · intro a ha; exact List.mem_append_left _ ha
      · intro a ha
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | ha | rfl
        · simp [rsRegs]
        · exact List.mem_append_right _ ha
        · simp [rsRegs]
      · intro a ha; exact List.mem_append_right _ ha
    · simp only [State.charge_wa, State.setW_wa]
      rw [hwa4 _ hgpIA, hr3wa, if_neg (by rintro ⟨-, h⟩; have := row_index_lt (l := l) hjn; omega)]
      exact hR.gpout q hq
    · simp only [State.charge_cost, State.setW_cost]
      have e1 : r3.cost = r1.cost + 2 := by simp [hr3]
      have := hR.lo
      simp only [State.charge_cost, State.setW_cost] at hc1a
      omega
    · simp only [State.charge_wlen, State.setW_wlen]
      rw [hwl4', hwl3, hR.wl]
    · simp only [State.charge_vlen, State.setW_vlen]
      rw [hvl4']
      have e1 : r3.vlen = r1.vlen := by simp [hr3]
      have e2 : r1.vlen = t.vlen := by
        rw [funext fun a => (hU1.varr a (by simp)).2]; simp
      rw [e1, e2, hR.vl]

end Step

/-! ## The re-selection loop and BM.23 -/

section LoopSpec

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

open Frontier.CHD.BM Frontier.CHD.RamInit

theorem ev_rowlen {st : State V} {arr len : String} {l n : ℕ} {xs : List ℕ} (hl : st.w "lvl" = l)
    (hR : RowRep st arr len n l xs) : evalW st (load len (var "lvl")) = some xs.length := by
  obtain ⟨-, -, h3, h4, -⟩ := hR
  simp [hl, h3, h4]

/-- **BM.23** (`reselect cmp dsIns`, agent-08's text by `ramSpine_reselect_eq`): every marked group that is
still nonempty gets a key-minimal member as its new pivot, which is inserted into `D` (in mark order);
all other pivots are kept. -/
theorem reselect_spec {β : Type*} [LinearOrder β] {cmp dsIns : Stmt} {KR : State V → Prop} {κ : ℕ → β}
    {dom : ℕ → Prop} {C Bud : ℕ} {CW CV FA FR : List String}
    {DR : State V → DGl G s → DStrM G s → Prop} {Inv : DGl G s → DStrM G s → Prop}
    {f : Fin G.n → WLab G s} {T K Ci : ℕ} {IA IVA IW IVR : List String}
    (hI : CmpI ops cmp KR κ dom C Bud CW CV FA FR) (hFR : ∀ a ∈ gmRegs ++ CW, a ∈ FR)
    (hCWi : "sp.i" ∉ CW)
    {vok : Fin G.n → Prop} {res : State V → ℕ} {rcap : ℕ}
    (hIns : InsI ops dsIns DR Inv vok res rcap f T K Ci IA IVA IW IVR)
    (hDRf : ∀ st r g D, DR st g D → Unchanged st r ["sp.gp"] [] (rsRegs ++ CW) CV → st.cost ≤ r.cost →
      DR r g D)
    (hKRf : ∀ st r, KR st → Unchanged st r ("sp.gp" :: IA) IVA (rsRegs ++ IW) IVR → st.cost ≤ r.cost → KR r)
    (hIWr : ∀ a ∈ rsRegs ++ CW, a ∉ IW)
    {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} {mks : List ℕ} {g : DGl G s}
    {D : DStrM G s}
    (hl : st.w "lvl" = l) (hn : st.w "n" = n) (hG0 : GrpRep st l n p P piv) (hnG : n = G.n)
    (hmk : RowRep st "sp.mk" "sp.mk.len" n l mks) (hmnd : mks.Nodup) (hmp : ∀ j ∈ mks, j < p)
    (hdom : ∀ j ∈ mks, ∀ x ∈ P j, dom x) (hK : KR st) (hD : DR st g D)
    (hvok : ∀ j ∈ mks, ∀ x ∈ P j, ∀ h : x < G.n, vok ⟨x, h⟩)
    (hres : ∀ (pf : ℕ → ℕ) (Lf : List (Fin G.n)),
      (∀ j ∈ mks, 0 < (P j).card → pf j ∈ P j ∧ ∀ x ∈ P j, κ (pf j) ≤ κ x) →
      Lf.map Fin.val = mks.filterMap (fun j => if 0 < (P j).card then some (pf j) else none) →
      res st + (insManyC (dlOps G s) T f Lf g D).2.2 + Lf.length ≤ rcap)
    (hInv : ∀ L : List (Fin G.n), L.length ≤ mks.length →
      Inv (insManyC (dlOps G s) T f L g D).1 (insManyC (dlOps G s) T f L g D).2.1)
    (hcap : (l + 1) * n + 2 < st.cap)
    (hbud : ∀ L : List (Fin G.n), L.length ≤ mks.length →
      st.cost + 3 + mks.length * 8 + (mks.map (gl st l n)).sum * (C + 8) +
        K * (insManyC (dlOps G s) T f L g D).2.2 + L.length * (Ci + 3) ≤ Bud) :
    Runs ops (reselect cmp dsIns) st (fun r => ∃ (piv' : ℕ → ℕ) (L : List (Fin G.n)),
      GrpRep r l n p P piv' ∧
      (∀ j ∈ mks, 0 < (P j).card → piv' j ∈ P j ∧ ∀ x ∈ P j, κ (piv' j) ≤ κ x) ∧
      (∀ j, ¬ (j ∈ mks ∧ 0 < (P j).card) → piv' j = piv j) ∧
      L.map Fin.val = mks.filterMap (fun j => if 0 < (P j).card then some (piv' j) else none) ∧
      DR r (insManyC (dlOps G s) T f L g D).1 (insManyC (dlOps G s) T f L g D).2.1 ∧
      KR r ∧ RowRep r "sp.mk" "sp.mk.len" n l mks ∧
      Unchanged st r ("sp.gp" :: IA) IVA (rsRegs ++ CW ++ IW) (CV ++ IVR) ∧ r.wlen = st.wlen ∧
      r.vlen = st.vlen ∧
      (∀ q, (q < l * n ∨ (l + 1) * n ≤ q) → r.wa "sp.gp" q = st.wa "sp.gp" q) ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 3 + mks.length * 8 + (mks.map (gl st l n)).sum * (C + 8) +
        K * (insManyC (dlOps G s) T f L g D).2.2 + L.length * (Ci + 3) ∧
      res r ≤ res st + (insManyC (dlOps G s) T f L g D).2.2 + L.length) := by
  have h1 : 1 < st.cap := by omega
  unfold reselect
  apply runs_seq
  refine runs_wset (evalW_lit_of (by omega)) ?_
  set s0 := (st.setW "sp.i" 0).charge 1 with hs0
  have hU0 : Unchanged st s0 [] [] ["sp.i"] [] := U_setW st "sp.i" 0 (by simp)
  have hgl0 : ∀ q, gl s0 l n q = gl st l n q := fun q => rfl
  have hG1 : GrpRep s0 l n p P piv := grpRep_of_eq hG0 (fun _ _ => rfl) (fun _ _ => rfl)
  have hbud' : ∀ L : List (Fin G.n), L.length ≤ mks.length →
      s0.cost + 1 + mks.length * 8 + (mks.map (gl s0 l n)).sum * (C + 8) +
        K * (insManyC (dlOps G s) T f L g D).2.2 + L.length * (Ci + 3) ≤ Bud := by
    intro L hL
    have := hbud L hL
    have e : s0.cost = st.cost + 1 := by simp [hs0]
    have hg : gl s0 l n = gl st l n := rfl
    rw [e, hg]
    omega
  have hres0 : res s0 = res st :=
    hIns.res_frame st s0 _ _ _ _ hU0 (fun a ha => by simp at ha; subst ha; exact hIWr _ (by simp [rsRegs]))
  have hres' : ∀ (pf : ℕ → ℕ) (Lf : List (Fin G.n)),
      (∀ j ∈ mks, 0 < (P j).card → pf j ∈ P j ∧ ∀ x ∈ P j, κ (pf j) ≤ κ x) →
      Lf.map Fin.val = mks.filterMap (fun j => if 0 < (P j).card then some (pf j) else none) →
      res s0 + (insManyC (dlOps G s) T f Lf g D).2.2 + Lf.length ≤ rcap := fun pf Lf h1 h2 => by
    rw [hres0]; exact hres pf Lf h1 h2
  unfold rsLoop
  refine (runs_while (fun i t => RSInv s0 l n p P piv mks κ KR DR f T g D C K Ci IA IVA IW IVR CW CV res i t)
    mks.length _ ?_ ?_ s0 ?_)
  · intro i hi t hR
    have ht1 : 1 < t.cap := by rw [hR.unch.cap]; simp [hs0]; omega
    refine ⟨1, ?_, one_ne_zero, rsStep hI hFR hCWi hIns hDRf hKRf hIWr hG1 hnG hmnd hmp hdom hvok hres'
      hInv (by simp [hs0]; omega) hbud' hR hi⟩
    rw [evalW_lt_of (x := i) (y := mks.length) (by simp [hR.ri]) (ev_rowlen hR.rl hR.mkrow) ht1, if_pos hi]
  · intro t hR
    have ht1 : 1 < t.cap := by rw [hR.unch.cap]; simp [hs0]; omega
    obtain ⟨piv', L, hGt, hmin, hkeep, hLf, hDt, hct, hrs⟩ := hR.ex
    have htake : mks.take mks.length = mks := List.take_length
    rw [htake] at hmin hLf hct
    refine ⟨?_, piv', L, grpRep_of_eq hGt (fun _ _ => rfl) (fun _ _ => rfl), hmin, fun j hj => hkeep j (by
        rw [htake]; exact hj), hLf, hDRf _ _ _ _ hDt (Unchanged.charge t 1 _ _ _ _) (by simp),
      hKRf t _ hR.kr (Unchanged.charge t 1 _ _ _ _) (by simp), RowRep.of_eq hR.mkrow rfl rfl rfl (fun _ _ => rfl),
      (hU0.mono (by simp) (by simp) (by simp [rsRegs]) (by simp)).trans (hR.unch.trans (Unchanged.charge t 1 _ _ _ _)),
      by simp [hR.wl, hs0], by simp [hR.vl, hs0], fun q hq => hR.gpout q hq, ?_, ?_, ?_⟩
    · rw [evalW_lt_of (x := mks.length) (y := mks.length) (by simp [hR.ri]) (ev_rowlen hR.rl hR.mkrow) ht1]
      simp
    · have := hR.lo; simp [hs0] at this ⊢; omega
    · simp only [State.charge_cost]
      have e : s0.cost = st.cost + 1 := by simp [hs0]
      have hg : gl s0 l n = gl st l n := rfl
      rw [e, hg] at hct
      omega
    · rw [hIns.res_frame _ _ _ _ _ _ (Unchanged.charge t 1 [] [] [] []) (by simp), ← hres0]; exact hrs
  · exact ⟨by simp [hs0], by simp [hs0, hl], by simp [hs0, hn], Nat.zero_le _,
      ⟨piv, [], hG1, fun j hj => by simp at hj, fun _ _ => rfl, by simp,
        (by simpa [insManyC] using (hDRf st s0 g D hD (hU0.mono (by simp) (by simp) (by
          intro a ha; simp at ha; subst ha; simp [rsRegs]) (by simp)) (by simp [hs0]))), by simp [insManyC],
        by simp [insManyC]⟩,
      hKRf st s0 hK (hU0.mono (by simp) (by simp) (by
          intro a ha; simp at ha; subst ha; simp [rsRegs]) (by simp)) (by simp [hs0]),
      RowRep.of_eq hmk rfl rfl rfl (fun _ _ => rfl), Unchanged.refl _ _ _ _ _, fun _ _ => rfl, le_rfl, rfl, rfl⟩

end LoopSpec

end Frontier.CHD.RamSpineU
