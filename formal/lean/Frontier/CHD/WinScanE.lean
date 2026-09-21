import Frontier.CHD.WinScanD
import Frontier.CHD.ExecLen

/-!
# WinScanE — the window scans over an ABSTRACT D layer (agent-02, NON-GATE)

The spine represents the lazy structures of all active levels by agent-08's abstract `DLayer`
(`DR st H g Ds lo`, instantiated by B-L3 with `DLRep`), and inserts through its `ins` procedure.
Here the per-edge relaxation calls that `ins`:

  `relaxWinD ins := relaxBM; if ok then (lo test; if lab.ge then (px := lab.xv; ins))`

(`lab.xv` = the vertex of the candidate = `dst e`; after `relaxBM` its label IS the candidate).
`DInsI` collects the fields needed: `DR`, the footprints, the disjoint-footprint frame (the
orientation fixed by agent-03/06/07), `ins`/`ins_spec` (write set with value registers `dVR`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DIns Frontier.CHD.RelaxIns Frontier.CHD.RamBaseCase WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- Registers the relaxation with the `lo` test writes (besides the D layer's). -/
def rwW : List String := relaxW ++ ["lab.c1", "lab.c2", "lab.lolt", "lab.ge", "px"]

/-- Registers the D layer must not write. -/
def scanRegs : List String :=
  rwW ++ ["lab.uselo", "lvl", "n", "re", "ru", "sp.lt", "sp.p", "sp.pe", "sp.go", "sp.i"]

/-- **The D-layer insertion interface of the scans** (a sub-interface of agent-08's `DLayer`). -/
structure DInsI (G : Graph) (s : Fin G.n) (T : ℕ → ℕ) where
  DR : State ℝ≥0 → (Fin G.n → ℕ → List (Fin G.m)) → BM.DGl G s → (ℕ → BM.DStrM G s) → ℕ → Prop
  dWA : List String
  dVA : List String
  dWR : List String
  dVR : List String
  frame : ∀ (st r : State ℝ≥0) (H H' : Fin G.n → ℕ → List (Fin G.m)) (g : BM.DGl G s)
    (Ds : ℕ → BM.DStrM G s) (lo : ℕ) (wa va wr vr : List String), DR st H g Ds lo →
    Unchanged st r wa va wr vr → (∀ a ∈ wa, a ∉ dWA) → (∀ a ∈ va, a ∉ dVA) →
    (∀ a ∈ wr, a ∉ dWR) → (∀ a ∈ vr, a ∉ dVR) → HExt H (vc st) H' (vc r) → DR r H' g Ds lo
  K : ℕ
  /-- the D layer's used capacity (Layer-A units) and its bound (agent-04's R2) -/
  use : State ℝ≥0 → ℕ
  ucap : ℕ
  /-- `use` reads only the D layer's registers -/
  use_frame : ∀ (st r : State ℝ≥0) (wa va wr vr : List String), Unchanged st r wa va wr vr →
    (∀ a ∈ wr, a ∉ dWR) → use r = use st
  ins : Stmt
  ins_spec : ∀ (st : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (g : BM.DGl G s)
    (Ds : ℕ → BM.DStrM G s) (l : ℕ) (d : Labels G s) (c0 : ℕ) (v : Fin G.n),
    DR st H g Ds l → LabAt st d H c0 → st.w "lvl" = l → st.w "n" = G.n → st.w "px" = v →
    d v < (Ds l).Bd →
    use st + ((BM.insC (BM.dlOps G s) (T l) g (Ds l) v (d v)).2.2 + 1) ≤ ucap →
    Runs realOps ins st (fun r =>
      DR r H (BM.insC (BM.dlOps G s) (T l) g (Ds l) v (d v)).1
        (Function.update Ds l (BM.insC (BM.dlOps G s) (T l) g (Ds l) v (d v)).2.1) l ∧
      Unchanged st r dWA dVA dWR dVR ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + K * ((BM.insC (BM.dlOps G s) (T l) g (Ds l) v (d v)).2.2 + 1) ∧
      use r ≤ use st + ((BM.insC (BM.dlOps G s) (T l) g (Ds l) v (d v)).2.2 + 1))
  hwa : ∀ a ∈ dWA, a ∉ labW ++ ["gSt", "gHead", "sp.ptr"]
  hva : ∀ a ∈ dVA, a ∉ labV ++ ["gW"]
  hwr : ∀ a ∈ dWR, a ∉ scanRegs
  hvr : ∀ a ∈ dVR, a ∉ relaxV

/-- One relaxation with insertion through the D layer's `ins`. -/
def relaxWinD (ins : Stmt) (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Stmt :=
  seq (relaxBM Kb kbf)
  (ite (var "ok")
    (seq (loTest Klo klof) (ite (var "lab.ge") (seq (wset "px" (var "lab.xv")) ins) skip))
    skip)

open Classical in
/-- The `lo` test (`lab.uselo ≠ 0`): `lab.ge := [b ≤ cand]`. -/
theorem loTest_some {st : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    (hH : GoodHist (s := s) H V) {x : MLabel G} {p : List (Fin G.m)} (hx : Holds st X0 x)
    (hxp : Rep (s := s) H V x p) {Klo : LReg} {klof : String} (hLor : BoundRegs Klo klof)
    {b : WLab G s} (hLo : WHolds st Klo klof H V b) (hul : st.w "lab.uselo" ≠ 0)
    (hcap : 1 < st.cap) :
    Runs realOps (loTest Klo klof) st (fun q =>
      q.w "lab.ge" = (if b ≤ ((toW p : WalkOrd G s) : WLab G s) then 1 else 0) ∧
      Unchanged st q [] [] ["lab.c1", "lab.c2", "lab.lolt", "lab.ge"] [] ∧
      st.cost + 1 ≤ q.cost ∧ q.cost ≤ st.cost + 16) := by
  rw [loTest]
  apply runs_ite_true (by simp : evalW st (WExpr.var "lab.uselo") = some (st.w "lab.uselo")) hul
  have hc1' : "lab.c1" ∉ Klo.ws := fun h => hLor.ws _ h (by decide)
  have hc2' : "lab.c2" ∉ Klo.ws := fun h => hLor.ws _ h (by decide)
  have hLoc : WHolds (st.charge 1) Klo klof H V b :=
    hLo.of_unchanged (Unchanged.charge st 1 [] [] [] []) (by simp) (by simp) (by simp)
  apply runs_seq
  apply wp_sound
  refine wp_mono _ ?_ _ (ltB_wp X0 Klo klof "lab.c1" "lab.c2" "lab.lolt"
    ⟨by decide, by decide, by decide, hc1', hc2'⟩ (st.charge 1) (by simpa using hcap))
  rintro q1 ⟨hlt1, hUl, hcl1, hcl2⟩
  have hbit := ltB_bit (V := V) hH (hx.charge 1) hxp hLoc
  rw [hbit] at hlt1
  apply wp_sound
  refine wp_mono _ ?_ _ (wset_eqz_wp (ops := realOps) "lab.ge" "lab.lolt" q1
    (by rw [hUl.cap]; simpa using hcap))
  rintro q ⟨h1, h2, h3⟩
  refine ⟨?_, (((Unchanged.charge st 1 [] [] [] []).comp hUl).comp h2).mono (by simp)
    (by simp) (by decide) (by simp), by simp at hcl1 h3 ⊢; omega, by simp at hcl2 h3 ⊢; omega⟩
  rw [h1, hlt1]
  by_cases hle : b ≤ ((toW p : WalkOrd G s) : WLab G s)
  · rw [if_neg (not_lt.mpr hle), if_pos rfl, if_pos hle]
  · rw [if_pos (lt_of_not_ge hle), if_neg one_ne_zero, if_neg hle]

/-- The machine state `r` represents the scan state `fs` over the abstract D layer: the level-`l`
structure is `fs.Dc`, the other levels are `Ds`. -/
structure RepsD {T : ℕ → ℕ} (DI : DInsI G s T) (l : ℕ) (Ds : ℕ → BM.DStrM G s) (c0 : ℕ)
    (B Bi : WLab G s) (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String)
    (r : State ℝ≥0) (fs : BM.RSt G s) (H' : Fin G.n → ℕ → List (Fin G.m)) : Prop where
  lab : LabAt r fs.d H' c0
  dr : DI.DR r H' fs.g (Function.update Ds l fs.Dc) l
  wk : WalkInv fs.d
  gr : GraphAt r G
  csr : CSRAt r G
  kb : WHolds r Kb kbf H' (vc r) B
  klo : WHolds r Klo klof H' (vc r) Bi
  uselo : r.w "lab.uselo" ≠ 0
  lvl : r.w "lvl" = l
  nn : r.w "n" = G.n
  bd : fs.Dc.Bd = B

/-- Steps outside the label table, the D layer, the graph and the bound registers keep `RepsD`. -/
theorem RepsD.of_unch {T : ℕ → ℕ} {DI : DInsI G s T} {l : ℕ} {Ds : ℕ → BM.DStrM G s} {c0 : ℕ}
    {B Bi : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    {r r' : State ℝ≥0} {fs : BM.RSt G s} {H' : Fin G.n → ℕ → List (Fin G.m)}
    {wa va wr vr : List String}
    (h : RepsD DI l Ds c0 B Bi Kb kbf Klo klof r fs H') (hu : Unchanged r r' wa va wr vr)
    (hc : r.cost ≤ r'.cost) (hwl : ∀ a ∈ labW, a ∉ wa) (hvl : "dlen" ∉ va)
    (hg1 : "gHead" ∉ wa) (hg2 : "gW" ∉ va) (hg3 : "gSt" ∉ wa)
    (hwD : ∀ a ∈ wa, a ∉ DI.dWA) (hvD : ∀ a ∈ va, a ∉ DI.dVA) (hrD : ∀ a ∈ wr, a ∉ DI.dWR)
    (hvrD : ∀ a ∈ vr, a ∉ DI.dVR)
    (hK : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "lvl", "n"], a ∉ wr)
    (hKl : Kb.l ∉ vr ∧ Klo.l ∉ vr) :
    RepsD DI l Ds c0 B Bi Kb kbf Klo klof r' fs H' := by
  have hvc : vc (G := G) r' = vc r := vc_of_unchanged hu (hwl _ (by decide))
  have hm : ∀ a, a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "lvl", "n"] →
      a ∉ wr := hK
  refine ⟨h.lab.of_unchanged hu hwl hvl hc, ?_, h.wk, graphAt_of_unchanged hu hg1 hg2 h.gr,
    CSRAt.of_unchanged h.csr hu hg3, ?_, ?_,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.uselo,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.lvl,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.nn, h.bd⟩
  · exact DI.frame r r' H' H' _ _ l wa va wr vr h.dr hu hwD hvD hrD hvrD
      (by rw [hvc]; exact HExt.refl _ _)
  · rw [hvc]
    exact h.kb.of_unchanged hu (fun a ha => hm a (by simp [ha])) hKl.1 (hm _ (by simp))
  · rw [hvc]
    exact h.klo.of_unchanged hu (fun a ha => hm a (by simp [ha])) hKl.2 (hm _ (by simp))

open Classical in
theorem relaxInsCc_blocks {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} (st : BM.RSt G s)
    (e : Fin G.m) :
    (BM.relaxInsCc (BM.dlOps G s) T B lo st e).Dc.blocks.length = st.Dc.blocks.length := by
  unfold BM.relaxInsCc
  by_cases hv : BM.ValidRelax G s st.d B e
  · rw [if_pos hv]
    have hBl := insC_Bd (T := T) st.g st.Dc (G.dst e) (ext (st.d (G.src e)) e)
    cases lo with
    | none => exact hBl.2
    | some b =>
      by_cases hb : b ≤ ext (st.d (G.src e)) e
      · simp only [if_pos hb]; exact hBl.2
      · simp only [if_neg hb]
  · rw [if_neg hv]

/-- Labels, block count and complete labels along a fold, without the concrete `DInv`. -/
theorem foldl_invs' {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} :
    ∀ (L : List (Fin G.m)) (st : BM.RSt G s), WalkInv st.d →
      WalkInv (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).d ∧
      (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).Dc.blocks.length = st.Dc.blocks.length ∧
      ∀ u, st.d u = dis (s := s) u →
        (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).d u = st.d u
  | [], st, hw => ⟨hw, rfl, fun _ _ => rfl⟩
  | e :: L, st, hw => by
    obtain ⟨hw1, hs1⟩ := relaxInsCc_d_complete (T := T) (B := B) (lo := lo) st hw e
    obtain ⟨hw2, hb2, hs2⟩ := foldl_invs' (T := T) (B := B) (lo := lo) L _ hw1
    refine ⟨hw2, hb2.trans (relaxInsCc_blocks st e), fun u hu => ?_⟩
    simp only [List.foldl_cons]
    rw [hs2 u (by rw [hs1 u hu]; exact hu), hs1 u hu]

theorem insC_cost_le {T : ℕ} (g : BM.DGl G s) (Dc : BM.DStrM G s) (v : Fin G.n)
    (lam : WLab G s) :
    (BM.insC (BM.dlOps G s) T g Dc v lam).2.2 ≤ Nat.log 2 Dc.blocks.length + 4 := by
  rw [insC_dl_cost]
  unfold DL.bsCost
  split_ifs <;> omega

/-- Registers the scans write besides the D layer's. -/
def allW : List String := rwW ++ winW ++ ["ru", "sp.pe", "sp.i"]

/-- Register hygiene of the bound blocks w.r.t. the scan and the D layer. -/
structure BlkHygD {T : ℕ → ℕ} (DI : DInsI G s T) (Kb : LReg) (kbf : String) (Klo : LReg)
    (klof : String) : Prop where
  kb : BoundRegs Kb kbf
  klo : BoundRegs Klo klof
  w : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof], a ∉ allW ∧ a ∉ DI.dWR
  l : Kb.l ∉ DI.dVR ∧ Klo.l ∉ DI.dVR

theorem BlkHygD.hK {T : ℕ → ℕ} {DI : DInsI G s T} {Kb : LReg} {kbf : String} {Klo : LReg}
    {klof : String} (hy : BlkHygD DI Kb kbf Klo klof) {wr : List String}
    (hwr : ∀ a ∈ wr, a ∈ allW ∨ a ∈ DI.dWR) :
    ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "lvl", "n"], a ∉ wr := by
  intro a ha haw
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · rcases hwr a haw with h | h
    · exact (hy.w a ha).1 h
    · exact (hy.w a ha).2 h
  · have hsm : ∀ b ∈ ["lab.uselo", "lvl", "n"], b ∉ allW := by decide
    have h1 : a ∉ allW := hsm a ha
    have h2 : a ∉ DI.dWR := fun hd => DI.hwr a hd (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide)
    rcases hwr a haw with h | h
    · exact h1 h
    · exact h2 h

theorem RepsD.setc {T : ℕ → ℕ} {DI : DInsI G s T} {l : ℕ} {Ds : ℕ → BM.DStrM G s} {c0 : ℕ}
    {B Bi : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    {r : State ℝ≥0} {d : Labels G s} {g : BM.DGl G s} {Dc : BM.DStrM G s} {c c' : ℕ}
    {H' : Fin G.n → ℕ → List (Fin G.m)}
    (h : RepsD DI l Ds c0 B Bi Kb kbf Klo klof r ⟨d, g, Dc, c⟩ H') :
    RepsD DI l Ds c0 B Bi Kb kbf Klo klof r ⟨d, g, Dc, c'⟩ H' :=
  ⟨h.lab, h.dr, h.wk, h.gr, h.csr, h.kb, h.klo, h.uselo, h.lvl, h.nn, h.bd⟩

theorem lenEq_of_unch {a b : State ℝ≥0} {wr vr : List String} (h : Unchanged a b [] [] wr vr) :
    b.wlen = a.wlen ∧ b.vlen = a.vlen :=
  ⟨funext fun x => (h.warr x (by simp)).2, funext fun x => (h.varr x (by simp)).2⟩

open Classical in
/-- **One scanned edge over the abstract D layer**: `relaxWinD DI.ins` refines
`relaxInsCc dlOps (T l) B (some Bi) fs e`; RAM cost `≤ (89 + K) ×` the Layer-A cost. -/
theorem RepsD.step {T : ℕ → ℕ} (DI : DInsI G s T) {l : ℕ} {Ds : ℕ → BM.DStrM G s} {c0 : ℕ}
    {B Bi : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    (hy : BlkHygD DI Kb kbf Klo klof) {r : State ℝ≥0} {fs : BM.RSt G s}
    {H' : Fin G.n → ℕ → List (Fin G.m)} (h : RepsD DI l Ds c0 B Bi Kb kbf Klo klof r fs H')
    (e : Fin G.m) (hru : r.w "ru" = G.src e) (hre : r.w "re" = e) (hu : fs.d (G.src e) ≠ ⊤)
    (hB : r.cost + 64 ≤ c0 + r.cap) (hm : G.m + 2 ≤ r.cap)
    (huse : DI.use r + (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fs e).c ≤ DI.ucap + fs.c) :
    Runs realOps (relaxWinD DI.ins Kb kbf Klo klof) r (fun r' => ∃ H'',
      HExt H' (vc r) H'' (vc r') ∧
      RepsD DI l Ds c0 B Bi Kb kbf Klo klof r'
        (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fs e) H'' ∧
      Unchanged r r' (labW ++ DI.dWA) (labV ++ DI.dVA) (rwW ++ DI.dWR) (relaxV ++ DI.dVR) ∧
      r.cost ≤ r'.cost ∧
      r'.cost ≤ r.cost + 89 + DI.K * (Nat.log 2 fs.Dc.blocks.length + 5) ∧
      r'.cost + (89 + DI.K) * fs.c ≤
        r.cost + (89 + DI.K) * (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fs e).c ∧
      r'.wlen = r.wlen ∧ r'.vlen = r.vlen ∧
      DI.use r' + fs.c ≤ DI.use r + (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fs e).c) := by
  have hlW : ∀ a ∈ labW, a ∉ DI.dWA := fun a ha hd => DI.hwa a hd (List.mem_append_left _ ha)
  have hlV : ∀ a ∈ labV, a ∉ DI.dVA := fun a ha hd => DI.hva a hd (List.mem_append_left _ ha)
  have hsR : ∀ a ∈ scanRegs, a ∉ DI.dWR := fun a ha hd => DI.hwr a hd ha
  have hrV : ∀ a ∈ relaxV, a ∉ DI.dVR := fun a ha hd => DI.hvr a hd ha
  have hrW : ∀ a ∈ rwW, a ∉ DI.dWR := fun a ha => hsR a (List.mem_append_left _ ha)
  have hdlen : "dlen" ∉ DI.dVA := hlV _ (by decide)
  obtain ⟨p0, hp⟩ : ∃ p : List (Fin G.m), fs.d (G.src e) = ((toW p : WalkOrd G s) : WLab G s) := by
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hu
    exact ⟨q, hq.symm⟩
  have hext : ext (fs.d (G.src e)) e = ((toW (p0 ++ [e]) : WalkOrd G s) : WLab G s) :=
    cand_ext e hp
  have hcap1 : 1 < r.cap := by omega
  obtain ⟨hwk', -⟩ := relaxInsCc_d_complete (T := T l) (B := B) (lo := some Bi) fs h.wk e
  rw [relaxInsCc_d] at hwk'
  apply runs_seq
  refine (Runs.len (by rfl) (Frontier.CHD.LabIInst.Runs.cost_ge
    (relaxBM_spec r fs.d H' c0 h.lab h.gr e hru hre hu Kb kbf hy.kb B h.kb hB hm))).mono ?_
  rintro r1 ⟨⟨⟨H1, hL1, hE1, hok1, hX1, hrep1, hg1, hU1, hc1⟩, hc1lo⟩, hw1, hv1⟩
  -- the representation after the label step (labels `d1`, same `g`, `Dc`)
  have hvcr : ∀ q : State ℝ≥0, ∀ {wa va wr vr : List String}, Unchanged r1 q wa va wr vr →
      "vcnt" ∉ wa → vc (G := G) q = vc r1 := fun q _ _ _ _ hq hv => vc_of_unchanged hq hv
  have hR1 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof r1
      ⟨if BM.ValidRelax G s fs.d B e then
        Function.update fs.d (G.dst e) (ext (fs.d (G.src e)) e) else fs.d, fs.g, fs.Dc, fs.c⟩ H1 :=
    ⟨hL1, DI.frame r r1 H' H1 _ _ l labW labV relaxW relaxV h.dr hU1 hlW hlV
        (fun a ha => hrW a (List.mem_append_left _ ha)) hrV hE1, hwk', hg1,
      CSRAt.of_unchanged h.csr hU1 (by decide),
      (h.kb.ext hE1).of_unchanged hU1 hy.kb.ws hy.kb.l hy.kb.f,
      (h.klo.ext hE1).of_unchanged hU1 hy.klo.ws hy.klo.l hy.klo.f,
      by rw [hU1.wreg _ (by decide)]; exact h.uselo, by rw [hU1.wreg _ (by decide)]; exact h.lvl,
      by rw [hU1.wreg _ (by decide)]; exact h.nn, h.bd⟩
  -- the used capacity is unchanged by the label step and register writes
  have useR : ∀ (q : State ℝ≥0) (wr : List String), Unchanged r1 q [] [] wr [] →
      (∀ a ∈ wr, a ∈ rwW) → DI.use q = DI.use r := fun q wr hq hwr =>
    DI.use_frame r q _ _ _ _ (hU1.comp hq) (fun a ha => by
      rcases List.mem_append.mp ha with h' | h'
      · exact hrW a (List.mem_append_left _ h')
      · exact hrW a (hwr a h'))
  -- register-only continuations from `r1`
  have hreg : ∀ (q : State ℝ≥0) (wr : List String), Unchanged r1 q [] [] wr [] →
      (∀ a ∈ wr, a ∈ rwW) → r1.cost ≤ q.cost → ∀ c',
      RepsD DI l Ds c0 B Bi Kb kbf Klo klof q
        ⟨if BM.ValidRelax G s fs.d B e then
          Function.update fs.d (G.dst e) (ext (fs.d (G.src e)) e) else fs.d, fs.g, fs.Dc, c'⟩ H1 ∧
      Unchanged r q (labW ++ DI.dWA) (labV ++ DI.dVA) (rwW ++ DI.dWR) (relaxV ++ DI.dVR) ∧
      vc (G := G) q = vc r1 := by
    intro q wr hq hwr hcq c'
    refine ⟨(hR1.of_unch hq hcq (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (fun a ha => hrW a (hwr a ha)) (by simp)
      (hy.hK (fun a ha => Or.inl (List.mem_append_left _ (List.mem_append_left _ (hwr a ha)))))
      ⟨by simp, by simp⟩).setc, (hU1.comp hq).mono ?_ ?_ ?_ ?_, hvcr q hq (by simp)⟩
    · intro a ha; simp only [List.mem_append] at ha ⊢; simp at ha; tauto
    · intro a ha; simp only [List.mem_append] at ha ⊢; simp at ha; tauto
    · intro a ha
      simp only [List.mem_append] at ha ⊢
      rcases ha with ha | ha
      · left; simp only [rwW, List.mem_append]; left; exact ha
      · left; exact hwr a ha
    · intro a ha; simp only [List.mem_append] at ha ⊢; simp at ha; tauto
  by_cases hvr : BM.ValidRelax G s fs.d B e
  · -- valid: the lo test, then the insertion
    have hok : r1.w "ok" = 1 := by rw [hok1, if_pos hvr]
    simp only [if_pos hvr] at hR1 hreg
    rw [if_pos hvr] at hL1 hwk'
    apply runs_ite_true (by simp [hok] : evalW r1 (WExpr.var "ok") = some 1) one_ne_zero
    have hcand : Rep (s := s) H1 (vc r1) (cand (tabOf (G := G) r) e) (p0 ++ [e]) := hrep1 p0 hp
    have hXc : Holds (r1.charge 1) X0 (cand (tabOf (G := G) r) e) := hX1.charge 1
    have hul1 : (r1.charge 1).w "lab.uselo" ≠ 0 := hR1.uselo
    have hLoc : WHolds (r1.charge 1) Klo klof H1 (vc r1) Bi :=
      hR1.klo.of_unchanged (Unchanged.charge r1 1 [] [] [] []) (by simp) (by simp) (by simp)
    apply runs_seq
    have hcap1' : 1 < r1.cap := by rw [hU1.cap]; exact hcap1
    refine (loTest_some hL1.rep.hist hXc hcand hy.klo hLoc hul1
      (by simpa using hcap1')).mono ?_
    rintro q ⟨hge, hUq, hcq1, hcq2⟩
    have hcq1' : r1.cost + 2 ≤ q.cost := by simp only [State.charge_cost] at hcq1; omega
    have hUq' : Unchanged r1 q [] [] ["lab.c1", "lab.c2", "lab.lolt", "lab.ge"] [] :=
      (unch_charge_left 1).mp hUq
    have hcq2' : q.cost ≤ r1.cost + 17 := by simp only [State.charge_cost] at hcq2; omega
    have hres := relaxInsCc_valid (T l) B (some Bi) fs e hvr
    simp only at hres
    by_cases hadm : Bi ≤ ext (fs.d (G.src e)) e
    · -- insert the candidate through the D layer
      rw [if_pos hadm] at hres
      have hge1 : q.w "lab.ge" = 1 := by rw [hge, ← hext, if_pos hadm]
      apply runs_ite_true (by simp [hge1] : evalW q (WExpr.var "lab.ge") = some 1) one_ne_zero
      apply runs_seq
      refine runs_wset_val (by simp : evalW (q.charge 1) (var "lab.xv") = some (q.w "lab.xv"))
        (fun q5 hpx5 hU5 hc5 => ?_)
      have hxv : q.w "lab.xv" = (G.dst e : ℕ) := by
        rw [hUq'.wreg "lab.xv" (by decide)]; exact hX1.2.2.1
      have hU15 : Unchanged r1 q5 [] [] (["lab.c1", "lab.c2", "lab.lolt", "lab.ge"] ++ ["px"]) [] :=
        (hUq'.comp ((unch_charge_left 1).mp hU5)).mono (by simp) (by simp) (by simp) (by simp)
      obtain ⟨hR5, hU05, hvc5⟩ := hreg q5 _ hU15 (by decide) (by simp only [State.charge_cost] at hc5 hcq1; omega) fs.c
      have hc5' : q5.cost = q.cost + 2 := by rw [hc5]; rfl
      have huse5 : DI.use q5 = DI.use r := useR q5 _ hU15 (by decide)
      rw [hres] at huse
      simp only at huse
      refine (DI.ins_spec q5 H1 fs.g (Function.update Ds l fs.Dc) l
        (Function.update fs.d (G.dst e) (ext (fs.d (G.src e)) e)) c0 (G.dst e) hR5.dr hR5.lab
        hR5.lvl hR5.nn (by rw [hpx5]; exact hxv)
        (by simp only [Function.update_self]; rw [h.bd]; exact hvr.2)
        (by simp only [Function.update_self]; rw [huse5]; omega)).mono ?_
      rintro r' ⟨hDr, hUr, hlr1, hlr2, hcr1, hcr2, husr⟩
      simp only [Function.update_self, Function.update_idem] at hDr hcr2 husr
      have hvcr' : vc (G := G) r' = vc q5 := vc_of_unchanged hUr (fun h => hlW _ (by decide) h)
      have hKb' := hR5.kb.of_unchanged hUr (fun a ha => (hy.w a (by simp [ha])).2)
        hy.l.1 (hy.w kbf (by simp)).2
      have hKlo' := hR5.klo.of_unchanged hUr (fun a ha => (hy.w a (by simp [ha])).2)
        hy.l.2 (hy.w klof (by simp)).2
      have hlog := insC_cost_le (T := T l) fs.g fs.Dc (G.dst e) (ext (fs.d (G.src e)) e)
      rw [hres]
      refine ⟨H1, by rw [hvcr', hvc5]; exact hE1, ⟨hR5.lab.of_unchanged hUr hlW hdlen hcr1, hDr,
        hwk', graphAt_of_unchanged hUr (fun h => DI.hwa _ h (by simp))
          (fun h => DI.hva _ h (by simp)) hR5.gr,
        CSRAt.of_unchanged hR5.csr hUr (fun h => DI.hwa _ h (by simp)),
        by rw [hvcr']; exact hKb', by rw [hvcr']; exact hKlo',
        by rw [hUr.wreg _ (hsR _ (by decide))]; exact hR5.uselo,
        by rw [hUr.wreg _ (hsR _ (by decide))]; exact hR5.lvl,
        by rw [hUr.wreg _ (hsR _ (by decide))]; exact hR5.nn,
        (insC_Bd (T := T l) fs.g fs.Dc (G.dst e) (ext (fs.d (G.src e)) e)).1.trans h.bd⟩,
        (hU05.comp hUr).mono ?_ ?_ ?_ ?_, by omega, ?_, ?_,
        by rw [hlr1, (lenEq_of_unch hU15).1, hw1], by rw [hlr2, (lenEq_of_unch hU15).2, hv1],
        by simp only; omega⟩
      · intro a ha; simp only [List.mem_append] at ha ⊢; tauto
      · intro a ha; simp only [List.mem_append] at ha ⊢; tauto
      · intro a ha; simp only [List.mem_append] at ha ⊢; tauto
      · intro a ha; simp only [List.mem_append] at ha ⊢; tauto
      · have : DI.K * ((BM.insC (BM.dlOps G s) (T l) fs.g fs.Dc (G.dst e)
            (ext (fs.d (G.src e)) e)).2.2 + 1) ≤ DI.K * (Nat.log 2 fs.Dc.blocks.length + 5) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      · show r'.cost + (89 + DI.K) * fs.c ≤ r.cost + (89 + DI.K) * (fs.c + 1 +
          (BM.insC (BM.dlOps G s) (T l) fs.g fs.Dc (G.dst e) (ext (fs.d (G.src e)) e)).2.2)
        have e1 : (89 + DI.K) * (fs.c + 1 + (BM.insC (BM.dlOps G s) (T l) fs.g fs.Dc (G.dst e)
            (ext (fs.d (G.src e)) e)).2.2) = (89 + DI.K) * fs.c + 89 + 89 *
            (BM.insC (BM.dlOps G s) (T l) fs.g fs.Dc (G.dst e) (ext (fs.d (G.src e)) e)).2.2 +
            DI.K * ((BM.insC (BM.dlOps G s) (T l) fs.g fs.Dc (G.dst e)
              (ext (fs.d (G.src e)) e)).2.2 + 1) := by ring
        omega
    · -- the lo bound rejects: only the label changed
      rw [if_neg hadm] at hres
      have hge0 : q.w "lab.ge" = 0 := by rw [hge, ← hext, if_neg hadm]
      apply runs_ite_false (by simp [hge0])
      apply runs_skip
      have hUz : Unchanged r1 ((q.charge 1).charge 1) [] []
          ["lab.c1", "lab.c2", "lab.lolt", "lab.ge"] [] := by
        rw [unch_charge, unch_charge]; exact hUq'
      obtain ⟨hRz, hU0z, hvcz⟩ := hreg _ _ hUz (by decide) (by simp; omega) (fs.c + 1)
      have huz : DI.use ((q.charge 1).charge 1) = DI.use r := useR _ _ hUz (by decide)
      rw [hres]
      refine ⟨H1, by rw [hvcz]; exact hE1, hRz, hU0z, by simp; omega, by simp; omega, ?_,
        by rw [(lenEq_of_unch hUz).1, hw1], by rw [(lenEq_of_unch hUz).2, hv1],
        by rw [huz]; simp only; omega⟩
      simp only [State.charge_cost]
      have : (89 + DI.K) * (fs.c + 1) = (89 + DI.K) * fs.c + 89 + DI.K := by ring
      omega
  · -- invalid: nothing else happens
    have hok : r1.w "ok" = 0 := by rw [hok1, if_neg hvr]
    simp only [if_neg hvr] at hR1 hreg
    apply runs_ite_false (by simp [hok])
    apply runs_skip
    have hres : BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fs e = ⟨fs.d, fs.g, fs.Dc, fs.c + 1⟩ := by
      unfold BM.relaxInsCc; rw [if_neg hvr]
    have hUz : Unchanged r1 ((r1.charge 1).charge 1) [] [] [] [] := by
      rw [unch_charge, unch_charge]; exact Unchanged.refl _ _ _ _ _
    obtain ⟨hRz, hU0z, hvcz⟩ := hreg _ _ hUz (by simp)
      (by simp only [State.charge_cost]; omega) (fs.c + 1)
    have huz : DI.use ((r1.charge 1).charge 1) = DI.use r := useR _ _ hUz (by simp)
    rw [hres]
    refine ⟨H1, by rw [hvcz]; exact hE1, hRz, hU0z, by simp; omega, by simp; omega, ?_,
      by rw [(lenEq_of_unch hUz).1, hw1], by rw [(lenEq_of_unch hUz).2, hv1],
      by rw [huz]; simp only; omega⟩
    simp only [State.charge_cost]
    have : (89 + DI.K) * (fs.c + 1) = (89 + DI.K) * fs.c + 89 + DI.K := by ring
    omega

/-- Registers the inner window loop writes besides the D layer's. -/
def inW : List String := rwW ++ winW

/-- Per-edge cost bound of the scan over the abstract D layer. -/
def CED (K nb : ℕ) : ℕ := 113 + K * (Nat.log 2 nb + 5)

/-- The window inner loop over the abstract D layer (agent-08's text with
`relaxWin := relaxWinD ins`). -/
def winInnerD (ins : Stmt) (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Stmt :=
  .while (var "sp.go")
    (seq (ite (lt (var "sp.p") (var "sp.pe"))
            (seq (wset "re" (var "sp.p")) (LabRAM.candB Kb kbf "sp.lt"))
            (wset "sp.lt" (lit 0)))
    (ite (var "sp.lt")
       (seq (relaxWinD ins Kb kbf Klo klof) (wset "sp.p" (add (var "sp.p") (lit 1))))
       (wset "sp.go" (lit 0))))

open Classical in
/-- **The inner window loop over the abstract D layer** (one vertex `u`). -/
theorem winInnerD_spec {T : ℕ → ℕ} (DI : DInsI G s T) {l : ℕ} {Ds : ℕ → BM.DStrM G s}
    {c0 : ℕ} {B Bi : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    (hy : BlkHygD DI Kb kbf Klo klof) (st : State ℝ≥0) (fs0 : BM.RSt G s)
    (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof st fs0 H0)
    (u : Fin G.n) (hcomp : fs0.d u = dis (s := s) u) (hfin : fs0.d u ≠ ⊤)
    (p0 pe : ℕ) (hp0 : st.w "sp.p" = p0) (hpe : st.w "sp.pe" = pe) (hgo : st.w "sp.go" = 1)
    (hru : st.w "ru" = u)
    (hrange : st.wa "gSt" u ≤ p0 ∧ p0 ≤ pe ∧ pe = st.wa "gSt" ((u : ℕ) + 1))
    (hB : st.cost + (pe - p0 + 1) * CED DI.K fs0.Dc.blocks.length + 64 ≤ c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap)
    (hUse : ∀ q, p0 ≤ q → q ≤ pe → (∀ j (hj : j < G.m), p0 ≤ j → j < q → ext (fs0.d u) ⟨j, hj⟩ < B) →
      DI.use st + ((slots G p0 q).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c ≤
        DI.ucap + fs0.c) :
    Runs realOps (winInnerD DI.ins Kb kbf Klo klof) st (fun r => ∃ q H',
      p0 ≤ q ∧ q ≤ pe ∧ r.w "sp.p" = q ∧
      (∀ j (hj : j < G.m), p0 ≤ j → j < q → ext (fs0.d u) ⟨j, hj⟩ < B) ∧
      (q < pe → ∃ hq : q < G.m, ¬ ext (fs0.d u) ⟨q, hq⟩ < B) ∧
      HExt H0 (vc st) H' (vc r) ∧
      RepsD DI l Ds c0 B Bi Kb kbf Klo klof r
        ((slots G p0 q).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0) H' ∧
      r.w "ru" = u ∧ r.w "sp.pe" = pe ∧
      Unchanged st r (labW ++ DI.dWA) (labV ++ DI.dVA) (inW ++ DI.dWR) (relaxV ++ DI.dVR) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + (q - p0) * CED DI.K fs0.Dc.blocks.length + 30 ∧
      r.cost + (113 + DI.K) * fs0.c ≤ st.cost + (113 + DI.K) *
        ((slots G p0 q).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c + 30 ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      DI.use r + fs0.c ≤ DI.use st +
        ((slots G p0 q).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c) := by
  set nb := fs0.Dc.blocks.length with hnb
  have hpeM : pe ≤ G.m := by rw [hrange.2.2]; exact h0.csr.le_m u
  -- the loop invariant
  let I : State ℝ≥0 → Prop := fun r => ∃ p H', r.w "sp.p" = p ∧ p0 ≤ p ∧ p ≤ pe ∧
    r.w "sp.pe" = pe ∧ r.w "ru" = u ∧ (r.w "sp.go" = 0 ∨ r.w "sp.go" = 1) ∧
    (∀ j (hj : j < G.m), p0 ≤ j → j < p → ext (fs0.d u) ⟨j, hj⟩ < B) ∧
    (r.w "sp.go" = 0 → (p = pe ∨ ∃ hp : p < G.m, ¬ ext (fs0.d u) ⟨p, hp⟩ < B)) ∧
    HExt H0 (vc st) H' (vc r) ∧
    RepsD DI l Ds c0 B Bi Kb kbf Klo klof r
      ((slots G p0 p).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0) H' ∧
    Unchanged st r (labW ++ DI.dWA) (labV ++ DI.dVA) (inW ++ DI.dWR) (relaxV ++ DI.dVR) ∧ r.cap = st.cap ∧
    st.cost ≤ r.cost ∧
    r.cost ≤ st.cost + (p - p0) * CED DI.K nb + (if r.w "sp.go" = 0 then 26 else 0) ∧
    r.cost + (113 + DI.K) * fs0.c ≤ st.cost +
      (113 + DI.K) * ((slots G p0 p).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c +
      (if r.w "sp.go" = 0 then 26 else 0) ∧
    r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
    DI.use r + fs0.c ≤ DI.use st +
      ((slots G p0 p).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c
  let μ : State ℝ≥0 → ℕ := fun r => 2 * (pe - r.w "sp.p") + r.w "sp.go"
  refine runs_while_var I μ _ (fun r hI => ?_) st ⟨p0, H0, hp0, le_rfl, hrange.2.1, hpe, hru,
    Or.inr hgo, fun j _ h1 h2 => absurd h2 (by omega), fun h => by rw [hgo] at h; exact absurd h one_ne_zero,
    HExt.refl _ _, by rw [slots_self]; exact h0, Unchanged.refl _ _ _ _ _, rfl, le_rfl,
    by rw [hgo]; simp, by rw [hgo, slots_self]; simp, rfl, rfl, by simp [slots_self]⟩
  obtain ⟨p, H', hp, hp0p, hppe, hpe', hru', hgo', hwin, hstop, hE, hR, hU, hcap', hclo, hchi,
    hrel, hwl0, hvl0, huse0⟩ := hI
  set fsp := (slots G p0 p).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0 with hfsp
  obtain ⟨-, hnbp, hstab⟩ := foldl_invs' (T := T l) (B := B) (lo := some Bi) (slots G p0 p) fs0
    h0.wk
  have hdu : fsp.d u = fs0.d u := hstab u hcomp
  have hsub : ∀ a ∈ allW, a ∈ scanRegs := by decide
  have hKr : ∀ {wr : List String}, (∀ a ∈ wr, a ∈ allW) →
      ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "lvl", "n"], a ∉ wr :=
    fun hwr => hy.hK (fun a ha => Or.inl (hwr a ha))
  have ofR : ∀ {q q' : State ℝ≥0} {fs : BM.RSt G s} {H : Fin G.n → ℕ → List (Fin G.m)}
      {wr vr : List String}, RepsD DI l Ds c0 B Bi Kb kbf Klo klof q fs H →
      Unchanged q q' [] [] wr vr → q.cost ≤ q'.cost → (∀ a ∈ wr, a ∈ allW) →
      (∀ a ∈ vr, a ∈ relaxV) → Kb.l ∉ vr ∧ Klo.l ∉ vr →
      RepsD DI l Ds c0 B Bi Kb kbf Klo klof q' fs H :=
    fun h hu hc hwr hvr hl => h.of_unch hu hc (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (fun a ha hd => DI.hwr a hd (hsub a (hwr a ha)))
      (fun a ha hd => DI.hvr a hd (hvr a ha)) (hKr hwr) hl
  have hKl : Kb.l ∉ [X0.l] ∧ Klo.l ∉ [X0.l] :=
    ⟨fun h => hy.kb.l (by simp only [X0, List.mem_singleton] at h; rw [h]; decide),
     fun h => hy.klo.l (by simp only [X0, List.mem_singleton] at h; rw [h]; decide)⟩
  have hKn : Kb.l ∉ ([] : List String) ∧ Klo.l ∉ ([] : List String) := ⟨by simp, by simp⟩
  have useF : ∀ {a b : State ℝ≥0} {wr vr : List String}, Unchanged a b [] [] wr vr →
      (∀ x ∈ wr, x ∈ scanRegs) → DI.use b = DI.use a :=
    fun h hw => DI.use_frame _ _ _ _ _ _ h (fun x hx hd => DI.hwr x hd (hw x hx))
  have toI : ∀ {a b : State ℝ≥0} {wa va wr vr : List String}, Unchanged a b wa va wr vr →
      (∀ x ∈ wa, x ∈ labW ++ DI.dWA) → (∀ x ∈ va, x ∈ labV ++ DI.dVA) →
      (∀ x ∈ wr, x ∈ inW ++ DI.dWR) → (∀ x ∈ vr, x ∈ relaxV ++ DI.dVR) →
      Unchanged a b (labW ++ DI.dWA) (labV ++ DI.dVA) (inW ++ DI.dWR) (relaxV ++ DI.dVR) :=
    fun h h1 h2 h3 h4 => h.mono (by intro x hx; exact h1 x hx) (by intro x hx; exact h2 x hx)
      (by intro x hx; exact h3 x hx) (by intro x hx; exact h4 x hx)
  have nW : ∀ x ∈ ["sp.p", "sp.go", "sp.pe", "ru", "sp.i"], x ∉ rwW ++ DI.dWR := by
    intro x hx hm
    rcases List.mem_append.mp hm with h | h
    · exact (by decide : ∀ y ∈ ["sp.p", "sp.go", "sp.pe", "ru", "sp.i"], y ∉ rwW) x hx h
    · exact DI.hwr x h ((by decide : ∀ y ∈ ["sp.p", "sp.go", "sp.pe", "ru", "sp.i"],
        y ∈ scanRegs) x hx)
  have inA : ∀ {wr : List String}, (∀ x ∈ wr, x ∈ inW) → ∀ x ∈ wr, x ∈ inW ++ DI.dWR :=
    fun h x hx => List.mem_append_left _ (h x hx)
  have inV : ∀ {vr : List String}, (∀ x ∈ vr, x ∈ relaxV) → ∀ x ∈ vr, x ∈ relaxV ++ DI.dVR :=
    fun h x hx => List.mem_append_left _ (h x hx)
  refine ⟨r.w "sp.go", by simp, fun hne => ?_, fun hz => ?_⟩
  · -- one more iteration
    have hg1 : r.w "sp.go" = 1 := by rcases hgo' with h | h; exact absurd h hne; exact h
    rw [hg1] at hchi hrel
    simp only [if_neg one_ne_zero, add_zero] at hchi hrel
    have hmr : G.m + 2 ≤ r.cap := by rw [hcap']; exact hm
    have h1c : 1 < r.cap := by omega
    apply runs_seq
    by_cases hpl : p < pe
    · -- a slot is left: test its candidate
      have hpm : p < G.m := lt_of_lt_of_le hpl hpeM
      set e : Fin G.m := ⟨p, hpm⟩ with he
      have hsrc : G.src e = u := (h0.csr.src e u).mpr
        ⟨le_trans hrange.1 hp0p, lt_of_lt_of_eq hpl hrange.2.2⟩
      have hdu' : fsp.d (G.src e) = fs0.d u := by rw [hsrc]; exact hdu
      have hfinp : fsp.d (G.src e) ≠ ⊤ := by rw [hdu']; exact hfin
      have hmulS : (p - p0 + 1) * CED DI.K nb = (p - p0) * CED DI.K nb + CED DI.K nb := by ring
      have hmulB : (p - p0 + 1) * CED DI.K nb ≤ (pe - p0 + 1) * CED DI.K nb :=
        Nat.mul_le_mul_right _ (by omega)
      have hCE : 113 ≤ CED DI.K nb := by unfold CED; omega
      have hlt1 : evalW (r.charge 1) (lt (var "sp.p") (var "sp.pe")) = some 1 := by
        rw [evalW_lt_of (s := r.charge 1) (x := p) (y := pe)
          (by rw [evalW_var]; exact congrArg some hp)
          (by rw [evalW_var]; exact congrArg some hpe') h1c, if_pos hpl]
      apply runs_ite_true hlt1 one_ne_zero
      apply runs_seq
      refine runs_wset_val (a := p) (by rw [evalW_var]; exact congrArg some hp)
        (fun r3 hre3 hU3 hc3 => ?_)
      have hU13 : Unchanged r r3 [] [] ["re"] [] :=
        (unch_charge_left 1).mp ((unch_charge_left 1).mp hU3)
      have hc3' : r3.cost = r.cost + 3 := by rw [hc3]; rfl
      have hR3 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof r3 fsp H' :=
        ofR hR hU13 (by omega) (by decide) (by simp) hKn
      have hru3 : r3.w "ru" = G.src e := by rw [hU13.wreg "ru" (by decide), hru', hsrc]
      have hcap3 : r3.cap = st.cap := hU13.cap.trans hcap'
      refine (candB_spec r3 fsp.d H' c0 hR3.lab hR3.gr e hru3 hre3 hfinp Kb kbf "sp.lt" hy.kb
        (by decide) B hR3.kb (by rw [hcap3]; omega) (by rw [hcap3]; exact hm)).mono ?_
      rintro r4 ⟨-, hvc4, -, -, hlt4, hU4, hc4a, hc4b⟩
      have hR4 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof r4 fsp H' :=
        ofR hR3 hU4 (by omega) (by decide) (by decide) hKl
      rw [hdu'] at hlt4
      have hcap4 : r4.cap = st.cap := hU4.cap.trans hcap3
      have hvc4' : vc (G := G) r4 = vc r := hvc4.trans (vc_of_unchanged hU13 (by simp))
      by_cases hc : ext (fs0.d u) e < B
      · -- the candidate is below `B`: relax (with insertion) and advance
        rw [if_pos hc] at hlt4
        apply runs_ite_true (x := 1) (by rw [evalW_var, hlt4]) one_ne_zero
        apply runs_seq
        have hR5 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof (r4.charge 1) fsp H' :=
          ofR hR4 (Unchanged.charge r4 1 [] [] [] []) (by show r4.cost ≤ r4.cost + 1; omega)
            (by simp) (by simp) hKn
        have hq1 := hUse (p + 1) (by omega) (by omega) (fun j hj h1 h2 => by
          rcases Nat.lt_or_ge j p with h3 | h3
          · exact hwin j hj h1 h3
          · have hjp : (⟨j, hj⟩ : Fin G.m) = e := Fin.ext (by show j = p; omega)
            rw [hjp]; exact hc)
        rw [slots_succ hp0p hpm, List.foldl_append] at hq1
        simp only [List.foldl_cons, List.foldl_nil] at hq1
        rw [← hfsp, ← he] at hq1
        have huse4 : DI.use (r4.charge 1) = DI.use r :=
          useF ((hU13.comp hU4).comp (Unchanged.charge r4 1 [] [] [] [])) (by decide)
        refine (RepsD.step DI hy hR5 e ?_ ?_ hfinp ?_ ?_ (by rw [huse4]; omega)).mono ?_
        · show r4.w "ru" = G.src e
          rw [hU4.wreg "ru" (by decide)]; exact hru3
        · show r4.w "re" = (e : ℕ)
          rw [hU4.wreg "re" (by decide)]; exact hre3
        · show r4.cost + 1 + 64 ≤ c0 + r4.cap
          rw [hcap4]; omega
        · show G.m + 2 ≤ r4.cap
          rw [hcap4]; exact hm
        rintro r6 ⟨H'', hE6, hR6, hU6, hc6a, hc6b, hc6c, hw6, hv6, hus6⟩
        have hΔ := relaxInsCc_c_ge (T := T l) (B := B) (lo := some Bi) fsp e
        have hp6 : r6.w "sp.p" = p := by
          rw [hU6.wreg "sp.p" (nW _ (by simp))]
          show r4.w "sp.p" = p
          rw [hU4.wreg "sp.p" (by decide), hU13.wreg "sp.p" (by decide)]; exact hp
        have hcap6 : r6.cap = st.cap := hU6.cap.trans hcap4
        have hCEe : 113 + DI.K * (Nat.log 2 fsp.Dc.blocks.length + 5) = CED DI.K nb := by
          rw [hnbp]; rfl
        have e1 : (113 + DI.K) * (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fsp e).c =
            (89 + DI.K) * (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fsp e).c +
            24 * (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fsp e).c := by ring
        have e2 : (113 + DI.K) * fsp.c = (89 + DI.K) * fsp.c + 24 * fsp.c := by ring
        have hc5 : (r4.charge 1).cost = r4.cost + 1 := rfl
        refine runs_wset_val (evalW_add_of (x := p) (y := 1)
          (by rw [evalW_var]; exact congrArg some hp6)
          (evalW_lit_of (by omega)) (by omega)) (fun r7 hp7 hU67 hc7 => ?_)
        have hvc5 : vc (G := G) (r4.charge 1) = vc r := hvc4'
        have hvc7 : vc (G := G) r7 = vc r6 := vc_of_unchanged hU67 (by simp)
        have hgo7 : r7.w "sp.go" = 1 := by
          rw [hU67.wreg "sp.go" (by decide), hU6.wreg "sp.go" (nW _ (by simp))]
          show r4.w "sp.go" = 1
          rw [hU4.wreg "sp.go" (by decide), hU13.wreg "sp.go" (by decide)]; exact hg1
        refine ⟨⟨p + 1, H'', hp7, by omega, by omega, ?_, ?_, Or.inr hgo7, ?_,
          fun h => absurd (h.symm.trans hgo7) zero_ne_one, ?_, ?_, ?_, hU67.cap.trans hcap6,
          by omega, ?_, ?_,
          by rw [(lenEq_of_unch hU67).1, hw6]; show r4.wlen = st.wlen
             rw [(lenEq_of_unch hU4).1, (lenEq_of_unch hU13).1]; exact hwl0,
          by rw [(lenEq_of_unch hU67).2, hv6]; show r4.vlen = st.vlen
             rw [(lenEq_of_unch hU4).2, (lenEq_of_unch hU13).2]; exact hvl0, ?_⟩, ?_⟩
        · rw [hU67.wreg "sp.pe" (by decide), hU6.wreg "sp.pe" (nW _ (by simp))]
          show r4.w "sp.pe" = pe
          rw [hU4.wreg "sp.pe" (by decide), hU13.wreg "sp.pe" (by decide)]; exact hpe'
        · rw [hU67.wreg "ru" (by decide), hU6.wreg "ru" (nW _ (by simp))]
          show r4.w "ru" = u
          rw [hU4.wreg "ru" (by decide), hU13.wreg "ru" (by decide)]; exact hru'
        · intro j hj h1 h2
          rcases Nat.lt_or_ge j p with h3 | h3
          · exact hwin j hj h1 h3
          · have hjp : (⟨j, hj⟩ : Fin G.m) = e := Fin.ext (by show j = p; omega)
            rw [hjp]; exact hc
        · rw [hvc7]
          exact hE.trans (by rw [← hvc5]; exact hE6)
        · rw [slots_succ hp0p hpm, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          exact ofR hR6 hU67 (by omega) (by decide) (by simp) hKn
        · refine hU.trans ((toI hU13 (by simp) (by simp) (inA (by decide)) (by simp)).trans
            ((toI hU4 (by simp) (by simp) (inA (by decide)) (inV (by decide))).trans
            ((toI (Unchanged.charge r4 1 [] [] [] []) (by simp) (by simp) (by simp) (by simp)).trans
            ((toI hU6 (fun x hx => hx) (fun x hx => hx) ?_ (fun x hx => hx)).trans
            (toI hU67 (by simp) (by simp) (inA (by decide)) (by simp))))))
          intro x hx
          simp only [List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · left; simp only [inW, List.mem_append]; left; exact hx
          · right; exact hx
        · rw [hgo7, if_neg one_ne_zero, add_zero]
          have : (p + 1 - p0) * CED DI.K nb = (p - p0) * CED DI.K nb + CED DI.K nb := by
            rw [show p + 1 - p0 = p - p0 + 1 by omega]; exact hmulS
          omega
        · rw [hgo7, if_neg one_ne_zero, add_zero, slots_succ hp0p hpm, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          show r7.cost + (113 + DI.K) * fs0.c ≤
            st.cost + (113 + DI.K) * (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fsp e).c
          omega
        · rw [slots_succ hp0p hpm, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          show DI.use r7 + fs0.c ≤
            DI.use st + (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi) fsp e).c
          have h7 : DI.use r7 = DI.use r6 := useF hU67 (by decide)
          omega
        · show 2 * (pe - r7.w "sp.p") + r7.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
          rw [hp7, hgo7, hp, hg1]; omega
      · -- the candidate is not below `B`: stop
        rw [if_neg hc] at hlt4
        apply runs_ite_false (by rw [evalW_var, hlt4])
        refine runs_wset_val (evalW_lit_of (by show 0 < r4.cap; omega))
          (fun r7 hgo7 hU47 hc7 => ?_)
        have hU47' : Unchanged r4 r7 [] [] ["sp.go"] [] := (unch_charge_left 1).mp hU47
        have hc7' : r7.cost = r4.cost + 2 := by rw [hc7]; rfl
        have hvc7 : vc (G := G) r7 = vc r := (vc_of_unchanged hU47' (by simp)).trans hvc4'
        have hp7 : r7.w "sp.p" = p := by
          rw [hU47'.wreg "sp.p" (by decide), hU4.wreg "sp.p" (by decide),
            hU13.wreg "sp.p" (by decide)]; exact hp
        refine ⟨⟨p, H', hp7, hp0p, hppe, ?_, ?_, Or.inl hgo7, hwin, fun _ => Or.inr ⟨hpm, hc⟩,
          by rw [hvc7]; exact hE, ofR hR4 hU47' (by omega) (by decide) (by simp) hKn, ?_,
          hU47'.cap.trans hcap4, by omega, ?_, ?_,
          by rw [(lenEq_of_unch hU47').1, (lenEq_of_unch hU4).1, (lenEq_of_unch hU13).1]; exact hwl0,
          by rw [(lenEq_of_unch hU47').2, (lenEq_of_unch hU4).2, (lenEq_of_unch hU13).2]; exact hvl0,
          by rw [useF ((hU13.comp hU4).comp hU47') (by decide), ← hfsp]; exact huse0⟩,
          ?_⟩
        · rw [hU47'.wreg "sp.pe" (by decide), hU4.wreg "sp.pe" (by decide),
            hU13.wreg "sp.pe" (by decide)]; exact hpe'
        · rw [hU47'.wreg "ru" (by decide), hU4.wreg "ru" (by decide),
            hU13.wreg "ru" (by decide)]; exact hru'
        · exact hU.trans ((toI hU13 (by simp) (by simp) (inA (by decide)) (by simp)).trans
            ((toI hU4 (by simp) (by simp) (inA (by decide)) (inV (by decide))).trans
            (toI hU47' (by simp) (by simp) (inA (by decide)) (by simp))))
        · rw [hgo7, if_pos rfl]
          have : r7.cost = r4.cost + 2 := by rw [hc7]; rfl
          omega
        · rw [hgo7, if_pos rfl, ← hfsp]
          omega
        · show 2 * (pe - r7.w "sp.p") + r7.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
          rw [hp7, hgo7, hp, hg1]; omega
    · -- the range is exhausted: stop
      have hpe_eq : p = pe := by omega
      have hlt0 : evalW (r.charge 1) (lt (var "sp.p") (var "sp.pe")) = some 0 := by
        rw [evalW_lt_of (s := r.charge 1) (x := p) (y := pe)
          (by rw [evalW_var]; exact congrArg some hp)
          (by rw [evalW_var]; exact congrArg some hpe') h1c, if_neg hpl]
      apply runs_ite_false hlt0
      refine runs_wset_val (evalW_lit_of (by show 0 < r.cap; omega)) (fun r3 hlt3 hU3 hc3 => ?_)
      have hU13 : Unchanged r r3 [] [] ["sp.lt"] [] :=
        (unch_charge_left 1).mp ((unch_charge_left 1).mp hU3)
      apply runs_ite_false (by rw [evalW_var, hlt3])
      refine runs_wset_val (evalW_lit_of (by show 0 < r3.cap; rw [hU13.cap]; omega))
        (fun r4 hgo4 hU4 hc4 => ?_)
      have hU34 : Unchanged r3 r4 [] [] ["sp.go"] [] := (unch_charge_left 1).mp hU4
      have hvc4 : vc (G := G) r4 = vc r :=
        (vc_of_unchanged hU34 (by simp)).trans (vc_of_unchanged hU13 (by simp))
      have hp4 : r4.w "sp.p" = p := by
        rw [hU34.wreg "sp.p" (by decide), hU13.wreg "sp.p" (by decide)]; exact hp
      have hc4' : r4.cost = r.cost + 5 := by rw [hc4]; show r3.cost + 1 + 1 = _; rw [hc3]; rfl
      refine ⟨⟨p, H', hp4, hp0p, hppe, ?_, ?_, Or.inl hgo4, hwin, fun _ => Or.inl hpe_eq,
        by rw [hvc4]; exact hE, ofR hR (hU13.comp hU34) (by omega) (by decide) (by simp) ⟨by simp, by simp⟩, ?_,
        hU34.cap.trans (hU13.cap.trans hcap'), by omega, ?_, ?_,
        by rw [(lenEq_of_unch hU34).1, (lenEq_of_unch hU13).1]; exact hwl0,
        by rw [(lenEq_of_unch hU34).2, (lenEq_of_unch hU13).2]; exact hvl0,
        by rw [useF (hU13.comp hU34) (by decide), ← hfsp]; exact huse0⟩, ?_⟩
      · rw [hU34.wreg "sp.pe" (by decide), hU13.wreg "sp.pe" (by decide)]; exact hpe'
      · rw [hU34.wreg "ru" (by decide), hU13.wreg "ru" (by decide)]; exact hru'
      · exact hU.trans ((toI hU13 (by simp) (by simp) (inA (by decide)) (by simp)).trans
          (toI hU34 (by simp) (by simp) (inA (by decide)) (by simp)))
      · rw [hgo4, if_pos rfl]; omega
      · rw [hgo4, if_pos rfl, ← hfsp]; omega
      · show 2 * (pe - r4.w "sp.p") + r4.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
        rw [hp4, hgo4, hp, hg1]; omega
  · -- exit
    have hcost : r.cost ≤ st.cost + (p - p0) * CED DI.K nb + 26 := by
      rw [hz, if_pos rfl] at hchi; exact hchi
    have hrel' : r.cost + (113 + DI.K) * fs0.c ≤ st.cost + (113 + DI.K) * fsp.c + 26 := by
      rw [hz, if_pos rfl] at hrel; exact hrel
    refine ⟨p, H', hp0p, hppe, hp, hwin, fun hq => ?_, hE,
      ofR hR (Unchanged.charge r 1 [] [] [] []) (by show r.cost ≤ r.cost + 1; omega)
        (by simp) (by simp) hKn, hru', hpe', (unch_charge 1).mpr hU, by show st.cost ≤ r.cost + 1; omega,
      by show r.cost + 1 ≤ _; omega,
      by show r.cost + 1 + (113 + DI.K) * fs0.c ≤ st.cost + (113 + DI.K) * fsp.c + 30; omega,
      hwl0, hvl0, by rw [useF (Unchanged.charge r 1 [] [] [] []) (by simp)]; exact huse0⟩
    rcases hstop hz with h | h
    · omega
    · exact h


/-! ### Canonical scan stops and prefix monotonicity (for outcome-indexed budgets) -/

/-- The stop slot of a scan is unique. -/
theorem ScanStop.unique {st : State ℝ≥0} {du : WLab G s} {u : Fin G.n} {p0 q q' : ℕ}
    {B : WLab G s} (hm : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m) (h : ScanStop st du u p0 q B)
    (h' : ScanStop st du u p0 q' B) : q = q' := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact a4 (by omega) (by omega) (b3 q (by omega) a1 hlt)
  · exact b4 (by omega) (by omega) (a3 q' (by omega) b1 hlt)

open Classical in
/-- A stop slot exists (for a start inside the range). -/
theorem ScanStop.exists {st : State ℝ≥0} (du : WLab G s) (u : Fin G.n) {p0 : ℕ} (B : WLab G s)
    (hm : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m) (hp0 : p0 ≤ st.wa "gSt" ((u : ℕ) + 1)) :
    ∃ q, ScanStop st du u p0 q B := by
  -- the least slot `q ≥ p0` that is the range end or has candidate `⪰ B`
  let R : ℕ → Prop := fun q => p0 ≤ q ∧ (q = st.wa "gSt" ((u : ℕ) + 1) ∨
    ∃ hq : q < G.m, q < st.wa "gSt" ((u : ℕ) + 1) ∧ ¬ ext du ⟨q, hq⟩ < B)
  have hR : ∃ q, R q := ⟨_, hp0, Or.inl rfl⟩
  refine ⟨Nat.find hR, ?_⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hR
  have hle : Nat.find hR ≤ st.wa "gSt" ((u : ℕ) + 1) := Nat.find_min' hR ⟨hp0, Or.inl rfl⟩
  refine ⟨h1, hle, fun j hj hj1 hj2 => ?_, fun hq hqe => ?_⟩
  · by_contra hc
    exact Nat.find_min hR hj2 ⟨hj1, Or.inr ⟨hj, by omega, hc⟩⟩
  · rcases h2 with h | ⟨hq', _, h⟩
    · omega
    · exact h

open Classical in
/-- **The canonical stop slot** of the scan of `u` from `p0` at bound `B` (label `du`). -/
noncomputable def stopOf (st : State ℝ≥0) (du : WLab G s) (u : Fin G.n) (p0 : ℕ) (B : WLab G s) :
    ℕ :=
  if h : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m ∧ p0 ≤ st.wa "gSt" ((u : ℕ) + 1) then
    Classical.choose (ScanStop.exists (st := st) du u B h.1 h.2)
  else p0

theorem stopOf_spec {st : State ℝ≥0} (du : WLab G s) (u : Fin G.n) {p0 : ℕ} (B : WLab G s)
    (hm : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m) (hp0 : p0 ≤ st.wa "gSt" ((u : ℕ) + 1)) :
    ScanStop st du u p0 (stopOf st du u p0 B) B := by
  unfold stopOf
  rw [dif_pos ⟨hm, hp0⟩]
  exact Classical.choose_spec (ScanStop.exists (st := st) du u B hm hp0)

/-- Every stop slot is the canonical one. -/
theorem ScanStop.eq_stopOf {st : State ℝ≥0} {du : WLab G s} {u : Fin G.n} {p0 q : ℕ}
    {B : WLab G s} (hm : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m) (h : ScanStop st du u p0 q B) :
    q = stopOf st du u p0 B :=
  h.unique hm (stopOf_spec du u B hm (le_trans h.1 h.2.1))

/-- The Layer-A cost counter only grows along a fold. -/
theorem foldl_c_mono {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} :
    ∀ (L : List (Fin G.m)) (st : BM.RSt G s),
      st.c ≤ (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).c
  | [], _ => le_rfl
  | e :: L, st => by
    simp only [List.foldl_cons]
    exact le_trans (Nat.le_succ_of_le (le_refl _) |>.trans
      (relaxInsCc_c_ge (T := T) (B := B) (lo := lo) st e)) (foldl_c_mono L _)

/-- A prefix of a relaxation list costs at most the whole list. -/
theorem foldl_c_prefix {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)}
    (A C : List (Fin G.m)) (st : BM.RSt G s) :
    (A.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).c ≤
      ((A ++ C).foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).c := by
  rw [List.foldl_append]; exact foldl_c_mono C _


/-- The row scan over the abstract D layer. -/
def scanLoopD (lenE elemE startE : WExpr) (ins : Stmt) (Kb : LReg) (kbf : String) (Klo : LReg)
    (klof : String) : Stmt :=
  seq (wset "sp.i" (lit 0))
  (.while (lt (var "sp.i") lenE)
     (seq (wset "ru" elemE)
     (seq (wset "sp.p" startE)
     (seq (wset "sp.pe" (load "gSt" (add (var "ru") (lit 1))))
     (seq (wset "sp.go" (lit 1))
     (seq (winInnerD ins Kb kbf Klo klof)
     (seq (wstore "sp.ptr" (var "ru") (var "sp.p"))
          (wset "sp.i" (add (var "sp.i") (lit 1))))))))))

/-- The frame of the scans over the abstract D layer. -/
def FrameWD {T : ℕ → ℕ} (DI : DInsI G s T) (st r : State ℝ≥0) : Prop :=
  Unchanged st r (labW ++ DI.dWA ++ ["sp.ptr"]) (labV ++ DI.dVA) (allW ++ DI.dWR)
    (relaxV ++ DI.dVR)

open Classical in
/-- **The row scan over the abstract D layer.** -/
theorem scanLoopD_spec {T : ℕ → ℕ} (DI : DInsI G s T) {l : ℕ} {Ds : ℕ → BM.DStrM G s}
    {c0 : ℕ} {B Bi : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    (hy : BlkHygD DI Kb kbf Klo klof) (lenE elemE startE : WExpr) (st : State ℝ≥0)
    (fs0 : BM.RSt G s) (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof st fs0 H0)
    (xs : List (Fin G.n)) (hxs : xs.Nodup) (P0 : Fin G.n → ℕ)
    (hlenE : ∀ r, FrameWD DI st r → evalW r lenE = some xs.length)
    (helemE : ∀ r (i : ℕ) (hi : i < xs.length), FrameWD DI st r → r.w "sp.i" = i →
      evalW r elemE = some (xs[i] : ℕ))
    (hstartE : ∀ r (u : Fin G.n), FrameWD DI st r → r.wlen "sp.ptr" = st.wlen "sp.ptr" →
      r.w "ru" = u → r.wa "sp.ptr" u = st.wa "sp.ptr" u → evalW r startE = some (P0 u))
    (hP0 : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ P0 u ∧ P0 u ≤ st.wa "gSt" ((u : ℕ) + 1))
    (hcomp : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧ fs0.d u ≠ ⊤)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap)
    (hB : st.cost + (xs.length + 1) * ((G.m + 1) * CED DI.K fs0.Dc.blocks.length + 101) ≤
      c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap)
    (hUse : ∀ Q : Fin G.n → ℕ, (∀ u ∈ xs, ScanStop st (fs0.d u) u (P0 u) (Q u) B) →
      DI.use st + ((xs.flatMap (fun u => slots G (P0 u) (Q u))).foldl
        (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c ≤ DI.ucap + fs0.c) :
    Runs realOps (scanLoopD lenE elemE startE DI.ins Kb kbf Klo klof) st
      (fun r => ∃ (H' : Fin G.n → ℕ → List (Fin G.m)) (Q : Fin G.n → ℕ),
      (∀ u ∈ xs, ScanStop st (fs0.d u) u (P0 u) (Q u) B ∧ r.wa "sp.ptr" u = Q u) ∧
      (∀ u : Fin G.n, u ∉ xs → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
      r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧
      HExt H0 (vc st) H' (vc r) ∧
      RepsD DI l Ds c0 B Bi Kb kbf Klo klof r
        ((xs.flatMap (fun u => slots G (P0 u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0) H' ∧
      FrameWD DI st r ∧ st.cost ≤ r.cost ∧
      r.cost + (113 + DI.K) * fs0.c ≤ st.cost + (113 + DI.K) *
        ((xs.flatMap (fun u => slots G (P0 u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c + 38 * xs.length + 2 ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      DI.use r + fs0.c ≤ DI.use st + ((xs.flatMap (fun u => slots G (P0 u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c) := by
  set nb := fs0.Dc.blocks.length with hnb
  set Y := (G.m + 1) * CED DI.K nb with hY
  have hCE : 113 ≤ CED DI.K nb := by unfold CED; omega
  have h1c : 1 < st.cap := by omega
  have hxl : xs.length ≤ G.n := by
    have := hxs.length_le_card; rwa [Fintype.card_fin] at this
  have hsub : ∀ a ∈ allW, a ∈ scanRegs := by decide
  have hKr : ∀ {wr : List String}, (∀ a ∈ wr, a ∈ allW) →
      ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "lvl", "n"], a ∉ wr :=
    fun hwr => hy.hK (fun a ha => Or.inl (hwr a ha))
  have ofR : ∀ {q q' : State ℝ≥0} {fs : BM.RSt G s} {H : Fin G.n → ℕ → List (Fin G.m)}
      {wr vr : List String}, RepsD DI l Ds c0 B Bi Kb kbf Klo klof q fs H →
      Unchanged q q' [] [] wr vr → q.cost ≤ q'.cost → (∀ a ∈ wr, a ∈ allW) →
      (∀ a ∈ vr, a ∈ relaxV) → Kb.l ∉ vr ∧ Klo.l ∉ vr →
      RepsD DI l Ds c0 B Bi Kb kbf Klo klof q' fs H :=
    fun h hu hc hwr hvr hl => h.of_unch hu hc (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (fun a ha hd => DI.hwr a hd (hsub a (hwr a ha)))
      (fun a ha hd => DI.hvr a hd (hvr a ha)) (hKr hwr) hl
  have hKn : Kb.l ∉ ([] : List String) ∧ Klo.l ∉ ([] : List String) := ⟨by simp, by simp⟩
  have useF : ∀ {a b : State ℝ≥0} {wa va wr vr : List String}, Unchanged a b wa va wr vr →
      (∀ x ∈ wr, x ∈ scanRegs) → DI.use b = DI.use a :=
    fun h hw => DI.use_frame _ _ _ _ _ _ h (fun x hx hd => DI.hwr x hd (hw x hx))
  have toF : ∀ {a b : State ℝ≥0} {wa va wr vr : List String}, Unchanged a b wa va wr vr →
      (∀ x ∈ wa, x ∈ labW ++ DI.dWA ++ ["sp.ptr"]) → (∀ x ∈ va, x ∈ labV ++ DI.dVA) →
      (∀ x ∈ wr, x ∈ allW ++ DI.dWR) → (∀ x ∈ vr, x ∈ relaxV ++ DI.dVR) →
      Unchanged a b (labW ++ DI.dWA ++ ["sp.ptr"]) (labV ++ DI.dVA) (allW ++ DI.dWR)
        (relaxV ++ DI.dVR) :=
    fun h h1 h2 h3 h4 => h.mono (by intro x hx; exact h1 x hx) (by intro x hx; exact h2 x hx)
      (by intro x hx; exact h3 x hx) (by intro x hx; exact h4 x hx)
  have inA : ∀ {wr : List String}, (∀ x ∈ wr, x ∈ allW) → ∀ x ∈ wr, x ∈ allW ++ DI.dWR :=
    fun h x hx => List.mem_append_left _ (h x hx)
  have nA : ∀ x ∈ ["gSt", "gHead", "sp.ptr"], x ∉ labW ++ DI.dWA := by
    intro x hx hm
    rcases List.mem_append.mp hm with h | h
    · exact (by decide : ∀ y ∈ ["gSt", "gHead", "sp.ptr"], y ∉ labW) x hx h
    · exact DI.hwa x h (List.mem_append_right _ hx)
  have nA' : ∀ x ∈ ["gSt", "gHead"], x ∉ labW ++ DI.dWA ++ ["sp.ptr"] := by
    intro x hx hm
    rcases List.mem_append.mp hm with h | h
    · exact nA x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto) h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx h; rcases hx with rfl | rfl <;>
        simp at h
  have nWi : ∀ x ∈ ["sp.i"], x ∉ inW ++ DI.dWR := by
    intro x hx hm
    rcases List.mem_append.mp hm with h | h
    · exact (by decide : ∀ y ∈ ["sp.i"], y ∉ inW) x hx h
    · exact DI.hwr x h ((by decide : ∀ y ∈ ["sp.i"], y ∈ scanRegs) x hx)
  -- the loop invariant after `k` vertices
  let I : ℕ → State ℝ≥0 → Prop := fun k r => ∃ (H' : Fin G.n → ℕ → List (Fin G.m))
    (Q : Fin G.n → ℕ),
    r.w "sp.i" = k ∧ FrameWD DI st r ∧ r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧
    (∀ u ∈ xs.take k, ScanStop st (fs0.d u) u (P0 u) (Q u) B ∧ r.wa "sp.ptr" u = Q u) ∧
    (∀ u : Fin G.n, u ∉ xs.take k → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
    HExt H0 (vc st) H' (vc r) ∧
    RepsD DI l Ds c0 B Bi Kb kbf Klo klof r
      (((xs.take k).flatMap (fun u => slots G (P0 u) (Q u))).foldl
        (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0) H' ∧
    st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 1 + k * (Y + 38) ∧
    r.cost + (113 + DI.K) * fs0.c ≤ st.cost + (113 + DI.K) * (((xs.take k).flatMap
      (fun u => slots G (P0 u) (Q u))).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c
      + 38 * k + 1 ∧
    r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
    DI.use r + fs0.c ≤ DI.use st + (((xs.take k).flatMap
      (fun u => slots G (P0 u) (Q u))).foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c
  apply runs_seq
  refine runs_wset_val (evalW_lit_of (by omega)) (fun r0 hi0 hU0 hc0 => ?_)
  refine runs_while I xs.length _ (fun k hk r hI => ?_) (fun r hI => ?_) r0 ?_
  · -- one vertex
    obtain ⟨H', Q, hik, hFW, hwl, hdone, hrest, hE, hR, hclo, hchi, hrel, hwL, hvL, huseK⟩ := hI
    have hux : xs[k] ∈ xs := List.getElem_mem hk
    set u : Fin G.n := xs[k] with hu
    have hunt : u ∉ xs.take k := by
      intro hm'
      rw [List.mem_take_iff_getElem] at hm'
      obtain ⟨j, hj, hjk⟩ := hm'
      have := (List.Nodup.getElem_inj_iff hxs).mp hjk
      omega
    have hcapr : r.cap = st.cap := Unchanged.cap hFW
    set Lk := (xs.take k).flatMap (fun w => slots G (P0 w) (Q w)) with hLk
    set fsk := Lk.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0 with hfsk
    obtain ⟨-, hnbk, hstab⟩ :=
      foldl_invs' (T := T l) (B := B) (lo := some Bi) Lk fs0 h0.wk
    have hdu : fsk.d u = fs0.d u := hstab u (hcomp u hux).1
    have hpeM : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m := h0.csr.le_m u
    have hcc : (r.charge 1).cost = r.cost + 1 := rfl
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (s := r) (x := k) (y := xs.length)
        (by rw [evalW_var]; exact congrArg some hik) (hlenE r hFW) (by omega), if_pos hk]
    have hFW0 : FrameWD DI st (r.charge 1) := (unch_charge 1).mpr hFW
    have hR0 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof (r.charge 1) fsk H' :=
      ofR hR (Unchanged.charge r 1 [] [] [] []) (by omega) (by simp) (by simp) hKn
    -- `ru := U[i]`
    apply runs_seq
    refine runs_wset_val (helemE (r.charge 1) k hk hFW0 hik) (fun r1 hru1 hU1 hc1 => ?_)
    have hFW1 : FrameWD DI st r1 :=
      Unchanged.trans hFW0 (toF hU1 (by simp) (by simp) (inA (by decide)) (by simp))
    have hp1 := hU1.warr "sp.ptr" (by simp)
    have hR1 := ofR hR0 hU1 (by omega) (by decide) (by simp) hKn
    -- `sp.p := start`
    apply runs_seq
    refine runs_wset_val (hstartE r1 u hFW1 (by rw [hp1.2]; exact hwl) hru1
      (by rw [hp1.1]; exact hrest u hunt)) (fun r2 hp2 hU2 hc2 => ?_)
    have hFW2 : FrameWD DI st r2 :=
      Unchanged.trans hFW1 (toF hU2 (by simp) (by simp) (inA (by decide)) (by simp))
    have hR2 := ofR hR1 hU2 (by omega) (by decide) (by simp) hKn
    have hg2 := Unchanged.warr hFW2 "gSt" (nA' _ (by simp))
    have hru2 : r2.w "ru" = u := by rw [hU2.wreg "ru" (by decide)]; exact hru1
    have hcap2 : r2.cap = st.cap := Unchanged.cap hFW2
    have hulen : (u : ℕ) + 1 < r2.wlen "gSt" := by
      rw [hg2.2]; have := h0.csr.len; have := u.isLt; omega
    -- `sp.pe := gSt[ru + 1]`
    apply runs_seq
    refine runs_wset_val (a := st.wa "gSt" ((u : ℕ) + 1)) ?_ (fun r3 hpe3 hU3 hc3 => ?_)
    · have := u.isLt
      rw [evalW_load_of (evalW_add_of (x := (u : ℕ)) (y := 1)
        (by rw [evalW_var]; exact congrArg some hru2) (evalW_lit_of (by omega)) (by omega)) hulen,
        hg2.1]
    have hFW3 : FrameWD DI st r3 :=
      Unchanged.trans hFW2 (toF hU3 (by simp) (by simp) (inA (by decide)) (by simp))
    have hR3 := ofR hR2 hU3 (by omega) (by decide) (by simp) hKn
    have hcap3 : r3.cap = st.cap := Unchanged.cap hFW3
    -- `sp.go := 1`
    apply runs_seq
    refine runs_wset_val (evalW_lit_of (by omega)) (fun r4 hgo4 hU4 hc4 => ?_)
    have hFW4 : FrameWD DI st r4 :=
      Unchanged.trans hFW3 (toF hU4 (by simp) (by simp) (inA (by decide)) (by simp))
    have hR4 := ofR hR3 hU4 (by omega) (by decide) (by simp) hKn
    have hcap4 : r4.cap = st.cap := Unchanged.cap hFW4
    have hg4 := Unchanged.warr hFW4 "gSt" (nA' _ (by simp))
    have hp4 : r4.w "sp.p" = P0 u := by
      rw [hU4.wreg "sp.p" (by decide), hU3.wreg "sp.p" (by decide)]; exact hp2
    have hpe4 : r4.w "sp.pe" = st.wa "gSt" ((u : ℕ) + 1) := by
      rw [hU4.wreg "sp.pe" (by decide)]; exact hpe3
    have hru4 : r4.w "ru" = u := by
      rw [hU4.wreg "ru" (by decide), hU3.wreg "ru" (by decide)]; exact hru2
    have hwa4 : r4.wa "sp.ptr" = r.wa "sp.ptr" := by
      rw [(hU4.warr "sp.ptr" (by simp)).1, (hU3.warr "sp.ptr" (by simp)).1,
        (hU2.warr "sp.ptr" (by simp)).1, hp1.1]; rfl
    have hwl4 : r4.wlen "sp.ptr" = st.wlen "sp.ptr" := by
      rw [(hU4.warr "sp.ptr" (by simp)).2, (hU3.warr "sp.ptr" (by simp)).2,
        (hU2.warr "sp.ptr" (by simp)).2, hp1.2]; exact hwl
    have hvc4 : vc (G := G) r4 = vc r :=
      (vc_of_unchanged hU4 (by simp)).trans ((vc_of_unchanged hU3 (by simp)).trans
        ((vc_of_unchanged hU2 (by simp)).trans ((vc_of_unchanged hU1 (by simp)).trans rfl)))
    have hc4' : r4.cost = r.cost + 5 := by omega
    -- the inner window loop of `u`
    have f1 : (k + 2) * (Y + 101) ≤ (xs.length + 1) * (Y + 101) :=
      Nat.mul_le_mul_right _ (by omega)
    have f2 : (k + 2) * (Y + 101) = k * (Y + 38) + 63 * k + 2 * Y + 202 := by ring
    have f3 : (st.wa "gSt" ((u : ℕ) + 1) - P0 u + 1) * CED DI.K nb ≤ Y :=
      Nat.mul_le_mul_right _ (by omega)
    -- the use budget of the inner loop: every window prefix of `u` extends to a full stop list
    have huse4 : DI.use r4 = DI.use r :=
      useF (((((Unchanged.charge r 1 [] [] [] []).comp hU1).comp hU2).comp hU3).comp hU4)
        (by decide)
    have hUin : ∀ q', P0 u ≤ q' → q' ≤ st.wa "gSt" ((u : ℕ) + 1) →
        (∀ j (hj : j < G.m), P0 u ≤ j → j < q' → ext (fsk.d u) ⟨j, hj⟩ < B) →
        DI.use r4 + ((slots G (P0 u) q').foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fsk).c ≤ DI.ucap + fsk.c := by
      intro q' hq1 hq2 hwinq
      have hmU : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m := h0.csr.le_m u
      set Q' : Fin G.n → ℕ := fun w => if w ∈ xs.take k then Q w
        else stopOf st (fs0.d w) w (P0 w) B with hQ'
      have hQ'S : ∀ w ∈ xs, ScanStop st (fs0.d w) w (P0 w) (Q' w) B := by
        intro w hw
        by_cases hwk : w ∈ xs.take k
        · simp only [hQ', if_pos hwk]; exact (hdone w hwk).1
        · simp only [hQ', if_neg hwk]; exact stopOf_spec _ w B (h0.csr.le_m w) (hP0 w hw).2
      have hqs : q' ≤ Q' u := by
        simp only [hQ', if_neg hunt]
        obtain ⟨s1, s2, s3, s4⟩ := stopOf_spec (fs0.d u) u B hmU (hP0 u hux).2
        by_contra hlt
        push_neg at hlt
        have hlt' : stopOf st (fs0.d u) u (P0 u) B < G.m := by omega
        exact s4 hlt' (by omega) (by have h := hwinq _ hlt' s1 hlt; rwa [hdu] at h)
      have hwhole : xs.flatMap (fun w => slots G (P0 w) (Q' w)) =
          (Lk ++ slots G (P0 u) q') ++ (slots G q' (Q' u) ++
            (xs.drop (k + 1)).flatMap (fun w => slots G (P0 w) (Q' w))) := by
        have e1 : (xs.take k).flatMap (fun w => slots G (P0 w) (Q' w)) = Lk :=
          List.flatMap_congr (fun w hw => by simp only [hQ', if_pos hw])
        have e2 : slots G (P0 u) (Q' u) = slots G (P0 u) q' ++ slots G q' (Q' u) :=
          slots_split hq1 hqs
        conv_lhs => rw [← List.take_append_drop (k + 1) xs]
        rw [List.flatMap_append, ← List.take_append_getElem hk, List.flatMap_append,
          List.flatMap_singleton, ← hu, e1, e2]
        simp only [List.append_assoc]
      have hpre := foldl_c_prefix (T := T l) (B := B) (lo := some Bi)
        (Lk ++ slots G (P0 u) q') (slots G q' (Q' u) ++
          (xs.drop (k + 1)).flatMap (fun w => slots G (P0 w) (Q' w))) fs0
      rw [← hwhole, List.foldl_append, ← hfsk] at hpre
      have hU' := hUse Q' hQ'S
      have hmono := foldl_c_mono (T := T l) (B := B) (lo := some Bi) Lk fs0
      rw [← hfsk] at hmono
      omega
    apply runs_seq
    refine (winInnerD_spec DI hy r4 fsk H' hR4 u (hdu.trans (hcomp u hux).1)
      (by rw [hdu]; exact (hcomp u hux).2) (P0 u) (st.wa "gSt" ((u : ℕ) + 1)) hp4 hpe4 hgo4
      hru4 ⟨by rw [hg4.1]; exact (hP0 u hux).1, (hP0 u hux).2, by rw [hg4.1]⟩
      (by rw [hnbk, hcap4, ← hnb]; omega) (by rw [hcap4]; exact hm) hUin).mono ?_
    rintro r5 ⟨q, H'', hq0, hqe, hp5, hwin5, hstop5, hE5, hR5, hru5, hpe5, hU5, hc5lo, hc5hi,
      hc5rel, hw5, hv5, hus5⟩
    rw [hnbk, ← hnb] at hc5hi
    have hptr5 := hU5.warr "sp.ptr" (nA _ (by simp))
    have hcap5 : r5.cap = st.cap := hU5.cap.trans hcap4
    -- `sp.ptr[ru] := sp.p`
    apply runs_seq
    refine runs_wstore_val (j := (u : ℕ)) (a := q) (by rw [evalW_var]; exact congrArg some hru5)
      (by rw [evalW_var]; exact congrArg some hp5)
      (by rw [hptr5.2, hwl4]; have := u.isLt; omega) (fun r6 hst6 hU6 hwl6 hc6 => ?_)
    have hi6 : r6.w "sp.i" = k := by
      rw [hU6.wreg "sp.i" (by simp), hU5.wreg "sp.i" (nWi _ (by simp)), hU4.wreg "sp.i" (by decide),
        hU3.wreg "sp.i" (by decide), hU2.wreg "sp.i" (by decide), hU1.wreg "sp.i" (by decide)]
      exact hik
    have hcap6 : r6.cap = st.cap := hU6.cap.trans hcap5
    -- `sp.i := sp.i + 1`
    refine runs_wset_val (evalW_add_of (x := k) (y := 1)
      (by rw [evalW_var]; exact congrArg some hi6) (evalW_lit_of (by omega)) (by omega))
      (fun r7 hi7 hU7 hc7 => ?_)
    have hwa7 : ∀ w : ℕ, r7.wa "sp.ptr" w = if w = u then q else r.wa "sp.ptr" w := by
      intro w
      rw [(hU7.warr "sp.ptr" (by simp)).1, hst6, hptr5.1, hwa4]
    have hvc7 : vc (G := G) r7 = vc r5 :=
      (vc_of_unchanged hU7 (by simp)).trans (vc_of_unchanged hU6 (by decide))
    have hL' : (xs.take (k + 1)).flatMap (fun w => slots G (P0 w) (Function.update Q u q w)) =
        Lk ++ slots G (P0 u) q := by
      rw [← List.take_append_getElem hk, List.flatMap_append, List.flatMap_singleton,
        Function.update_self]
      congr 1
      exact List.flatMap_congr (fun w hw => by
        have hwu : w ≠ u := fun h => hunt (h ▸ hw)
        rw [Function.update_of_ne hwu])
    have f4 : (q - P0 u) * CED DI.K nb ≤ Y := Nat.mul_le_mul_right _ (by omega)
    have f5 : (k + 1) * (Y + 38) = k * (Y + 38) + Y + 38 := by ring
    have hw46 : r4.wlen = r.wlen ∧ r4.vlen = r.vlen := by
      refine ⟨?_, ?_⟩
      · rw [(lenEq_of_unch hU4).1, (lenEq_of_unch hU3).1, (lenEq_of_unch hU2).1,
          (lenEq_of_unch hU1).1]; rfl
      · rw [(lenEq_of_unch hU4).2, (lenEq_of_unch hU3).2, (lenEq_of_unch hU2).2,
          (lenEq_of_unch hU1).2]; rfl
    have hw65 : r6.wlen = r5.wlen := funext fun a => by
      by_cases ha : a = "sp.ptr"
      · subst ha; exact hwl6
      · exact (hU6.warr a (by simpa using ha)).2
    have hv65 : r6.vlen = r5.vlen := funext fun a => (hU6.varr a (by simp)).2
    have hus7 : DI.use r7 = DI.use r5 :=
      (useF hU7 (by decide)).trans (DI.use_frame r5 r6 _ _ _ _ hU6 (by simp))
    refine ⟨H'', Function.update Q u q, hi7, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_,
      by rw [(lenEq_of_unch hU7).1, hw65, hw5, hw46.1]; exact hwL,
      by rw [(lenEq_of_unch hU7).2, hv65, hv5, hw46.2]; exact hvL, ?_⟩
    · exact Unchanged.trans hFW4 (Unchanged.trans
        (toF hU5 (fun x hx => List.mem_append_left _ hx) (fun x hx => hx)
          (fun x hx => by
            rcases List.mem_append.mp hx with h | h
            · exact List.mem_append_left _ (by simp only [allW, inW, List.mem_append] at h ⊢; tauto)
            · exact List.mem_append_right _ h) (fun x hx => hx))
        (Unchanged.trans (toF hU6 (by simp) (by simp) (by simp) (by simp))
          (toF hU7 (by simp) (by simp) (inA (by decide)) (by simp))))
    · rw [(hU7.warr "sp.ptr" (by simp)).2, hwl6, hptr5.2, hwl4]
    · intro w hw
      rw [← List.take_append_getElem hk, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · have hwu : w ≠ u := fun h => hunt (h ▸ hw)
        have hwu' : (w : ℕ) ≠ u := fun h => hwu (Fin.ext h)
        rw [Function.update_of_ne hwu, hwa7, if_neg hwu']
        exact hdone w hw
      · subst hw
        rw [Function.update_self, hwa7, if_pos rfl]
        refine ⟨⟨hq0, hqe, fun j hj h1 h2 => ?_, fun hq hqlt => ?_⟩, rfl⟩
        · have := hwin5 j hj h1 h2; rwa [hdu] at this
        · obtain ⟨hq', h⟩ := hstop5 hqlt
          rw [hdu] at h; exact h
    · intro w hw
      rw [← List.take_append_getElem hk, List.mem_append, List.mem_singleton, not_or] at hw
      have hwu' : (w : ℕ) ≠ u := fun h => hw.2 (Fin.ext h)
      rw [hwa7, if_neg hwu']
      exact hrest w hw.1
    · rw [hvc7]
      exact hE.trans (by rw [← hvc4]; exact hE5)
    · rw [hL', List.foldl_append]
      exact hR5.of_unch (hU6.comp hU7) (by omega) (by decide) (by simp) (by decide) (by simp)
        (by decide) (fun a ha hd => by
          simp only [List.append_nil, List.mem_singleton] at ha; subst ha
          exact DI.hwa _ hd (by simp))
        (by simp) (fun a ha hd => by
          simp only [List.nil_append, List.mem_singleton] at ha; subst ha
          exact DI.hwr _ hd (by decide)) (by simp)
        (hKr (by decide)) ⟨by simp, by simp⟩
    · rw [hL', List.foldl_append, ← hfsk]
      omega
    · rw [hL', List.foldl_append, ← hfsk]
      omega
  · -- exit
    obtain ⟨H', Q, hik, hFW, hwl, hdone, hrest, hE, hR, hclo, hchi, hrel, hwL, hvL, huseK⟩ := hI
    rw [List.take_length] at hdone hrest hR hrel huseK
    have hcapr : r.cap = st.cap := Unchanged.cap hFW
    refine ⟨by rw [evalW_lt_of (s := r) (x := xs.length) (y := xs.length)
        (by rw [evalW_var]; exact congrArg some hik) (hlenE r hFW) (by omega),
        if_neg (lt_irrefl _)], H', Q, hdone, hrest, hwl, hE,
      ofR hR (Unchanged.charge r 1 [] [] [] []) (by simp) (by simp) (by simp) hKn,
      (unch_charge 1).mpr hFW, by simp; omega, by simp; omega, hwL, hvL,
      by rw [useF (Unchanged.charge r 1 [] [] [] []) (by simp)]; exact huseK⟩
  · -- the start
    have hp0 := hU0.warr "sp.ptr" (by simp)
    refine ⟨H0, fun _ => 0, hi0, toF hU0 (by simp) (by simp) (inA (by decide)) (by simp), hp0.2,
      fun u hu => by simp at hu, fun u _ => by rw [hp0.1], ?_, ?_, by omega,
      by rw [zero_mul]; omega, ?_, (lenEq_of_unch hU0).1, (lenEq_of_unch hU0).2,
      by rw [useF hU0 (by decide)]; simp⟩
    · rw [vc_of_unchanged hU0 (by simp)]; exact HExt.refl _ _
    · simp only [List.take_zero, List.flatMap_nil, List.foldl_nil]
      exact ofR h0 hU0 (by omega) (by decide) (by simp) hKn
    · simp only [List.take_zero, List.flatMap_nil, List.foldl_nil]; omega

/-- BM.19–21 over the abstract D layer: agent-08's
`windowScan (candB Kb kbf "sp.lt") (relaxWinD DL.ins Kb kbf Klo klof)`. -/
def winScanD (ins : Stmt) (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Stmt :=
  scanLoopD (load "U.len" (sub (var "lvl") (lit 1))) (load "U" (chr (var "sp.i")))
    (load "sp.ptr" (var "ru")) ins Kb kbf Klo klof

/-- BM.27–28 over the abstract D layer: the scan of a `W'` row from the range heads. -/
def wScanD (lenE elemE : WExpr) (ins : Stmt) (Kb : LReg) (kbf : String) (Klo : LReg)
    (klof : String) : Stmt :=
  scanLoopD lenE elemE (load "gSt" (var "ru")) ins Kb kbf Klo klof

theorem FrameWD.reg {T : ℕ → ℕ} {DI : DInsI G s T} {st r : State ℝ≥0} (h : FrameWD DI st r)
    {x : String} (h1 : x ∉ allW) (h2 : x ∈ scanRegs) : r.w x = st.w x :=
  Unchanged.wreg h x (fun hm => by
    rcases List.mem_append.mp hm with h' | h'
    · exact h1 h'
    · exact DI.hwr x h' h2)

theorem FrameWD.arr {T : ℕ → ℕ} {DI : DInsI G s T} {st r : State ℝ≥0} (h : FrameWD DI st r)
    {a : String} (h1 : a ∉ labW ++ ["sp.ptr"]) (h2 : a ∉ DI.dWA) :
    r.wa a = st.wa a ∧ r.wlen a = st.wlen a :=
  Unchanged.warr h a (fun hm => by
    rcases List.mem_append.mp hm with h' | h'
    · rcases List.mem_append.mp h' with h'' | h''
      · exact h1 (List.mem_append_left _ h'')
      · exact h2 h''
    · exact h1 (List.mem_append_right _ h'))

open Classical in
/-- **BM.19–21 over the abstract D layer** (`L'` = LoopD's window list; pointer invariant
`Bi → B`; RAM cost `≤ (113 + K) ×` Layer-A cost `+ 38 |U_i| + 2`). -/
theorem winScanD_spec {T : ℕ → ℕ} (DI : DInsI G s T) {l : ℕ} {Ds : ℕ → BM.DStrM G s}
    {c0 : ℕ} {B Bi : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    (hy : BlkHygD DI Kb kbf Klo klof) (hsort : CSRSorted G s) (hBiB : Bi ≤ B)
    (hUd : "U" ∉ DI.dWA ∧ "U.len" ∉ DI.dWA) (st : State ℝ≥0) (fs0 : BM.RSt G s)
    (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : RepsD DI l Ds c0 B Bi Kb kbf Klo klof st fs0 H0) (hl1 : 1 ≤ l)
    (hrow : l * G.n < st.cap) (xs : List (Fin G.n)) (hxs : xs.Nodup)
    (hU : RamLevel.RowRep st "U" "U.len" G.n (l - 1) (xs.map Fin.val))
    (hcomp : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧ fs0.d u ≠ ⊤)
    (hptr : ∀ u ∈ xs, PtrAt st (fs0.d u) u Bi)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap)
    (hB : st.cost + (xs.length + 1) * ((G.m + 1) * CED DI.K fs0.Dc.blocks.length + 101) ≤
      c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap)
    (hUse : ∀ L' : List (Fin G.m), L'.Nodup →
      (∀ e, e ∈ L' ↔ G.src e ∈ xs ∧ Bi ≤ ext (fs0.d (G.src e)) e ∧
        ext (fs0.d (G.src e)) e < B) →
      DI.use st + (L'.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c ≤
        DI.ucap + fs0.c) :
    Runs realOps (winScanD DI.ins Kb kbf Klo klof) st (fun r => ∃ (L' : List (Fin G.m))
      (H' : Fin G.n → ℕ → List (Fin G.m)),
      L'.Nodup ∧
      (∀ e, e ∈ L' ↔ G.src e ∈ xs ∧ Bi ≤ ext (fs0.d (G.src e)) e ∧
        ext (fs0.d (G.src e)) e < B) ∧
      HExt H0 (vc st) H' (vc r) ∧
      RepsD DI l Ds c0 B Bi Kb kbf Klo klof r
        (L'.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0) H' ∧
      (∀ u ∈ xs, PtrAt r (fs0.d u) u B) ∧
      (∀ u : Fin G.n, u ∉ xs → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
      r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧ FrameWD DI st r ∧ st.cost ≤ r.cost ∧
      r.cost + (113 + DI.K) * fs0.c ≤ st.cost +
        (113 + DI.K) * (L'.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c +
        38 * xs.length + 2 ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      DI.use r + fs0.c ≤ DI.use st +
        (L'.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bi)) fs0).c) := by
  have hbnd0 : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ st.wa "sp.ptr" u ∧
      st.wa "sp.ptr" u ≤ st.wa "gSt" ((u : ℕ) + 1) := fun u hu => ⟨(hptr u hu).1, (hptr u hu).2.1⟩
  have hlv := h0.lvl
  have hnw := h0.nn
  -- the RAM's relaxation lists are exactly LoopD's window lists
  have hchar : ∀ Q : Fin G.n → ℕ, (∀ u ∈ xs, ScanStop st (fs0.d u) u (st.wa "sp.ptr" u) (Q u) B) →
      (xs.flatMap (fun u : Fin G.n => slots G (st.wa "sp.ptr" u) (Q u))).Nodup ∧
      ∀ e, e ∈ xs.flatMap (fun u : Fin G.n => slots G (st.wa "sp.ptr" u) (Q u)) ↔
        G.src e ∈ xs ∧ Bi ≤ ext (fs0.d (G.src e)) e ∧ ext (fs0.d (G.src e)) e < B := by
    intro Q hQ
    have hbnd : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ st.wa "sp.ptr" u ∧
        Q u ≤ st.wa "gSt" ((u : ℕ) + 1) := fun u hu => ⟨(hptr u hu).1, (hQ u hu).2.1⟩
    refine ⟨flatSlots_nodup h0.csr hxs hbnd, fun e => ?_⟩
    rw [flatSlots_mem h0.csr hbnd e]
    constructor
    · rintro ⟨hu, h1, h2⟩
      exact ⟨hu, (window_char hsort h0.csr (hptr _ hu) (hQ _ hu) e rfl).mp ⟨h1, h2⟩⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, (window_char hsort h0.csr (hptr _ hu) (hQ _ hu) e rfl).mpr h1⟩
  refine (scanLoopD_spec DI hy _ _ _ st fs0 H0 h0 xs hxs (fun u => st.wa "sp.ptr" u) ?_ ?_ ?_
    hbnd0 hcomp hptrl hncap hB hm (fun Q hQ => hUse _ (hchar Q hQ).1 (hchar Q hQ).2)).mono ?_
  · -- the row length
    intro r hr
    have hlv' : r.w "lvl" = l := by rw [hr.reg (by decide) (by decide)]; exact hlv
    have hUl := hr.arr (by decide) hUd.2
    have hcap : r.cap = st.cap := Unchanged.cap hr
    have e1 : evalW r (sub (var "lvl") (lit 1)) = some (l - 1) :=
      evalW_sub_of' (by rw [evalW_var, hlv']) (evalW_lit_of (by omega))
    rw [evalW_load_of e1 (by rw [hUl.2]; exact hU.2.2.1), hUl.1, hU.2.2.2.1, List.length_map]
  · -- the `i`-th vertex of the row
    intro r i hi hr hri
    have hlv' : r.w "lvl" = l := by rw [hr.reg (by decide) (by decide)]; exact hlv
    have hnw' : r.w "n" = G.n := by rw [hr.reg (by decide) (by decide)]; exact hnw
    have hUa := hr.arr (by decide) hUd.1
    have hcap : r.cap = st.cap := Unchanged.cap hr
    have hlen : xs.length ≤ G.n := by have := hU.1; simpa using this
    have hsplit : l * G.n = (l - 1) * G.n + G.n := by
      conv_lhs => rw [show l = (l - 1) + 1 by omega]
      rw [Nat.succ_mul]
    have hwU : (l - 1 + 1) * G.n ≤ st.wlen "U" := hU.2.1
    rw [show l - 1 + 1 = l by omega] at hwU
    have e1 : evalW r (sub (var "lvl") (lit 1)) = some (l - 1) :=
      evalW_sub_of' (by rw [evalW_var, hlv']) (evalW_lit_of (by omega))
    have e2 : evalW r (mul (sub (var "lvl") (lit 1)) (var "n")) = some ((l - 1) * G.n) :=
      evalW_mul_of' e1 (by rw [evalW_var, hnw']) (by omega)
    have e3 : evalW r (chr (var "sp.i")) = some ((l - 1) * G.n + i) :=
      evalW_add_of e2 (by rw [evalW_var, hri]) (by omega)
    rw [evalW_load_of e3 (by rw [hUa.2]; omega), hUa.1,
      hU.2.2.2.2 i (by simpa using hi), List.getElem_map]
  · -- the start slot = the pointer
    intro r u hr hwl hru hpu
    rw [evalW_load_of (j := (u : ℕ)) (by rw [evalW_var]; exact congrArg some hru)
      (by rw [hwl]; have := u.isLt; omega), hpu]
  · rintro r ⟨H', Q, hQ, hrest, hwl, hE, hR, hFW, hclo, hrel, hwL, hvL, huR⟩
    have hc := hchar Q (fun u hu => (hQ u hu).1)
    refine ⟨xs.flatMap (fun u : Fin G.n => slots G (st.wa "sp.ptr" u) (Q u)), H',
      hc.1, hc.2, hE, hR, fun u hu => ?_, hrest, hwl, hFW, hclo, hrel, hwL, hvL, huR⟩
    · exact ptr_advance (hFW.arr (by decide) (fun h => DI.hwa _ h (by simp))).1 hBiB (hptr u hu)
        (hQ u hu).1 (hQ u hu).2

theorem RepsD.shift {T : ℕ → ℕ} {DI : DInsI G s T} {l : ℕ} {Ds : ℕ → BM.DStrM G s} {c0 : ℕ}
    {B Bi : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    {r : State ℝ≥0} {fs : BM.RSt G s} {H' : Fin G.n → ℕ → List (Fin G.m)}
    (h : RepsD DI l Ds c0 B Bi Kb kbf Klo klof r fs H') (k : ℕ) :
    RepsD DI l Ds c0 B Bi Kb kbf Klo klof r ⟨fs.d, fs.g, fs.Dc, fs.c + k⟩ H' :=
  ⟨h.lab, h.dr, h.wk, h.gr, h.csr, h.kb, h.klo, h.uselo, h.lvl, h.nn, h.bd⟩

/-- `fold_full` without the concrete `DInv` (the stability of complete labels needs only
`WalkInv`). -/
theorem fold_full' {st : State ℝ≥0} (hsort : CSRSorted G s) (hcsr : CSRAt st G) {T : ℕ}
    {B lo' : WLab G s} (Q : Fin G.n → ℕ) :
    ∀ (ys : List (Fin G.n)) (st0 : BM.RSt G s), WalkInv st0.d →
      (∀ u ∈ ys, st0.d u = dis (s := s) u ∧
        ScanStop st (dis (s := s) u) u (st.wa "gSt" u) (Q u) B) →
      ∃ k, (ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0 =
        ⟨((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).d,
          ((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).g,
          ((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).Dc,
          ((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).c + k⟩
  | [], st0, _, _ => ⟨0, rfl⟩
  | u :: ys, st0, hw, h => by
    obtain ⟨hdu, q1, q2, q3, q4⟩ := h u (by simp)
    set st1 := (slots G (st.wa "gSt" u) (Q u)).foldl
      (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0 with hst1
    obtain ⟨hw1, -, hstab1⟩ :=
      foldl_invs' (T := T) (B := B) (lo := some lo') (slots G (st.wa "gSt" u) (Q u)) st0 hw
    have hd1u : st1.d u = dis (s := s) u := (hstab1 u hdu).trans hdu
    have htail : ∀ e ∈ slots G (Q u) (st.wa "gSt" ((u : ℕ) + 1)),
        ¬ ext (st1.d (G.src e)) e < B := by
      intro e he
      rw [mem_slots] at he
      have hsrc : G.src e = u := (hcsr.src e u).mpr ⟨le_trans q1 he.1, he.2⟩
      rw [hsrc, hd1u]
      have hqm : Q u < G.m := lt_of_le_of_lt he.1 e.isLt
      have hqe : Q u < st.wa "gSt" ((u : ℕ) + 1) := lt_of_le_of_lt he.1 he.2
      have hsq : G.src ⟨Q u, hqm⟩ = u := (hcsr.src _ u).mpr ⟨q1, hqe⟩
      intro hlt
      exact q4 hqm hqe (lt_of_le_of_lt (hsort ⟨Q u, hqm⟩ e (hsq.trans hsrc.symm) he.1 _) hlt)
    have hsplit := slots_split (G := G) q1 q2
    have hrest : ∀ v ∈ ys, st1.d v = dis (s := s) v ∧
        ScanStop st (dis (s := s) v) v (st.wa "gSt" v) (Q v) B := fun v hv => by
      obtain ⟨h1, h2⟩ := h v (by simp [hv])
      exact ⟨(hstab1 v h1).trans h1, h2⟩
    obtain ⟨k, hk⟩ := fold_full' hsort hcsr Q ys st1 hw1 hrest
    refine ⟨k + (slots G (Q u) (st.wa "gSt" ((u : ℕ) + 1))).length, ?_⟩
    simp only [List.flatMap_cons, List.foldl_append]
    rw [hsplit, List.foldl_append, ← hst1, foldl_invalid _ st1 htail, foldl_shift, hk]
    simp only [BM.RSt.mk.injEq, true_and] <;> omega

open Classical in
/-- **BM.27–28 over the abstract D layer**: the Layer-A list `L` = the full CSR ranges of the
`W'` row (it enumerates the out-edges of `W'`, `fullSlots_enum`). -/
theorem wScanD_spec {T : ℕ → ℕ} (DI : DInsI G s T) {l : ℕ} {Ds : ℕ → BM.DStrM G s}
    {c0 : ℕ} {B Bf : WLab G s} {Kb : LReg} {kbf : String} {Klo : LReg} {klof : String}
    (hy : BlkHygD DI Kb kbf Klo klof) (hsort : CSRSorted G s) (lenE elemE : WExpr)
    (st : State ℝ≥0) (fs0 : BM.RSt G s) (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : RepsD DI l Ds c0 B Bf Kb kbf Klo klof st fs0 H0)
    (xs : List (Fin G.n)) (hxs : xs.Nodup)
    (hlenE : ∀ r, FrameWD DI st r → evalW r lenE = some xs.length)
    (helemE : ∀ r (i : ℕ) (hi : i < xs.length), FrameWD DI st r → r.w "sp.i" = i →
      evalW r elemE = some (xs[i] : ℕ))
    (hcomp : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧ fs0.d u ≠ ⊤)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap)
    (hB : st.cost + (xs.length + 1) * ((G.m + 1) * CED DI.K fs0.Dc.blocks.length + 101) ≤
      c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap)
    (hUse : ∀ L : List (Fin G.m), BM.Enumerates G L xs.toFinset →
      DI.use st + (L.foldl (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c ≤
        DI.ucap + fs0.c) :
    Runs realOps (wScanD lenE elemE DI.ins Kb kbf Klo klof) st (fun r =>
      ∃ H' : Fin G.n → ℕ → List (Fin G.m),
      HExt H0 (vc st) H' (vc r) ∧
      RepsD DI l Ds c0 B Bf Kb kbf Klo klof r
        ((xs.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0) H' ∧
      (∀ u ∈ xs, PtrAt r (fs0.d u) u B) ∧
      (∀ u : Fin G.n, u ∉ xs → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
      r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧ FrameWD DI st r ∧ st.cost ≤ r.cost ∧
      r.cost + (113 + DI.K) * fs0.c ≤ st.cost + (113 + DI.K) * ((xs.flatMap (fun u : Fin G.n =>
        slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c + 38 * xs.length + 2 ∧
      r.wlen = st.wlen ∧ r.vlen = st.vlen ∧
      DI.use r + fs0.c ≤ DI.use st + ((xs.flatMap (fun u : Fin G.n =>
        slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c) := by
  have hP0 : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ st.wa "gSt" u ∧
      st.wa "gSt" u ≤ st.wa "gSt" ((u : ℕ) + 1) := fun u _ => ⟨le_rfl, h0.csr.le u⟩
  -- a stop list costs at most the full enumeration (its skipped tails are invalid)
  have hfullc : ∀ Q : Fin G.n → ℕ, (∀ u ∈ xs, ScanStop st (fs0.d u) u (st.wa "gSt" u) (Q u) B) →
      ∃ k, ((xs.flatMap (fun u : Fin G.n =>
        slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c =
        ((xs.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c + k := by
    intro Q hQ
    have hQ' : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧
        ScanStop st (dis (s := s) u) u (st.wa "gSt" u) (Q u) B := fun u hu => by
      have h1 := (hcomp u hu).1
      exact ⟨h1, h1 ▸ hQ u hu⟩
    obtain ⟨k, hk⟩ := fold_full' (T := T l) (lo' := Bf) hsort h0.csr Q xs fs0 h0.wk hQ'
    exact ⟨k, by rw [hk]⟩
  refine (scanLoopD_spec DI hy lenE elemE _ st fs0 H0 h0 xs hxs
    (fun u => st.wa "gSt" u) hlenE helemE ?_ hP0 hcomp hptrl hncap hB hm (fun Q hQ => by
      obtain ⟨k, hk⟩ := hfullc Q hQ
      have := hUse _ (fullSlots_enum h0.csr hxs)
      omega)).mono ?_
  · intro r u hr _ hru _
    have hg := hr.arr (a := "gSt") (by decide) (fun h => DI.hwa _ h (by simp))
    have hlen := h0.csr.len
    have hu := u.isLt
    rw [evalW_load_of (j := (u : ℕ)) (by rw [evalW_var]; exact congrArg some hru)
      (by rw [hg.2]; omega), hg.1]
  · rintro r ⟨H', Q, hQ, hrest, hwl, hE, hR, hFW, hclo, hrel, hwL, hvL, huR⟩
    have hQ' : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧
        ScanStop st (dis (s := s) u) u (st.wa "gSt" u) (Q u) B := fun u hu => by
      have h1 := (hcomp u hu).1
      exact ⟨h1, h1 ▸ (hQ u hu).1⟩
    obtain ⟨k, hk⟩ := fold_full' (T := T l) (lo' := Bf) hsort h0.csr Q xs fs0 h0.wk hQ'
    obtain ⟨k', hk'⟩ := hfullc Q (fun u hu => (hQ u hu).1)
    refine ⟨H', hE, ?_, fun u hu => ?_, hrest, hwl, hFW, hclo, ?_, hwL, hvL, by omega⟩
    · rw [hk]; exact hR.shift k
    · have hg := (hFW.arr (a := "gSt") (by decide) (fun h => DI.hwa _ h (by simp))).1
      unfold PtrAt
      rw [(hQ u hu).2]
      unfold ScanStop
      rw [hg]
      exact (hQ u hu).1
    · rw [hk]
      show r.cost + (113 + DI.K) * fs0.c ≤ st.cost + (113 + DI.K) * (((xs.flatMap
        (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
        (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c + k) + 38 * xs.length + 2
      have : (113 + DI.K) * (((xs.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c + k) =
          (113 + DI.K) * ((xs.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) (T l) B (some Bf)) fs0).c + (113 + DI.K) * k := by ring
      omega

end Frontier.CHD.WinScan
