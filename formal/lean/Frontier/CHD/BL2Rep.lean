import Frontier.CHD.FPIface

/-!
# Frontier.CHD.BL2Rep — RAM representation of a FindPivots-HD local search (agent-09, B-L2, NON-GATE)

Layout (all FindPivots-private names carry the prefix `fp.`):
* heap: unsorted array `fp.H[0..fp.hsz)`, positions `fp.hp[v]`, membership bitmap `fp.inH`;
* members: `fp.K[0..fp.kl)` in arrival order, bitmap `fp.inK`; valid part: bitmap `fp.val`;
* tree mark `fp.fm` (the trees `T` of the invocation); discovery edges `fp.kp[v]`;
* cap register `fp.k`; end marker register `gM` (= number of slots);
* graph (agent-10's L6 format): heads `gHead`, live out-lists `gHd` / `gNxt`.
The live out-list of `w` is `(c.out w).filter (· ∉ D)` (Layer A's persistent deleted set `D`).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

instance (l₁ l₂ : List String) : Decidable (Disj l₁ l₂) :=
  inferInstanceAs (Decidable (∀ x ∈ l₁, x ∉ l₂))

/-- The registers the FindPivots representation reads or writes. -/
def myRegs : List String :=
  ["fp.u", "fp.p", "fp.pp", "fp.v", "fp.go", "fp.res", "fp.kl", "fp.k", "fp.hsz", "fp.cu",
   "fp.cv", "gM"]

/-- The arrays the FindPivots representation reads or writes. -/
def myArrs : List String :=
  ["gHead", "gNxt", "gHd", "fp.H", "fp.hp", "fp.inH", "fp.K", "fp.inK", "fp.val", "fp.fm",
   "fp.kp"]

/-- The arrays FindPivots WRITES (a subset of `myArrs` plus the tree arrays; `gHead` is read-only). -/
def myWArrs : List String :=
  ["gNxt", "gHd", "fp.H", "fp.hp", "fp.inH", "fp.K", "fp.inK", "fp.val", "fp.fm", "fp.kp"]

/-! ## Generic array views -/

/-- `arr` is a bitmap of the finset `S` over `Fin G.n`. -/
def Bits (st : State V) (arr : String) (S : Finset (Fin G.n)) : Prop :=
  st.wlen arr = G.n ∧ ∀ v : Fin G.n, st.wa arr v = if v ∈ S then 1 else 0

/-- `arr[0..|L|)` lists `L`. -/
def LArr (st : State V) (arr : String) (L : List (Fin G.n)) : Prop :=
  ∀ i (h : i < L.length), st.wa arr i = (L.get ⟨i, h⟩ : ℕ)

/-- The unsorted-array heap represents the finset `H`. -/
def HeapRep (st : State V) (k : ℕ) (H : Finset (Fin G.n)) : Prop :=
  ∃ hl : List (Fin G.n), hl.Nodup ∧ hl.toFinset = H ∧ st.w "fp.hsz" = hl.length ∧
    k ≤ st.wlen "fp.H" ∧ LArr st "fp.H" hl ∧ st.wlen "fp.hp" = G.n ∧
    (∀ i (h : i < hl.length), st.wa "fp.hp" (hl.get ⟨i, h⟩) = i) ∧ Bits st "fp.inH" H

/-- Slot indices of an edge list. -/
def sl (L : List (Fin G.m)) : List ℕ := L.map Fin.val

/-- The live out-list of `w` (slots). -/
def live (c : FPCtx G s) (D : Finset (Fin G.m)) (w : Fin G.n) : List ℕ :=
  sl ((c.out w).filter (fun e => e ∉ D))

/-- All live out-lists are linked from `gHd` through `gNxt`, ending at `G.m`. -/
def OutRep (st : State V) (c : FPCtx G s) (D : Finset (Fin G.m)) : Prop :=
  G.n ≤ st.wlen "gHd" ∧ ∀ w : Fin G.n, Seg st "gNxt" G.m (st.wa "gHd" w) (live c D w) G.m

/-- During the scan of `u`: the other lists are intact; `u`'s live list is split at the cursor
`fp.p` into the already scanned live prefix (last kept slot in `fp.pp`, or `G.m` if none) and
the live part of the remaining Layer-A list `Lrem`. -/
def Cursor (st : State V) (c : FPCtx G s) (D : Finset (Fin G.m)) (u : Fin G.n)
    (Lrem : List (Fin G.m)) : Prop :=
  G.n ≤ st.wlen "gHd" ∧
  (∀ w : Fin G.n, w ≠ u → Seg st "gNxt" G.m (st.wa "gHd" w) (live c D w) G.m) ∧
  ∃ Pre : List (Fin G.m), c.out u = Pre ++ Lrem ∧
    Seg st "gNxt" G.m (st.wa "gHd" u) (sl (Pre.filter (fun e => e ∉ D))) (st.w "fp.p") ∧
    Seg st "gNxt" G.m (st.w "fp.p") (sl (Lrem.filter (fun e => e ∉ D))) G.m ∧
    ((Pre.filter (fun e => e ∉ D) = [] ∧ st.w "fp.pp" = G.m) ∨
      ∃ (P0 : List (Fin G.m)) (e0 : Fin G.m), Pre.filter (fun e => e ∉ D) = P0 ++ [e0] ∧ st.w "fp.pp" = (e0 : ℕ))

/-- The FindPivots-private part of the representation of a search state (everything except the
label layer and the out-lists). -/
structure MyRep (c : FPCtx G s) (T : Finset (Fin G.n)) (σ : SSt G s) (st : State V) : Prop where
  gM : st.w "gM" = G.m
  headL : G.m ≤ st.wlen "gHead"
  head : ∀ q : Fin G.m, st.wa "gHead" q = G.dst q
  heap : HeapRep st c.k σ.H
  kl : st.w "fp.kl" = σ.K.length
  kcap : c.k ≤ st.wlen "fp.K"
  karr : LArr st "fp.K" σ.K
  inK : Bits st "fp.inK" σ.K.toFinset
  val : Bits st "fp.val" σ.val
  fm : Bits st "fp.fm" T
  kpL : st.wlen "fp.kp" = G.n
  kp : ∀ v ∈ σ.K, st.wa "fp.kp" v = σ.kpar v
  kreg : st.w "fp.k" = c.k
  Knd : σ.K.Nodup
  HK : σ.H ⊆ σ.K.toFinset

/-- The label-layer part: labels, bound slot `B`, threshold slot `L_X`. -/
structure LabRep (LI : LabI V ops G s) (c : FPCtx G s) (slB slX : String) (d : Labels G s)
    (g : LI.Gh) (st : State V) : Prop where
  lab : LI.LT st d g
  sB : LI.LS st slB c.B g
  sX : LI.LS st slX c.Lx g

/-! ## Name hygiene: the label layer and FindPivots write disjoint cells -/

/-- Disjointness facts between B-L2's names and B-LAB's footprints / write sets (discharged by
`decide` once B-LAB's names are fixed). -/
structure Names (LI : LabI V ops G s) (slB slX : String) : Prop where
  myR_slB : Disj myRegs (LI.slWR slB)
  myR_slX : Disj myRegs (LI.slWR slX)
  myR_c : Disj myRegs LI.cWR
  myW_tab : Disj myWArrs LI.tabWA
  myA_slB : Disj myArrs (LI.slWA slB)
  myA_slX : Disj myArrs (LI.slWA slX)
  cand_my : Disj LI.candWR myRegs
  cand_slB : Disj LI.candWR (LI.slWR slB)
  cand_slX : Disj LI.candWR (LI.slWR slX)
  candV_slB : Disj LI.candVR (LI.slVR slB)
  candV_slX : Disj LI.candVR (LI.slVR slX)
  cmp_my : Disj LI.cmpWR myRegs
  cmp_slB : Disj LI.cmpWR (LI.slWR slB)
  cmp_slX : Disj LI.cmpWR (LI.slWR slX)
  cmpV_slB : Disj LI.cmpVR (LI.slVR slB)
  cmpV_slX : Disj LI.cmpVR (LI.slVR slX)
  rel_my : Disj LI.relWR myRegs
  rel_slB : Disj LI.relWR (LI.slWR slB)
  rel_slX : Disj LI.relWR (LI.slWR slX)
  relV_slB : Disj LI.relVR (LI.slVR slB)
  relV_slX : Disj LI.relVR (LI.slVR slX)
  relA_my : Disj LI.relWA myArrs
  relA_slB : Disj LI.relWA (LI.slWA slB)
  relA_slX : Disj LI.relWA (LI.slWA slX)
  relAV_slB : Disj LI.relVA (LI.slVA slB)
  relAV_slX : Disj LI.relVA (LI.slVA slX)
  ifc_my : Disj [LI.ru, LI.re, LI.rv] myRegs
  ifc_slB : Disj [LI.ru, LI.re, LI.rv] (LI.slWR slB)
  ifc_slX : Disj [LI.ru, LI.re, LI.rv] (LI.slWR slX)
  ok_c : LI.ok ∉ LI.cWR
  rv_cmp : LI.rv ∉ LI.cmpWR
  cand_rv : LI.rv ∉ LI.candWR
  ru_re : LI.ru ≠ LI.re
  ru_rv : LI.ru ≠ LI.rv
  re_rv : LI.re ≠ LI.rv

/-! ## Frame lemmas -/

theorem Disj.mono_left {l₁ l₁' l₂ : List String} (h : Disj l₁ l₂) (hs : l₁' ⊆ l₁) : Disj l₁' l₂ :=
  fun x hx => h x (hs hx)

theorem Disj.mono_right {l₁ l₂ l₂' : List String} (h : Disj l₁ l₂) (hs : l₂' ⊆ l₂) : Disj l₁ l₂' :=
  fun x hx hx' => h x hx (hs hx')

theorem Disj.symm {l₁ l₂ : List String} (h : Disj l₁ l₂) : Disj l₂ l₁ :=
  fun x hx hx' => h x hx' hx

theorem Disj.singleton {x : String} {l : List String} (h : x ∉ l) : Disj [x] l := by
  intro y hy; simp at hy; subst hy; exact h

theorem Disj.of_mem {x : String} {l₁ l₂ : List String} (h : Disj l₁ l₂) (hx : x ∈ l₁) :
    Disj [x] l₂ :=
  Disj.singleton (h x hx)

/-- `MyRep` only reads FindPivots-private names. -/
theorem MyRep.frame {c : FPCtx G s} {T : Finset (Fin G.n)} {σ : SSt G s} {st st' : State V}
    {wa va wr vr : List String} (h : MyRep c T σ st) (hu : Unchanged st st' wa va wr vr)
    (hwa : Disj wa myArrs) (hwr : Disj wr myRegs) : MyRep c T σ st' := by
  have A : ∀ a ∈ myArrs, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a :=
    fun a ha => hu.warr a (fun h' => hwa a h' ha)
  have R : ∀ x ∈ myRegs, st'.w x = st.w x := fun x hx => hu.wreg x (fun h' => hwr x h' hx)
  have aH := A "gHead" (by simp [myArrs])
  have aHp := A "fp.H" (by simp [myArrs])
  have ahp := A "fp.hp" (by simp [myArrs])
  have ainH := A "fp.inH" (by simp [myArrs])
  have aK := A "fp.K" (by simp [myArrs])
  have ainK := A "fp.inK" (by simp [myArrs])
  have aval := A "fp.val" (by simp [myArrs])
  have afm := A "fp.fm" (by simp [myArrs])
  have akp := A "fp.kp" (by simp [myArrs])
  have rgM := R "gM" (by simp [myRegs])
  have rkl := R "fp.kl" (by simp [myRegs])
  have rk := R "fp.k" (by simp [myRegs])
  have rh := R "fp.hsz" (by simp [myRegs])
  obtain ⟨hl, hnd, hset, hsz, hcap, harr, hpL, hpos, hbL, hb⟩ := h.heap
  refine ⟨by rw [rgM]; exact h.gM, by rw [aH.2]; exact h.headL, fun q => by rw [aH.1]; exact h.head q,
    ⟨hl, hnd, hset, by rw [rh]; exact hsz, by rw [aHp.2]; exact hcap,
      fun i hi => by rw [aHp.1]; exact harr i hi, by rw [ahp.2]; exact hpL,
      fun i hi => by rw [ahp.1]; exact hpos i hi, by rw [ainH.2]; exact hbL,
      fun v => by rw [ainH.1]; exact hb v⟩,
    by rw [rkl]; exact h.kl, by rw [aK.2]; exact h.kcap, fun i hi => by rw [aK.1]; exact h.karr i hi,
    ⟨by rw [ainK.2]; exact h.inK.1, fun v => by rw [ainK.1]; exact h.inK.2 v⟩,
    ⟨by rw [aval.2]; exact h.val.1, fun v => by rw [aval.1]; exact h.val.2 v⟩,
    ⟨by rw [afm.2]; exact h.fm.1, fun v => by rw [afm.1]; exact h.fm.2 v⟩,
    by rw [akp.2]; exact h.kpL, fun v hv => by rw [akp.1]; exact h.kp v hv, by rw [rk]; exact h.kreg,
    h.Knd, h.HK⟩

/-- Charging does not change the representation. -/
theorem MyRep.charge' {c : FPCtx G s} {T : Finset (Fin G.n)} {σ : SSt G s} {st : State V}
    (h : MyRep c T σ st) (k : ℕ) : MyRep c T σ (st.charge k) :=
  h.frame (Unchanged.charge st k [] [] [] []) (Disj.nil_left _) (Disj.nil_left _)

/-- The label-layer part survives writes outside its footprint. -/
theorem LabRep.frame {LI : LabI V ops G s} {c : FPCtx G s} {slB slX : String} {d : Labels G s}
    {g : LI.Gh} {st st' : State V} {wa va wr vr : List String} (h : LabRep LI c slB slX d g st)
    (hu : Unchanged st st' wa va wr vr) (htab : Disj wa LI.tabWA) (htabV : Disj va LI.tabVA)
    (hB : Disj wa (LI.slWA slB)) (hBv : Disj va (LI.slVA slB)) (hBr : Disj wr (LI.slWR slB))
    (hBrv : Disj vr (LI.slVR slB))
    (hX : Disj wa (LI.slWA slX)) (hXv : Disj va (LI.slVA slX)) (hXr : Disj wr (LI.slWR slX))
    (hXrv : Disj vr (LI.slVR slX)) (hc : st.cost ≤ st'.cost) : LabRep LI c slB slX d g st' :=
  ⟨LI.LT_frame h.lab hu htab htabV hc, LI.LS_frame h.sB hu hB hBv hBr hBrv,
    LI.LS_frame h.sX hu hX hXv hXr hXrv⟩

/-- Out-lists only read `gHd` and `gNxt`. -/
theorem OutRep.frame {c : FPCtx G s} {D : Finset (Fin G.m)} {st st' : State V}
    {wa va wr vr : List String} (h : OutRep st c D) (hu : Unchanged st st' wa va wr vr)
    (hwa : Disj wa myArrs) : OutRep st' c D := by
  have hF := hu.warr "gHd" (fun h' => hwa _ h' (by simp [myArrs]))
  have hN := hu.warr "gNxt" (fun h' => hwa _ h' (by simp [myArrs]))
  refine ⟨by rw [hF.2]; exact h.1, fun w => ?_⟩
  rw [hF.1]
  exact (h.2 w).of_eq hN.1 hN.2

theorem Cursor.frame {c : FPCtx G s} {D : Finset (Fin G.m)} {u : Fin G.n} {Lrem : List (Fin G.m)}
    {st st' : State V} {wa va wr vr : List String} (h : Cursor st c D u Lrem)
    (hu : Unchanged st st' wa va wr vr) (hwa : Disj wa myArrs) (hwr : Disj wr myRegs) :
    Cursor st' c D u Lrem := by
  have hF := hu.warr "gHd" (fun h' => hwa _ h' (by simp [myArrs]))
  have hN := hu.warr "gNxt" (fun h' => hwa _ h' (by simp [myArrs]))
  have hp := hu.wreg "fp.p" (fun h' => hwr _ h' (by simp [myRegs]))
  have hpp := hu.wreg "fp.pp" (fun h' => hwr _ h' (by simp [myRegs]))
  obtain ⟨h1, h2, Pre, hPre, hs1, hs2, h3⟩ := h
  refine ⟨by rw [hF.2]; exact h1, fun w hw => ?_, Pre, hPre, ?_, ?_, ?_⟩
  · rw [hF.1]; exact (h2 w hw).of_eq hN.1 hN.2
  · rw [hF.1, hp]; exact hs1.of_eq hN.1 hN.2
  · rw [hp]; exact hs2.of_eq hN.1 hN.2
  · rw [hpp]; exact h3

/-! ## Unchanged for single machine updates -/

theorem unch_setW (st : State V) (x : String) (a : ℕ) :
    Unchanged st (st.setW x a) [] [] [x] [] where
  warr _ _ := ⟨rfl, rfl⟩
  varr _ _ := ⟨rfl, rfl⟩
  wreg y hy := by simp at hy; simp [State.setW, hy]
  vreg _ _ := rfl
  cap := rfl
  procs := rfl

theorem unch_storeW (st : State V) (arr : String) (j a : ℕ) :
    Unchanged st (st.storeW arr j a) [arr] [] [] [] where
  warr b hb := by simp at hb; exact ⟨by funext i; simp [State.storeW, hb], rfl⟩
  varr _ _ := ⟨rfl, rfl⟩
  wreg _ _ := rfl
  vreg _ _ := rfl
  cap := rfl
  procs := rfl

theorem unch_charge' (st : State V) (k : ℕ) : Unchanged st (st.charge k) [] [] [] [] :=
  Unchanged.charge st k [] [] [] []

theorem Unchanged.trans' {st₁ st₂ st₃ : State V} {wa va wr vr wa' va' wr' vr' : List String}
    (h₁ : Unchanged st₁ st₂ wa va wr vr) (h₂ : Unchanged st₂ st₃ wa' va' wr' vr') :
    Unchanged st₁ st₃ (wa ++ wa') (va ++ va') (wr ++ wr') (vr ++ vr') :=
  (h₁.mono (List.subset_append_left _ _) (List.subset_append_left _ _)
      (List.subset_append_left _ _) (List.subset_append_left _ _)).trans
    (h₂.mono (List.subset_append_right _ _) (List.subset_append_right _ _)
      (List.subset_append_right _ _) (List.subset_append_right _ _))

/-- Dot-notation alias of `Unchanged.trans'`. -/
theorem _root_.Frontier.RAM.Unchanged.cat {st₁ st₂ st₃ : State V}
    {wa va wr vr wa' va' wr' vr' : List String}
    (h₁ : Unchanged st₁ st₂ wa va wr vr) (h₂ : Unchanged st₂ st₃ wa' va' wr' vr') :
    Unchanged st₁ st₃ (wa ++ wa') (va ++ va') (wr ++ wr') (vr ++ vr') := Unchanged.trans' h₁ h₂

end Frontier.CHD.BL2
