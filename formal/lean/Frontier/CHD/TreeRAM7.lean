import Frontier.CHD.TreeRAM6
import Frontier.CHD.BL2Tree

/-!
# Frontier.CHD.TreeRAM7 — agent-09's `TreeI`, instantiated (B-L2 tree layer; owner agent-03)

**NON-GATE** (Layer B).  `treeImpl : TreeI V ops G s`:
* `FR st trees := FR0 st G.n trees` — agent-03's `ForestRep` without the tree-vertex bitmap `fp.fm` (which the
  invocation loop tracks as `Bits fp.fm tv`); footprint `frWA0` (seven tree arrays) and register `tr.nt`;
* `TA := TA0 G.n` — the seven tree arrays have length `≥ n` and `tr.inP` is clean;
* `init := tr.nt := 0` (cost 1);
* `grow := if fp.sres = 3 then newTree else mergeProg` — agent-05's `growForest` (FH.23 new tree / FH.12 contact
  merge), cost `≤ 41 (|K| + 1)`, footprint `trArrs` / `trRegs` (syntactic frame, `WFrame`).
The Layer-A facts `grow` needs (search `K` nodup with head `x`, disjoint from the forest, contact `u ∈ K`,
`v` in the forest, `kpath ⊆ K` nodup) are derived from agent-05's `Search.treeInv`, `Search.result_info`,
`kpath_spec` inside `growProg_spec`, whose hypotheses are exactly `TreeI.grow_spec`'s.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition Frontier.CHD.BL2

variable {V : Type} {ops : VOps V}

/-- The forest arrays of `FR0`. -/
def frWA0 : List String := ["tr.tid", "tr.nx", "fp.par", "tr.inP", "tr.hd", "tr.tl", "tr.ln"]

/-- `ForestRep` without the tree-vertex bitmap. -/
structure FR0 (st : State V) (N : ℕ) (trees : List (TreeRec (Fin N))) : Prop where
  nt : st.w "tr.nt" = trees.length
  ne : ∀ t (ht : t < trees.length), trees[t].ord ≠ []
  root : ∀ t (ht : t < trees.length), trees[t].ord.head? = some trees[t].root
  hd : ∀ t (ht : t < trees.length), trees[t].ord.head?.map Fin.val = some (st.wa "tr.hd" t)
  tl : ∀ t (ht : t < trees.length), trees[t].ord.getLast?.map Fin.val = some (st.wa "tr.tl" t)
  ln : ∀ t (ht : t < trees.length), st.wa "tr.ln" t = trees[t].ord.length
  ll : ∀ t (ht : t < trees.length), LL st "tr.nx" (trees[t].ord.map Fin.val)
  tid : ∀ t (ht : t < trees.length), ∀ v ∈ trees[t].ord, st.wa "tr.tid" v.val = t
  par : ∀ t (ht : t < trees.length), ∀ v ∈ trees[t].ord.tail, st.wa "fp.par" v.val = (trees[t].par v).val
  inP : ∀ v : Fin N, st.wa "tr.inP" v.val = 0
  disj : trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord)
  nodup : ∀ T ∈ trees, T.ord.Nodup
  lens : N ≤ st.wlen "tr.tid" ∧ N ≤ st.wlen "tr.nx" ∧ N ≤ st.wlen "fp.par" ∧ N ≤ st.wlen "tr.inP" ∧
    N ≤ st.wlen "tr.hd" ∧ N ≤ st.wlen "tr.tl" ∧ N ≤ st.wlen "tr.ln"

/-- The tree arrays are allocated (length `≥ N`) and `tr.inP` is clean. -/
def TA0 (N : ℕ) (st : State V) : Prop :=
  (N ≤ st.wlen "tr.tid" ∧ N ≤ st.wlen "tr.nx" ∧ N ≤ st.wlen "fp.par" ∧ N ≤ st.wlen "tr.inP" ∧
    N ≤ st.wlen "tr.hd" ∧ N ≤ st.wlen "tr.tl" ∧ N ≤ st.wlen "tr.ln") ∧ ∀ v : Fin N, st.wa "tr.inP" v.val = 0

theorem ForestRep.toFR0 {st : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} (h : ForestRep st N trees) :
    FR0 st N trees := by
  obtain ⟨-, l2, l3, l4, l5, l6, l7, l8⟩ := h.lens
  exact ⟨h.nt, h.ne, h.root, h.hd, h.tl, h.ln, h.ll, h.tid, h.par, h.inP, h.disj, h.nodup,
    ⟨l2, l3, l4, l5, l6, l7, l8⟩⟩

theorem FR0.toForestRep {st : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} (h : FR0 st N trees)
    (hfm : ∀ v : Fin N, st.wa "fp.fm" v.val = if ∃ T ∈ trees, v ∈ T.ord then 1 else 0)
    (hfml : N ≤ st.wlen "fp.fm") : ForestRep st N trees := by
  obtain ⟨l2, l3, l4, l5, l6, l7, l8⟩ := h.lens
  exact ⟨h.nt, h.ne, h.root, h.hd, h.tl, h.ln, h.ll, h.tid, h.par, hfm, h.inP, h.disj, h.nodup,
    ⟨hfml, l2, l3, l4, l5, l6, l7, l8⟩⟩

theorem FR0.toTA {st : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} (h : FR0 st N trees) : TA0 N st :=
  ⟨h.lens, h.inP⟩

theorem ForestRep.charge {st : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} (h : ForestRep st N trees)
    (k : ℕ) : ForestRep (st.charge k) N trees :=
  ⟨h.nt, h.ne, h.root, h.hd, h.tl, h.ln, fun t ht => LL.frame_charge (h.ll t ht) k, h.tid, h.par, h.fm, h.inP,
    h.disj, h.nodup, h.lens⟩

/-- `FR0` depends only on the arrays `frWA0` and the register `tr.nt`. -/
theorem FR0.frame {st st' : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} (h : FR0 st N trees)
    (hA : ∀ a ∈ frWA0, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a) (hnt : st'.w "tr.nt" = st.w "tr.nt") :
    FR0 st' N trees := by
  have e : ∀ a ∈ frWA0, st'.wa a = st.wa a := fun a ha => (hA a ha).1
  have l : ∀ a ∈ frWA0, st'.wlen a = st.wlen a := fun a ha => (hA a ha).2
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := h.lens
  refine ⟨hnt.trans h.nt, h.ne, h.root, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht v hv => ?_, fun t ht v hv => ?_, fun v => ?_, h.disj, h.nodup, ?_⟩
  · rw [e "tr.hd" (by decide)]; exact h.hd t ht
  · rw [e "tr.tl" (by decide)]; exact h.tl t ht
  · rw [e "tr.ln" (by decide)]; exact h.ln t ht
  · exact LL.frame (h.ll t ht) (fun j _ => by rw [e "tr.nx" (by decide)])
  · rw [e "tr.tid" (by decide)]; exact h.tid t ht v hv
  · rw [e "fp.par" (by decide)]; exact h.par t ht v hv
  · rw [e "tr.inP" (by decide)]; exact h.inP v
  · rw [l "tr.tid" (by decide), l "tr.nx" (by decide), l "fp.par" (by decide), l "tr.inP" (by decide),
      l "tr.hd" (by decide), l "tr.tl" (by decide), l "tr.ln" (by decide)]
    exact ⟨l1, l2, l3, l4, l5, l6, l7⟩

theorem TA0.frame {st st' : State V} {N : ℕ} (h : TA0 N st)
    (hA : ∀ a ∈ frWA0, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a) : TA0 N st' := by
  obtain ⟨⟨l1, l2, l3, l4, l5, l6, l7⟩, hin⟩ := h
  have e : ∀ a ∈ frWA0, st'.wa a = st.wa a := fun a ha => (hA a ha).1
  have l : ∀ a ∈ frWA0, st'.wlen a = st.wlen a := fun a ha => (hA a ha).2
  refine ⟨?_, fun v => ?_⟩
  · rw [l "tr.tid" (by decide), l "tr.nx" (by decide), l "fp.par" (by decide), l "tr.inP" (by decide),
      l "tr.hd" (by decide), l "tr.tl" (by decide), l "tr.ln" (by decide)]
    exact ⟨l1, l2, l3, l4, l5, l6, l7⟩
  · rw [e "tr.inP" (by decide)]; exact hin v

theorem unch_frWA0 {st st' : State V} {wa va wr vr : List String} (hU : Unchanged st st' wa va wr vr)
    (hwa : Disj wa frWA0) : ∀ a ∈ frWA0, st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a :=
  fun a ha => hU.warr a (fun h' => hwa a h' ha)

/-- Postcondition-side cost monotonicity. -/
theorem Runs.cost_mono' {c : Stmt} {s : State V} {Q : State V → Prop} (h : Runs ops c s Q) :
    Runs ops c s (fun r => Q r ∧ s.cost ≤ r.cost) := by
  obtain ⟨f, r, h1, h2⟩ := h
  exact ⟨f, r, h1, h2, exec_cost_mono f c s r h1⟩

theorem sub_of_all {l₁ l₂ : List String} (h : l₁.all (fun a => decide (a ∈ l₂)) = true) : l₁ ⊆ l₂ := by
  intro a ha
  have := List.all_eq_true.mp h a ha
  simpa using this

/-! ## `init` -/

def initProg : Stmt := .wset "tr.nt" (.lit 0)

theorem initProg_spec {N : ℕ} {st : State V} (hTA : TA0 N st) (hcap : 1 < st.cap) :
    Runs ops initProg st (fun st' => FR0 st' N [] ∧ Unchanged st st' [] [] ["tr.nt"] [] ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 1) := by
  obtain ⟨⟨l1, l2, l3, l4, l5, l6, l7⟩, hin⟩ := hTA
  refine runs_wset (a := 0) (by simp [fit_of_lt (show 0 < st.cap by omega)]) ?_
  refine ⟨⟨by simp, fun t ht => absurd ht (by simp), fun t ht => absurd ht (by simp),
    fun t ht => absurd ht (by simp), fun t ht => absurd ht (by simp), fun t ht => absurd ht (by simp),
    fun t ht => absurd ht (by simp), fun t ht => absurd ht (by simp), fun t ht => absurd ht (by simp),
    fun v => hin v, List.Pairwise.nil, fun T hT => absurd hT List.not_mem_nil,
    ⟨l1, l2, l3, l4, l5, l6, l7⟩⟩, ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun y hy => ?_,
    fun _ _ => rfl, rfl, rfl⟩, by simp, by simp⟩
  simp only [List.mem_singleton] at hy
  simp [hy]

/-! ## `grow` -/

/-- (FH.23 / FH.12) One `growForest` step: new tree on success (`fp.sres = 3`), merge on contact. -/
def growProg : Stmt := .ite (.eq (.var "fp.sres") (.lit 3)) newTree mergeProg

theorem mergeTree_eq_mergeRec {G : Graph} (Tr : TreeRec (Fin G.n)) (K : List (Fin G.n))
    (kpar : Fin G.n → Fin G.n) (x u v : Fin G.n) :
    mergeTree (G := G) Tr K kpar x u v = mergeRec Tr K kpar x u v := rfl

/-- **The tree layer's `grow` refines `growForest`** (hypotheses exactly those of `TreeI.grow_spec`). -/
theorem growProg_spec {G : Graph} {s : Fin G.n} {st : State V} {c : FPCtx G s} {ι : IState G s}
    {x : Fin G.n} {σ' : SSt G s} {res : SearchRes} {n : ℕ}
    (hout : OutOK c) (hsort : OutSorted c) (hx : x ∉ ι.tv) (hres : res ≠ .failed)
    (hs : Search c ι.tv (initSt ι.d ι.D x) σ' res n) (hS0 : SInv c (initSt ι.d ι.D x)) (hFI : FInv c ι)
    (hFR : FR0 st G.n ι.trees) (hB : Bits st "fp.fm" ι.tv)
    (hLA : LArr st "fp.K" σ'.K) (hkl : st.w "fp.kl" = σ'.K.length) (hKl : σ'.K.length ≤ st.wlen "fp.K")
    (hkpl : st.wlen "fp.kp" = G.n) (hkp : ∀ v ∈ σ'.K, st.wa "fp.kp" v = σ'.kpar v)
    (hfx : st.w "fp.x" = x)
    (hcont : res = .contact → ∃ a b : Fin G.n, σ'.hit = some (a, b) ∧ st.w "fp.cu" = a ∧
      st.w "fp.cv" = b)
    (hsr : SResCode st res) (hcap : G.n + 2 < st.cap) :
    Runs ops growProg st (fun st' => FR0 st' G.n (growForest res ι.trees x σ') ∧
      Bits st' "fp.fm" (ι.tv ∪ σ'.K.toFinset) ∧
      Unchanged st st' trArrs [] trRegs [] ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 41 * (σ'.K.length + 1)) := by
  -- Layer-A facts
  have hTI : TreeInv c ι.tv x σ' := Search.treeInv hout hsort hs hS0 (treeInv_initSt hx)
  obtain ⟨-, hcI⟩ := Search.result_info hout hsort hs hS0
  obtain ⟨hKnd, hKhd, -⟩ := hTI.pf
  have hKtv : ∀ w ∈ σ'.K, ∀ T ∈ ι.trees, w ∉ T.ord := fun w hw T hT hwT =>
    hTI.disj w hw ((hFI.tv w).mpr ⟨T, hT, hwT⟩)
  have hFn := growForest_inv hout hsort hx hres hs hS0 hFI
  have hF : ForestRep st G.n ι.trees := hFR.toForestRep (fun v => by
      rw [hB.2 v]
      by_cases h : v ∈ ι.tv
      · rw [if_pos h, if_pos ((hFI.tv v).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((hFI.tv v).mpr h'))]) (by rw [hB.1])
  have hK : ∀ i (h : i < σ'.K.length), st.wa "fp.K" i = (σ'.K[i]).val := fun i h => hLA i h
  have hG1 : 0 < G.n := Fin.pos s
  have hfit3 : fit st.cap 3 = some 3 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt (by omega)
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hWS : WS growProg := by
    simp [WS, growProg, newTree, ntLoop, ntBody, markBlk, mergeProg, mergePre, mergeMid, pwLoop, pwBody, pwRec,
      pwIte, rpLoop, rpBody, rpApp, pcLoop, pcBody]
  have hwr : wregsOf growProg ⊆ trRegs := sub_of_all (by decide)
  have hwa : warrsOf growProg ⊆ trArrs := sub_of_all (by decide)
  suffices hmain : Runs ops growProg st (fun st' => ForestRep st' G.n (growForest res ι.trees x σ') ∧
      st'.cost ≤ st.cost + 41 * (σ'.K.length + 1)) by
    refine Runs.mono (Runs.cost_mono' (Runs.wframe hWS hmain)) ?_
    rintro st' ⟨⟨⟨hF', hc'⟩, hW⟩, hmono⟩
    refine ⟨hF'.toFR0, ⟨?_, fun v => ?_⟩, hW.unchanged hwa hwr, hmono, hc'⟩
    · rw [hW.wlen]; exact hB.1
    · rw [hF'.fm v]
      have hv := hFn.tv v
      by_cases h : v ∈ ι.tv ∪ σ'.K.toFinset
      · rw [if_pos h, if_pos (hv.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hv.mpr h'))]
  rcases hsr with ⟨rfl, -⟩ | ⟨rfl, h2⟩ | ⟨rfl, h3⟩
  · exact absurd rfl hres
  · -- contact: merge into the tree of the contact head
    obtain ⟨a, b, hab, hcu, hcv⟩ := hcont rfl
    obtain ⟨u, v, huv, huK, hvT, -⟩ := hcI rfl
    rw [hab] at huv
    obtain ⟨rfl, rfl⟩ : a = u ∧ b = v := by simpa using huv
    refine runs_ite_false (by simp [h2, hfit3, hfit0]) ?_
    obtain ⟨hpA, -, -, hpD, -⟩ := kpath_spec hTI.pf σ'.K.length a huK (List.idxOf_lt_length_of_mem huK).le
    have hgf : growForest .contact ι.trees x σ' =
        ι.trees.map (fun T => if b ∈ T.ord then mergeRec T σ'.K σ'.kpar x a b else T) := by
      simp only [growForest, hab]; rfl
    rw [hgf]
    refine Runs.mono (mergeProg_spec (ops := ops) (st0 := st.charge 1) (hF.charge 1) ((hFI.tv b).mp hvT) hKnd
      hKtv (fun w hw => (hpA w hw).1) hpD hK hkl hKl hkp hkpl.ge hfx hcu hcv hcap) ?_
    rintro st' ⟨hF', -, hc'⟩
    refine ⟨hF', ?_⟩
    simp only [State.charge_cost] at hc'
    omega
  · -- success: a new tree
    refine runs_ite_true (x := 1) (by simp [h3, hfit3, hfit1]) one_ne_zero ?_
    have hgf : growForest .success ι.trees x σ' = ι.trees ++ [⟨x, σ'.K, σ'.kpar⟩] := by simp [growForest]
    rw [hgf]
    have hKne : σ'.K ≠ [] := fun h => by rw [h] at hKhd; simp at hKhd
    refine Runs.mono (newTree_spec (ops := ops) (st0 := st.charge 1) (hF.charge 1) hKne hKhd hKnd hKtv hK hkl
      hKl hkp hkpl.ge hcap) ?_
    rintro st' ⟨hF', -, -, -, -, hc'⟩
    refine ⟨hF', ?_⟩
    simp only [State.charge_cost] at hc'
    omega

/-- **agent-09's `TreeI`, instantiated by agent-03's RAM tree layer.** -/
def treeImpl (V : Type) (ops : VOps V) (G : Graph) (s : Fin G.n) : TreeI V ops G s where
  FR st trees := FR0 st G.n trees
  frWA := frWA0
  frVA := []
  frWR := ["tr.nt"]
  frVR := []
  FR_frame := fun h hU hwa _ hwr _ => FR0.frame h (unch_frWA0 hU hwa)
    (hU.wreg "tr.nt" (fun h' => hwr _ h' (by decide)))
  TA := TA0 G.n
  TA_frame := fun h hU hwa _ _ _ => TA0.frame h (unch_frWA0 hU hwa)
  FR_TA := fun h => FR0.toTA h
  init := initProg
  Cinit := 1
  iWA := []
  iVA := []
  iWR := ["tr.nt"]
  iVR := []
  init_spec := fun hTA hcap => initProg_spec hTA (by omega)
  grow := growProg
  Cg := 41
  gWA := trArrs
  gVA := []
  gWR := trRegs
  gVR := []
  grow_spec := fun hout hsort hx hres hs hS0 hFI hFR hB hLA hkl hKl hkpl hkp hfx hcont hsr hcap =>
    growProg_spec hout hsort hx hres hs hS0 hFI hFR hB hLA hkl hKl hkpl hkp hfx hcont hsr hcap

end Frontier.CHD.PartitionRAM
