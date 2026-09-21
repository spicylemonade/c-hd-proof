import Frontier.CHD.TreeRAM8
import Frontier.CHD.MarkLoop

/-!
# Frontier.CHD.TreeRAM9 — (T4) FP-TAIL: from the forest to the pivot groups (owner agent-03)

**NON-GATE** (Layer B).  After agent-09's invocation loop, `fpTail sA`:
1. compacts the forest (T3, `compactProg`) into the PT layout;
2. marks `S` (the roots `sA[fp.sb, fp.sb + fp.sn)`) in `fp.inS` and `Q` (`fp.Q[fp.ob, fp.ob + fp.ql)`) in `fp.inQ`;
3. runs the PT program (`ptProg`: Algorithm 5 on every tree, then MakePivots) — groups as `GrpOut`;
4. clears `fp.inS`, `fp.inQ` and the tree-vertex bitmap `fp.fm` (over `fp.TV[0, Σ|T|)`).
`fpTail_spec`: the groups are exactly Layer A's `forestGroups S Q k trees` (relabelled by `Fin.val`, via the
equivariance lemmas of `PartitionMap`), `fp.fm = ∅` and the tail arrays are clean again (`PTA`), footprint
`tailWA`/`tailWR` (syntactic frame), cost `≤ 188 Σ|T| + 8 |S| + 8 |Q| + 30`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition Frontier.CHD.BL2

variable {V : Type} {ops : VOps V}

/-- Boolean test for word-only statements (decided by evaluation). -/
def wsB : Stmt → Bool
  | .skip => true
  | .wset _ _ => true
  | .wstore _ _ _ => true
  | .seq a b => wsB a && wsB b
  | .ite _ a b => wsB a && wsB b
  | .while _ b => wsB b
  | _ => false

theorem WS_of_wsB : ∀ c, wsB c = true → WS c
  | .skip, _ => trivial
  | .wset _ _, _ => trivial
  | .wstore _ _ _, _ => trivial
  | .seq a b, h => by
    simp only [wsB, Bool.and_eq_true] at h; exact ⟨WS_of_wsB a h.1, WS_of_wsB b h.2⟩
  | .ite _ a b, h => by
    simp only [wsB, Bool.and_eq_true] at h; exact ⟨WS_of_wsB a h.1, WS_of_wsB b h.2⟩
  | .while _ b, h => WS_of_wsB b h
  | .vset _ _, h => by simp [wsB] at h
  | .vle _ _ _, h => by simp [wsB] at h
  | .vstore _ _ _, h => by simp [wsB] at h
  | .walloc _ _, h => by simp [wsB] at h
  | .valloc _ _, h => by simp [wsB] at h
  | .call _, h => by simp [wsB] at h

/-- `ForestAt` depends only on `fp.nt`, `fp.toff`, `fp.tlen`, `fp.TV`, `fp.par` and the lengths. -/
theorem ForestAt.frame {st st' : State V} {trees : List (TreeRec ℕ)} (h : ForestAt st trees)
    (hnt : st'.w "fp.nt" = st.w "fp.nt") (hlen : st'.wlen = st.wlen)
    (e1 : st'.wa "fp.toff" = st.wa "fp.toff") (e2 : st'.wa "fp.tlen" = st.wa "fp.tlen")
    (e3 : st'.wa "fp.TV" = st.wa "fp.TV") (e4 : st'.wa "fp.par" = st.wa "fp.par") : ForestAt st' trees := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hnt.trans h1, by rw [hlen]; exact h2, fun t ht => ?_, fun T hT v hv => by rw [e4]; exact h4 T hT v hv,
    h5, h6⟩
  obtain ⟨a, b, c⟩ := h3 t ht
  exact ⟨by rw [e1, hlen]; exact a, by rw [e2]; exact b, fun j hj => by rw [e3, e1]; exact c j hj⟩

/-- The tail arrays are allocated (length `≥ N`, `pt.GV` `≥ 2N`) and the bitmaps are clean. -/
structure PTA (N : ℕ) (st : State V) : Prop where
  len : N ≤ st.wlen "pt.an" ∧ N ≤ st.wlen "pt.af" ∧ N ≤ st.wlen "pt.al" ∧ N ≤ st.wlen "pt.nx" ∧
    N ≤ st.wlen "fp.inS" ∧ N ≤ st.wlen "fp.inQ" ∧ N ≤ st.wlen "pt.as" ∧
    N ≤ st.wlen "pt.PT" ∧ N ≤ st.wlen "pt.PF" ∧ N ≤ st.wlen "pt.PL" ∧ N ≤ st.wlen "pt.PN" ∧
    2 * N ≤ st.wlen "pt.GV" ∧ N ≤ st.wlen "pt.GO" ∧ N ≤ st.wlen "pt.GL" ∧
    N ≤ st.wlen "fp.TV" ∧ N ≤ st.wlen "fp.toff" ∧ N ≤ st.wlen "fp.tlen"
  inS : BitRep st "fp.inS" ∅ N
  inQ : BitRep st "fp.inQ" ∅ N
  as : BitRep st "pt.as" ∅ N

/-! ## Marking a stored segment -/

def markSeg (eb ee : WExpr) (arrL arrB : String) (val : ℕ) : Stmt :=
  .seq (.wset "mk.j" eb) (.seq (.wset "mk.e" ee) (markLoop arrL arrB val))

theorem markSeg_spec {st : State V} {eb ee : WExpr} {arrL arrB : String} {val b : ℕ} {L : List ℕ}
    (hLB : arrL ≠ arrB) (hb : evalW st eb = some b)
    (he : evalW ((st.setW "mk.j" b).charge 1) ee = some (b + L.length))
    (hseg : SegAt st arrL b L) (hLl : b + L.length ≤ st.wlen arrL) (hBl : ∀ x ∈ L, x < st.wlen arrB)
    (hcap : b + L.length + 1 < st.cap) (hval : val < st.cap) :
    Runs ops (markSeg eb ee arrL arrB val) st (fun st' =>
      (∀ x, st'.wa arrB x = if x ∈ L then val else st.wa arrB x) ∧
      (∀ arr j, arr ≠ arrB → st'.wa arr j = st.wa arr j) ∧
      (∀ y, y ≠ "mk.x" → y ≠ "mk.j" → y ≠ "mk.e" → st'.w y = st.w y) ∧ st'.wlen = st.wlen ∧
      st'.cap = st.cap ∧ st'.cost ≤ st.cost + 4 * L.length + 3) := by
  apply runs_seq
  refine runs_wset (a := b) hb ?_
  apply runs_seq
  refine runs_wset (a := b + L.length) he ?_
  generalize hs2 : (((st.setW "mk.j" b).charge 1).setW "mk.e" (b + L.length)).charge 1 = s2
  have h2wa : s2.wa = st.wa := by rw [← hs2]; rfl
  have h2len : s2.wlen = st.wlen := by rw [← hs2]; rfl
  have h2cap : s2.cap = st.cap := by rw [← hs2]; rfl
  have h2cost : s2.cost = st.cost + 2 := by rw [← hs2]; simp
  have h2j : s2.w "mk.j" = b := by rw [← hs2]; simp
  have h2e : s2.w "mk.e" = b + L.length := by rw [← hs2]; simp
  have h2w : ∀ y, y ≠ "mk.j" → y ≠ "mk.e" → s2.w y = st.w y := by
    intro y h1 h2; rw [← hs2]; simp [h1, h2]
  have hMK : MKI s2 arrL arrB val b L (s2.cost + 4 * L.length) L.length s2 :=
    ⟨le_refl _, by rw [h2j]; simp, fun x => by simp, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, le_refl _⟩
  refine Runs.mono (markLoop_spec (ops := ops) (st0 := s2) hLB (fun i hi => by rw [h2wa]; exact hseg i hi) h2e
    (by rw [h2len]; exact hLl) (fun x hx => by rw [h2len]; exact hBl x hx) (by rw [h2cap]; exact hcap)
    (by rw [h2cap]; exact hval) _ s2 hMK) ?_
  rintro st' ⟨hB, harr, hreg, hlen, hcap', hcost⟩
  refine ⟨fun x => by rw [hB x, h2wa], fun arr j h => by rw [harr arr j h, h2wa], fun y h1 h2 h3 => by
    rw [hreg y h1 h2, h2w y h2 h3], by rw [hlen, h2len], by rw [hcap', h2cap], by omega⟩

/-! ## The tail -/

def markS (sA : String) (v : ℕ) : Stmt :=
  markSeg (.var "fp.sb") (.add (.var "fp.sb") (.var "fp.sn")) sA "fp.inS" v

def markQ (v : ℕ) : Stmt := markSeg (.var "fp.ob") (.add (.var "fp.ob") (.var "fp.ql")) "fp.Q" "fp.inQ" v

def clearFm : Stmt := markSeg (.lit 0) (.var "ct.o") "fp.TV" "fp.fm" 0

/-- (T4) FP-TAIL. -/
def fpTail (sA : String) : Stmt :=
  .seq compactProg <| .seq (markS sA 1) <| .seq (markQ 1) <|
  .seq (.wset "pt.km1" (.sub (.var "fp.k") (.lit 1))) <| .seq ptProg <|
  .seq (markS sA 0) <| .seq (markQ 0) clearFm

/-- Arrays written by the tail. -/
def tailWA : List String := ["fp.TV", "fp.toff", "fp.tlen", "fp.inS", "fp.inQ", "fp.fm"] ++ ptOut

/-- Registers written by the tail. -/
def tailWR : List String := ctRegs ++ ["fp.nt", "mk.j", "mk.e", "mk.x", "pt.km1"] ++ ptRegs

theorem fpTail_ws (sA : String) : WS (fpTail sA) := WS_of_wsB _ rfl

theorem fpTail_wregs (sA : String) : wregsOf (fpTail sA) ⊆ tailWR := by
  rw [show wregsOf (fpTail sA) = wregsOf (fpTail "") from rfl]; exact sub_of_all (by decide)

theorem fpTail_warrs (sA : String) : warrsOf (fpTail sA) ⊆ tailWA := by
  rw [show warrsOf (fpTail sA) = warrsOf (fpTail "") from rfl]; exact sub_of_all (by decide)

/-- **(T4) FP-TAIL refines Layer A's pivot groups**: from the tree layer's forest (`FR0`, with agent-05's
parent-first trees), the tree-vertex bitmap, the roots `S` at `sA` and the failed roots `Q`, the tail stores
exactly `forestGroups S Q k trees` (relabelled by `Fin.val`) as `GrpOut`, clears `fp.fm` and its own bitmaps. -/
theorem fpTail_spec {G : Graph} {st0 : State V} {trees : List (TreeRec (Fin G.n))}
    {tv S Q : Finset (Fin G.n)} {SL ql : List (Fin G.n)} {k : ℕ} {sA : String}
    (hk : 2 ≤ k) (hFR : FR0 st0 G.n trees) (hpf : ∀ T ∈ trees, ParentFirst T.par T.root T.ord)
    (htv : ∀ v, v ∈ tv ↔ ∃ T ∈ trees, v ∈ T.ord) (hfm : Bits st0 "fp.fm" tv)
    (hSL : ∀ x, x ∈ SL ↔ x ∈ S)
    (hroots : ∀ j (h : j < SL.length), st0.wa sA (st0.w "fp.sb" + j) = (SL[j] : ℕ))
    (hsbL : st0.w "fp.sb" + SL.length ≤ st0.wlen sA) (hsn : st0.w "fp.sn" = SL.length)
    (hql : ∀ x, x ∈ ql ↔ x ∈ Q)
    (hQ : ∀ i (h : i < ql.length), st0.wa "fp.Q" (st0.w "fp.ob" + i) = (ql[i] : ℕ))
    (hqlen : st0.w "fp.ql" = ql.length) (hQL : st0.w "fp.ob" + ql.length ≤ st0.wlen "fp.Q")
    (hkreg : st0.w "fp.k" = k) (hPTA : PTA G.n st0) (hsA : sA ∉ tailWA)
    (hcap : 2 * G.n + st0.w "fp.sb" + SL.length + st0.w "fp.ob" + ql.length + 2 * k + 4 < st0.cap) :
    Runs ops (fpTail sA) st0 (fun st' =>
      GrpOut st' ((forestGroups S Q k trees).map (List.map Fin.val)) ∧
      Bits st' "fp.fm" (∅ : Finset (Fin G.n)) ∧ PTA G.n st' ∧
      Unchanged st0 st' tailWA [] tailWR [] ∧
      st'.cost ≤ st0.cost + 188 * (trees.map (fun T => T.ord.length)).sum + 8 * SL.length +
        8 * ql.length + 30) := by
  obtain ⟨lan, laf, lal, lnx', lS, lQ, las, lPT, lPF, lPL, lPN, lGV, lGO, lGL, lTV, ltoff, ltlen⟩ := hPTA.len
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hFR.lens
  have hsig := sum_len_le hFR.disj hFR.nodup
  have hsumN : ((trees.map natTree).map (fun T => T.ord.length)).sum = (trees.map (fun T => T.ord.length)).sum := by
    simp [natTree, relabel, Function.comp_def]
  have hsA' : ∀ a ∈ tailWA, sA ≠ a := fun a ha h => hsA (h ▸ ha)
  have sTV : sA ≠ "fp.TV" := hsA' _ (by decide)
  have stoff : sA ≠ "fp.toff" := hsA' _ (by decide)
  have stlen : sA ≠ "fp.tlen" := hsA' _ (by decide)
  have sinS : sA ≠ "fp.inS" := hsA' _ (by decide)
  have sinQ : sA ≠ "fp.inQ" := hsA' _ (by decide)
  have sfm : sA ≠ "fp.fm" := hsA' _ (by decide)
  have sptOut : sA ∉ ptOut := fun h => hsA (List.mem_append_right _ h)
  have memS : ∀ x, x ∈ SL.map Fin.val ↔ x ∈ S.image Fin.val := by
    intro x; simp only [List.mem_map, Finset.mem_image]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, (hSL a).mp ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, (hSL a).mpr ha, h⟩⟩
  have memQ : ∀ x, x ∈ ql.map Fin.val ↔ x ∈ Q.image Fin.val := by
    intro x; simp only [List.mem_map, Finset.mem_image]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, (hql a).mp ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, (hql a).mpr ha, h⟩⟩
  suffices hmain : Runs ops (fpTail sA) st0 (fun st' =>
      GrpOut st' ((forestGroups S Q k trees).map (List.map Fin.val)) ∧
      Bits st' "fp.fm" (∅ : Finset (Fin G.n)) ∧ PTA G.n st' ∧
      st'.cost ≤ st0.cost + 188 * (trees.map (fun T => T.ord.length)).sum + 8 * SL.length +
        8 * ql.length + 30) by
    refine Runs.mono (Runs.wframe (fpTail_ws sA) hmain) ?_
    rintro st' ⟨⟨h1, h2, h3, h4⟩, hW⟩
    exact ⟨h1, h2, h3, hW.unchanged (fpTail_warrs sA) (fpTail_wregs sA), h4⟩
  -- (1) compaction
  apply runs_seq
  refine Runs.mono (compact_forestAt (ops := ops) hFR hpf ⟨lTV, ltoff, ltlen⟩ (by omega)) ?_
  rintro s1 ⟨hFA1, -, hct1, hTV1, htoff1, h1arr, h1reg, h1len, h1cap, h1cost⟩
  have r1 : ∀ y, y ≠ "fp.nt" → y ∉ ctRegs → s1.w y = st0.w y := h1reg
  -- (2) mark `S`
  have hsb1 : s1.w "fp.sb" = st0.w "fp.sb" := r1 _ (by decide) (by decide)
  have hsn1 : s1.w "fp.sn" = SL.length := by rw [r1 _ (by decide) (by decide)]; exact hsn
  have hseg1 : SegAt s1 sA (st0.w "fp.sb") (SL.map Fin.val) := fun i hi => by
    rw [h1arr sA _ sTV stoff stlen]; simpa using hroots i (by simpa using hi)
  apply runs_seq
  refine Runs.mono (markSeg_spec (ops := ops) (st := s1) (L := SL.map Fin.val) sinS (by simp [hsb1])
    (by simp [hsb1, hsn1, fit_of_lt (show st0.w "fp.sb" + SL.length < s1.cap by rw [h1cap]; omega)])
    hseg1 (by rw [h1len]; simpa using hsbL) (fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; rw [h1len]; have := a.2; omega)
    (by rw [h1cap]; simp; omega) (by rw [h1cap]; omega)) ?_
  rintro s2 ⟨h2S, h2arr, h2reg, h2len, h2cap, h2cost⟩
  -- (3) mark `Q`
  have r2 : ∀ y, y ≠ "mk.x" → y ≠ "mk.j" → y ≠ "mk.e" → y ≠ "fp.nt" → y ∉ ctRegs → s2.w y = st0.w y :=
    fun y a b c d e => by rw [h2reg y a b c, r1 y d e]
  have hob2 : s2.w "fp.ob" = st0.w "fp.ob" := r2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hql2 : s2.w "fp.ql" = ql.length := by
    rw [r2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hqlen
  have hseg2 : SegAt s2 "fp.Q" (st0.w "fp.ob") (ql.map Fin.val) := fun i hi => by
    rw [h2arr _ _ (by decide), h1arr _ _ (by decide) (by decide) (by decide)]
    simpa using hQ i (by simpa using hi)
  apply runs_seq
  refine Runs.mono (markSeg_spec (ops := ops) (st := s2) (L := ql.map Fin.val) (by decide) (by simp [hob2])
    (by simp [hob2, hql2, fit_of_lt (show st0.w "fp.ob" + ql.length < s2.cap by rw [h2cap, h1cap]; omega)])
    hseg2 (by rw [h2len, h1len]; simpa using hQL) (fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; rw [h2len, h1len]; have := a.2; omega)
    (by rw [h2cap, h1cap]; simp; omega) (by rw [h2cap, h1cap]; omega)) ?_
  rintro s3 ⟨h3Q, h3arr, h3reg, h3len, h3cap, h3cost⟩
  have r3 : ∀ y, y ≠ "mk.x" → y ≠ "mk.j" → y ≠ "mk.e" → y ≠ "fp.nt" → y ∉ ctRegs → s3.w y = st0.w y :=
    fun y a b c d e => by rw [h3reg y a b c, r2 y a b c d e]
  have hk3 : s3.w "fp.k" = k := by
    rw [r3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hkreg
  -- (4) `pt.km1 := fp.k - 1`
  have hcap3 : 1 < s3.cap := by rw [h3cap, h2cap, h1cap]; omega
  apply runs_seq
  refine runs_wset (a := k - 1) (by simp [hk3, fit_of_lt hcap3]) ?_
  generalize hs4 : (s3.setW "pt.km1" (k - 1)).charge 1 = s4
  have h4wa : s4.wa = s3.wa := by rw [← hs4]; rfl
  have h4len : s4.wlen = s3.wlen := by rw [← hs4]; rfl
  have h4cap : s4.cap = s3.cap := by rw [← hs4]; rfl
  have h4cost : s4.cost = s3.cost + 1 := by rw [← hs4]; simp
  have h4km : s4.w "pt.km1" = k - 1 := by rw [← hs4]; simp
  have h4w : ∀ y, y ≠ "pt.km1" → s4.w y = s3.w y := by intro y h; rw [← hs4]; simp [h]
  -- the facts at `s4`
  have e4 : ∀ a j, a ≠ "fp.inS" → a ≠ "fp.inQ" → a ≠ "fp.TV" → a ≠ "fp.toff" → a ≠ "fp.tlen" →
      s4.wa a j = st0.wa a j := fun a j a1 a2 a3 a4 a5 => by
    rw [h4wa, h3arr a j a2, h2arr a j a1, h1arr a j a3 a4 a5]
  have e41 : ∀ a j, a ≠ "fp.inS" → a ≠ "fp.inQ" → s4.wa a j = s1.wa a j := fun a j a1 a2 => by
    rw [h4wa, h3arr a j a2, h2arr a j a1]
  have hlen4 : s4.wlen = st0.wlen := by rw [h4len, h3len, h2len, h1len]
  have hcap4 : s4.cap = st0.cap := by rw [h4cap, h3cap, h2cap, h1cap]
  have hFA4 : ForestAt s4 (trees.map natTree) := hFA1.frame
    (by rw [h4w _ (by decide), h3reg _ (by decide) (by decide) (by decide),
      h2reg _ (by decide) (by decide) (by decide)])
    (by rw [h4len, h3len, h2len])
    (funext fun j => e41 _ j (by decide) (by decide)) (funext fun j => e41 _ j (by decide) (by decide))
    (funext fun j => e41 _ j (by decide) (by decide)) (funext fun j => e41 _ j (by decide) (by decide))
  have hSb4 : BitRep s4 "fp.inS" (S.image Fin.val) G.n := by
    intro x hx
    rw [h4wa, h3arr _ _ (by decide), h2S x, h1arr _ _ (by decide) (by decide) (by decide), hPTA.inS x hx]
    by_cases h : x ∈ SL.map Fin.val
    · rw [if_pos h, if_pos ((memS x).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((memS x).mpr h'))]; simp
  have hQb4 : BitRep s4 "fp.inQ" (Q.image Fin.val) G.n := by
    intro x hx
    rw [h4wa, h3Q x, h2arr _ _ (by decide), h1arr _ _ (by decide) (by decide) (by decide), hPTA.inQ x hx]
    by_cases h : x ∈ ql.map Fin.val
    · rw [if_pos h, if_pos ((memQ x).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((memQ x).mpr h'))]; simp
  have hA4 : BitRep s4 "pt.as" ∅ G.n := fun x hx => by
    rw [e4 _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hPTA.as x hx
  -- (5) the PT program
  apply runs_seq
  refine Runs.mono (ptProg_spec (ops := ops) (st0 := s4) (k := k) (N := G.n) (trees := trees.map natTree)
    (S := S.image Fin.val) (Q := Q.image Fin.val) hk hFA4
    (fun T hT x hx => by
      obtain ⟨T0, -, rfl⟩ := List.mem_map.mp hT
      simp only [natTree, relabel] at hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact a.2)
    (by rw [hlen4]; exact ⟨l3, lan, laf, lal, lnx', lS, lQ, las⟩)
    (by rw [hlen4, hsumN]; exact ⟨by omega, by omega, by omega, by omega⟩)
    (by rw [hlen4, hsumN]; exact ⟨by omega, by omega, by omega⟩)
    (fun t ht => by
      have ht' : t < trees.length := by simpa using ht
      have hb := htoff1 t ht'
      rw [e41 _ _ (by decide) (by decide), hcap4]
      simp only [List.getElem_map, natTree, relabel, List.length_map]
      omega)
    (by rw [hcap4]; omega) (by rw [hcap4, hsumN]; omega) h4km hSb4 hQb4 hA4) ?_
  rintro s5 ⟨hG5, hA5, h5arr, h5reg, h5len, h5cap, h5cost⟩
  have r5 : ∀ y, y ∉ ptRegs → y ≠ "pt.km1" → y ≠ "mk.x" → y ≠ "mk.j" → y ≠ "mk.e" → y ≠ "fp.nt" →
      y ∉ ctRegs → s5.w y = st0.w y := fun y a b c d e f g => by
    rw [h5reg y a, h4w y b, r3 y c d e f g]
  have e5 : ∀ a j, a ∉ ptOut → a ≠ "fp.inS" → a ≠ "fp.inQ" → a ≠ "fp.TV" → a ≠ "fp.toff" → a ≠ "fp.tlen" →
      s5.wa a j = st0.wa a j := fun a j a0 a1 a2 a3 a4 a5' => by rw [h5arr a j a0, e4 a j a1 a2 a3 a4 a5']
  have hlen5 : s5.wlen = st0.wlen := by rw [h5len, hlen4]
  have hcap5 : s5.cap = st0.cap := by rw [h5cap, hcap4]
  -- (6) clear `S`
  have hsb5 : s5.w "fp.sb" = st0.w "fp.sb" :=
    r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsn5 : s5.w "fp.sn" = SL.length := by
    rw [r5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsn
  have hseg5 : SegAt s5 sA (st0.w "fp.sb") (SL.map Fin.val) := fun i hi => by
    rw [e5 sA _ sptOut sinS sinQ sTV stoff stlen]; simpa using hroots i (by simpa using hi)
  apply runs_seq
  refine Runs.mono (markSeg_spec (ops := ops) (st := s5) (L := SL.map Fin.val) (val := 0) sinS (by simp [hsb5])
    (by simp [hsb5, hsn5, fit_of_lt (show st0.w "fp.sb" + SL.length < s5.cap by rw [hcap5]; omega)])
    hseg5 (by rw [hlen5]; simpa using hsbL) (fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; rw [hlen5]; have := a.2; omega)
    (by rw [hcap5]; simp; omega) (by rw [hcap5]; omega)) ?_
  rintro s6 ⟨h6S, h6arr, h6reg, h6len, h6cap, h6cost⟩
  -- (7) clear `Q`
  have r6 : ∀ y, y ∉ ptRegs → y ≠ "pt.km1" → y ≠ "mk.x" → y ≠ "mk.j" → y ≠ "mk.e" → y ≠ "fp.nt" →
      y ∉ ctRegs → s6.w y = st0.w y := fun y a b c d e f g => by rw [h6reg y c d e, r5 y a b c d e f g]
  have hob6 : s6.w "fp.ob" = st0.w "fp.ob" :=
    r6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hql6 : s6.w "fp.ql" = ql.length := by
    rw [r6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hqlen
  have hseg6 : SegAt s6 "fp.Q" (st0.w "fp.ob") (ql.map Fin.val) := fun i hi => by
    rw [h6arr _ _ (by decide), e5 _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa using hQ i (by simpa using hi)
  have hlen6 : s6.wlen = st0.wlen := by rw [h6len, hlen5]
  have hcap6 : s6.cap = st0.cap := by rw [h6cap, hcap5]
  apply runs_seq
  refine Runs.mono (markSeg_spec (ops := ops) (st := s6) (L := ql.map Fin.val) (val := 0) (by decide)
    (by simp [hob6])
    (by simp [hob6, hql6, fit_of_lt (show st0.w "fp.ob" + ql.length < s6.cap by rw [hcap6]; omega)])
    hseg6 (by rw [hlen6]; simpa using hQL) (fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; rw [hlen6]; have := a.2; omega)
    (by rw [hcap6]; simp; omega) (by rw [hcap6]; omega)) ?_
  rintro s7 ⟨h7Q, h7arr, h7reg, h7len, h7cap, h7cost⟩
  -- (8) clear `fp.fm` over the tree vertices
  have r7 : ∀ y, y ∉ ptRegs → y ≠ "pt.km1" → y ≠ "mk.x" → y ≠ "mk.j" → y ≠ "mk.e" → s7.w y = s1.w y :=
    fun y a b c d e => by rw [h7reg y c d e, h6reg y c d e, h5reg y a, h4w y b, h3reg y c d e, h2reg y c d e]
  have hlen7 : s7.wlen = st0.wlen := by rw [h7len, hlen6]
  have hcap7 : s7.cap = st0.cap := by rw [h7cap, hcap6]
  have hct7 : s7.w "ct.o" = (trees.map (fun T => T.ord.length)).sum := by
    rw [r7 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hct1
  have hflat : ((trees.map (fun T => T.ord.map Fin.val)).flatten).length = (trees.map (fun T => T.ord.length)).sum := by
    simp [List.length_flatten, Function.comp_def]
  have e71 : ∀ a j, a ∉ ptOut → a ≠ "fp.inS" → a ≠ "fp.inQ" → s7.wa a j = s1.wa a j := fun a j a0 a1 a2 => by
    rw [h7arr a j a2, h6arr a j a1, h5arr a j a0, e41 a j a1 a2]
  have hseg7 : SegAt s7 "fp.TV" 0 (trees.map (fun T => T.ord.map Fin.val)).flatten := fun i hi => by
    rw [e71 _ _ (by decide) (by decide) (by decide)]; exact hTV1 i hi
  have hfmlen : s7.wlen "fp.fm" = G.n := by rw [hlen7]; exact hfm.1
  refine Runs.mono (markSeg_spec (ops := ops) (st := s7) (L := (trees.map (fun T => T.ord.map Fin.val)).flatten)
    (val := 0) (by decide) (by simp [fit_of_lt (show 0 < s7.cap by rw [hcap7]; omega)])
    (by simp [hct7, hflat]) hseg7 (by rw [hflat, hlen7]; omega) (fun x hx => by
      rw [hfmlen]
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
      obtain ⟨T, -, rfl⟩ := List.mem_map.mp hl
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hxl; exact a.2)
    (by rw [hflat, hcap7]; omega) (by rw [hcap7]; omega)) ?_
  rintro s8 ⟨h8fm, h8arr, h8reg, h8len, h8cap, h8cost⟩
  have hlen8 : s8.wlen = st0.wlen := by rw [h8len, hlen7]
  -- the groups
  have hgroups : makePivots (S.image Fin.val) (Q.image Fin.val) (forestPieces k (trees.map natTree)) =
      (forestGroups S Q k trees).map (List.map Fin.val) := by
    have e : trees.map natTree = trees.map (relabel Fin.val (fun T => natPar T.par)) := rfl
    rw [e, forestPieces_map Fin.val Fin.val_injective k _ trees (fun T _ a => natPar_val T.par a),
      makePivots_map Fin.val Fin.val_injective S Q]
    rfl
  refine ⟨?_, ⟨by rw [hlen8]; exact hfm.1, fun v => ?_⟩, ⟨?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [← hgroups]
    refine GrpOut.congr hG5 ?_ ?_ (fun j => ?_) (fun j => ?_) (fun j => ?_)
    · rw [h8reg _ (by decide) (by decide) (by decide), h7reg _ (by decide) (by decide) (by decide),
        h6reg _ (by decide) (by decide) (by decide)]
    · rw [h8reg _ (by decide) (by decide) (by decide), h7reg _ (by decide) (by decide) (by decide),
        h6reg _ (by decide) (by decide) (by decide)]
    · rw [h8arr _ _ (by decide), h7arr _ _ (by decide), h6arr _ _ (by decide)]
    · rw [h8arr _ _ (by decide), h7arr _ _ (by decide), h6arr _ _ (by decide)]
    · rw [h8arr _ _ (by decide), h7arr _ _ (by decide), h6arr _ _ (by decide)]
  · rw [h8fm v.val]
    have hv : v.val ∈ (trees.map (fun T => T.ord.map Fin.val)).flatten ↔ v ∈ tv := by
      rw [htv v, List.mem_flatten]
      constructor
      · rintro ⟨l, hl, hvl⟩
        obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hl
        exact ⟨T, hT, mem_map_val.mp hvl⟩
      · rintro ⟨T, hT, hvT⟩
        exact ⟨_, List.mem_map_of_mem hT, mem_map_val.mpr hvT⟩
    by_cases h : v ∈ tv
    · rw [if_pos (hv.mpr h)]; simp
    · rw [if_neg (fun h' => h (hv.mp h')), e71 _ _ (by decide) (by decide) (by decide),
        h1arr _ _ (by decide) (by decide) (by decide), hfm.2 v, if_neg h]; simp
  · rw [hlen8]; exact hPTA.len
  · rw [h8arr _ _ (by decide), h7arr _ _ (by decide), h6S x]
    by_cases h : x ∈ SL.map Fin.val
    · rw [if_pos h]; simp
    · rw [if_neg h, h5arr _ _ (by decide), hSb4 x hx, if_neg (fun h' => h ((memS x).mpr h'))]; simp
  · rw [h8arr _ _ (by decide), h7Q x]
    by_cases h : x ∈ ql.map Fin.val
    · rw [if_pos h]; simp
    · rw [if_neg h, h6arr _ _ (by decide), h5arr _ _ (by decide), hQb4 x hx,
        if_neg (fun h' => h ((memQ x).mpr h'))]; simp
  · rw [h8arr _ _ (by decide), h7arr _ _ (by decide), h6arr _ _ (by decide)]; exact hA5 x hx
  · have c1 := h1cost
    rw [hsumN] at c1 h5cost
    have hSLl : (SL.map Fin.val).length = SL.length := List.length_map _
    have hqll : (ql.map Fin.val).length = ql.length := List.length_map _
    rw [hSLl] at h2cost h6cost
    rw [hqll] at h3cost h7cost
    rw [hflat] at h8cost
    omega

end Frontier.CHD.PartitionRAM
