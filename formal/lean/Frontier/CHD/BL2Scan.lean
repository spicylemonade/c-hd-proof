import Frontier.CHD.BL2Rep
import Frontier.RAMWP

/-!
# Frontier.CHD.BL2Scan — B-L2: the RAM scan of one out-list (FH.7–FH.22) (agent-09, scratch, NON-GATE)

Program text of the scan of the extracted vertex `fp.u` and its refinement of agent-05's
Layer-A relation `Scan` (one loop iteration per live slot: `brk`, `lxdel`, `contact`,
`newFull`, `newCont`, `inK`; deleted slots are physically unlinked, so Layer A's `del` steps cost
nothing).  Result register `fp.res`: 0 = list exhausted, 1 = range stop (both `ScanRes.cont`),
2 = contact (edge `(fp.cu, fp.cv)`), 3 = member cap reached (`ScanRes.full`).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-! ## Program text -/

/-- keep the current slot and move on -/
def fpAdvance : Stmt :=
  seq (wset "fp.pp" (var "fp.p"))
  (seq (wset "fp.p" (load "gNxt" (var "fp.p")))
       (wset "fp.go" (lt (var "fp.p") (var "gM"))))

/-- FH.9: unlink the current slot through its predecessor cell and move on -/
def fpUnlink : Stmt :=
  seq (ite (eq (var "fp.pp") (var "gM"))
        (wstore "gHd" (var "fp.u") (load "gNxt" (var "fp.p")))
        (wstore "gNxt" (var "fp.pp") (load "gNxt" (var "fp.p"))))
  (seq (wset "fp.p" (load "gNxt" (var "fp.p")))
       (wset "fp.go" (lt (var "fp.p") (var "gM"))))

/-- insert `fp.v` into the heap unless it is there -/
def fpHeapIns : Stmt :=
  ite (load "fp.inH" (var "fp.v")) skip
    (seq (wstore "fp.H" (var "fp.hsz") (var "fp.v"))
    (seq (wstore "fp.hp" (var "fp.v") (var "fp.hsz"))
    (seq (wstore "fp.inH" (var "fp.v") (lit 1))
         (wset "fp.hsz" (add (var "fp.hsz") (lit 1))))))

/-- stop the scan with result code `r` -/
def fpStop (r : ℕ) : Stmt := seq (wset "fp.res" (lit r)) (wset "fp.go" (lit 0))

variable (LI : LabI V ops G s)

/-- FH.16: append `fp.v` to `K`, mark it, record its first-discovery parent `fp.u`. -/
def fpMemAdd : Stmt :=
  seq (wstore "fp.K" (var "fp.kl") (var "fp.v"))
  (seq (wset "fp.kl" (add (var "fp.kl") (lit 1)))
  (seq (wstore "fp.inK" (var "fp.v") (lit 1))
       (wstore "fp.kp" (var "fp.v") (var "fp.u"))))

/-- FH.17 / FH.22: on a valid relaxation, mark `fp.v` valid and put it into the heap. -/
def fpOkPart (okr : String) : Stmt :=
  ite (var okr) (seq (wstore "fp.val" (var "fp.v") (lit 1)) fpHeapIns) skip

/-- FH.15–FH.19: a new member (valid: explored; invalid: leaf) -/
def fpNew : Stmt :=
  seq LI.relaxC (seq fpMemAdd (seq (fpOkPart LI.ok)
    (ite (lt (var "fp.kl") (var "fp.k")) fpAdvance (fpStop 3))))

/-- FH.20–FH.22: an existing member (improvement, leaf promotion) -/
def fpOld : Stmt :=
  seq LI.relaxC (seq (fpOkPart LI.ok) fpAdvance)

/-- FH.10–FH.13: contact with a tree -/
def fpContact : Stmt :=
  seq LI.relaxC (seq (wset "fp.cu" (var "fp.u")) (seq (wset "fp.cv" (var "fp.v")) (fpStop 2)))

/-- One iteration of the scan loop (the slot `fp.p` of `fp.u`). -/
def fpScanBody (slB slX : String) : Stmt :=
  seq (wset "fp.v" (load "gHead" (var "fp.p")))
  (seq (wset LI.ru (var "fp.u"))
  (seq (wset LI.re (var "fp.p"))
  (seq (LI.candB slB)
    (ite (var LI.bit)
      (seq (wset LI.rv (var "fp.v"))
      (seq (LI.cmpTS slX)
        (ite (var LI.bit) fpUnlink
          (ite (load "fp.fm" (var "fp.v")) (fpContact LI)
            (ite (load "fp.inK" (var "fp.v")) (fpOld LI) (fpNew LI))))))
      (fpStop 1)))))

/-- Start the scan of `fp.u`. -/
def fpScanInit : Stmt :=
  seq (wset "fp.p" (load "gHd" (var "fp.u")))
  (seq (wset "fp.pp" (var "gM"))
  (seq (wset "fp.res" (lit 0))
       (wset "fp.go" (lt (var "fp.p") (var "gM")))))

/-- The scan of the live out-list of `fp.u` (FH.7–FH.22). -/
def fpScan (slB slX : String) : Stmt :=
  seq fpScanInit (Stmt.while (var "fp.go") (fpScanBody LI slB slX))

/-! ## List facts -/

theorem filt_dels {D : Finset (Fin G.m)} {Ld L : List (Fin G.m)} (h : ∀ x ∈ Ld, x ∈ D) :
    (Ld ++ L).filter (fun e => e ∉ D) = L.filter (fun e => e ∉ D) := by
  rw [List.filter_append]
  have : Ld.filter (fun e => e ∉ D) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simpa using h a ha
  rw [this, List.nil_append]

theorem filt_cons_live {D : Finset (Fin G.m)} {e : Fin G.m} {L : List (Fin G.m)} (he : e ∉ D) :
    (e :: L).filter (fun e => e ∉ D) = e :: L.filter (fun e => e ∉ D) := by
  simp [List.filter_cons, he]

theorem filt_insert_of_not_mem {D : Finset (Fin G.m)} {e : Fin G.m} {L : List (Fin G.m)}
    (he : e ∉ L) :
    L.filter (fun x => x ∉ insert e D) = L.filter (fun x => x ∉ D) := by
  apply List.filter_congr
  intro x hx
  have : x ≠ e := fun h => he (h ▸ hx)
  simp [Finset.mem_insert, this]

/-- The first live edge of a list with a nonempty live part. -/
theorem split_first {D : Finset (Fin G.m)} :
    ∀ {L : List (Fin G.m)}, L.filter (fun e => e ∉ D) ≠ [] →
      ∃ Ld e L'', L = Ld ++ e :: L'' ∧ (∀ x ∈ Ld, x ∈ D) ∧ e ∉ D
  | [], h => absurd rfl h
  | e :: L, h => by
    by_cases he : e ∈ D
    · have h' : L.filter (fun e => e ∉ D) ≠ [] := by
        simpa [List.filter_cons, he] using h
      obtain ⟨Ld, e', L'', rfl, hLd, he'⟩ := split_first h'
      exact ⟨e :: Ld, e', L'', rfl, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he
        · exact hLd x hx, he'⟩
    · exact ⟨[], e, L, rfl, fun x hx => absurd hx List.not_mem_nil, he⟩

theorem mem_sl {L : List (Fin G.m)} {e : Fin G.m} : (e : ℕ) ∈ sl L ↔ e ∈ L := by
  simp [sl, Fin.val_inj]

theorem sl_append (L₁ L₂ : List (Fin G.m)) : sl (L₁ ++ L₂) = sl L₁ ++ sl L₂ := by
  simp [sl]

theorem sl_cons (e : Fin G.m) (L : List (Fin G.m)) : sl (e :: L) = (e : ℕ) :: sl L := rfl

theorem sl_nil : sl ([] : List (Fin G.m)) = [] := rfl

theorem mem_live {c : FPCtx G s} {D : Finset (Fin G.m)} {w : Fin G.n} {q : ℕ} :
    q ∈ live c D w ↔ ∃ e : Fin G.m, (e : ℕ) = q ∧ e ∈ c.out w ∧ e ∉ D := by
  unfold live sl
  constructor
  · intro hq
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hq
    obtain ⟨h1, h2⟩ := List.mem_filter.mp he
    exact ⟨e, heq, h1, by simpa using h2⟩
  · rintro ⟨e, heq, h1, h2⟩
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨h1, by simpa using h2⟩, heq⟩

/-! ## Cursor steps -/

/-- Reading the cursor: the current slot is the first live edge of the remaining list. -/
theorem Cursor.first {st : State V} {c : FPCtx G s} {D : Finset (Fin G.m)} {u : Fin G.n}
    {Lrem : List (Fin G.m)} (hC : Cursor st c D u Lrem) (hp : st.w "fp.p" < G.m) :
    ∃ Ld e L'', Lrem = Ld ++ e :: L'' ∧ (∀ x ∈ Ld, x ∈ D) ∧ e ∉ D ∧ st.w "fp.p" = e ∧
      (e : ℕ) < st.wlen "gNxt" ∧
      Seg st "gNxt" G.m (st.wa "gNxt" e) (sl (L''.filter (fun e => e ∉ D))) G.m := by
  obtain ⟨-, -, Pre, -, -, hs2, -⟩ := hC
  have hne : Lrem.filter (fun e => e ∉ D) ≠ [] := by
    intro h0
    rw [h0, sl_nil] at hs2
    have := hs2.nil_inv
    omega
  obtain ⟨Ld, e, L'', rfl, hLd, he⟩ := split_first hne
  rw [filt_dels hLd, filt_cons_live he, sl_cons] at hs2
  obtain ⟨hpe, -, hl, hs⟩ := hs2.cons_inv
  exact ⟨Ld, e, L'', rfl, hLd, he, hpe, hl, hpe ▸ hs⟩

/-- FH.9 bookkeeping-free move: keep the current live slot `e`. -/
theorem advance_spec {st : State V} {c : FPCtx G s} {D : Finset (Fin G.m)} {u : Fin G.n}
    {Ld L'' : List (Fin G.m)} {e : Fin G.m}
    (hC : Cursor st c D u (Ld ++ e :: L'')) (hLd : ∀ x ∈ Ld, x ∈ D) (he : e ∉ D)
    (hp : st.w "fp.p" = e) (hgM : st.w "gM" = G.m) (hcap : 1 < st.cap) :
    Runs ops fpAdvance st (fun st' => Cursor st' c D u L'' ∧
      st'.w "fp.go" = (if st'.w "fp.p" < G.m then 1 else 0) ∧
      Unchanged st st' [] [] ["fp.pp", "fp.p", "fp.go"] [] ∧ st'.cost = st.cost + 3) := by
  obtain ⟨hF, hoth, Pre, hPre, hs1, hs2, hpp⟩ := hC
  rw [filt_dels hLd, filt_cons_live he, sl_cons] at hs2
  obtain ⟨hpe, heM, hl, hs⟩ := hs2.cons_inv
  have h0 : 0 < st.cap := by omega
  apply wp_sound
  simp only [fpAdvance, wp, evalW_var, evalW_load', evalW_lt', State.charge_w, State.setW_w,
    State.charge_wa, State.setW_wa, State.charge_wlen, State.setW_wlen, State.charge_cap,
    State.setW_cap, Option.bind_some, hp, hl, if_true, hgM]
  simp only [show ("fp.p" = "fp.pp") = False by decide, show ("gM" = "fp.p") = False by decide,
    show ("gM" = "fp.pp") = False by decide, if_false, hp, hgM, hl, if_true, Option.bind_some,
    fit, show (if st.wa "gNxt" ↑e < G.m then 1 else 0) < st.cap by split_ifs <;> omega]
  refine ⟨⟨by simpa using hF, fun w hw => ?_, Pre ++ Ld ++ [e], ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hoth w hw).of_eq (by simp) (by simp)
  · rw [hPre]; simp
  · have hk : (Pre ++ Ld ++ [e]).filter (fun e => e ∉ D) = Pre.filter (fun e => e ∉ D) ++ [e] := by
      rw [List.append_assoc, List.filter_append, filt_dels hLd, filt_cons_live he]; simp
    rw [hk, sl_append]
    have := (Seg.snoc_iff (st := st) (nxt := "gNxt") (E := G.m) (a := st.wa "gHd" u)
      (b := st.wa "gNxt" e) (q := e) (L := sl (Pre.filter (fun e => e ∉ D)))).mpr
      ⟨hpe ▸ hs1, heM, hl, rfl⟩
    refine Seg.of_eq (st := st) ?_ (by simp) (by simp)
    simpa [sl] using this
  · exact hs.of_eq (by simp) (by simp)
  · right
    refine ⟨Pre.filter (fun e => e ∉ D), e, ?_, by simp⟩
    rw [List.append_assoc, List.filter_append, filt_dels hLd, filt_cons_live he]; simp
  · simp
  · refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
    simp at hx
    simp [hx.1, hx.2.1, hx.2.2]
  · simp

/-- Nodup bookkeeping for a split out-list. -/
theorem split_nodup {Pre Ld L'' : List (Fin G.m)} {e : Fin G.m}
    (hnd : (Pre ++ (Ld ++ e :: L'')).Nodup) : e ∉ Pre ∧ e ∉ L'' ∧
      ∀ x ∈ Pre, x ∉ L'' ∧ x ≠ e := by
  rw [List.nodup_append] at hnd
  obtain ⟨-, h2, h3⟩ := hnd
  rw [List.nodup_append] at h2
  obtain ⟨-, h22, -⟩ := h2
  have he2 : e ∉ L'' := (List.nodup_cons.mp h22).1
  refine ⟨fun h => ?_, he2, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact h3 e h e (by simp) rfl
  · exact h3 x hx x (by simp [h]) rfl
  · exact h3 x hx e (by simp) h

/-- FH.9: unlink the current live slot `e` (it joins the deleted set). -/
theorem unlink_spec {st : State V} {c : FPCtx G s} {D : Finset (Fin G.m)} {u : Fin G.n}
    {Ld L'' : List (Fin G.m)} {e : Fin G.m}
    (hown : ∀ w e, e ∈ c.out w → G.src e = w) (hnd : (c.out u).Nodup)
    (hC : Cursor st c D u (Ld ++ e :: L'')) (hLd : ∀ x ∈ Ld, x ∈ D) (he : e ∉ D)
    (hp : st.w "fp.p" = e) (hu : st.w "fp.u" = u) (hgM : st.w "gM" = G.m) (hcap : 1 < st.cap) :
    Runs ops fpUnlink st (fun st' => Cursor st' c (insert e D) u L'' ∧
      st'.w "fp.go" = (if st'.w "fp.p" < G.m then 1 else 0) ∧
      Unchanged st st' ["gHd", "gNxt"] [] ["fp.p", "fp.go"] [] ∧ st'.cost = st.cost + 4) := by
  obtain ⟨hF, hoth, Pre, hPre, hs1, hs2, hpp⟩ := hC
  rw [filt_dels hLd, filt_cons_live he, sl_cons] at hs2
  obtain ⟨hpe, heM, hl, hs⟩ := hs2.cons_inv
  have hnd' := hPre ▸ hnd
  obtain ⟨heP, heL, hPL⟩ := split_nodup hnd'
  have hsrc : G.src e = u := hown u e (by rw [hPre]; simp)
  have h0 : 0 < st.cap := by omega
  -- the live lists of the other vertices do not change when `e` is deleted
  have hlive : ∀ w : Fin G.n, w ≠ u → live c (insert e D) w = live c D w := by
    intro w hw
    unfold live
    rw [filt_insert_of_not_mem]
    intro hew
    exact hw ((hown w e hew).symm.trans hsrc)
  have hkeep : (Pre ++ Ld ++ [e]).filter (fun x => x ∉ insert e D) =
      Pre.filter (fun x => x ∉ D) := by
    rw [List.append_assoc, List.filter_append, filt_insert_of_not_mem heP]
    have : (Ld ++ [e]).filter (fun x => x ∉ insert e D) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · simp [Finset.mem_insert, hLd a ha]
      · simp
    rw [this, List.append_nil]
  have hrest : L''.filter (fun x => x ∉ insert e D) = L''.filter (fun x => x ∉ D) :=
    filt_insert_of_not_mem heL
  have huL : (u : ℕ) < st.wlen "gHd" := lt_of_lt_of_le u.isLt hF
  have segnil : ∀ (st₀ : State V) (a b : ℕ), a = b → Seg st₀ "gNxt" G.m a [] b := by
    rintro st₀ a b rfl; exact Seg.nil a
  rcases hpp with ⟨hk0, hpp0⟩ | ⟨P0, e0, hk0, hpp0⟩
  · -- no kept slot yet: the head cell `gHd[u]` points to `e`
    rw [hk0, sl_nil] at hs1
    have hgo : (if st.wa "gNxt" ↑e < G.m then 1 else 0) < st.cap := by split_ifs <;> omega
    apply wp_sound
    simp [fpUnlink, wp, hp, hu, hgM, hpp0, hl, huL, fit, hcap, h0, hgo]
    refine ⟨⟨by simpa using hF, fun w hw => ?_, Pre ++ Ld ++ [e], by rw [hPre]; simp, ?_, ?_, ?_⟩, ?_⟩
    · have hw' : (w : ℕ) ≠ u := fun h => hw (Fin.ext h)
      rw [hlive w hw]
      refine Seg.of_eq (st := st) ?_ (by funext j; simp) (by simp)
      simpa [hw'] using hoth w hw
    · rw [hkeep, hk0, sl_nil]
      apply segnil
      simp
    · rw [hrest]
      refine Seg.of_eq (st := st) ?_ (by funext j; simp) (by simp)
      simpa using hs
    · left; exact ⟨by rw [hkeep, hk0], by simpa using hpp0⟩
    · refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
      · simp only [List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, or_false] at ha
        refine ⟨?_, by simp⟩
        funext j; simp [ha.1]
      · simp only [List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, or_false] at hx
        simp [hx.1, hx.2]
  · -- the last kept slot `e0` points to `e`
    have hk0' : (Pre.filter (fun x => x ∉ D)).Nodup := List.Nodup.sublist List.filter_sublist
      (List.Nodup.sublist (List.sublist_append_left _ _) hnd')
    rw [hk0] at hk0'
    have he0P0 : e0 ∉ P0 := by
      rw [List.nodup_append] at hk0'
      exact fun h => hk0'.2.2 e0 h e0 (by simp) rfl
    have he0Pre : e0 ∈ Pre := by
      have : e0 ∈ Pre.filter (fun x => x ∉ D) := by rw [hk0]; simp
      exact (List.mem_filter.mp this).1
    obtain ⟨he0L, he0e⟩ := hPL e0 he0Pre
    rw [hk0, sl_append] at hs1
    have hs1' := (Seg.snoc_iff (st := st) (L := sl P0) (q := (e0 : ℕ))).mp hs1
    obtain ⟨hsP0, he0M, he0l, hpnx⟩ := hs1'
    have hne : (e0 : ℕ) ≠ G.m := by omega
    have hee0 : (e : ℕ) ≠ e0 := fun h => he0e (Fin.ext h).symm
    have he0own : G.src e0 = u := hown u e0 (by rw [hPre]; simp [he0Pre])
    have hgo : (if st.wa "gNxt" ↑e < G.m then 1 else 0) < st.cap := by split_ifs <;> omega
    apply wp_sound
    simp [fpUnlink, wp, hp, hu, hgM, hpp0, hl, fit, hcap, h0, hgo, hne, he0l, hee0]
    refine ⟨⟨by simpa using hF, fun w hw => ?_, Pre ++ Ld ++ [e], by rw [hPre]; simp, ?_, ?_, ?_⟩, ?_⟩
    · rw [hlive w hw]
      refine Seg.congr (st := st) (by simpa using hoth w hw) (fun q hq => ?_) (by simp)
      have : q ≠ e0 := by
        intro hqe
        obtain ⟨x, hxq, hxw, -⟩ := mem_live.mp hq
        have : x = e0 := Fin.ext (hxq.trans hqe)
        subst this
        exact hw ((hown w x hxw).symm.trans he0own)
      simp [this]
    · rw [hkeep, hk0, sl_append, show sl [e0] = [(e0 : ℕ)] from rfl]
      refine (Seg.snoc_iff).mpr ⟨?_, he0M, by simpa using he0l, by simp⟩
      refine Seg.congr_start (st := st) hsP0 (by simp) (fun q hq => ?_) (by simp)
      have : q ≠ e0 := by rintro rfl; exact he0P0 (mem_sl.mp hq)
      simp [this]
    · rw [hrest]
      refine Seg.congr (st := st) (by simpa using hs) (fun q hq => ?_) (by simp)
      have : q ≠ e0 := by
        rintro rfl
        exact he0L (List.mem_filter.mp (mem_sl.mp hq)).1
      simp [this]
    · right; exact ⟨P0, e0, by rw [hkeep, hk0], by simpa using hpp0⟩
    · refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
      · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
        refine ⟨?_, by simp⟩
        funext j; simp [ha.2]
      · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
        simp [hx.1, hx.2]

/-! ## Heap insertion -/

theorem Bits.update {st : State V} {arr : String} {S : Finset (Fin G.n)} (h : Bits st arr S)
    (v : Fin G.n) :
    Bits ((st.storeW arr v 1).charge 1) arr (insert v S) := by
  refine ⟨by simpa using h.1, fun w => ?_⟩
  by_cases hw : w = v
  · subst hw; simp
  · have : (w : ℕ) ≠ v := fun h' => hw (Fin.ext h')
    simp [this, hw, h.2 w]

/-- Heap insertion of `fp.v` (skipped if already present): `H ↦ insert v H`. -/
theorem heapIns_spec {st : State V} {k : ℕ} {H : Finset (Fin G.n)} {v : Fin G.n}
    (hH : HeapRep st k H) (hv : st.w "fp.v" = v) (hroom : v ∉ H → H.card < k)
    (hcap : H.card + 1 < st.cap) :
    Runs ops fpHeapIns st (fun st' => HeapRep st' k (insert v H) ∧
      Unchanged st st' ["fp.H", "fp.hp", "fp.inH"] [] ["fp.hsz"] [] ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 5) := by
  obtain ⟨hl, hnd, hset, hsz, hcapH, harr, hpL, hpos, hbL, hb⟩ := hH
  have hvL : (v : ℕ) < st.wlen "fp.inH" := by rw [hbL]; exact v.isLt
  have hvL' : (v : ℕ) < st.wlen "fp.hp" := by rw [hpL]; exact v.isLt
  have hlen : hl.length = H.card := by rw [← hset, List.toFinset_card_of_nodup hnd]
  by_cases hmem : v ∈ H
  · -- already present: `skip`
    have hbit : st.wa "fp.inH" v = 1 := by rw [hb v]; simp [hmem]
    apply wp_sound
    simp only [fpHeapIns, wp, evalW_var, evalW_load', hv, hvL, ite_true, Option.bind_some, hbit]
    refine ⟨fun _ => ?_, fun h => absurd h one_ne_zero⟩
    rw [Finset.insert_eq_of_mem hmem]
    refine ⟨⟨hl, hnd, hset, by simpa using hsz, by simpa using hcapH, fun i hi => by simpa using harr i hi,
      by simpa using hpL, fun i hi => by simpa using hpos i hi, by simpa using hbL,
      fun w => by simpa using hb w⟩, ?_, by simp <;> omega, by simp <;> omega⟩
    exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  · have hbit : st.wa "fp.inH" v = 0 := by rw [hb v]; simp [hmem]
    have hk := hroom hmem
    have hszk : st.w "fp.hsz" < st.wlen "fp.H" := by rw [hsz, hlen]; omega
    apply wp_sound
    simp only [fpHeapIns, wp, evalW_var, evalW_load', hv, hvL, ite_true, Option.bind_some, hbit]
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    have hszk' : H.card < st.wlen "fp.H" := by rw [← hlen, ← hsz]; exact hszk
    simp [hv, hvL', hvL, fit, hsz, hlen, hcap, show 1 < st.cap by omega]
    refine ⟨hszk', ⟨hl ++ [v], ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, fun w => ?_⟩, ?_,
      by omega⟩
    · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton v, by
        intro a ha b hb' hab; simp at hb'; subst hb'; subst hab
        exact hmem (hset ▸ List.mem_toFinset.mpr ha)⟩
    · rw [List.toFinset_append, hset]; ext x; simp [or_comm]
    · simp [hlen]
    · simpa using hcapH
    · by_cases hi' : i = hl.length
      · subst hi'; simp [hlen]
      · have hi2 : i < hl.length := by simp at hi; omega
        have : i ≠ H.card := by omega
        simp [this, List.getElem_append_left hi2, harr i hi2]
    · simpa using hpL
    · by_cases hi' : i = hl.length
      · subst hi'; simp [hlen]
      · have hi2 : i < hl.length := by simp at hi; omega
        have hne : ((hl[i] : Fin G.n) : ℕ) ≠ v := by
          intro h
          have : hl[i] = v := Fin.ext h
          exact hmem (hset ▸ List.mem_toFinset.mpr (this ▸ List.getElem_mem hi2))
        have := hpos i hi2
        simp only [List.get_eq_getElem] at this
        simp [List.getElem_append_left hi2, hne, this]
    · simpa using hbL
    · by_cases hw : w = v
      · subst hw; simp
      · have : (w : ℕ) ≠ v := fun h' => hw (Fin.ext h')
        simp [this, hw, hb w]
    · refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
      · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
        refine ⟨?_, by simp⟩
        funext j; simp [ha.1, ha.2.1, ha.2.2]
      · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
        simp [hx]

end Frontier.CHD.BL2
