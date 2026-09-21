import Frontier.CostModel

/-!
# L6 preprocessing, interface v2 — RAM program text (agent-10, scratch)

NON-GATE.  Compact CSR layout (board post "L6 interface v2", 2026-09-20 12:0x):

* `gKeep[v] = 1` iff `v = s` or some non-loop edge enters `v` (other vertices are unreachable);
* per kept `u`: dedup (first minimum-weight edge to each head `v ≠ u`, flag `g_kept[e]`), kept
  degree `g_deg[u]`, `c_u = max 1 ⌈d_u/(δ-1)⌉` virtual vertices from `g_off[u]`, slots from `g_sl[u]`;
* virtual vertex `x = g_off[u] + q` owns the static slot range `[gSt[x], gSt[x+1])`: a non-last
  chunk has `δ-1` real edges and the chain edge `x → x+1` (weight `0`) in its last slot, the last
  chunk has the remaining real edges;
* `gSrc`, `gHead`, `gW` (value array): the reduced graph `H = ⟨gN, gM, gSrc, gHead, gW⟩`;
* initial live lists `gHd[x]` (first slot or `gM`), `gNxt[p]` (next slot or `gM`);
* `gRep[v] = g_off[v]`, `gOwn[x] = u`, `gS = gRep[s]`; core parameters `cn = min(n, m+1)`, `cm = m`.

The per-range sort by `(gW, gHead)` (agent-06's `sortRange`) and the output mapping are separate
fragments (`sortPass`, `outProg`).
-/

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt

def inc (x : String) : Stmt := wset x (add (var x) (lit 1))

/-! ## (0) keep pass -/

def keepBody : Stmt :=
  seq (wset "g_u" (load "src" (var "g_e")))
  (seq (wset "g_v" (load "dst" (var "g_e")))
  (seq (ite (eq (var "g_u") (var "g_v")) skip (wstore "gKeep" (var "g_v") (lit 1)))
  (inc "g_e")))

def keepLoop : Stmt := .while (lt (var "g_e") (var "m")) keepBody

def keepProg : Stmt :=
  seq (walloc "gKeep" (var "n"))
  (seq (wset "g_e" (lit 0))
  (seq keepLoop
  (wstore "gKeep" (var "s") (lit 1))))

/-! ## (1) parameters -/

def paramProg : Stmt :=
  seq (wset "g_t" (div (add (add (var "m") (var "m")) (sub (var "n") (lit 1))) (var "n")))
  (seq (ite (lt (var "g_t") (lit 3)) (wset "gD" (lit 3)) (wset "gD" (var "g_t")))
  (seq (ite (lt (add (var "m") (lit 1)) (var "n")) (wset "cn" (add (var "m") (lit 1)))
          (wset "cn" (var "n")))
  (wset "cm" (var "m"))))

/-! ## (2) counting sort by source (verified in `L6.CSort`) -/

def countBody : Stmt :=
  seq (wset "g_u" (load "src" (var "g_e")))
    (seq (wstore "g_cnt" (add (var "g_u") (lit 1)) (add (load "g_cnt" (add (var "g_u") (lit 1))) (lit 1)))
      (inc "g_e"))

def countLoop : Stmt := .while (lt (var "g_e") (var "m")) countBody

def prefBody : Stmt :=
  seq (wstore "g_cnt" (add (var "g_u") (lit 1))
      (add (load "g_cnt" (add (var "g_u") (lit 1))) (load "g_cnt" (var "g_u"))))
    (inc "g_u")

def prefLoop : Stmt := .while (lt (var "g_u") (var "n")) prefBody

def copyBody : Stmt := seq (wstore "g_pos" (var "g_u") (load "g_cnt" (var "g_u"))) (inc "g_u")

def copyLoop : Stmt := .while (lt (var "g_u") (add (var "n") (lit 1))) copyBody

def placeBody : Stmt :=
  seq (wset "g_u" (load "src" (var "g_e")))
    (seq (wstore "g_ord" (load "g_pos" (var "g_u")) (var "g_e"))
      (seq (wstore "g_pos" (var "g_u") (add (load "g_pos" (var "g_u")) (lit 1))) (inc "g_e")))

def placeLoop : Stmt := .while (lt (var "g_e") (var "m")) placeBody

def csortProg : Stmt :=
  seq (walloc "g_cnt" (add (var "n") (lit 1)))
  (seq (wset "g_e" (lit 0))
  (seq countLoop
  (seq (wset "g_u" (lit 0))
  (seq prefLoop
  (seq (walloc "g_pos" (add (var "n") (lit 1)))
  (seq (wset "g_u" (lit 0))
  (seq copyLoop
  (seq (walloc "g_ord" (var "m"))
  (seq (wset "g_e" (lit 0)) placeLoop)))))))))

/-! ## (3) pass A: dedup, kept flags, degrees, offsets -/

/-- The loop test "`g_j` inside `u`'s group". -/
def inGroup : WExpr := lt (var "g_j") (load "g_cnt" (add (var "g_u") (lit 1)))

/-- One step of the dedup scan (stamp `g_z`): `g_best[v]` := first minimum-weight edge `u → v`. -/
def dedupBody : Stmt :=
  seq (wset "g_e" (load "g_ord" (var "g_j")))
  (seq (wset "g_v" (load "dst" (var "g_e")))
  (seq (ite (eq (var "g_v") (var "g_u")) skip
     (ite (eq (load "g_mark" (var "g_v")) (var "g_z"))
        (seq (vle "g_b" (VExpr.load "w" (load "g_best" (var "g_v"))) (VExpr.load "w" (var "g_e")))
             (ite (var "g_b") skip (wstore "g_best" (var "g_v") (var "g_e"))))
        (seq (wstore "g_mark" (var "g_v") (var "g_z")) (wstore "g_best" (var "g_v") (var "g_e")))))
  (inc "g_j")))

def dedupLoop : Stmt := .while inGroup dedupBody

/-- Flag the kept edges of `u` and count them in `g_d`. -/
def flagBody : Stmt :=
  seq (wset "g_e" (load "g_ord" (var "g_j")))
  (seq (wset "g_v" (load "dst" (var "g_e")))
  (seq (ite (eq (var "g_v") (var "g_u")) skip
          (ite (eq (load "g_best" (var "g_v")) (var "g_e"))
             (seq (wstore "g_kept" (var "g_e") (lit 1)) (inc "g_d")) skip))
  (inc "g_j")))

def flagLoop : Stmt := .while inGroup flagBody

/-- Work for a kept vertex `u` in pass A. -/
def passAKept : Stmt :=
  seq (wset "g_z" (add (var "g_u") (lit 1)))
  (seq (wset "g_j" (load "g_cnt" (var "g_u")))
  (seq dedupLoop
  (seq (wset "g_d" (lit 0))
  (seq (wset "g_j" (load "g_cnt" (var "g_u")))
  (seq flagLoop
  (seq (wstore "g_deg" (var "g_u") (var "g_d"))
  (seq (wset "g_c" (div (add (var "g_d") (sub (var "gD") (lit 2))) (sub (var "gD") (lit 1))))
  (seq (ite (eq (var "g_c") (lit 0)) (wset "g_c" (lit 1)) skip)
  (seq (wset "g_x" (add (var "g_x") (var "g_c")))
       (wset "g_y" (sub (add (var "g_y") (add (var "g_d") (var "g_c"))) (lit 1))))))))))))

def passABody : Stmt :=
  seq (wstore "g_off" (var "g_u") (var "g_x"))
  (seq (wstore "g_sl" (var "g_u") (var "g_y"))
  (seq (ite (eq (load "gKeep" (var "g_u")) (lit 0)) skip passAKept)
  (inc "g_u")))

def passALoop : Stmt := .while (lt (var "g_u") (var "n")) passABody

def passAProg : Stmt :=
  seq (walloc "g_mark" (var "n"))
  (seq (walloc "g_best" (var "n"))
  (seq (walloc "g_deg" (var "n"))
  (seq (walloc "g_off" (add (var "n") (lit 1)))
  (seq (walloc "g_sl" (add (var "n") (lit 1)))
  (seq (walloc "g_kept" (var "m"))
  (seq (wset "g_x" (lit 0))
  (seq (wset "g_y" (lit 0))
  (seq (wset "g_u" (lit 0))
  (seq passALoop
  (seq (wstore "g_off" (var "n") (var "g_x"))
  (seq (wstore "g_sl" (var "n") (var "g_y"))
  (seq (wset "gN" (var "g_x"))
       (wset "gM" (var "g_y"))))))))))))))

/-! ## (4) pass B: layout -/

/-- Per slot `g_p + g_k` of the current virtual vertex: source and next link. -/
def slotBody : Stmt :=
  seq (wstore "gSrc" (add (var "g_p") (var "g_k")) (var "g_x"))
  (seq (wstore "gNxt" (add (var "g_p") (var "g_k")) (add (add (var "g_p") (var "g_k")) (lit 1)))
  (inc "g_k"))

def slotLoop : Stmt := .while (lt (var "g_k") (var "g_r")) slotBody

/-- Per virtual vertex `g_x` of `u`: owner, range start, chain edge, range length, links, head. -/
def vertBody : Stmt :=
  seq (wset "g_q" (sub (var "g_x") (load "g_off" (var "g_u"))))
  (seq (wset "g_p" (add (load "g_sl" (var "g_u")) (mul (var "g_q") (var "gD"))))
  (seq (wstore "gOwn" (var "g_x") (var "g_u"))
  (seq (wstore "gSt" (var "g_x") (var "g_p"))
  (seq (ite (lt (add (var "g_x") (lit 1)) (load "g_off" (add (var "g_u") (lit 1))))
          (seq (wset "g_r" (var "gD"))
          (seq (wstore "gHead" (sub (add (var "g_p") (var "gD")) (lit 1)) (add (var "g_x") (lit 1)))
               (vstore "gW" (sub (add (var "g_p") (var "gD")) (lit 1)) VExpr.zero)))
          (wset "g_r" (sub (load "g_deg" (var "g_u")) (mul (var "g_q") (sub (var "gD") (lit 1))))))
  (seq (wset "g_k" (lit 0))
  (seq slotLoop
  (seq (ite (eq (var "g_r") (lit 0)) (wstore "gHd" (var "g_x") (var "gM"))
          (seq (wstore "gHd" (var "g_x") (var "g_p"))
               (wstore "gNxt" (sub (add (var "g_p") (var "g_r")) (lit 1)) (var "gM"))))
  (inc "g_x"))))))))

def vertLoop : Stmt := .while (lt (var "g_x") (load "g_off" (add (var "g_u") (lit 1)))) vertBody

/-- Emission of the `g_i`-th kept edge of `u` at slot `g_sl[u] + (i/(δ-1))δ + i mod (δ-1)`. -/
def emitBody : Stmt :=
  seq (wset "g_e" (load "g_ord" (var "g_j")))
  (seq (ite (eq (load "g_kept" (var "g_e")) (lit 0)) skip
     (seq (wset "g_q" (div (var "g_i") (sub (var "gD") (lit 1))))
     (seq (wset "g_p" (add (add (load "g_sl" (var "g_u")) (mul (var "g_q") (var "gD")))
            (sub (var "g_i") (mul (var "g_q") (sub (var "gD") (lit 1))))))
     (seq (wstore "gHead" (var "g_p") (load "g_off" (load "dst" (var "g_e"))))
     (seq (vstore "gW" (var "g_p") (VExpr.load "w" (var "g_e")))
          (inc "g_i"))))))
  (inc "g_j"))

def emitLoop : Stmt := .while inGroup emitBody

def passBKept : Stmt :=
  seq (wstore "gRep" (var "g_u") (load "g_off" (var "g_u")))
  (seq (wset "g_x" (load "g_off" (var "g_u")))
  (seq vertLoop
  (seq (wset "g_i" (lit 0))
  (seq (wset "g_j" (load "g_cnt" (var "g_u")))
       emitLoop))))

def passBBody : Stmt :=
  seq (ite (eq (load "gKeep" (var "g_u")) (lit 0)) skip passBKept) (inc "g_u")

def passBLoop : Stmt := .while (lt (var "g_u") (var "n")) passBBody

def passBProg : Stmt :=
  seq (walloc "gSt" (add (var "gN") (lit 1)))
  (seq (walloc "gHd" (var "gN"))
  (seq (walloc "gNxt" (var "gM"))
  (seq (walloc "gSrc" (var "gM"))
  (seq (walloc "gHead" (var "gM"))
  (seq (valloc "gW" (var "gM"))
  (seq (walloc "gRep" (var "n"))
  (seq (walloc "gOwn" (var "gN"))
  (seq (wset "g_u" (lit 0))
  (seq passBLoop
  (seq (wstore "gSt" (var "gN") (var "gM"))
       (wset "gS" (load "gRep" (var "s")))))))))))))

/-! ## (5) per-range sort (the range sorter `srt` reads `ms_a`, `ms_b`) and (6) output mapping -/

def sortBody (srt : Stmt) : Stmt :=
  seq (wset "ms_a" (load "gSt" (var "g_x")))
  (seq (wset "ms_b" (load "gSt" (add (var "g_x") (lit 1))))
  (seq srt (inc "g_x")))

def sortPass (srt : Stmt) : Stmt :=
  seq (wset "g_x" (lit 0)) (.while (lt (var "g_x") (var "gN")) (sortBody srt))

/-- The L6 prefix before the core (with range sorter `srt`). -/
def l6Prog (srt : Stmt) : Stmt :=
  seq keepProg (seq paramProg (seq csortProg (seq passAProg (seq passBProg (sortPass srt)))))

def outBody : Stmt :=
  seq (ite (eq (load "gKeep" (var "g_v")) (lit 0)) skip
        (seq (wstore "reach" (var "g_v") (load "dfin" (load "gRep" (var "g_v"))))
             (vstore "dist" (var "g_v") (VExpr.load "dlen" (load "gRep" (var "g_v"))))))
  (inc "g_v")

def outProg : Stmt :=
  seq (walloc "reach" (var "n"))
  (seq (valloc "dist" (var "n"))
  (seq (wset "g_v" (lit 0))
  (.while (lt (var "g_v") (var "n")) outBody)))

end Frontier.CHD.L6
