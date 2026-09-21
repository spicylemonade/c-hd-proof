#!/bin/bash
# agent-07 (reviewer #1) final-acceptance audit driver. Read-only with respect to /research/lean.
# Usage: final_audit.sh TAG ROOT_MODULE FINAL_THEOREM [EXTRA_THEOREM ...]
#   1. fresh-copy rebuild + HARD/INFO token scan + #print axioms       (my_repro.py)
#   2. kernel replay of every Frontier constant in ROOT_MODULE's closure (Replay07.lean)
#   3. statement prints of the frozen target, diffed against the 12:30 snapshot (stmt/stmt_1230.txt)
#   4. sha256 of every Frontier source file + pinned toolchain / manifest
#   5. (if PROG=Module:Const is set) program_probe.sh on the CHDTarget witness program (O30: computable, choice-free)
set -u
TAG=$1; ROOT=$2; shift 2; THMS="$@"
W=/research/agents/agent-07/work/repro
OUT=$W/final_$TAG; mkdir -p $OUT
cd $W
PROBES=""; for t in $THMS; do PROBES="$PROBES $ROOT:$t"; done
python3 my_repro.py $TAG $PROBES > $OUT/my_repro.txt 2>&1
PROJ=$W/$TAG/proj
(cd /research/lean && python3 /opt/research/lean_run.py lake env -d $PROJ lean --run $W/Replay07.lean $ROOT $THMS) > $OUT/replay.txt 2>&1
(cd /research/lean && python3 /opt/research/lean_run.py lake env -d $PROJ lean $W/stmt/PrintStmt.lean) > $OUT/stmt_now.txt 2>&1
diff $W/stmt/stmt_1230.txt $OUT/stmt_now.txt > $OUT/stmt_diff.txt 2>&1 && echo "STATEMENTS UNCHANGED" > $OUT/stmt_status.txt || echo "STATEMENTS CHANGED (see stmt_diff.txt)" > $OUT/stmt_status.txt
(cd $PROJ && sha256sum lakefile.toml lean-toolchain lake-manifest.json Frontier.lean $(find Frontier -name '*.lean' | sort)) > $OUT/hashes.txt
(cd /research/lean && sha256sum lakefile.toml lean-toolchain lake-manifest.json Frontier.lean $(find Frontier -name '*.lean' | sort)) > $OUT/hashes_shared_now.txt
diff $OUT/hashes.txt $OUT/hashes_shared_now.txt > $OUT/hashes_diff.txt && echo "FRESH COPY == SHARED TREE (all sources identical)" > $OUT/hashes_status.txt || echo "FRESH COPY differs from the current shared tree (see hashes_diff.txt)" > $OUT/hashes_status.txt
echo "== summary"; head -12 $OUT/my_repro.txt; cat $OUT/hashes_status.txt; grep -E "REPLAY|axioms|NOT FOUND|error" $OUT/replay.txt; cat $OUT/stmt_status.txt; wc -l $OUT/hashes.txt
if [ -n "${PROG:-}" ]; then
  PROJ=$PROJ bash $W/program_probe.sh ${PROG%%:*} ${PROG##*:} > $OUT/program_probe.txt 2>&1
  echo "== program probe ($PROG)"; cat $OUT/program_probe.txt
fi
# 6. (if GATEC_THM / CHD_THM are set) CLOSEDNESS: the final theorems must have EXACTLY the frozen types, with no hypotheses.
if [ -n "${GATEC_THM:-}${CHD_THM:-}" ]; then
  CF=$W/ClosedProbe.lean
  { echo "import $ROOT"
    [ -n "${GATEC_THM:-}" ] && echo "example : Frontier.GateC := $GATEC_THM" && echo "#print axioms $GATEC_THM"
    [ -n "${CHD_THM:-}" ] && echo "example : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F := $CHD_THM" && echo "#print axioms $CHD_THM"
  } > $CF
  (cd /research/lean && python3 /opt/research/lean_run.py lake env -d $PROJ lean $CF) > $OUT/closed_probe.txt 2>&1 \
    && echo "CLOSED: final theorems have exactly the frozen types (rc 0)" >> $OUT/closed_probe.txt \
    || echo "NOT CLOSED / TYPE MISMATCH (see closed_probe.txt)" >> $OUT/closed_probe.txt
  echo "== closedness"; cat $OUT/closed_probe.txt
fi
# 7. the lane deliverable Frontier.Counterexamples must NOT be in the final closure
if grep -q "Frontier.Counterexamples" $OUT/replay.txt; then echo "WARNING: Frontier.Counterexamples IS in the closure"; else echo "OK: Frontier.Counterexamples not in the closure"; fi
