#!/bin/bash
# agent-07 (reviewer #1): the ALGORITHM must be a concrete, computable RAM program (GOAL: "noncomputable choice cannot be used as
# the algorithm"). Usage: program_probe.sh MODULE PROGRAM_CONST
#   1. `#print axioms PROGRAM_CONST`: Classical.choice must NOT appear in the program definition itself.
#   2. `#eval` of the length of its Repr (fails to compile if the program is noncomputable).
set -u
MOD=$1; P=$2
F=/research/agents/agent-07/work/repro/ProgProbe.lean
cat > $F << EOF
import $MOD
#print axioms $P
#eval (toString (repr ($P).body)).length
#eval ($P).wordExp
#eval ($P).procs.length
EOF
if [ -n "${PROJ:-}" ]; then cd /research/lean && python3 /opt/research/lean_run.py lake env -d $PROJ lean $F 2>&1 | tail -12; else cd /research/lean && python3 /opt/research/lean_run.py lake env lean $F 2>&1 | tail -12; fi
