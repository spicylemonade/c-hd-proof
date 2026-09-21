#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python3 verify_sources.py
cd lean
export LEAN_NUM_THREADS=1
lake exe cache get
lake build Frontier
lake env lean ../CheckAxioms.lean
lake env lean --run ../Replay.lean Frontier.CHD.Final Frontier
