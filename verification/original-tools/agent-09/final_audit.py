#!/usr/bin/env python3
"""agent-09 final acceptance audit harness (generation 2). Read-only on shared files.

Usage:
  python3 final_audit.py --root Frontier.AuditGateC --theorem Frontier.GateCTarget.chdTarget_F_imp_gateC \
      [--theorem ...] [--def Frontier.RAM.BF.bfProgram ...] [--tag NAME]

Steps: (1) sha256 of every Frontier .lean file + manifest/toolchain; (2) Frontier import closure of --root and
forbidden-token scan (comments/strings stripped); (3) lake build --root; (4) #print axioms for every --theorem
(must be subset of {propext, Classical.choice, Quot.sound}) and every --def (must depend on NO axioms: computable
algorithm syntax); (5) independent kernel replay (replay/Replay.lean) of all Frontier constants in the closure.
Writes audit_runs/final_<tag>.json and prints a summary. Exit 0 iff everything passes.
"""
import argparse, hashlib, json, re, subprocess, sys, time
from pathlib import Path

LEAN_ROOT = Path('/research/lean')
OUT = Path('/research/agents/agent-09/work/audit_runs')
REPLAY = Path('/research/agents/agent-09/work/replay/Replay.lean')
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
# note (20:10): `simp (config := { decide := true })` is a SAFE kernel-checked tactic option; removed from the list.
FORBIDDEN = [r'\bsorry\b', r'\badmit\b', r'\bnative_decide\b', r'^\s*axiom\b', r'\bunsafe\b', r'implemented_by',
             r'@\[\s*extern', r'\bopaque\b', r'ofReduceBool', r'@\[\s*csimp', r'skipKernelTC', r'set_option\s+debug',
             r'run_cmd', r'#eval', r'\bpostulate\b', r'Lean\.Elab\.Command']

def strip_comments(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth:
            if src[i] == '\n': out.append('\n')
            i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = len(src) if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < len(src) and src[j] != '"': j += 2 if src[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)

def mpath(m): return LEAN_ROOT / (m.replace('.', '/') + '.lean')

def closure(mods):
    seen, st = set(), list(mods)
    while st:
        m = st.pop()
        if m in seen or not (m == 'Frontier' or m.startswith('Frontier.')): continue
        p = mpath(m)
        if not p.exists(): continue
        seen.add(m)
        for line in p.read_text().splitlines():
            mm = re.match(r'\s*import\s+(.+)', line)
            if mm: st.extend(mm.group(1).split())
    return sorted(seen)

def run(cmd): return subprocess.run(cmd, capture_output=True, text=True, cwd=str(LEAN_ROOT))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True)
    ap.add_argument('--theorem', action='append', default=[])
    ap.add_argument('--def', dest='defs', action='append', default=[])
    ap.add_argument('--tag', default=time.strftime('%Y%m%dT%H%M%S'))
    ap.add_argument('--skip-build', action='store_true',
                    help='do not run lake build (tree already built; avoids the exclusive full-build lock); '
                         'the probe/replay still load the installed oleans')
    a = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    rep = {'tag': a.tag, 'time_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'root': a.root}
    files = sorted((LEAN_ROOT / 'Frontier').rglob('*.lean')) + [LEAN_ROOT / f for f in
             ['Frontier.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'RUNTIME_LOCK.json']]
    rep['hashes'] = {str(p.relative_to(LEAN_ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files if p.exists()}
    mods = closure([a.root]); rep['closure'] = mods
    hits = []
    for m in mods:
        src = strip_comments(mpath(m).read_text())
        for ln, line in enumerate(src.splitlines(), 1):
            for pat in FORBIDDEN:
                if re.search(pat, line): hits.append([m, ln, pat, line.strip()[:160]])
    rep['forbidden_hits'] = hits
    ok = not hits
    if a.skip_build:
        class _B: returncode = 'skipped'; stdout = ''; stderr = 'build step skipped (--skip-build)'
        b = _B()
        rep['build_rc'] = 'skipped'; rep['build_tail'] = b.stderr
    else:
        b = run(['python3', '/opt/research/lean_run.py', 'lake', 'build', a.root])
        rep['build_rc'] = b.returncode; rep['build_tail'] = (b.stdout + b.stderr)[-3000:]
        ok &= b.returncode == 0
    probe = OUT / f'Probe_final_{a.tag}.lean'
    probe.write_text(f'import {a.root}\n' + ''.join(f'#print axioms {t}\n' for t in a.theorem + a.defs))
    r = run(['python3', '/opt/research/lean_run.py', 'lake', 'env', 'lean', str(probe)])
    rep['probe_out'] = r.stdout + r.stderr
    ax = {}
    for line in (r.stdout + r.stderr).splitlines():
        mm = re.match(r"'([^']+)' depends on axioms: \[(.*)\]", line)
        if mm: ax[mm.group(1)] = [x.strip() for x in mm.group(2).split(',') if x.strip()]
        mm2 = re.match(r"'([^']+)' does not depend on any axioms", line)
        if mm2: ax[mm2.group(1)] = []
    rep['axioms'] = ax
    for t in a.theorem:
        if t not in ax or not set(ax[t]) <= STANDARD: ok = False
    for d in a.defs:
        if d not in ax or ax[d]: ok = False
    rp = run(['python3', '/opt/research/lean_run.py', 'lake', 'env', 'lean', '--run', str(REPLAY), a.root])
    rep['replay_out'] = (rp.stdout + rp.stderr)[-2000:]
    ok &= 'KERNEL REPLAY OK' in rp.stdout
    rep['ok'] = ok
    outp = OUT / f'final_{a.tag}.json'; outp.write_text(json.dumps(rep, indent=1))
    print(f"root={a.root} closure={len(mods)} forbidden_hits={len(hits)} build_rc={b.returncode}")
    for k, v in ax.items(): print(f"  axioms {k}: {v}")
    print('  ' + [l for l in rp.stdout.splitlines() if 'REPLAY' in l][-1:][0] if 'REPLAY' in rp.stdout else '  replay: no output')
    print(f"OK={ok}  report={outp}")
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
