#!/usr/bin/env bash
# Usage: expert_input/ported/build.sh [-j N] [-k] [-o MODULE] <PortDir>
# Compiles every .lean file under <PortDir> (module name = path relative to <PortDir>, dots for
# slashes) in dependency order against the project's Mathlib (and the project's own Erdos289
# oleans), writing .olean files to <PortDir>/.out. -j N compiles up to N independent files at once.
# -k keeps going after a failure (files depending on a failed file are skipped and listed).
# -o MODULE compiles only that module (its dependencies must already be built). Then, unless -o was
# given, elaborates <PortDir>/Axioms.lean if present. Never touches the project's .lake.
set -u
PROJ=/home/johan/math_erdos_289
J=1; KEEP=0; ONLY=""
while [ $# -gt 1 ]; do
  case "$1" in
    -j) J="$2"; shift 2;;
    -k) KEEP=1; shift;;
    -o) ONLY="$2"; shift 2;;
    *) echo "unknown flag $1"; exit 2;;
  esac
done
DIR="$(cd "$1" && pwd)"
OUT="$DIR/.out"
LEANBIN=$(cd "$PROJ" && lake env printenv LEAN)
LP="$OUT:$(cd "$PROJ" && lake env printenv LEAN_PATH)"
mkdir -p "$OUT"
cd "$DIR"
export LEANBIN LP OUT DIR J KEEP ONLY
python3 - <<'PY'
import os,re,sys,subprocess,time
from concurrent.futures import ThreadPoolExecutor, as_completed
root=os.environ['DIR']; out=os.environ['OUT']; J=int(os.environ['J']); KEEP=os.environ['KEEP']=='1'; ONLY=os.environ['ONLY']
files={}
for dp,_,fs in os.walk(root):
    if '/.out' in dp or dp.endswith('/.out'): continue
    for f in fs:
        if f.endswith('.lean'):
            p=os.path.relpath(os.path.join(dp,f),root)
            files[p[:-5].replace('/','.')]=p
imp=re.compile(r'^\s*(?:public\s+)?import\s+([\w.₀-₉]+)',re.M)
deps={m:[d for d in imp.findall(open(os.path.join(root,p),encoding='utf-8').read()) if d in files and d!=m] for m,p in files.items()}
def olean(m): return os.path.join(out,m.replace('.','/')+'.olean')
def uptodate(m):
    o=olean(m); p=os.path.join(root,files[m])
    return os.path.exists(o) and os.path.getmtime(o)>=os.path.getmtime(p) and all(os.path.exists(olean(d)) and os.path.getmtime(olean(d))<=os.path.getmtime(o) for d in deps[m])
def compile(m):
    o=olean(m); os.makedirs(os.path.dirname(o),exist_ok=True)
    t=time.time()
    r=subprocess.run([os.environ['LEANBIN'],'-o',o,files[m]],env=dict(os.environ,LEAN_PATH=os.environ['LP']),capture_output=True,text=True)
    return m,r.returncode,r.stdout+r.stderr,time.time()-t
if ONLY:
    m=ONLY
    if m not in files: print("no such module",m); sys.exit(2)
    m,rc,log,dt=compile(m); print(log,end=''); print(("OK" if rc==0 else "FAILED"),m,f"({dt:.0f}s)"); sys.exit(rc)
targets=[m for m in files if m!='Axioms']
done=set(); failed=set(); skipped=set(); status=0
remaining=set(targets)
for m in list(remaining):
    if uptodate(m): done.add(m); remaining.discard(m)
print(f"{len(done)} up to date, {len(remaining)} to compile, -j {J}")
with ThreadPoolExecutor(max_workers=J) as ex:
    running={}
    while remaining or running:
        ready=[m for m in remaining if all(d in done for d in deps[m])]
        for m in ready:
            if len(running)>=J: break
            remaining.discard(m); print("compiling:",m,flush=True); running[ex.submit(compile,m)]=m
        if not running:
            # everything left depends on a failure
            for m in remaining:
                skipped.add(m)
            remaining=set(); break
        fut=next(as_completed(list(running.keys())))
        m=running.pop(fut); mm,rc,log,dt=fut.result()
        if rc==0:
            done.add(m); print(f"ok: {m} ({dt:.0f}s)",flush=True)
        else:
            failed.add(m); status=1; print(f"FAILED: {m} ({dt:.0f}s)",flush=True); print(log,flush=True)
            if not KEEP:
                remaining=set()
                for f in running.values(): skipped.add(f)
                # let running ones finish
                for f in list(running.keys()):
                    m2=running.pop(f); mm2,rc2,log2,dt2=f.result()
                    if rc2==0: done.add(m2); print(f"ok: {m2} ({dt2:.0f}s)")
                    else: failed.add(m2); print(f"FAILED: {m2} ({dt2:.0f}s)"); print(log2)
                break
        # drop skipped: anything depending (transitively) on failed
    def depends_on_failed(m,seen=set()):
        return any(d in failed or (d in remaining and depends_on_failed(d)) for d in deps[m])
print(f"\nSUMMARY: {len(done)} ok, {len(failed)} failed, {len(skipped)+len(remaining)} not attempted")
for m in sorted(failed): print("FAILED",m)
for m in sorted(skipped|remaining): print("SKIPPED",m)
if status==0 and not ONLY and os.path.exists(os.path.join(root,'Axioms.lean')):
    print("--- Axioms.lean ---",flush=True)
    r=subprocess.run([os.environ['LEANBIN'],'Axioms.lean'],env=dict(os.environ,LEAN_PATH=os.environ['LP']),capture_output=True,text=True)
    print(r.stdout+r.stderr,end=''); status=r.returncode
sys.exit(status)
PY
