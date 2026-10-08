#!/usr/bin/env bash
# Replay the retained textual proof with the official Lean 4.34.0 kernel.
# Usage: bash verify-second-lean.sh [path/to/logarithm-main.ndjson[.gz]]
# CROSSCHECK_ROOT optionally selects the retained build/cache directory.
set -euo pipefail
bundle=$(cd "$(dirname "$0")" && pwd)
cross_root=${CROSSCHECK_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/codex-logarithm-lean-4.34.0}
mkdir -p "$cross_root/tools"
archive="$cross_root/tools/lean-4.34.0-linux.zip"
if [ ! -f "$archive" ]; then
  curl --fail --location --silent --show-error --retry 2 \
    https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux.zip \
    -o "$archive"
fi
printf '%s  %s\n' 5f14e0f3762058a529b1598f4355e6787c5f155be1bcce72ae288b9c35e3adb4 "$archive" | sha256sum --check
if [ ! -x "$cross_root/tools/lean-4.34.0-linux/bin/lean" ]; then
  unzip -q "$archive" -d "$cross_root/tools"
fi
second_tool="$cross_root/tools/lean-4.34.0-linux"
export PATH="$second_tool/bin:/usr/local/bin:/usr/bin:/bin"
export LD_LIBRARY_PATH="$second_tool/lib/lean"
export LEAN_SYSROOT="$second_tool"
export LEAN_NUM_THREADS=4
unset LEAN_PATH
lean --version
lean --version | grep -F 'version 4.34.0'
lean --version | grep -F '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b'

arena="$cross_root/tools/lean-kernel-arena"
if [ ! -d "$arena/.git" ]; then
  git clone https://github.com/leanprover/lean-kernel-arena "$arena"
fi
git -C "$arena" checkout --detach b83254de5146ef34147ab82a48edbe1856b0edcc
project="$cross_root/tools/export-replay"
mkdir -p "$project"
cp "$arena/checkers/official/Main.lean" "$project/Main.lean"
printf '%s  %s\n' 556dd7ff4498ab19fecfa3c268d48090b2e7e723abd59f43d8e513c9769d8e5c "$project/Main.lean" | sha256sum --check
printf '%s\n' leanprover/lean4:v4.34.0 > "$project/lean-toolchain"
cat > "$project/lakefile.toml" <<'EOF'
name = "kernel"
version = "0.1.0"
defaultTargets = ["kernel"]
[[lean_exe]]
name = "kernel"
root = "Main"
[[require]]
name = "lean4export"
git = "https://github.com/leanprover/lean4export"
rev = "076e8e57707e813375e8f9da8bf989799ace9680"
EOF
cd "$project"
lake build kernel
cat .lake/build/bin/kernel.rsp
ldd .lake/build/bin/kernel

input=${1:-"$bundle/../release-assets/logarithm-main.ndjson.gz"}
if [[ "$input" != /* ]]; then input="$OLDPWD/$input"; fi
if [[ "$input" == *.gz ]]; then
  gzip -dc "$input" > "$project/logarithm-main.ndjson"
  input="$project/logarithm-main.ndjson"
fi
printf '%s  %s\n' 031249e63ebd33862c73b090a60faefeb1131ead9e07c32d0952cb45b80d71b3 "$input" | sha256sum --check

# Independent export audit: the replay API skips unsafe/partial declarations.
# Require that there are none, and require exactly the three standard axioms.
python3 - "$input" "$project" <<'PY'
import json,pathlib,sys
names={0:''}; axioms=[]; unsafe=[]; partial=[]; count=0
for line in open(sys.argv[1]):
    item=json.loads(line)
    if 'in' in item:
        d=item.get('str',item.get('num')); prefix=names[d['pre']]
        names[item['in']]=prefix+('.' if prefix else '')+str(d.get('str',d.get('i')))
    ds=[]
    for key in ['axiom','def','thm','opaque','quot']:
        if key in item:
            d=item[key];ds.append(d)
            if key=='axiom':axioms.append(names[d['name']])
    if 'inductive' in item:
        for key in ['types','ctors','recs']:ds.extend(item['inductive'][key])
    for d in ds:
        count+=1
        if d.get('isUnsafe') or d.get('safety')=='unsafe':unsafe.append(names[d['name']])
        if d.get('safety')=='partial':partial.append(names[d['name']])
report={'axioms':sorted(axioms),'unsafe':unsafe,'partial':partial,'declarations':count}
print(json.dumps(report,indent=2))
assert set(axioms)=={'propext','Quot.sound','Classical.choice'}
assert not unsafe and not partial
assert count==117774
(pathlib.Path(sys.argv[2])/'export-audit.json').write_text(json.dumps(report,indent=2)+'\n')
PY

# Well-formed export syntax containing an ill-typed theorem body. Parsing must
# succeed, while the same normal kernel-checking CLI must reject that body.
cat > "$project/positive.ndjson" <<'EOF'
{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"False"}}
{"ie":0,"sort":0}
{"in":2,"str":{"pre":1,"str":"rec"}}
{"in":3,"str":{"pre":0,"str":"u"}}
{"il":1,"param":3}
{"in":4,"str":{"pre":0,"str":"motive"}}
{"in":5,"str":{"pre":0,"str":"t"}}
{"const":{"name":1,"us":[]},"ie":1}
{"ie":2,"sort":1}
{"forallE":{"binderInfo":"default","body":2,"name":5,"type":1},"ie":3}
{"bvar":1,"ie":4}
{"bvar":0,"ie":5}
{"app":{"arg":5,"fn":4},"ie":6}
{"forallE":{"binderInfo":"default","body":6,"name":5,"type":1},"ie":7}
{"forallE":{"binderInfo":"default","body":7,"name":4,"type":3},"ie":8}
{"inductive":{"ctors":[],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[3],"name":2,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[],"type":8}],"types":[{"all":[1],"ctors":[],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}
{"in":8,"str":{"pre":0,"str":"deliberatelyIllTyped"}}
EOF
cp "$project/positive.ndjson" "$project/ill-typed.ndjson"
printf '%s\n' '{"thm":{"all":[8],"levelParams":[],"name":8,"type":1,"value":1}}' >> "$project/ill-typed.ndjson"
.lake/build/bin/kernel "$project/positive.ndjson"
.lake/build/bin/kernel --parse-only "$project/ill-typed.ndjson"
if .lake/build/bin/kernel "$project/ill-typed.ndjson" > "$project/negative-control.log" 2>&1; then
  printf '%s\n' 'ERROR: checker accepted the ill-typed proof.' >&2
  exit 1
fi
cat "$project/negative-control.log"
grep -F '(kernel) declaration type mismatch' "$project/negative-control.log"

# No parse-only flag: stock Main creates a trust-level-zero empty environment
# and invokes Lean.Kernel.Environment.replay, checking proof bodies.
date -u +'%Y-%m-%dT%H:%M:%SZ'
/usr/bin/time -v .lake/build/bin/kernel "$input"
date -u +'%Y-%m-%dT%H:%M:%SZ'
printf '%s\n' 'Lean 4.34.0 fresh textual kernel replay accepted.'
