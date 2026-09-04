#!/usr/bin/env bash
# Self-contained reproduction. Run on a compute host or GitHub Actions.
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p out
CXX="${CXX:-c++}"
"$CXX" -std=c++17 -O2 -Wall -Wextra -UNDEBUG exhaustive_local.cpp -o out/exhaustive
"$CXX" -std=c++17 -O2 -Wall -Wextra -UNDEBUG replay_certificate.cpp -o out/replay

# Regenerate all cases even when a banked certificate is supplied.
./out/exhaustive | tee out/exhaustive.log
cmp exhaustive.log out/exhaustive.log
python3 - <<'PY'
import gzip
import hashlib
from pathlib import Path
p = Path('out/partitions.bin').read_bytes()
assert len(p) == 25_708_552
assert hashlib.sha256(p).hexdigest() == '51fe93dad24911b568121b928fb14c308ceccd3c1af337ddf50576b0c8322fc8'
banked = Path('partitions.bin.gz')
if banked.exists():
    assert gzip.decompress(banked.read_bytes()) == p
    print('PASS: regenerated certificate agrees byte for byte with banked certificate')
else:
    print('PASS: regenerated certificate has the published length and SHA-256')
PY
./out/replay | tee out/replay.log
cmp replay.log out/replay.log
python3 verify_physical_lifts.py | tee out/physical_lifts.log
cmp physical_lifts.log out/physical_lifts.log
echo 'PASS: full enumeration, certificate replay, and 2000 physical cover checks'
