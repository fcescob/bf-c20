#!/usr/bin/env python3
"""Hash the distributed proof sources, certificate, and verification workflows."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parent
files = [p for p in root.iterdir() if p.is_file() and not p.name.startswith('.') and p.name != 'SHA256SUMS']
files += list((root / 'C20MatchingFinite').glob('Head*.lean'))
files += list((root / '.github' / 'workflows').glob('*.yml'))
files.sort(key=lambda p: p.relative_to(root).as_posix())
(root / 'SHA256SUMS').write_text(''.join(
    hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(root).as_posix() + '\n'
    for p in files
))
