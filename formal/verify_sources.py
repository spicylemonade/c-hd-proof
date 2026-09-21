from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
manifest = root.parent / 'verification/FROZEN_SOURCES.sha256'
n = 0
for line in manifest.read_text().splitlines():
    if not line.strip():
        continue
    expected, relative = line.split(None, 1)
    relative = relative.lstrip('*')
    original = root / 'frozen-build-33' / relative
    assert hashlib.sha256(original.read_bytes()).hexdigest() == expected, relative
    if relative not in {'lakefile.toml', 'lake-manifest.json'}:
        portable = root / 'lean' / relative
        assert portable.read_bytes() == original.read_bytes(), relative
    n += 1
print(f'PASS: {n} frozen files verified; portable proof sources are byte-identical.')
