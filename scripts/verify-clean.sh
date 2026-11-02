#!/usr/bin/env bash
# Rebuild every project module without reusing project compilation artifacts.
# Only the pinned external dependency cache is retained.
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

python3 scripts/check-lean-sources.py
lake exe cache get

# Cached dependency artifacts must correspond to the checked-in source pins.
python3 - <<'PY'
import json
from pathlib import Path
import subprocess

manifest = json.loads(Path('lake-manifest.json').read_text())
packages = Path(manifest['packagesDir'])
for package in manifest['packages']:
    if package['type'] != 'git':
        raise SystemExit(f"Unpinned dependency type for {package['name']}")
    directory = packages / package['name']
    head = subprocess.check_output(
        ['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True
    ).strip()
    if head != package['rev']:
        raise SystemExit(f"{package['name']}: checkout {head} differs from manifest {package['rev']}")
    if subprocess.run(['git', '-C', str(directory), 'diff', '--quiet', 'HEAD', '--']).returncode:
        raise SystemExit(f"{package['name']}: tracked dependency sources have local changes")
print(f"Verified exact clean source revisions for {len(manifest['packages'])} dependencies.")
PY
python3 scripts/check-mathlib-imports.py
lake env lean --version

# Do not use `lake clean` on the dependencies: mathlib's pinned cache is an
# external build input. Remove every project build product, including IR.
python3 - <<'PY_CLEAN'
from pathlib import Path
import shutil

lake_directory = Path.cwd() / '.lake'
build_directory = lake_directory / 'build'
if lake_directory.is_symlink() or build_directory.is_symlink():
    raise SystemExit('Refusing to remove a symbolic-link build directory')
if build_directory.exists():
    if not build_directory.is_dir() or build_directory.resolve().parent != lake_directory:
        raise SystemExit('Unexpected project build directory')
    shutil.rmtree(build_directory)
print('Removed project compilation artifacts; external dependency cache retained.')
PY_CLEAN
lake build Torsion SubmissionStatement Solution
lake env lean Audit.lean
# The intentional reference placeholder is checked in its own environment.
lake build Challenge
