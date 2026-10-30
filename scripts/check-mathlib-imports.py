#!/usr/bin/env python3
"""Require project mathlib imports to exist in its pinned Git source tree."""
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
package = root / ".lake/packages/mathlib"
manifest = json.loads((root / "lake-manifest.json").read_text())
revision = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
head = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
if head != revision:
    raise SystemExit(f"mathlib checkout {head} differs from manifest {revision}")
tracked = set(subprocess.check_output(
    ["git", "-C", str(package), "ls-tree", "-r", "--name-only", "HEAD"], text=True
).splitlines())
failed = []
for source in [*root.glob("*.lean"), *(root / "Torsion").rglob("*.lean")]:
    for number, line in enumerate(source.read_text().splitlines(), 1):
        words = line.split("--", 1)[0].split()
        if "import" not in words or words[0] not in {"import", "public", "meta"}:
            continue
        for module in words[words.index("import") + 1:]:
            if module == "Mathlib" or module.startswith("Mathlib."):
                if module.replace(".", "/") + ".lean" not in tracked:
                    failed.append(f"{source.relative_to(root)}:{number}: {module} is absent from pinned mathlib")
if failed:
    raise SystemExit("\n".join(failed))
print("All project mathlib imports exist in the pinned dependency source tree.")
