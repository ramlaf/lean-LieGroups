#!/usr/bin/env python3
"""Check the optional adapters against an existing, built BFRF checkout.

Usage: python3 scripts/check_bfrf_compatibility.py [path/to/BFRF]

Run `lake build` in this repository first. The runner reports any additional
DifferentialGeometry prerequisite targets needed by BFRF's imports.
BFRF's dependencies through
`BFRF.HomogeneousLieAlgebra` must already be built with the same Lean toolchain.
Their sources and locked dependencies must be current; shared dependency pins
must match this checkout's pins.
This check does not build BFRF, change either project's dependency pins, or write
to the BFRF checkout. It recompiles BFRF's actual integration and isotropy sources
and the adapters into a temporary directory, then runs the examples and axiom audits.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent


def require_file(path: Path, explanation: str) -> None:
    if not path.is_file():
        raise RuntimeError(f"Missing file: {path}\n{explanation}")


def dependency_identities(manifest_path: Path) -> dict[str, tuple[str, str, str]]:
    """Read resolved Git identities, excluding the intentionally replaced LieGroups."""
    require_file(manifest_path, "Both checkouts need their locked dependency manifests.")
    manifest = json.loads(manifest_path.read_text())
    identities = {}
    for package in manifest["packages"]:
        name = package["name"]
        if name == "LieGroups":
            continue
        if package.get("type") != "git":
            raise RuntimeError(
                f"Cannot compare dependency {name} in {manifest_path}: "
                f"unsupported dependency type {package.get('type')!r}. "
                "Compatibility checking requires resolved Git dependencies."
            )
        url, revision = package.get("url"), package.get("rev")
        subdirectory = package.get("subDir") or ""
        if not isinstance(url, str) or not url or not isinstance(revision, str) or not revision:
            raise RuntimeError(
                f"Dependency {name} in {manifest_path} lacks a resolved Git URL or revision."
            )
        if not isinstance(subdirectory, str):
            raise RuntimeError(f"Dependency {name} in {manifest_path} has an invalid subDir.")
        if name in identities:
            raise RuntimeError(f"Duplicate dependency {name} in {manifest_path}.")
        identities[name] = (url, revision, subdirectory)
    return identities


def check_dependency_compatibility(bfrf_root: Path) -> None:
    """Do not trust BFRF object files against differently pinned dependencies."""
    local = dependency_identities(ROOT / "lake-manifest.json")
    bfrf = dependency_identities(bfrf_root / "lake-manifest.json")
    for name in ("mathlib", "DifferentialGeometry"):
        if name not in local or name not in bfrf:
            raise RuntimeError(f"Both dependency manifests must contain {name}.")
    mismatches = []
    for name in sorted(local.keys() & bfrf.keys()):
        if local[name] != bfrf[name]:
            mismatches.append(
                f"  {name}:\n    LieGroups: {local[name]}\n    BFRF: {bfrf[name]}"
            )
    if mismatches:
        raise RuntimeError(
            "Shared dependency identities differ:\n" + "\n".join(mismatches)
            + "\nUse a BFRF checkout built with matching resolved dependencies; "
            "this runner does not change pins or rebuild BFRF."
        )


def lake_environment() -> dict[str, str]:
    """Use only this checkout's dependencies, ignoring inherited LEAN_PATH."""
    manifest_path = ROOT / "lake-manifest.json"
    require_file(manifest_path, "Build this LieGroups checkout with `lake build` first.")
    manifest = json.loads(manifest_path.read_text())
    packages_root = ROOT / manifest.get("packagesDir", ".lake/packages")
    # Fail before invoking Lake when a checkout is missing: this runner must not
    # trigger dependency cloning as a side effect of loading Lake's environment.
    for package in manifest["packages"]:
        if package["type"] == "git":
            package_root = packages_root / package["name"]
            if package.get("subDir"):
                package_root /= package["subDir"]
        elif package["type"] == "path":
            package_root = ROOT / package["dir"]
        else:
            raise RuntimeError(f"Unsupported dependency type: {package['type']}")
        require_file(
            package_root / package["configFile"],
            "Install and build this LieGroups checkout's dependencies first.",
        )
    inherited = os.environ.copy()
    inherited.pop("LEAN_PATH", None)
    result = subprocess.run(
        [
            "lake", "--no-cache", "env", sys.executable, "-c",
            "import json, os; print(json.dumps(dict(os.environ)))",
        ],
        cwd=ROOT,
        env=inherited,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return json.loads(result.stdout)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "bfrf_root", nargs="?", type=Path, default=ROOT.parent / "BFRF",
        help="existing BFRF checkout (default: sibling BFRF directory)",
    )
    args = parser.parse_args()
    bfrf_root = args.bfrf_root.expanduser().resolve()
    integration_source = bfrf_root / "BFRF/HomogeneousLieGroupIntegration.lean"
    isotropy_source = bfrf_root / "BFRF/HomogeneousIsotropySubgroup.lean"
    bfrf_library = bfrf_root / ".lake/build/lib/lean"
    adapter_source = ROOT / "compat/BFRF/HomomorphismLieAlgebra.lean"
    check_source = ROOT / "scripts/CheckBFRFCompatibility.lean"
    subgroup_adapter_source = ROOT / "compat/BFRF/LieSubgroup.lean"
    subgroup_check_source = ROOT / "scripts/CheckBFRFLieSubgroup.lean"
    require_file(integration_source, "Pass the path to an existing BFRF checkout.")
    require_file(isotropy_source, "BFRF's isotropy subgroup source is missing.")
    for root in (ROOT, bfrf_root):
        require_file(root / "lean-toolchain", "Both checkouts need a Lean toolchain file.")
    if (ROOT / "lean-toolchain").read_text().strip() != (
        bfrf_root / "lean-toolchain"
    ).read_text().strip():
        raise RuntimeError("BFRF and LieGroups must use the same Lean toolchain.")
    check_dependency_compatibility(bfrf_root)
    require_file(
        bfrf_library / "BFRF/HomogeneousLieAlgebra.olean",
        "BFRF's prerequisite build is missing. In that checkout, run "
        "`lake build BFRF.HomogeneousLieAlgebra` first.",
    )
    require_file(
        ROOT / ".lake/build/lib/lean/LieGroups/HomomorphismLieAlgebra.olean",
        "Run `lake build` in this LieGroups checkout first.",
    )
    require_file(
        ROOT / ".lake/build/lib/lean/LieGroups/EmbeddedSubgroupTangent.olean",
        "Run `lake build` in this LieGroups checkout first.",
    )
    # These are the external DifferentialGeometry imports in BFRF's integration
    # source closure. Its two maximal roots build all five without adding a
    # downstream dependency or using BFRF's separately pinned LieGroups package.
    geometry_library = ROOT / ".lake/packages/DifferentialGeometry/.lake/build/lib/lean"
    required_geometry = (
        "DifferentialGeometry.Geometry.Connection.LeviCivita.Defs",
        "DifferentialGeometry.Geometry.Connection.Realization.Embedding",
        "DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling",
        "DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs",
        "DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan",
    )
    missing_geometry = [
        name for name in required_geometry
        if not (geometry_library / (name.replace(".", "/") + ".olean")).is_file()
    ]
    if missing_geometry:
        raise RuntimeError(
            "Unbuilt DifferentialGeometry prerequisites in this LieGroups checkout:\n  "
            + "\n  ".join(missing_geometry)
            + "\nRun here: lake build "
            "DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling "
            "DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan"
        )
    require_file(adapter_source, "The optional BFRF adapter source is missing.")
    require_file(check_source, "The BFRF adapter examples and audit are missing.")
    require_file(subgroup_adapter_source, "The optional BFRF subgroup adapter is missing.")
    require_file(subgroup_check_source, "The BFRF subgroup examples and audit are missing.")
    env = lake_environment()
    lean = shutil.which("lean", path=env.get("PATH"))
    if lean is None:
        raise RuntimeError("Lean is not available in this checkout's Lake environment.")
    with tempfile.TemporaryDirectory(prefix="liegroups-bfrf-") as temporary:
        output_root = Path(temporary)
        bfrf_overlay = output_root / "BFRF"
        bfrf_overlay.mkdir()
        # Lean resolves the first matching top-level module directory, without
        # falling through to later BFRF directories for individual imports.
        # Overlay the already-built prerequisites with read-only symlink use;
        # No output module may be a symlink into the sibling checkout.
        rebuilt_modules = {
            "HomogeneousLieGroupIntegration", "HomomorphismLieAlgebra",
            "HomogeneousIsotropySubgroup", "LieSubgroup",
        }
        for artifact in (bfrf_library / "BFRF").iterdir():
            if artifact.name.split(".", 1)[0] not in rebuilt_modules:
                (bfrf_overlay / artifact.name).symlink_to(artifact)
        env["LEAN_PATH"] = os.pathsep.join(
            [str(output_root), str(bfrf_library), env["LEAN_PATH"]]
        )
        for label, source, module_root, output in (
            (
                "BFRF integration source", integration_source, bfrf_root,
                output_root / "BFRF/HomogeneousLieGroupIntegration.olean",
            ),
            (
                "BFRF adapter", adapter_source, ROOT / "compat",
                output_root / "BFRF/HomomorphismLieAlgebra.olean",
            ),
            (
                "BFRF isotropy source", isotropy_source, bfrf_root,
                output_root / "BFRF/HomogeneousIsotropySubgroup.olean",
            ),
            (
                "BFRF subgroup adapter", subgroup_adapter_source, ROOT / "compat",
                output_root / "BFRF/LieSubgroup.olean",
            ),
        ):
            print(f"Checking {label}: {source}", flush=True)
            subprocess.run(
                [lean, f"--root={module_root}", "-o", str(output), str(source)],
                cwd=ROOT, env=env, check=True,
            )
        print("Checking BFRF adapter examples and axiom audit", flush=True)
        subprocess.run([lean, str(check_source)], cwd=ROOT, env=env, check=True)
        print("Checking BFRF subgroup examples and axiom audit", flush=True)
        subprocess.run([lean, str(subgroup_check_source)], cwd=ROOT, env=env, check=True)
    print("BFRF compatibility check passed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        print(f"BFRF compatibility check failed (exit {error.returncode}).", file=sys.stderr)
        sys.exit(error.returncode)
    except (OSError, RuntimeError, ValueError, KeyError) as error:
        print(f"BFRF compatibility check failed: {error}", file=sys.stderr)
        sys.exit(1)
