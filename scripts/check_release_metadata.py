#!/usr/bin/env python3
"""Check release metadata and the reproducible Lean/Mathlib lockfile.

Standard-library-only preflight used by CI and available locally:

    python3 scripts/check_release_metadata.py

This checks coherence, not the correctness of a Mathlib tag's upstream SHA;
that tag is independently verified before the lockfile is committed.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ZENODO_CONCEPT_DOI = "10.5281/zenodo.22696492"


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def match_one(pattern: str, contents: str, description: str, *, flags: int = 0) -> str:
    match = re.search(pattern, contents, flags)
    if match is None:
        raise SystemExit(f"Cannot read {description}")
    return match.group(1)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    toolchain = read("lean-toolchain").strip()
    lean_version = match_one(
        r"^leanprover/lean4:(v\d+\.\d+\.\d+)$",
        toolchain,
        "a stable lean-toolchain",
    )

    lakefile = read("lakefile.toml")
    project_version = match_one(
        r'^version = "([^"]+)"$',
        lakefile,
        "Lake project version",
        flags=re.MULTILINE,
    )
    mathlib_version = match_one(
        r'\[\[require\]\]\s*\nname = "mathlib"\s*\n'
        r'git = "https://github\.com/leanprover-community/mathlib4\.git"\s*\n'
        r'rev = "([^"]+)"',
        lakefile,
        "Mathlib require/revision",
    )
    require(
        lean_version == mathlib_version,
        f"Lean/Mathlib release mismatch: {lean_version} != {mathlib_version}",
    )

    manifest = json.loads(read("lake-manifest.json"))
    packages = manifest["packages"]
    package_names = [package["name"] for package in packages]
    require(
        len(package_names) == len(set(package_names)),
        "Duplicate package name in lake-manifest.json",
    )
    mathlib_packages = [pkg for pkg in packages if pkg["name"] == "mathlib"]
    require(len(mathlib_packages) == 1, "Expected exactly one Mathlib package")
    mathlib = mathlib_packages[0]
    require(
        mathlib["inputRev"] == mathlib_version,
        "Mathlib manifest inputRev differs from lakefile.toml",
    )
    require(
        mathlib["url"] == "https://github.com/leanprover-community/mathlib4.git",
        "Unexpected Mathlib Git URL in lake-manifest.json",
    )
    require(
        mathlib.get("inherited") is False,
        "Mathlib must be a direct, non-inherited dependency",
    )
    for package in packages:
        require(
            re.fullmatch(r"[0-9a-f]{40}", package["rev"]) is not None,
            f"Dependency {package['name']} is not locked to a commit SHA",
        )

    citation = read("CITATION.cff")
    citation_version = match_one(
        r'^version:\s*"?([^"\s]+)"?$',
        citation,
        "citation version",
        flags=re.MULTILINE,
    )
    citation_doi = match_one(
        r'^doi:\s*"?([^"\s]+)"?$',
        citation,
        "citation DOI",
        flags=re.MULTILINE,
    )
    require(
        project_version == citation_version,
        f"Lake/CITATION version mismatch: {project_version} != {citation_version}",
    )
    require(
        citation_doi == ZENODO_CONCEPT_DOI,
        "CITATION.cff must use the project's stable Zenodo concept DOI",
    )

    notes_path = ROOT / "docs" / "releases" / f"v{project_version}.md"
    require(notes_path.is_file(), f"Missing release notes: {notes_path}")
    notes = notes_path.read_text(encoding="utf-8")
    require(
        lean_version in notes and mathlib["rev"] in notes,
        "Release notes must record the pinned Lean version and Mathlib commit",
    )
    require(
        f"## [{project_version}]" in read("CHANGELOG.md"),
        "The changelog must include the proposed project version",
    )

    readme = read("README.md")
    require(
        f"https://zenodo.org/badge/DOI/{citation_doi}.svg" in readme
        and f"https://doi.org/{citation_doi}" in readme,
        "README badge must use the same stable Zenodo concept DOI as CITATION.cff",
    )

    print(f"Project version: {project_version}")
    print(f"Lean/Mathlib release: {lean_version}")
    print(f"Mathlib commit: {mathlib['rev']}")
    print(f"Locked packages: {len(packages)}")
    print(f"Zenodo concept DOI: {citation_doi}")
    print("Release metadata preflight passed.")


if __name__ == "__main__":
    main()
