#!/usr/bin/env python3
"""Local structural preflight for the Palomar submission candidate.

Requirements snapshot: PalomarRegistry/PalomarPolicy CONTRIBUTING.md and
PalomarRegistry/PalomarSubmission toolchains.json, read 2026-10-08. This does not replace Palomar's trusted
verification, Lean parser checks, dependency authentication, Challenge import
closure inspection, licence detector, independent kernels, or editorial review.
The generated project-local work/ directory is not a submission source tree;
omit it from the committed repository/package. Use --sources-only before a
build, and the full check after dependencies have been fetched.

Requires Python 3.11+; full metadata checking also requires PyYAML.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

MINIMUM_TOOLCHAIN = "v4.35.0-rc2"
COMMENT_MARKER = re.compile(r"/-|-/")
# Header scanner follows PalomarTemplate/scripts/check-lean-sources.py. The
# official verifier additionally asks Lean's parser to confirm module headers.
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
GITHUB_URL = re.compile(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?")
COMMIT = re.compile(r"[0-9a-f]{40}")
LICENCE_NAME = re.compile(r"(?:LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?", re.I)
COMPILED_SUFFIXES = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def physical_lines(text: str) -> int:
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def has_module_header(text: str) -> bool:
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
            if depth:
                return False
        else:
            return text.startswith("module", index) and IDENTIFIER_CONTINUATION.match(text, index + 6) is None
    return False


def files_in_candidate(root: Path):
    """Walk contained projects/vendor files; never follow directory symlinks."""
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        here = Path(directory)
        for name in sorted(subdirectories):
            if (here / name).is_symlink() and name.endswith(".lean"):
                yield here / name
        subdirectories[:] = sorted(name for name in subdirectories
            if name not in {".git", ".lake"}
            and not (here == root and name == "work")
            and not (here / name).is_symlink())
        for name in sorted(names):
            path = here / name
            if path.is_symlink() or path.is_file():
                yield path


class Check:
    def __init__(self, root: Path):
        self.root = root
        self.errors: list[str] = []
        self.warnings: list[str] = []
        self.facts: dict = {"minimum_toolchain_snapshot": MINIMUM_TOOLCHAIN}

    def fail(self, message: str):
        self.errors.append(message)

    def regular(self, path: Path, limit: int, *, nonempty: bool = True) -> bool:
        name = str(path.relative_to(self.root))
        if path.is_symlink() or not path.is_file():
            self.fail(f"{name}: required regular non-symlink file is missing or invalid")
            return False
        size = path.stat().st_size
        if size > limit or (nonempty and size == 0):
            self.fail(f"{name}: size {size} bytes is outside 1..{limit}")
            return False
        return True

    def text(self, path: Path, limit: int) -> str | None:
        if not self.regular(path, limit):
            return None
        try:
            return path.read_bytes().decode("utf-8")
        except UnicodeError:
            self.fail(f"{path.relative_to(self.root)}: invalid UTF-8")
            return None

    def object_json(self, path: Path, limit: int = 1024 * 1024) -> dict | None:
        source = self.text(path, limit)
        if source is None:
            return None
        try:
            def unique(pairs):
                result = {}
                for key, value in pairs:
                    if key in result:
                        raise ValueError(f"duplicate key {key!r}")
                    result[key] = value
                return result
            value = json.loads(source, object_pairs_hook=unique)
            if not isinstance(value, dict):
                raise ValueError("expected one object")
            return value
        except ValueError as error:
            self.fail(f"{path.relative_to(self.root)}: invalid JSON: {error}")
            return None

    def sources(self):
        count, total, maximum = 0, 0, 0
        for path in files_in_candidate(self.root):
            relative = path.relative_to(self.root)
            if path.suffix == ".lean":
                if path.is_symlink():
                    self.fail(f"{relative}: Lean source symlinks are rejected")
                    continue
                source = self.text(path, 500 * 1024 * 1024)
                if source is None:
                    continue
                lines = physical_lines(source)
                count += 1
                maximum = max(maximum, lines)
                if lines > 10_000:
                    self.fail(f"{relative}: {lines} physical lines exceeds 10,000")
                if path.name != "lakefile.lean" and not has_module_header(source):
                    self.fail(f"{relative}: missing initial module header")
            if not path.is_symlink():
                total += path.stat().st_size
                if path.suffix in COMPILED_SUFFIXES:
                    self.fail(f"{relative}: compiled artifact outside .lake")
                with path.open("rb") as handle:
                    if handle.read(130).startswith(b"version https://git-lfs.github.com/spec/v1\n"):
                        self.fail(f"{relative}: Git LFS pointer must be replaced by ordinary source")
        if total > 500 * 1024 * 1024:
            self.fail(f"candidate source files: {total} bytes exceeds 500 MiB")
        self.facts.update(lean_source_files=count, maximum_source_lines=maximum, candidate_bytes=total)
        # work/ is excluded here only because it is generated scratch. Palomar
        # does not exempt arbitrary committed work/ files from source rules.
        if (self.root / ".git").exists():
            tracked = subprocess.run(["git", "ls-files", "-z", "work"], cwd=self.root, capture_output=True)
            if tracked.returncode == 0 and tracked.stdout:
                self.fail("work/: generated scratch must not be tracked in the submission repository")
            index = subprocess.run(["git", "ls-files", "--stage", "-z"], cwd=self.root, capture_output=True)
            if index.returncode == 0 and any(entry.startswith(b"160000 ") for entry in index.stdout.split(b"\0")):
                self.fail("submission repository: Git submodules are rejected")

    def environment(self, require_local: bool) -> dict:
        lakefiles = [self.root / name for name in ("lakefile.toml", "lakefile.lean")
                     if (self.root / name).exists() or (self.root / name).is_symlink()]
        settings = {}
        if len(lakefiles) != 1:
            self.fail("project root: require exactly one lakefile.toml or lakefile.lean")
        elif (source := self.text(lakefiles[0], 1024 * 1024)) is not None:
            if lakefiles[0].suffix == ".toml":
                try:
                    settings = tomllib.loads(source)
                except tomllib.TOMLDecodeError as error:
                    self.fail(f"lakefile.toml: {error}")
        source = self.text(self.root / "lean-toolchain", 4096)
        toolchain = source.strip() if source is not None else ""
        self.facts["toolchain"] = toolchain
        def release(version):
            match = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", version)
            return tuple(map(int, match.group(1, 2, 3))) + (int(match[4]) if match[4] else sys.maxsize,) if match else None
        submitted = release(toolchain.removeprefix("leanprover/lean4:"))
        if not toolchain.startswith("leanprover/lean4:") or submitted is None:
            self.fail("lean-toolchain: expected leanprover/lean4:vMAJOR.MINOR.PATCH[-rcN]")
        elif submitted < release(MINIMUM_TOOLCHAIN):
            self.fail(f"lean-toolchain: below official minimum snapshot {MINIMUM_TOOLCHAIN}")
        manifest = self.object_json(self.root / "lake-manifest.json")
        if manifest is None:
            return settings
        packages = manifest.get("packages")
        if not isinstance(packages, list):
            self.fail("lake-manifest.json: packages must be a list")
            return settings
        mathlib = None
        for package in packages:
            if not isinstance(package, dict):
                self.fail("lake-manifest.json: package entries must be objects")
                continue
            if package.get("type") == "git":
                url, rev = package.get("url"), package.get("rev")
                if not isinstance(url, str) or not GITHUB_URL.fullmatch(url):
                    self.fail(f"dependency {package.get('name')}: require public credential-free HTTPS GitHub URL")
                if not isinstance(rev, str) or not COMMIT.fullmatch(rev):
                    self.fail(f"dependency {package.get('name')}: require full lowercase commit SHA")
                if url in {"https://github.com/leanprover-community/mathlib4", "https://github.com/leanprover-community/mathlib4.git"}:
                    mathlib = package
        if mathlib:
            self.facts["mathlib_revision"] = mathlib.get("rev")
            local = self.root / ".lake" / "packages" / mathlib["name"]
            if not (local / "lean-toolchain").is_file():
                message = "Mathlib exact toolchain consistency: local dependency unavailable; fetch dependencies and rerun"
                (self.fail if require_local else self.warnings.append)(message)
            else:
                if (local / "lean-toolchain").read_text(encoding="utf-8").strip() != toolchain:
                    self.fail("lean-toolchain: differs from local resolved Mathlib toolchain (including rc/patch)")
                head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=local, text=True, capture_output=True)
                if head.returncode != 0 or head.stdout.strip() != mathlib.get("rev"):
                    self.fail("local Mathlib checkout: HEAD does not match lake-manifest.json revision")
                else:
                    self.facts["mathlib_local_toolchain_consistency"] = "passed; upstream authentication deferred to Palomar"
            requirements = settings.get("require", [])
            for package in requirements if isinstance(requirements, list) else []:
                if package.get("name") == mathlib["name"] and package.get("rev") != mathlib.get("rev"):
                    self.fail("lakefile.toml: Mathlib requested revision differs from committed manifest")
        return settings

    def comparator(self, settings: dict):
        config = self.object_json(self.root / "comparator.json")
        if config is None:
            return
        required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
        if not required <= config.keys() or config.keys() - required - {"definition_names", "enable_nanoda"}:
            self.fail("comparator.json: missing required keys or unaccepted fields")
        modules = [config.get(key) for key in ("challenge_module", "solution_module")]
        if any(not isinstance(name, str) or not MODULE_NAME.fullmatch(name) for name in modules) or modules[0] == modules[1]:
            self.fail("comparator.json: require distinct valid dotted Challenge/Solution module names")
            return
        for key in ("theorem_names", "definition_names", "permitted_axioms"):
            values = config.get(key, [])
            if not isinstance(values, list) or any(not isinstance(value, str) or not value.strip() for value in values):
                self.fail(f"comparator.json: {key} must be a list of nonempty strings")
            elif key == "theorem_names" and not values:
                self.fail("comparator.json: theorem_names must be nonempty")
            elif key == "permitted_axioms" and set(values) - STANDARD_AXIOMS:
                self.fail("comparator.json: only propext, Quot.sound, Classical.choice are permitted")
        # Local TOML source-directory approximation; Palomar obtains the actual
        # ordered source paths from Lake, and checks the transitive import graph.
        directories = [self.root]
        for library in settings.get("lean_lib", []):
            if isinstance(library, dict) and isinstance(library.get("srcDir"), str):
                candidate = (self.root / library["srcDir"]).resolve()
                if candidate.is_relative_to(self.root) and candidate not in directories:
                    directories.append(candidate)
        for index, module in enumerate(modules):
            relative = Path(*module.split(".")).with_suffix(".lean")
            candidates = [directory / relative for directory in directories]
            path = next((path for path in candidates if path.is_file() and not path.is_symlink()), candidates[0])
            source = self.text(path, 100 * 1024 if index == 0 else 500 * 1024 * 1024)
            if index == 0 and source is not None:
                lines, size = physical_lines(source), path.stat().st_size
                self.facts["challenge"] = {"module": module, "file": str(path.relative_to(self.root)), "lines": lines, "bytes": size}
                if lines > 1000:
                    self.fail(f"{module}: Challenge exceeds 1,000 physical lines")
                if lines > 300 or size > 32 * 1024:
                    self.warnings.append(f"{module}: Challenge exceeds preferred 300-line/32-KiB audit size")

    def metadata(self):
        source = self.text(self.root / "formalization.yaml", 256 * 1024)
        if source is None:
            return
        try:
            import yaml
        except ImportError:
            self.fail("metadata check requires PyYAML: python3 -m pip install PyYAML==6.0.3")
            return
        class UniqueLoader(yaml.SafeLoader):
            pass
        def mapping(loader, node, deep=False):
            result = {}
            for key_node, value_node in node.value:
                if key_node.value == "<<":
                    raise ValueError("YAML merge keys are not accepted")
                key = loader.construct_object(key_node, deep=deep)
                if key in result:
                    raise ValueError(f"duplicate mapping key {key!r}")
                result[key] = loader.construct_object(value_node, deep=deep)
            return result
        UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, mapping)
        try:
            data = yaml.load(source, Loader=UniqueLoader)
            if not isinstance(data, dict):
                raise ValueError("require one top-level mapping")
        except (yaml.YAMLError, ValueError, TypeError) as error:
            self.fail(f"formalization.yaml: {error}")
            return
        def nonempty(value):
            return isinstance(value, str) and bool(value.strip()) and value.strip().upper() not in {"TODO", "TBD", "UNKNOWN", "PENDING"}
        def people(value, field):
            if not isinstance(value, list) or not value or any(not nonempty(item) for item in value):
                self.fail(f"formalization.yaml: {field} requires nonempty human name strings")
            elif any(item.strip().lower() in {"chatgpt", "codex", "openai", "gpt-6", "gpt-6 (codex)", "ai agent", "autonomous agent"} for item in value):
                self.fail(f"formalization.yaml: {field} reserves authorship/responsibility for humans")
        if data.get("version") != "v0.4":
            self.fail("formalization.yaml: use current version v0.4")
        project = data.get("project") if isinstance(data.get("project"), dict) else {}
        for key, limit in (("name", 300), ("description", 10_000), ("license", 300)):
            value = project.get(key)
            if not nonempty(value) or len(value) > limit:
                self.fail(f"formalization.yaml: project.{key} requires a nonempty string of at most {limit} characters")
        people(project.get("authors"), "project.authors")
        people(project.get("responsible_maintainers"), "project.responsible_maintainers")
        self.license(project.get("license"))
        repository = data.get("repository", {})
        if not isinstance(repository, dict):
            self.fail("formalization.yaml: repository must be a mapping when supplied")
        else:
            substantive = repository.get("substantive_formalization")
            role = repository.get("role", "thin-wrapper" if substantive else "substantive-development")
            if role == "thin-wrapper":
                if not isinstance(substantive, dict) or not nonempty(substantive.get("id")) or not isinstance(substantive.get("revision"), str) or not COMMIT.fullmatch(substantive["revision"]):
                    self.fail("formalization.yaml: thin-wrapper requires substantive repository id and full lowercase commit SHA")
                elif not (GITHUB_URL.fullmatch(substantive["id"]) or re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", substantive["id"])):
                    self.fail("formalization.yaml: substantive_formalization.id must identify a GitHub owner/repository")
            elif role != "substantive-development" or substantive is not None:
                self.fail("formalization.yaml: inconsistent repository role/substantive_formalization")
        sources = data.get("sources")
        valid_sources = isinstance(sources, list) and bool(sources) and all(isinstance(item, dict) for item in sources)
        if not valid_sources:
            self.fail("formalization.yaml: sources requires a nonempty list of mappings")
        else:
            for index, item in enumerate(sources):
                if not nonempty(item.get("title")) or item.get("relationship") not in {"formalizes", "adapts", "independently-proves", "background", "other"}:
                    self.fail(f"formalization.yaml: sources[{index}] requires title and canonical relationship")
                if "type" in item and item["type"] not in {"paper", "book", "web discussion", "folklore", "original-proof", "other"}:
                    self.fail(f"formalization.yaml: sources[{index}].type is not a Palomar source type")
                contributors = item.get("contributors", [])
                if not isinstance(contributors, list) or any(not isinstance(person, dict) or not nonempty(person.get("name")) or not nonempty(person.get("role")) or len(person["role"]) > 200 for person in contributors):
                    self.fail(f"formalization.yaml: sources[{index}].contributors requires name and role strings")
            original = any(item.get("type") == "original-proof" for item in sources)
            if original:
                if any(item.get("relationship") not in {"background", "other"} or (item.get("type") == "original-proof" and item.get("relationship") != "other") for item in sources):
                    self.fail("formalization.yaml: inconsistent original-proof source relationships")
            elif not any(item.get("relationship") in {"formalizes", "adapts", "independently-proves"} for item in sources):
                self.fail("formalization.yaml: source-based result requires a substantive source relationship")
        classification = data.get("classification") if isinstance(data.get("classification"), dict) else {}
        taxonomy = self.object_json(self.root / "tools" / "palomar-taxonomies.json")
        allowed = taxonomy.get("codes", {}) if taxonomy else {}
        for key, minimum in (("arxiv", 1), ("msc2020", 0)):
            values = classification.get(key, [])
            if not isinstance(values, list) or not minimum <= len(values) <= 8 or any(not isinstance(value, str) or value not in allowed.get(key, []) for value in values) or len(set(values)) != len(values):
                self.fail(f"formalization.yaml: classification.{key} requires {minimum}..8 distinct official taxonomy codes")
        automation = data.get("automation") if isinstance(data.get("automation"), dict) else {}
        methods = automation.get("methods")
        if not isinstance(methods, list) or not methods or any(not isinstance(item, dict) or item.get("method") not in {"manual", "copilot", "agent", "autonomous", "other"} for item in methods):
            self.fail("formalization.yaml: automation.methods requires nonempty portable method entries")
        review = data.get("review") if isinstance(data.get("review"), dict) else {}
        if not nonempty(review.get("status")):
            self.fail("formalization.yaml: review.status requires completed review status")
        self.warnings.append("Human attribution, licence detection, factual metadata, and current standards require Palomar/editorial confirmation")

    def license(self, declared):
        candidates = [path for path in self.root.iterdir() if LICENCE_NAME.fullmatch(path.name)]
        if len(candidates) != 1:
            self.fail("project root: require exactly one conventional LICENSE/LICENCE/COPYING/UNLICENSE/OFL text file")
            return
        source = self.text(candidates[0], 1024 * 1024)
        if source is None:
            return
        # These are local evidence checks, not Palomar's licensee detector.
        identifiers = set(re.findall(r"SPDX-License-Identifier:\s*([^\r\n]+)", source))
        patterns = {
            "Apache-2.0": r"Apache License\s+Version 2\.0",
            "MIT": r"Permission is hereby granted, free of charge, to any person obtaining a copy",
            "BSD-3-Clause": r"Neither the name of .+? nor the names of its contributors may be used",
            "ISC": r"Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee",
            "CC0-1.0": r"CC0 1\.0 Universal",
            "Unlicense": r"This is free and unencumbered software released into the public domain",
        }
        identifiers.update(key for key, pattern in patterns.items() if re.search(pattern, source, re.I | re.S))
        identifiers = {identifier.strip() for identifier in identifiers}
        if len(identifiers) != 1 or next(iter(identifiers), "") not in patterns:
            self.fail(f"{candidates[0].name}: local scan cannot establish one unambiguous SPDX identifier; verify using Palomar's licence detector")
        elif declared != next(iter(identifiers)):
            self.fail(f"{candidates[0].name}: detected local identifier differs from project.license")
        else:
            self.facts["repository_license_local_match"] = declared


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--sources-only", action="store_true", help="Check source headers/size/artifacts without metadata or dependencies")
    parser.add_argument("--require-local-mathlib", action="store_true", help="Fail if exact local Mathlib toolchain/revision cannot be inspected")
    parser.add_argument("--skip-metadata", action="store_true", help="Check build inputs independently of unresolved human attribution/licensing")
    parser.add_argument("--report", type=Path, help="Optional JSON report path, relative to the project root")
    args = parser.parse_args()
    check = Check(args.root.resolve())
    check.sources()
    if not args.sources_only:
        settings = check.environment(args.require_local_mathlib)
        check.comparator(settings)
        if not args.skip_metadata:
            check.metadata()
    scope = "sources_only" if args.sources_only else "build_inputs_without_metadata" if args.skip_metadata else "full_local_preflight"
    report = {"check": "local_structural_preflight", "status": "failed" if check.errors else "passed", "scope": scope, "facts": check.facts, "errors": check.errors, "warnings": check.warnings}
    if args.report:
        path = check.root / args.report
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return int(bool(check.errors))


if __name__ == "__main__":
    raise SystemExit(main())
