#!/usr/bin/env python3
"""Audit project declarations without treating proposition definitions as proofs.

Run after installing the pinned Lean toolchain and mathlib cache:
    python3 tools/audit.py
Generated Lean, logs, and JSON reports stay in project-local work/.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|constant|native_decide)\b")
VENDOR_FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|native_decide)\b")
NUMBERED_RESULT_IDS = (
    "1_1", "1_2", "2_1", "2_2", "2_3", "3_1", "4_1",
    "5_1", "5_2", "5_3", "5_4", "5_5", "5_6", "6_1", "6_2",
)
NUMBERED_TARGET_PROOFS = {
    f"Paper.Numbered.Statement_{number}": f"Paper.Numbered.result_{number}"
    for number in NUMBERED_RESULT_IDS
}
TARGET_PROOFS = {
    "Paper.MainReplicaSymmetryTarget": "Paper.replicaSymmetry",
    "Paper.SmoothATBoundaryTarget": "Paper.smoothATBoundary",
    "Paper.StrictReplicaSymmetryTarget": "Paper.strictReplicaSymmetry",
    **NUMBERED_TARGET_PROOFS,
}
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?P<modifiers>(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|structure|inductive|class|axiom|constant)\s+"
    r"(?P<name>[^\s(:{]+)"
)


def mask_comments_and_strings(source: str) -> str:
    """Replace comments/strings by whitespace, retaining line/column locations."""
    out = list(source)
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out[i] = " "
                if source[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif source.startswith("--", i):
            j = source.find("\n", i)
            if j == -1:
                j = len(source)
            out[i:j] = " " * (j - i)
            i = j
        elif source[i] == '"':
            out[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    return "".join(out)


def scan_sources(root: Path) -> tuple[list[dict], list[dict]]:
    declarations: list[dict] = []
    violations: list[dict] = []
    paths = set((root / "Paper").rglob("*.lean"))
    if (root / "Paper.lean").is_file():
        paths.add(root / "Paper.lean")
    for path in sorted(paths):
        masked = mask_comments_and_strings(path.read_text(encoding="utf-8"))
        relative = str(path.relative_to(root))
        for match in FORBIDDEN.finditer(masked):
            violations.append({
                "file": relative,
                "line": masked.count("\n", 0, match.start()) + 1,
                "token": match.group(),
            })
        lines = masked.splitlines()
        scope: list[tuple[str, str]] = []
        for index, line in enumerate(lines):
            namespace = re.match(r"\s*namespace\s+([\w.]+)\s*$", line)
            section = re.match(
                r"\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*"
                r"section(?:\s+([\w.]+))?\s*$", line
            )
            end = re.match(r"\s*end(?:\s+([\w.]+))?\s*$", line)
            if namespace:
                scope.append(("namespace", namespace.group(1)))
                continue
            if section:
                scope.append(("section", section.group(1) or ""))
                continue
            if end:
                if scope:
                    scope.pop()
                continue
            match = DECLARATION.match(line)
            if not match:
                continue
            name = match.group("name")
            namespace_prefix = ".".join(n for kind, n in scope if kind == "namespace")
            qualified = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(
                part for part in (namespace_prefix, name) if part
            )
            # The header ends before the definition/proof body.
            header = "\n".join(lines[index:])
            header = re.split(r":=|\bwhere\b", header, maxsplit=1)[0]
            is_prop_definition = match.group("kind") in {"def", "abbrev", "opaque"} and bool(
                re.search(r":\s*Prop\s*$", header)
            )
            is_private = "private" in match.group("modifiers").split()
            kind = match.group("kind")
            if kind in {"theorem", "lemma"}:
                classification = "proved_theorem"
            elif is_prop_definition and (name.endswith("Target") or qualified in TARGET_PROOFS):
                classification = "target_definition"
            elif is_prop_definition:
                classification = "proposition_definition"
            elif kind in {"def", "abbrev", "opaque"}:
                classification = "definition"
            else:
                classification = "type_declaration"
            declarations.append({
                "name": qualified,
                "kind": kind,
                "classification": classification,
                "private": is_private,
                "file": relative,
                "line": index + 1,
                "axiom_check": "pending" if not is_private else "transitive_only",
            })
    return declarations, violations


def scan_vendor_sources(root: Path) -> tuple[int, list[dict]]:
    paths = sorted((root / "vendor").rglob("*.lean"))
    violations: list[dict] = []
    for path in paths:
        masked = mask_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in VENDOR_FORBIDDEN.finditer(masked):
            violations.append({
                "file": str(path.relative_to(root)),
                "line": masked.count("\n", 0, match.start()) + 1,
                "token": match.group(),
            })
    return len(paths), violations


def source_snapshot(root: Path) -> dict[str, str]:
    # Hash the complete source candidate, including metadata, licences, CI,
    # provenance and compatibility patches. Generated evidence stays outside
    # the snapshot to avoid hashing this audit's own report or changing logs.
    excluded = {".git", ".lake", "work", "audits", "__pycache__"}
    paths = {
        path for path in root.rglob("*")
        if path.is_file() and not path.is_symlink()
        and not (set(path.relative_to(root).parts) & excluded)
    }
    return {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def run_command(argv: list[str], root: Path, logfile: Path) -> subprocess.CompletedProcess:
    """Execute literal argv; no shell or string interpolation is involved."""
    result = subprocess.run(argv, cwd=root, text=True, capture_output=True, env=os.environ.copy())
    logfile.write_text(result.stdout + result.stderr, encoding="utf-8")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-only", action="store_true", help="Do not run Lean")
    parser.add_argument("--no-build", action="store_true", help="Audit an already-built aggregate Paper")
    parser.add_argument("--lake", default="lake", help="Lake executable; passed as one literal argument")
    parser.add_argument("--report", default="work/audit-report.json", help="Report path, relative to project root")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    work = root / "work"
    work.mkdir(exist_ok=True)
    snapshot = source_snapshot(root)
    declarations, violations = scan_sources(root)
    vendor_count, vendor_violations = scan_vendor_sources(root)
    report = {
        "schema_version": 3,
        "source_sha256": snapshot,
        "standard_axiom_whitelist": sorted(STANDARD_AXIOMS),
        "source_scan": "passed" if not violations else "failed",
        "source_violations": violations,
        "vendor_source_scan": "passed" if not vendor_violations else "failed",
        "vendor_source_file_count": vendor_count,
        "project_lean_file_count": len(list((root / "Paper").rglob("*.lean"))) + 1,
        "vendor_source_violations": vendor_violations,
        "build_status": "not_run",
        "lean_audit_status": "not_run",
        "aggregate_module": "Paper",
        "numbered_results": [
            {"number": number.replace("_", "."), "target": target,
             "proof": proof, "closed_proof_check": "not_run"}
            for number, (target, proof) in zip(NUMBERED_RESULT_IDS, NUMBERED_TARGET_PROOFS.items())
        ],
        "declarations": declarations,
        "classification_note": (
            "A Prop-valued def describes a proposition and is not a proof. "
            "A target is discharged only by typechecking its designated closed proof. "
            "Private declarations are checked transitively through public declarations. "
            "A theorem is verified only if compilation and its axiom audit pass; "
            "its explicit hypotheses remain mathematical assumptions. "
            "Vendor sources are scanned separately; imported proof dependencies are "
            "checked transitively through project declarations."
        ),
    }
    errors = bool(violations or vendor_violations)
    public = [d for d in declarations if not d["private"]]
    if not args.scan_only:
        lake = shutil.which(args.lake)
        if lake is None:
            report["lean_audit_status"] = "failed"
            report["error"] = "Lake executable not found; configure PATH or pass --lake"
            errors = True
        elif not (root / "Paper.lean").is_file():
            report["lean_audit_status"] = "failed"
            report["error"] = "Aggregate Paper.lean is missing"
            errors = True
        else:
            build_ok = True
            if not args.no_build:
                build = run_command([lake, "build", "Paper"], root, work / "audit-build.log")
                build_ok = build.returncode == 0
                report["build_status"] = "passed" if build_ok else "failed"
                report["build_return_code"] = build.returncode
                errors |= not build_ok
            else:
                report["build_status"] = "skipped_by_request"
            if build_ok:
                invalid = [d["name"] for d in public if not re.fullmatch(r"[\w'.]+", d["name"])]
                if invalid:
                    report["lean_audit_status"] = "failed"
                    report["error"] = "Scanner cannot safely emit these identifiers"
                    report["invalid_identifiers"] = invalid
                    errors = True
                else:
                    scratch = work / "Audit.lean"
                    scratch.write_text("module\npublic import Paper\n\n" + "".join(
                        "#print axioms " + d["name"] + "\n" for d in public
                    ) + "".join(
                        f"example : {target} := {proof}\n"
                        for target, proof in TARGET_PROOFS.items()
                    ), encoding="utf-8")
                    lean = run_command([lake, "env", "lean", str(scratch)], root, work / "audit-lean.log")
                    report["lean_return_code"] = lean.returncode
                    output = lean.stdout + lean.stderr
                    dependencies: dict[str, list[str]] = {}
                    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
                        dependencies[match.group(1)] = [a.strip() for a in match.group(2).split(",") if a.strip()]
                    for match in re.finditer(r"'([^']+)' does not depend on any axioms", output):
                        dependencies[match.group(1)] = []
                    for declaration in public:
                        axioms = dependencies.get(declaration["name"])
                        if axioms is None:
                            declaration["axiom_check"] = "missing_report"
                            errors = True
                            continue
                        declaration["axioms"] = axioms
                        declaration["unexpected_axioms"] = sorted(set(axioms) - STANDARD_AXIOMS)
                        declaration["axiom_check"] = "failed" if declaration["unexpected_axioms"] else "passed"
                        errors |= bool(declaration["unexpected_axioms"])
                    errors |= lean.returncode != 0
                    report["lean_audit_status"] = "failed" if errors else "passed"
                    if lean.returncode == 0:
                        checked = {d["name"]: d for d in public}
                        for declaration in declarations:
                            proof = TARGET_PROOFS.get(declaration["name"])
                            if proof and checked.get(proof, {}).get("axiom_check") == "passed":
                                declaration["classification"] = "discharged_target_definition"
                                declaration["closed_proof"] = proof
                        for numbered in report["numbered_results"]:
                            proof = checked.get(numbered["proof"], {})
                            target = checked.get(numbered["target"], {})
                            passed = (proof.get("axiom_check") == "passed" and
                                      target.get("classification") == "discharged_target_definition")
                            numbered["closed_proof_check"] = "passed" if passed else "failed"
                            errors |= not passed
    current_snapshot = source_snapshot(root)
    report["source_changed_during_audit"] = snapshot != current_snapshot
    if report["source_changed_during_audit"]:
        errors = True
        if report["lean_audit_status"] == "passed":
            report["lean_audit_status"] = "source_changed_during_audit"
    elif errors and report["lean_audit_status"] == "passed":
        report["lean_audit_status"] = "failed"
    counts: dict[str, int] = {}
    for declaration in declarations:
        counts[declaration["classification"]] = counts.get(declaration["classification"], 0) + 1
    report["declaration_counts"] = counts
    report["public_theorem_count"] = sum(
        d["classification"] == "proved_theorem" and not d["private"] for d in declarations
    )
    report["source_file_count"] = len(snapshot)
    report_path = root / args.report
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "source_scan": report["source_scan"],
        "build_status": report["build_status"],
        "lean_audit_status": report["lean_audit_status"],
        "public_theorems": report["public_theorem_count"],
        "discharged_target_definitions": counts.get("discharged_target_definition", 0),
        "undischarged_target_definitions": counts.get("target_definition", 0),
        "vendor_source_scan": report["vendor_source_scan"],
        "numbered_results_passed": sum(
            n["closed_proof_check"] == "passed" for n in report["numbered_results"]
        ),
        "report": str(report_path),
    }, ensure_ascii=False))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
