"""Exercise the full KonceptDefCCD certificate path on a synthetic ontology.

The real demo's learned embedding currently earns only the weak
(uniform-functional) essentiality grade, so the strong certificate path —
emitting a term of `KonceptDefCCD`, with commensurate attention profiles and
`genusScale/diffScale := rfl` — would otherwise ship untested. This fixture
is a hand-crafted ontology engineered to pass every check, proving the
emission path end to end: run this script, then `lake build` kernel-checks
SignificanceUnified/AuditCertSynthetic.lean.

The construction: one definition F = D G over four entities. The genus
attends mostly to dimension 0, the differentia mostly to dimension 1 (equal
total attention, 240 each); members sit at positions with zero on dimension
0, so the differentia's placement dominates the genus's on every dimension —
a strict product-order raise, no functional collapse needed.

Run from the repo root:  .venv/bin/python src/sigml/synthetic_cert_test.py
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from audit import (  # noqa: E402
    Concept,
    Definition,
    Ontology,
    audit,
    emit_lean_certificate,
    report,
)

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

ENTITIES = ["ada", "bee", "cat", "dot"]
POS = {"ada": (0, 2), "bee": (0, 3), "cat": (5, 0), "dot": (9, 9)}

CONCEPTS = {
    "genusG": (["ada", "bee", "cat"], (200, 40)),
    "diffD": (["ada", "bee"], (40, 200)),
    "defF": (["ada", "bee"], (200, 40)),
}

DEFINITIONS = [Definition("defF", "genusG", "diffD")]


def build() -> Ontology:
    concepts = {}
    for cname, (members, w) in CONCEPTS.items():
        chi = {
            e: tuple(wi * pi for wi, pi in zip(w, POS[e], strict=True))
            for e in ENTITIES
        }
        concepts[cname] = Concept(cname, members, chi, weights=w)
    return Ontology(ENTITIES, concepts, DEFINITIONS, 2, pos=POS)


def main() -> None:
    onto = build()
    findings = audit(onto)
    rep = report(findings)
    print(f"synthetic audit: {rep['passed']}/{rep['checks']} checks passed")
    for f in findings:
        mark = "ok " if f.passed else "FAIL"
        print(f"  [{mark}] {f.check:14s} {f.subject}: {f.detail}")
    failed = [f for f in findings if not f.passed]
    if failed:
        raise SystemExit("synthetic fixture must pass every check")

    cert = emit_lean_certificate(
        onto, findings, namespace="AuditCertSynthetic",
        source="a hand-crafted fixture exercising the KonceptDefCCD path")
    path = os.path.join(REPO, "SignificanceUnified", "AuditCertSynthetic.lean")
    with open(path, "w") as fh:
        fh.write(cert)
    if "KonceptDefCCD" not in cert:
        raise SystemExit("strong certificate path did not fire")
    print(f"\nwrote {path} (contains a KonceptDefCCD term)")
    print("run `lake build` to kernel-check it")


if __name__ == "__main__":
    main()
