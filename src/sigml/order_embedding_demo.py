"""Order embeddings -> audit -> Lean certificate, end to end.

The pipeline this demo exercises:

  1. TRAIN   a Vendrov-style order embedding (numpy SGD) on a toy taxonomy:
             membership pairs (entity, concept) are embedded in R^d_{>=0} so
             that members dominate their concepts componentwise.
  2. PLACE   each entity on each concept's characteristic scale:
             chi_C(a) = round(emb(a) * emb(C)) elementwise -- the concept's
             vector is its dimension profile, the entity's placement under a
             concept is its position weighted by that profile. Quantized to
             Z^d, matching the Lean spec's decidable integer scales.
  3. AUDIT   the placements against the verified spec (audit.py mirrors
             ConceptualSpace.lean): CCD3 grounding, essentiality raises,
             meet structure, two-unit rule, acyclicity.
  4. CERTIFY the passing subset by emitting SignificanceUnified/AuditCert.lean,
             whose proofs are all closed by `decide`. `lake build` is the
             final judge -- the kernel checks what this script claims.

The toy ontology deliberately contains one bad definition (Dog = Domestic
Canid, whose definiendum is a singleton) so the audit has a real violation
to catch: the two-unit rule (KonceptDefN.has_two_units) rejects it, and it
is excluded from the certificate with the reason recorded.

Run from the repo root:

    .venv/bin/python src/sigml/order_embedding_demo.py
    lake build          # kernel-checks the emitted certificate
"""

from __future__ import annotations

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from audit import (  # noqa: E402
    Concept,
    Definition,
    Ontology,
    audit,
    emit_lean_certificate,
    report,
    save_report,
)

RNG = np.random.default_rng(7)
DIM = 3
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


# ── toy taxonomy ────────────────────────────────────────────────────

ENTITIES = ["socrates", "hypatia", "rex", "luna", "tom", "tweety", "oak"]

MEMBERSHIP = {
    "animal": ["socrates", "hypatia", "rex", "luna", "tom", "tweety"],
    "rational": ["socrates", "hypatia"],
    "human": ["socrates", "hypatia"],  # = rational animal
    "canid": ["rex", "luna"],
    "domestic": ["rex", "tom"],
    "dog": ["rex"],  # = domestic canid -- SINGLETON, should fail the audit
}

DEFINITIONS = [
    Definition("human", "animal", "rational"),
    Definition("dog", "canid", "domestic"),
]


# ── 1. train order embeddings ───────────────────────────────────────


def train(epochs: int = 4000, lr: float = 0.05, margin: float = 1.0) -> dict[str, np.ndarray]:
    """Vendrov et al. order embeddings: for a positive pair (x below y in the
    hierarchy, i.e. entity x a member of concept y), penalize the amount by
    which y fails to be dominated by x:  E(x, y) = ||max(0, y - x)||^2.
    Negatives are pushed to energy >= margin. Nonnegativity by projection."""
    names = ENTITIES + list(MEMBERSHIP)
    emb = {n: RNG.uniform(0.1, 1.0, DIM) for n in names}
    positives = [(e, c) for c, mem in MEMBERSHIP.items() for e in mem]
    # subsumptions implied by the definitions are training signal too
    positives += [("human", "animal"), ("human", "rational"),
                  ("dog", "canid"), ("dog", "domestic")]
    negatives = [
        (e, c)
        for c, mem in MEMBERSHIP.items()
        for e in ENTITIES
        if e not in mem
    ]
    for _ in range(epochs):
        x, y = positives[RNG.integers(len(positives))]
        gap = np.maximum(0.0, emb[y] - emb[x])
        emb[x] += lr * gap
        emb[y] -= lr * gap
        x, y = negatives[RNG.integers(len(negatives))]
        gap = np.maximum(0.0, emb[y] - emb[x])
        if gap @ gap < margin:
            emb[x] -= lr * gap
            emb[y] += lr * gap
        for n in (x, y):
            np.maximum(emb[n], 0.0, out=emb[n])
    return emb


# ── 2. quantized per-concept placements ─────────────────────────────


def placements(emb: dict[str, np.ndarray]) -> Ontology:
    concepts = {}
    for cname, members in MEMBERSHIP.items():
        chi = {
            e: tuple(int(v) for v in np.round(emb[e] * emb[cname] * 4))
            for e in ENTITIES
        }
        concepts[cname] = Concept(cname, list(members), chi)
    return Ontology(ENTITIES, concepts, DEFINITIONS, DIM)


# ── 3 & 4. audit and certify ────────────────────────────────────────


def main() -> None:
    print("training order embedding on", len(ENTITIES), "entities /",
          len(MEMBERSHIP), "concepts ...")
    emb = train()
    onto = placements(emb)

    findings = audit(onto)
    rep = report(findings)
    print(f"audit: {rep['passed']}/{rep['checks']} checks passed")
    for f in findings:
        mark = "ok " if f.passed else "FAIL"
        print(f"  [{mark}] {f.check:14s} {f.subject}: {f.detail}")

    results = os.path.join(REPO, "results")
    os.makedirs(results, exist_ok=True)
    save_report(findings, os.path.join(results, "audit_report.json"))

    cert = emit_lean_certificate(onto, findings)
    cert_path = os.path.join(REPO, "SignificanceUnified", "AuditCert.lean")
    with open(cert_path, "w") as fh:
        fh.write(cert)
    print(f"\nwrote {cert_path}")
    print("run `lake build` to kernel-check the certificate")


if __name__ == "__main__":
    main()
