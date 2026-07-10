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


def placements_dot(emb: dict[str, np.ndarray]) -> Ontology:
    """The naive rule from the first iteration: entity position weighted by
    the concept's own vector. Kept for comparison; its known failure mode is
    that very general concepts have near-zero vectors, so their scales
    degenerate (the `animal` pathology)."""
    concepts = {}
    for cname, members in MEMBERSHIP.items():
        chi = {
            e: tuple(int(v) for v in np.round(emb[e] * emb[cname] * 4))
            for e in ENTITIES
        }
        concepts[cname] = Concept(cname, list(members), chi)
    return Ontology(ENTITIES, concepts, DEFINITIONS, DIM)


def diagnostic_weights(
    pos: dict[str, tuple[int, ...]], members: list[str], foil: list[str]
) -> tuple[int, ...]:
    """Integer diagnosticity of each dimension, matching `diagWeightIn` in
    ContrastScale.lean exactly:

        w_i = |#foil * sum_members pos_i  -  #members * sum_foil pos_i|

    (the member-vs-foil separation along i, scaled to stay integral), then
    reduced by the gcd across dimensions — the canonical primitive
    representative of the weighting ray, so scales of different concepts are
    comparable and certificate numbers stay small. The Lean theorems are
    about the raw weights; only ratios between dimensions matter for the
    audit, and gcd reduction preserves those."""
    w = [
        abs(
            len(foil) * sum(pos[a][i] for a in members)
            - len(members) * sum(pos[a][i] for a in foil)
        )
        for i in range(DIM)
    ]
    # Commensuration: rescale every concept's weighting to the same total
    # attention (L1 = 240). Raw diagnostic weights of different concepts have
    # arbitrary relative magnitude (they scale with #members * #foil), and
    # essentiality compares values ACROSS two concepts' scales — Rand's
    # requirement that the characteristic be a COMMON denominator, appearing
    # as a normalization obligation. Ratios between dimensions (all the Lean
    # degeneracy/invariance theorems speak of) are preserved up to rounding.
    total = sum(w)
    if total == 0:
        return tuple(0 for _ in w)
    return tuple(int(round(240 * x / total)) for x in w)


def placements_contrast(emb: dict[str, np.ndarray]) -> Ontology:
    """Contrast-derived placement (ContrastScale.lean): the scale on which a
    concept measures its units is the scale on which its units differ from
    their foil.

    Foil choice: for a concept serving as the differentia of a definition,
    the foil is the REST OF ITS GENUS (the differentia divides the genus —
    the foil for `rational` is the other animals, not the oak); otherwise
    the foil is everything outside the concept."""
    pos = {e: tuple(int(v) for v in np.round(emb[e] * 4)) for e in ENTITIES}
    diff_of = {d.differentia: d for d in DEFINITIONS}
    concepts = {}
    for cname, members in MEMBERSHIP.items():
        if cname in diff_of:
            d = diff_of[cname]
            foil = [
                e
                for e in MEMBERSHIP[d.genus]
                if e not in MEMBERSHIP[d.definiendum]
            ]
        else:
            foil = [e for e in ENTITIES if e not in members]
        w = diagnostic_weights(pos, list(members), foil)
        chi = {
            e: tuple(int(wi * pi) for wi, pi in zip(w, pos[e], strict=True))
            for e in ENTITIES
        }
        concepts[cname] = Concept(cname, list(members), chi)
    return Ontology(ENTITIES, concepts, DEFINITIONS, DIM)


# ── 3 & 4. audit and certify ────────────────────────────────────────


def main() -> None:
    print("training order embedding on", len(ENTITIES), "entities /",
          len(MEMBERSHIP), "concepts ...")
    emb = train()

    # baseline rule, for comparison
    dot_findings = audit(placements_dot(emb))
    dot_rep = report(dot_findings)
    save_report(dot_findings, os.path.join(REPO, "results", "audit_report_dot.json"))

    # contrast-derived rule (ContrastScale.lean)
    onto = placements_contrast(emb)
    findings = audit(onto)
    rep = report(findings)

    print(f"\naudit (dot rule, baseline):      "
          f"{dot_rep['passed']}/{dot_rep['checks']} checks passed")
    print(f"audit (contrast-derived scales): "
          f"{rep['passed']}/{rep['checks']} checks passed\n")
    for f in findings:
        mark = "ok " if f.passed else "FAIL"
        print(f"  [{mark}] {f.check:14s} {f.subject}: {f.detail}")

    # the prediction: the animal degeneracy was an artifact of the dot rule
    animal_dot = [f for f in dot_findings if f.subject == "animal" and f.check == "ccd3"]
    animal_con = [f for f in findings if f.subject == "animal" and f.check == "ccd3"]
    print(f"\nprediction check — animal CCD₃ groundings: "
          f"dot rule {sum(f.passed for f in animal_dot)}/{len(animal_dot)}, "
          f"contrast-derived {sum(f.passed for f in animal_con)}/{len(animal_con)}")

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
