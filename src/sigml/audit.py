"""Audit learned concept embeddings against the Lean-verified spec.

The Lean formalization (SignificanceUnified/ConceptualSpace.lean) defines what
a well-formed concept over a multi-dimensional conceptual space is:

  * KonceptN      — a predicate plus a placement chi : entity -> Z^n
  * CCD3N         — contrast grounding: any two distinct units admit an
                    outside witness both are closer to each other than to
  * RaiseProd     — the strict product order on Z^n (deeper on every
                    dimension, strictly somewhere)
  * KonceptDefN   — essential definition: definiendum = genus meet
                    differentia, with RaiseProd(genus.chi a, diff.chi a)
                    for every unit, grounded by a CCD witness whose
                    contrast lacks the differentia

This module re-implements those definitions over plain integer vectors and
audits a learned embedding against them. Everything here is the UNVERIFIED
mirror: the point of the pipeline is that `emit_lean_certificate` writes the
passing subset back out as a Lean file whose proofs are closed by `decide`,
so the final arbiter is the Lean kernel, not this code.

Vocabulary: a "placement" maps each entity to an integer vector (one per
concept — each concept carries its own characteristic scale, exactly as
Koncept does in Basic.lean).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from itertools import combinations


Vec = tuple[int, ...]


# ── the spec, mirrored ──────────────────────────────────────────────


def dist1(a: Vec, b: Vec) -> int:
    """L1 distance — mirrors `dist₁`."""
    return sum(abs(x - y) for x, y in zip(a, b, strict=True))


def similar_by_contrast(a: Vec, b: Vec, c: Vec) -> bool:
    """Mirrors `SimilarByContrastN a b c`."""
    d = dist1(a, b)
    return a != b and d < dist1(a, c) and d < dist1(b, c)


def raise_prod(a: Vec, b: Vec) -> bool:
    """Mirrors `RaiseProd a b`: b dominates a and differs somewhere."""
    return all(x <= y for x, y in zip(a, b, strict=True)) and a != b


# ── model of a learned ontology ─────────────────────────────────────


@dataclass
class Concept:
    name: str
    members: list[str]
    chi: dict[str, Vec]  # placement of EVERY entity on this concept's scale


@dataclass
class Definition:
    definiendum: str
    genus: str
    differentia: str


@dataclass
class Ontology:
    entities: list[str]
    concepts: dict[str, Concept]
    definitions: list[Definition]
    dim: int


@dataclass
class Finding:
    check: str
    subject: str
    passed: bool
    detail: str
    witness: dict = field(default_factory=dict)


# ── checks ──────────────────────────────────────────────────────────


def check_ccd3(onto: Ontology, concept: Concept) -> list[Finding]:
    """CCD₃N: every pair of distinct units needs an outside contrast witness."""
    findings = []
    outsiders = [e for e in onto.entities if e not in concept.members]
    for a, b in combinations(concept.members, 2):
        witness = next(
            (
                c
                for c in outsiders
                if similar_by_contrast(concept.chi[a], concept.chi[b], concept.chi[c])
            ),
            None,
        )
        if witness is None:
            findings.append(
                Finding(
                    "ccd3",
                    concept.name,
                    False,
                    f"no contrast witness for units ({a}, {b}): "
                    f"the pair does not cluster against any outsider",
                )
            )
        else:
            findings.append(
                Finding(
                    "ccd3",
                    concept.name,
                    True,
                    f"({a}, {b}) grounded by contrast {witness}",
                    witness={"a": a, "b": b, "contrast": witness},
                )
            )
    if not findings:
        findings.append(
            Finding(
                "ccd3",
                concept.name,
                False,
                "fewer than two units: satisfies CCD₃ only vacuously "
                "(ccd3_of_subsingleton) and cannot be essentially defined",
            )
        )
    return findings


def check_definition(onto: Ontology, d: Definition) -> list[Finding]:
    """KonceptDefN: meet structure, essentiality raise, two units, contrast."""
    findings = []
    dfn = onto.concepts[d.definiendum]
    gen = onto.concepts[d.genus]
    dif = onto.concepts[d.differentia]
    label = f"{d.definiendum} = {d.differentia} {d.genus}"

    meet = sorted(set(gen.members) & set(dif.members))
    if sorted(dfn.members) != meet:
        findings.append(
            Finding(
                "isMeet",
                label,
                False,
                f"definiendum extension {sorted(dfn.members)} != "
                f"genus ∩ differentia {meet}",
            )
        )
    else:
        findings.append(Finding("isMeet", label, True, "extension is the meet"))

    for a in dfn.members:
        ok = raise_prod(gen.chi[a], dif.chi[a])
        # the uniform DepthFunctional collapse: direction imposed by equal
        # weights, the spec's own mechanism (DepthFunctional.mono /
        # functionals_disagree) for recovering 1-D direction
        scalar_ok = sum(gen.chi[a]) < sum(dif.chi[a])
        detail = (
            f"unit {a}: genus χ {gen.chi[a]} "
            f"{'<' if ok else '⊀ (incomparable or reversed)'} "
            f"differentia χ {dif.chi[a]}"
        )
        if not ok:
            detail += (
                "; uniform-functional collapse "
                f"{'HOLDS' if scalar_ok else 'fails'} "
                f"({sum(gen.chi[a])} vs {sum(dif.chi[a])})"
            )
        findings.append(
            Finding(
                "isEssential",
                label,
                ok,
                detail,
                witness={"unit": a, "scalar_ok": scalar_ok},
            )
        )

    if len(dfn.members) < 2:
        findings.append(
            Finding(
                "has_two_units",
                label,
                False,
                f"definiendum has {len(dfn.members)} unit(s); "
                "essential definitions need two (KonceptDefN.has_two_units)",
            )
        )
    else:
        # a CCD witness whose contrast also lacks the differentia (ccd_contrast)
        outsiders = [
            e
            for e in onto.entities
            if e not in dfn.members and e not in dif.members
        ]
        a, b = dfn.members[0], dfn.members[1]
        pair_witness = None
        for aa, bb in combinations(dfn.members, 2):
            w = next(
                (
                    c
                    for c in outsiders
                    if similar_by_contrast(dfn.chi[aa], dfn.chi[bb], dfn.chi[c])
                ),
                None,
            )
            if w is not None:
                pair_witness = (aa, bb, w)
                break
        if pair_witness is None:
            findings.append(
                Finding(
                    "ccd_witness",
                    label,
                    False,
                    "no unit pair clusters against an outsider lacking the "
                    "differentia — the definition is ungrounded",
                )
            )
        else:
            aa, bb, w = pair_witness
            findings.append(
                Finding(
                    "ccd_witness",
                    label,
                    True,
                    f"({aa}, {bb}) grounded by contrast {w} (lacks {d.differentia})",
                    witness={"a": aa, "b": bb, "contrast": w},
                )
            )
    return findings


def check_acyclicity(onto: Ontology) -> list[Finding]:
    """Definition links must admit a topological order (no_definition_cycleN).

    In the Lean development acyclicity is a THEOREM: each definition carries a
    strict raise, and strict orders have no cycles. Here we run the check
    contrapositively: if the link graph (differentia of one definition feeding
    the genus of another) has a cycle, no consistent depth assignment can
    exist and some essentiality raise must be violated.
    """
    edges = [(d.genus, d.differentia) for d in onto.definitions]
    nodes = {n for e in edges for n in e}
    order: list[str] = []
    remaining = dict.fromkeys(nodes)
    graph = {n: [b for a, b in edges if a == n] for n in nodes}
    temp: set[str] = set()
    cycle: list[str] = []

    def visit(n: str) -> bool:
        if n not in remaining:
            return True
        if n in temp:
            cycle.append(n)
            return False
        temp.add(n)
        for m in graph[n]:
            if not visit(m):
                return False
        temp.discard(n)
        del remaining[n]
        order.append(n)
        return True

    ok = all(visit(n) for n in list(nodes))
    if ok:
        return [
            Finding(
                "acyclicity",
                "definition graph",
                True,
                f"genus→differentia links admit a topological order: "
                f"{' ≺ '.join(order)}",
            )
        ]
    return [
        Finding(
            "acyclicity",
            "definition graph",
            False,
            f"definition links contain a cycle near {cycle[0]}: "
            "no depth certificate can exist (no_definition_cycleN)",
        )
    ]


def audit(onto: Ontology) -> list[Finding]:
    findings: list[Finding] = []
    for c in onto.concepts.values():
        findings.extend(check_ccd3(onto, c))
    for d in onto.definitions:
        findings.extend(check_definition(onto, d))
    findings.extend(check_acyclicity(onto))
    return findings


def report(findings: list[Finding]) -> dict:
    failed = [f for f in findings if not f.passed]
    return {
        "checks": len(findings),
        "passed": len(findings) - len(failed),
        "failed": len(failed),
        "findings": [f.__dict__ for f in findings],
    }


# ── Lean certificate emission ───────────────────────────────────────
#
# The passing subset is written out as Lean definitions plus theorems whose
# proofs are `by decide`. If `lake build` accepts the file, the learned
# structure REALLY satisfies the spec — the kernel checked it, not us.


def _ident(name: str) -> str:
    out = "".join(ch if ch.isalnum() else " " for ch in name).title().replace(" ", "")
    return out[0].lower() + out[1:] if out else "x"


def _ctor(name: str) -> str:
    return _ident(name)


def _vec(v: Vec) -> str:
    return "![" + ", ".join(str(x) for x in v) + "]"


def emit_lean_certificate(onto: Ontology, findings: list[Finding]) -> str:
    """Write the audited-and-passing structure as a Lean file.

    Concepts become KonceptN terms; definitions whose every check passed
    become KonceptDefN terms (inhabiting the verified spec's type is the
    certificate); per-pair CCD groundings become `decide` theorems.
    """
    ok = {(f.check, f.subject) for f in findings if f.passed}
    bad_subjects = {f.subject for f in findings if not f.passed}

    ents = [(_ctor(e), e) for e in onto.entities]
    lines = [
        "import ConceptualSpace",
        "",
        "/-!",
        "# Machine-generated audit certificate — do not edit",
        "",
        "Generated by src/sigml/audit.py from a learned order embedding.",
        "Entities were embedded, placements quantized to ℤ^"
        + str(onto.dim)
        + ",",
        "and the structure audited against the spec in ConceptualSpace.lean.",
        "Only concepts and definitions that PASSED the audit appear here;",
        "every proof below is closed by `decide`, so acceptance of this file",
        "by the Lean kernel certifies that the learned structure satisfies",
        "the formal spec.",
        "-/",
        "",
        "namespace AuditCert",
        "",
        "inductive E",
        "  | " + " | ".join(c for c, _ in ents),
        "  deriving DecidableEq, Fintype",
        "",
    ]

    for cname, concept in onto.concepts.items():
        ci = _ident(cname)
        lines.append(f"def {ci}Members : List E := "
                     f"[{', '.join('.' + _ctor(m) for m in concept.members)}]")
        lines.append(f"def {ci}Chi : E → Point {onto.dim}")
        for ent in onto.entities:
            lines.append(f"  | .{_ctor(ent)} => {_vec(concept.chi[ent])}")
        lines.append("")
        lines.append(f"def k{ci[0].upper()}{ci[1:]} : KonceptN {onto.dim} E where")
        lines.append(f"  pred := fun a => a ∈ {ci}Members")
        lines.append(f"  χ    := {ci}Chi")
        lines.append("")

    for f in findings:
        if f.check == "ccd3" and f.passed and f.witness:
            c = onto.concepts[f.subject]
            ci = _ident(f.subject)
            a, b, w = f.witness["a"], f.witness["b"], f.witness["contrast"]
            lines.append(
                f"/-- CCD grounding for {f.subject}: "
                f"{a} and {b} cluster against {w}. -/"
            )
            lines.append(
                f"theorem {ci}_ccd_{_ctor(a)}_{_ctor(b)} :"
            )
            lines.append(
                f"    SimilarByContrastN ({ci}Chi .{_ctor(a)}) "
                f"({ci}Chi .{_ctor(b)}) ({ci}Chi .{_ctor(w)}) := by decide"
            )
            lines.append("")

    uniform_emitted = False
    for d in onto.definitions:
        label = f"{d.definiendum} = {d.differentia} {d.genus}"
        if label in bad_subjects:
            lines.append(f"-- Definition '{label}' FAILED the audit; not certified.")
            for f in findings:
                if f.subject == label and not f.passed:
                    lines.append(f"--   ✗ {f.check}: {f.detail}")
            lines.append("")
            # partial certificate: if ONLY the product-order essentiality
            # failed while the uniform DepthFunctional collapse holds on
            # every unit (and the rest of the definition is sound), certify
            # the weaker, weighting-dependent claim — direction imposed by
            # equal weights, per DepthFunctional.mono / functionals_disagree.
            def_findings = [f for f in findings if f.subject == label]
            only_essential_failed = all(
                f.passed for f in def_findings if f.check != "isEssential"
            )
            scalar_all = [
                f.witness.get("scalar_ok")
                for f in def_findings
                if f.check == "isEssential" and not f.passed
            ]
            if only_essential_failed and scalar_all and all(scalar_all):
                gi, di_ = _ident(d.genus), _ident(d.differentia)
                fi = _ident(d.definiendum)
                if not uniform_emitted:
                    lines.extend(
                        [
                            "/-- The uniform depth functional: equal attention "
                            "to every dimension. -/",
                            f"def uniform : DepthFunctional {onto.dim} :=",
                            "  ⟨fun _ => 1, fun _ => Int.zero_lt_one⟩",
                            "",
                        ]
                    )
                    uniform_emitted = True
                lines.extend(
                    [
                        f"/-- Weaker certificate for '{label}': the product-order",
                        "    raise fails (genus and differentia attentions are",
                        "    incomparable), but under the uniform functional the",
                        "    differentia is deeper on every unit. Direction is",
                        "    imposed by the weighting, not discovered — exactly",
                        "    what `functionals_disagree` warns. -/",
                        f"theorem {fi}_functional_essential :",
                        f"    ∀ a, (a ∈ {gi}Members ∧ a ∈ {di_}Members) →",
                        f"      Raise (uniform.eval ({gi}Chi a)) "
                        f"(uniform.eval ({di_}Chi a)) := by",
                        "  decide",
                        "",
                    ]
                )
            continue
        gi, di_, fi = _ident(d.genus), _ident(d.differentia), _ident(d.definiendum)
        gK = f"k{gi[0].upper()}{gi[1:]}"
        dK = f"k{di_[0].upper()}{di_[1:]}"
        w = next(
            f.witness
            for f in findings
            if f.subject == label and f.check == "ccd_witness" and f.passed
        )
        a, b, c = _ctor(w["a"]), _ctor(w["b"]), _ctor(w["contrast"])
        name = f"def{fi[0].upper()}{fi[1:]}"
        lines.extend(
            [
                f"/-- Certified essential definition: {label}. "
                f"A term of `KonceptDefN` IS the certificate. -/",
                f"def {name} : KonceptDefN {onto.dim} E where",
                f"  definiendum := {gK}.meet {dK}",
                f"  genus       := {gK}",
                f"  differentia := {dK}",
                "  isMeet      := rfl",
                "  isEssential := by",
                f"    show ∀ a, (a ∈ {gi}Members ∧ a ∈ {di_}Members) →",
                f"      RaiseProd ({gi}Chi a) ({di_}Chi a)",
                "    decide",
                "  ccd := {",
                f"    k        := {gK}.meet {dK}",
                f"    a        := .{a}",
                f"    b        := .{b}",
                f"    contrast := .{c}",
                f"    ha       := by show E.{a} ∈ {gi}Members ∧ "
                f"E.{a} ∈ {di_}Members; decide",
                f"    hb       := by show E.{b} ∈ {gi}Members ∧ "
                f"E.{b} ∈ {di_}Members; decide",
                f"    hc       := by show ¬(E.{c} ∈ {gi}Members ∧ "
                f"E.{c} ∈ {di_}Members); decide",
                "    hab      := by decide",
                "    similar  := by",
                "      show SimilarByContrastN",
                f"        (fun i => max ({gi}Chi (E.{a}) i) ({di_}Chi (E.{a}) i))",
                f"        (fun i => max ({gi}Chi (E.{b}) i) ({di_}Chi (E.{b}) i))",
                f"        (fun i => max ({gi}Chi (E.{c}) i) ({di_}Chi (E.{c}) i))",
                "      decide }",
                "  ccd_concept  := rfl",
                f"  ccd_contrast := by show ¬(E.{c} ∈ {di_}Members); decide",
                "",
                f"/-- Downstream theorems come free once the term exists: "
                f"e.g. two units. -/",
                f"example : ∃ a b, ({gK}.meet {dK}).pred a ∧ "
                f"({gK}.meet {dK}).pred b ∧ a ≠ b :=",
                f"  {name}.has_two_units",
                "",
            ]
        )

    lines.append("end AuditCert")
    lines.append("")
    return "\n".join(lines)


def save_report(findings: list[Finding], path: str) -> None:
    with open(path, "w") as fh:
        json.dump(report(findings), fh, indent=2)
