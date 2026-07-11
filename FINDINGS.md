# Findings & status — what to trust

This project has two parts: a **Lean formalization** of significance/concepts
(all machine-checked, `lake build` is green, no `sorry` outside widget demos)
and a **Python audit pipeline** (`src/sigml`) that tests learned taxonomy
embeddings against that spec. The Lean side is settled. The empirical side ran
a sequence of experiments whose conclusions vary in strength — this file is the
honest map, so nobody has to reverse-engineer it from commit history.

Legend: ✅ validated · 🟡 provisional · ⏳ open · ❌ retracted

## Does the Python audit actually run off the Lean theory? — ✅ (primitives)

`sigml validate` + `lake build`. The audit's core predicates in `audit.py`
(`dist1`, `similar_by_contrast`, `raise_prod`) are a hand transcription of the
Lean definitions (`dist₁`, `SimilarByContrastN`, `RaiseProd`). A differential
check now confirms the transcription is faithful: 1,800 random cases (dims 2, 3,
5, 6 — including the dims the WordNet and OBO audits actually use), spanning
**both** verdicts, are emitted as Lean theorems asserting the *Python* verdict
and closed by `decide`. `ValidateMirror.lean` kernel-checks, so Python and Lean
agree on every case; a transcription bug (`<` vs `≤`, L1 vs L2, an off-by-one)
would fail the build on the offending line.

Scope of this guarantee, in two layers:

- **Primitives** (`ValidateMirror.lean`): the 1,800 cases above verify `dist₁`,
  `SimilarByContrastN`, `RaiseProd` match value-for-value / verdict-for-verdict.
- **Composed grounding decision** (`ValidateComposed.lean`): 120 random concepts,
  where Python's whole pairs-and-witnesses CCD₃ *search* is cross-checked against
  the Lean `CCD₃N` proposition itself (`CCD₃N k` / `¬CCD₃N k` by `decide`, both
  verdicts). So the audit's per-concept grounding *decision* — not just the inner
  predicate — provably agrees with the spec. (This checks pure `CCD₃N`; the
  audit's extra "singletons are undefinable" usability rule is a deliberate
  layer on top and is excluded.)

Still conventional Python (not differentially checked): the essentiality
grading, the contrast weighting, and the certificate-emission plumbing. Those are
spot-checked by the `AuditCert*.lean` files but not swept. So the grounding audit
is verified end-to-end against the theory; the essentiality machinery is not.

## Lean formalization — ✅

Everything in `SignificanceUnified/` type-checks against Mathlib. The core
results (two comparison primitives, the concept preorder, essential
definitions, the syllogistic, the surprising consequences, the multi-dimensional
generalization, the FCA bridge, concept functors, the shared-CCD structure) are
theorems, not claims. The machine-generated certificates (`AuditCert*.lean`) are
kernel-checked: a learned/parsed structure inhabiting a spec type, proofs closed
by `decide`.

## Grounding audit (CCD₃ clustering) — ✅

`sigml wordnet`. On a real WordNet Carnivora subtree, ~80–96% of within-family
member pairs cluster against out-family outsiders, and a trained order embedding
and an independent structural embedding **agree** on which families ground —
so the result is attributable to the taxonomy, not the embedding. Failures
concentrate in heterogeneous ("wastebasket") families, which is the right
behavior. This is the OntoClean-style use case, with proved criteria. Trust it.

## Essentiality grades on real definitions — 🟡

`sigml obo cl|envo`. Grades OBO logical definitions `T = genus ∩ (R some F)` as
strict / functional / neither. Runs, is reproducible, and scales to hundreds of
definitions across two domains. **But the metric has known confounds** and the
numbers should not be treated as settled:
- Strict `RaiseProd` is near-unreachable *by construction* (the
  `functionals_disagree` theorem), so "0 strict" is the theorem, not data.
- The functional bar is near-random at scale (~83% of definitions are
  seed-noise, not a classification).
- The whole grade rests on the same commensuration machinery the two-scale
  probe showed to be unsound across incommensurable genus/differentia — so these
  numbers deserve the same case-by-case audit before being trusted.

## Two-scale Definition-Diamond probe — ⏳ (one sub-claim ❌ retracted)

`sigml twoscale`. Measures subsumption breadth vs relational depth.
- ✅ The two axes are genuinely independent when depth is normalized (corr ≈ 0)
  — the Definition Diamond holds empirically.
- ✅ Genera are reliably the wider concept (78–89%).
- ❌ **Retracted:** an earlier version concluded the essentialist depth-ordering
  "is not a property of real definitions." Inspecting the failing cases showed
  they are valid textbook definitions (*band form neutrophil = neutrophil with a
  banded nucleus*) and the depth proxy was at fault — it scores a terminal
  quality as shallow no matter how essential it is, and compares across
  incommensurable ontology branches.
- ⏳ **Open:** the significance/depth axis has resisted every operationalization
  tried (contrast-χ near-random; relational depth incommensurable). Essentiality
  is therefore **untested, not refuted.** A valid, commensurable depth measure —
  honoring the spec's own CCD requirement — is the main open problem.

## The through-line

The formalization's *structure* keeps getting vindicated by real data (two
independent scales; the necessity of a common denominator), while its
*normative* depth-ordering (`isEssential`) has no validated empirical correlate
yet. The usable, trustworthy tool today is the **grounding auditor**; the
essentiality work is a research thread, not a product.
