# Significance as a Preorder — A Unified Formalization

A Lean 4 formalization (with Mathlib) that models significance as a preorder, unifying rhetorical amplification with Aristotelian essential definition.

## Core idea

A single integer scale `χ : α → ℤ` ("depth") induces **two** comparison primitives:

- **Raise** (level comparison): `χ a < χ b` — strict order, composes transitively
- **SimilarByContrast** (gap comparison): `|χ a - χ b| < |χ a - χ c|` — ternary, relative, does not compose

## What is formalized

1. `Raise`, `Gap`, `SimilarByContrast` on ℤ with basic properties
2. `Koncept` (predicate + characteristic), `CCD₃` axiom, `CCDWitness₃`
3. Kennedy's rhetorical `AmplificationMove`
4. `SignificanceRaise` — the abstract shared structure
5. Two total embeddings into `SignificanceRaise`
6. `AmplificationOver` round-trip through `KonceptDefWithUnit`
7. Unified significance theorem
8. Concrete examples (dogs/wolves/cats, "Man = Rational Animal")
9. Cicero's argument chain
10. Classical syllogisms (Barbara, Celarent, Darii) derived from `KonceptDef`

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
curl https://elan-init.lean-lang.org/ -sSf | sh
lake build
```

On first build, Mathlib will be fetched and compiled (this takes a while). To use pre-built Mathlib oleans:

```bash
lake exe cache get
lake build
```
