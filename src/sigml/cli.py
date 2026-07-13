"""sigml — audit learned taxonomies against a Lean-verified concept spec.

One entry point over the pieces that grew out of this project. Each subcommand
maps to an experiment module; the help text marks how much to trust each one.

    sigml wordnet                 grounding audit on a WordNet subtree   [validated]
    sigml obo [cl|envo]           essentiality grades on an OBO ontology [provisional]
    sigml twoscale [cl|envo|all]  the two-scale Definition-Diamond probe [diagnostic]

"validated" — the check does what it claims and was cross-checked against an
   independent signal (WordNet grounding: trained vs structural positions agree).
"provisional" — runs and is reproducible, but the metric has known confounds
   (see FINDINGS.md); do not treat the numbers as settled.
"diagnostic" — a probe for understanding structure, not a pass/fail auditor.

Every subcommand that can emit a Lean certificate does so only for structures
that pass; `lake build` then kernel-checks the emitted file, so the Lean kernel
(not this Python) is the final arbiter of any certified claim.
"""

from __future__ import annotations

import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        prog="sigml",
        description="Audit learned taxonomies against a Lean-verified concept spec.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    sub = p.add_subparsers(dest="cmd")

    sub.add_parser(
        "wordnet",
        help="[validated] CCD3 grounding audit on a WordNet Carnivora subtree",
    )
    po = sub.add_parser(
        "obo",
        help="[provisional] essentiality grades on an OBO ontology",
    )
    po.add_argument("ontology", nargs="?", default="cl",
                    help="cl | envo | all (default: cl)")
    pt = sub.add_parser(
        "twoscale",
        help="[diagnostic] two independent scales (the Definition Diamond)",
    )
    pt.add_argument("ontology", nargs="?", default="all",
                    help="cl | envo | all (default: all)")
    sub.add_parser(
        "validate",
        help="[foundation] regenerate the Python≡Lean differential check "
             "(then `lake build`)",
    )
    pr = sub.add_parser(
        "repr",
        help="[diagnostic] measure how faithfully the embedding learns the "
             "hierarchy",
    )
    pr.add_argument("ontology", nargs="?", default="all",
                    help="cl | envo | all (default: all)")
    pa = sub.add_parser(
        "audit-strict",
        help="[diagnostic] case-audit the strict-essentiality survivors "
             "(global embedding)",
    )
    pa.add_argument("ontology", nargs="?", default="cl",
                    help="cl | envo (default: cl)")

    args = p.parse_args(argv)
    if not args.cmd:
        p.print_help()
        return 1

    if args.cmd == "wordnet":
        import wordnet_slice
        wordnet_slice.main()
    elif args.cmd == "obo":
        import obo_slice
        if args.ontology == "all":
            for name in obo_slice.CONFIGS:
                obo_slice.main(name)
        else:
            obo_slice.main(args.ontology)
    elif args.cmd == "twoscale":
        import essence_twoscale
        sys.argv = ["essence_twoscale", args.ontology]
        essence_twoscale.main()
    elif args.cmd == "validate":
        import validate
        validate.main()
    elif args.cmd == "repr":
        import repr_quality
        sys.argv = ["repr_quality", args.ontology]
        repr_quality.main()
    elif args.cmd == "audit-strict":
        import audit_strict
        sys.argv = ["audit_strict", args.ontology]
        audit_strict.main()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
