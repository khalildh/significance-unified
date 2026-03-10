import Lake
open Lake DSL

package «significance-unified» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «SignificanceUnified» where
  srcDir := "SignificanceUnified"
  roots := #[`Basic, `Consequences, `CategoryTheory, `test]
