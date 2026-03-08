import Lake
open Lake DSL

package equivalenceTheorem where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib EquivalenceTheorem where
