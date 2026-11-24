import Lake
open Lake DSL

package firstClass where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib FirstClass where
