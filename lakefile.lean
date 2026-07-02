import Lake
open Lake DSL

package «lean-eureka» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_lib «Eureka» where
  srcDir := "."

lean_lib «EurekaMathlib» where
  srcDir := "."
