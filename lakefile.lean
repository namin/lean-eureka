import Lake
open Lake DSL

package «lean-eureka» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «Eureka» where
  srcDir := "."
