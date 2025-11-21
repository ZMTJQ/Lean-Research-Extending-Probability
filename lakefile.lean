import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.4.0"

package «LeanResearchExtendingProbability» where
  -- Add any package configuration options here if needed


lean_lib BrownCs22 {
  -- add library configuration options here
  roots := #[`BrownCs22]
  globs := #[Glob.submodules `BrownCs22]
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.unusedVariables, false⟩]
}

@[default_target]
lean_lib «LeanResearchExtendingProbability» where
  roots := #[`LeanResearchExtendingProbability.n_choose_k]
