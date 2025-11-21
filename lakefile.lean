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
  -- for development focus, use the stars-and-bars library as the root so
  -- the rest of the (archival) files with unfinished proofs do not block
  -- quick builds. Change this later if you want the initial_work_archives
  -- to be included in the default target.
  roots := #[`LeanResearchExtendingProbability.lean_stars_and_bars.src.stars_and_bars_lib]
