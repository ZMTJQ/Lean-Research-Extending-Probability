
/-
This file is guided by the following two questions:

1. How could we write a theorem like n-choose-k or stars and bars in Lean
2. How do we imagine students writing a good proof about n-choose-k, stars and bars, etc in Lean?

We have to keep in mind that CS22 is an introductory logic, discrete math, and probability course.
CS22 is not meant to requiring vast Lean knowledge, but rather Lean should be a learning tool.
Thus, these theorems/proofs/problems can't be too hard. They may also require us making new libraries
-/


import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs

open Nat

#check Nat.choose
#check Nat.factorial
#check Nat.choose_eq_factorial_div_factorial
#eval Nat.choose 5 2


/- This is hard coded into mathlib, but where's the fun in that-/
theorem choose_factorial_formula (n k : ℕ) (hk : k ≤ n) :
    Nat.choose n k = n.factorial / (k.factorial * (n - k).factorial) :=
  by
  exact Nat.choose_eq_factorial_div_factorial hk

/- We can define our own factorial method-/
def fact : ℕ → ℕ
  | 0 => 1
  | (n+1) => (n+1) * fact n

/- test that it works -/
#eval fact 10

/-
   proof that factorial is always positive
   I did by induction
-/
theorem fact_pos: ∀ n : ℕ, 0 < fact n := by
    basic_induction
    { dsimp fact
      numbers
    }
    {
      fix x
      assume h
      dsimp fact
      apply mul_pos -- this is a new tactic, not seen in CS22
      { linarith }
      { assumption }
    }

/- really simple proof, basically just definition of factorial -/
theorem fact_succ (n : ℕ) : fact (n + 1) = (n + 1) * fact n := by
    dsimp fact -- unfolding definition is enough

/- defines n choose k using Pascal's recursion-/
def n_choose_k : ℕ → ℕ → ℕ
  | n, 0 => 1
  | 0, k+1 => 0
  | n+1, k+1 => n_choose_k n k + n_choose_k n (k+1)

#eval n_choose_k 5 2

theorem choose_pascal (n k : ℕ) :
    n_choose_k (n+1) (k+1) = n_choose_k n k + n_choose_k n (k+1) := by
    dsimp n_choose_k -- unfolding definition is enough


theorem choose_formula (hk : ∀ n: ℕ, ∀ k: ℕ, k ≤ n) :
    choose n k = fact n / (fact k * fact (n - k)) := by
    -- basic_induction
    sorry
    -- ok, this might be impossible haha
