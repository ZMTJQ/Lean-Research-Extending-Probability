/-
  In this file, we’ll explore the *Stars and Bars* theorem —
  a useful formula in combinatorics that counts the number of ways
  to distribute identical objects into boxes.

  Just like we defined and proved things about n-choose-k in the last
  assignment, we’ll now connect that formula to a new counting problem.

  This file is meant to help solidify your understanding of both
  how to *use* the stars-and-bars formula and *why* it makes sense.
-/
----------------------------------------------------------------------------------------------------
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
-- import LeanResearchExtendingProbability.n_choose_k

/- Import didn't work, pasting functions from n_choose_k.lean directly here-/

def fact : ℕ → ℕ
  | 0 => 1
  | (n + 1 ) => (n + 1) * fact n

theorem fact_pos: ∀ n : ℕ, 0 < fact n := by
    basic_induction
    { dsimp fact
      numbers
    }
    {
      fix x
      assume h
      dsimp fact
      apply mul_pos -- this is a new tactic, not previously seen in CS22
      { linarith }
      { assumption }
    }

def nCk (n k : ℕ) : ℕ :=
  if k ≤ n then fact n / (fact k * fact (n-k))
  else 0

/-
  Stars and Bars Motivation:

  Suppose we want to find the number of nonnegative integer solutions to:

      x₁ + x₂ + ⋯ + xₖ = n

  How might we solve this? For small examples like if n = 3, k = 2, then we can
  count the possible solutions without doing much work. They are:
        (0,3), (1,2), (2,1), (3,0)
  so there are 4 solutions.

  But in general, here is the intuition for this problem:
    - Each solution can be represented as n "stars" (*) and k-1 "bars" (|),
      which divide the stars into k groups.
    - The total number of symbols is n + k - 1.
    - Choosing where the bars go determines the solution completely.

  So we can think of this problem as "choosing k−1 positions for bars" out of
  n+k−1 total slots.
-/
-- What we want out of stars and bars? Not to prove
-- why the formula works, but instead apply it as a tactic
-- for other problems

-- Task 1: Using this intuition and nCk from the last assignment, define stars_and_bars below.
def stars_and_bars (n k : ℕ) : ℕ :=
  nCk (n + k - 1) (k - 1)   -- I did it here:

#eval stars_and_bars 3 2  -- expect 4: (3,0),(2,1),(1,2),(0,3) from above

/-
Note:
  - `stars_and_bars n k` uses `n + k - 1` and `k - 1`. With `k = 0` the
    `k - 1` and `n + k - 1` are handled by nat subtraction saturating at 0.
-/

/-
Task 2:
Prove there is exactly 1 way to distribute n stars into 1 box:
             all n go into the single box.

Hint: unfold `stars_and_bars`, `nCk`, and simplify the `k = 1` arithmetic
      (you will see `nCk n 0`).
-/
theorem stars_and_bars_one_box (n : ℕ) :
    stars_and_bars n 1 = 1 := by
  dsimp stars_and_bars
  simp -- if we proved nCk_zero, we're done. Can we use theorems in proofs?
  dsimp nCk
  simp
  dsimp fact
  simp
  have hpos : 0 < fact n := fact_pos n
  rw [Nat.div_self hpos]

/-
Task 3:
Prove that if there are zero stars, there is exactly 1 way to distribute them:
every box receives 0 stars.

Formally: for any k, stars_and_bars 0 k = 1.
(Hint: when `n = 0` the formula becomes `nCk (k - 1) (k - 1)` which is 1.)
-/
theorem stars_and_bars_no_stars (k : ℕ) :
    stars_and_bars 0 k = 1 := by
  dsimp stars_and_bars
  simp
  dsimp nCk
  simp
  dsimp fact
  simp
  have hpos : 0 < fact (k-1) := fact_pos (k-1)
  rw [Nat.div_self hpos]

/-
Task 4:
If there are zero boxes but n > 0 stars, there are 0 ways to distribute.
Formally: for n > 0, stars_and_bars n 0 = 0.

-/
theorem stars_and_bars_no_boxes (n : ℕ) :
    stars_and_bars n 0 = 0 := by
  dsimp [stars_and_bars, nCk]
  simp
  dsimp fact
  simp
  -- this is wrong
  sorry


/-
-------------------------------------------
 PART 2 — Proving stars and bars? Algebraic explanation (derivation)?
------------------------------------------- -/
