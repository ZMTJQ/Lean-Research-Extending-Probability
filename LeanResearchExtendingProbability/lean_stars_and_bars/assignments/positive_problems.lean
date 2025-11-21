import LeanResearchExtendingProbability.lean_stars_and_bars.src.stars_and_bars_lib

open StarsAndBars

/-
  Assignment: Positive-integer solutions practice (≈10–20 minutes)

  Task: For each problem below, do the small reduction to a stars-and-bars
  `counts : List Nat` and then compute the numeric answer using
  `StarsAndBars.solve_from_counts counts` (or `#eval StarsAndBars.stars_and_bars_count`).

  Steps for each problem (explicit):
  1. Identify k (number of types/bins) and n (total stars or adjusted total).
  2. Provide a concrete `counts : List Nat` of length k whose sum is n.
  3. Use `def form := StarsAndBars.by_tuple counts` to wrap it.
  4. Show `form = StarsAndBars.by_tuple counts` (this is definitional while
	  the automation is being developed), and `#eval` the numeric answer.
-/

/- Problem: Positive integer solutions to x₁ + x₂ + x₃ + x₄ = 12
	Hint: set y_i = x_i - 1, so y1 + y2 + y3 + y4 = 8. Here k = 4 and n = 8.
-/

-- Step 1: supply a counts list for the nonnegative variables y_i that sums to 8
def counts : List Nat := [2,1,3,2]

-- Step 2: canonical form (constructor picks up the sum automatically)
def form := StarsAndBars.by_tuple counts

-- Step 3: trivial equality (constructor is definitional) -- tactic TODO
example : form = StarsAndBars.by_tuple counts := rfl

-- Step 4: numeric solution (what students should compute / check)
#eval StarsAndBars.solve_from_counts counts    -- 165
#eval StarsAndBars.solve_from_counts_trace counts -- Stars/Bars info + 165

/- Next exercise: change the counts above to a different valid decomposition
  (still summing to 8) and verify the numeric answer stays the same using
  `StarsAndBars.solve_from_counts`.
-/
