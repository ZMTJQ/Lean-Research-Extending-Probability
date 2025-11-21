import LeanResearchExtendingProbability.lean_stars_and_bars.src.stars_and_bars_lib

open StarsAndBars

/-
Problem: Non-decreasing sequences of length 3 from dice {1..6}
-/
-- Step 1: counts
-- Problem: Non-decreasing sequences of length 3 from dice {1..6}

/- This problem is a classic stars-and-bars example: a non-decreasing
	sequence of length 3 from {1..6} is determined by the counts of each
	face. There are k = 6 types and n = 3 total items.
-/
-- Step 1: counts (fill this in so `counts.sum = 3` and `counts.length = 6`)
def counts : List Nat := [1,1,0,0,1,0]  -- TODO: replace with your own decomposition

-- Step 2: canonical form (constructor picks up the sum automatically)
def form := StarsAndBars.by_tuple counts

-- Step 3: trivial equality (constructor is definitional) -- tactic TODO
example : form = StarsAndBars.by_tuple counts := rfl

-- Step 4: numeric solution
#eval StarsAndBars.solve_from_counts counts    -- 56
#eval StarsAndBars.solve_from_counts_trace counts -- Stars/Bars info + 56
