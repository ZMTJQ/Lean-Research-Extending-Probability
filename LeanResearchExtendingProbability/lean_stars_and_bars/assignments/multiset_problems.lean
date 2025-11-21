import LeanResearchExtendingProbability.lean_stars_and_bars.src.stars_and_bars_lib
open StarsAndBars

/-
Problem: Number of multisets of size 4 from 3 types of items
-/
-- Step 1: counts
-- Problem: Number of multisets of size 4 from 3 types of items

/- Here k = 3 types and n = 4 total items. A student should supply a
	`counts : List Nat` of length 3 summing to 4 and then compute the
	numeric answer with `solve_from_counts`.
-/

-- Step 1: counts (replace or keep example) - must sum to 4 and have length 3
def counts : List Nat := [2,1,1]   -- TODO: change this to another valid decomposition

-- Step 2: canonical form
-- Step 2: canonical form (constructor picks up the sum automatically)
def form := StarsAndBars.by_tuple counts

-- Step 3: trivial equality (constructor is definitional) -- tactic TODO
example : form = StarsAndBars.by_tuple counts := rfl

-- Step 4: numeric solution
#eval StarsAndBars.solve_from_counts counts    -- 15
#eval StarsAndBars.solve_from_counts_trace counts -- Stars/Bars info + 15
