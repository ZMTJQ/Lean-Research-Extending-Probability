import ../src/StarsAndBars.lean

open StarsAndBars

/-
Problem: Non-decreasing sequences of length 3 from dice {1..6}
-/

-- Step 1: counts
def counts := [1,1,0,0,1,0]  -- numeric example

-- Step 2: canonical form
def form := StarsAndBars.count_form.by_tuple counts 3

-- Step 3: proof using tactic
example : form = StarsAndBars.count_form.by_tuple counts 3 := by stars_and_bars

-- Step 4: numeric solution
#eval StarsAndBars.solve_from_counts counts    -- 56
#eval StarsAndBars.solve_from_counts_trace counts -- Stars/Bars info + 56
