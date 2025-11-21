import ../src/StarsAndBars.lean

open StarsAndBars

/-
Problem: Positive integer solutions to x₁ + x₂ + x₃ + x₄ = 12
Shift: y_i = x_i - 1, sum = 12 - 4 = 8
-/

-- Step 1: counts
def counts := [2,1,3,2]  -- example numeric counts for shifted variables

-- Step 2: canonical form
def form := StarsAndBars.count_form.by_tuple counts 8

-- Step 3: proof using tactic
example : form = StarsAndBars.count_form.by_tuple counts 8 := by stars_and_bars

-- Step 4: numeric solution
#eval StarsAndBars.solve_from_counts counts    -- 165
#eval StarsAndBars.solve_from_counts_trace counts -- Stars/Bars info + 165
