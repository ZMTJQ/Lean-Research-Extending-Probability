import StarsAndBars
-- I hate lean why do imports never ever ever ever ever ever ever ever work
open StarsAndBars

/-
Problem: Number of multisets of size 4 from 3 types of items
-/

-- Step 1: counts
def counts := [2,1,1]   -- numeric example

-- Step 2: canonical form
def form := StarsAndBars.count_form.by_tuple counts 4

-- Step 3: proof using tactic
example : form = StarsAndBars.count_form.by_tuple counts 4 := by stars_and_bars

-- Step 4: numeric solution
#eval StarsAndBars.solve_from_counts counts    -- 15
#eval StarsAndBars.solve_from_counts_trace counts -- Stars/Bars info + 15
