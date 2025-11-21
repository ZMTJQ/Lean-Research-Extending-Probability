import LeanResearchExtendingProbability.lean_stars_and_bars.src.stars_and_bars_lib

open StarsAndBars

/- Example worked problem (this file is a short, fully worked example
	that students can read through before attempting the exercises.) -/

/- Problem: Roll 3 six-sided dice and ask for the probability the result
	is a non-decreasing sequence (e.g., (1,1,5)). -/

-- Step A: Identify k and n
/- There are k = 6 faces and n = 3 rolls (stars). -/

/- Step B: explain reduction: non-decreasing sequences correspond to
	multisets of size 3 from the 6 faces, so count is C(n + k - 1, k - 1).
-/
-- Step C: Provide one counts vector corresponding to the multiset {1,1,5}
def counts_example : List Nat := [2,0,0,0,1,0]

-- Step D: verify the sum and compute the numeric answer
example : counts_example.sum = 3 := by rfl
#eval StarsAndBars.solve_from_counts counts_example -- shows 56 when evaluated on any valid counts

/- Instructor note: students should try to produce `counts_example` on their
	own for a few samples and then use `#eval` to check the numeric counts.
