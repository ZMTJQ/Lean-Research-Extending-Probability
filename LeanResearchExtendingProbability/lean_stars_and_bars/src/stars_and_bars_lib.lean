import Mathlib

namespace StarsAndBars

/-- Canonical stars-and-bars form: counts of each type, total stars n -/
structure count_form (counts : List Nat) (n : Nat) :=
  (sum_eq : counts.sum = n)

/-- Tactic placeholder: proves formula (stub for now) -/
macro "stars_and_bars" : tactic => `(tactic| skip)

/-- Compute numeric solution given count vector -/
def solve_from_counts (counts : List Nat) : Nat :=
  let n := counts.sum
  let k := counts.length
  Nat.choose (n + k - 1) (k - 1)

/-- Optional trace for teaching -/
def solve_from_counts_trace (counts : List Nat) : Nat :=
  let n := counts.sum
  let k := counts.length
  -- trace! "Stars (n): {n}, Bars (k-1): {k-1}"
  Nat.choose (n + k - 1) (k - 1)

/-- Create canonical count_form for numeric counts -/
def by_tuple (counts : List Nat) : count_form counts counts.sum :=
  { sum_eq := rfl }

/-- Create canonical count_form for symbolic counts with proof -/
def by_tuple_symbolic (counts : List Nat) (n : Nat) (h : counts.sum = n) : count_form counts n :=
{ sum_eq := h }

end StarsAndBars
