import Mathlib

/-
  A small, course-local stars-and-bars library with student-friendly helpers.
  This file intentionally keeps representations simple: students work with
  `List Nat` (a length-k list of counts) and use the helpers below. The
  internal counting formula is the usual binomial coefficient
  C(n + k - 1, k - 1).
-/

namespace StarsAndBars

/- Canonical stars-and-bars form: counts of each type, total stars n -/
structure count_form (counts : List Nat) (n : Nat) :=
  (sum_eq : counts.sum = n)

/- Tactic placeholder: proves formula (stub for now) -/
macro "stars_and_bars" : tactic => `(tactic| skip)

/- Numeric helpers -/
/-- Compute the stars-and-bars numeric answer for nonnegative counts.
    Given n stars and k bins, returns C(n + k - 1, k - 1). -/
def stars_and_bars_count (n k : Nat) : Nat :=
  Nat.choose (n + k - 1) (k - 1)

/-- Variant for the strictly-positive case (each xi ≥ 1).
    Counting positive integer solutions to x1+...+xk = n is equivalent to
    counting nonnegative solutions y1+...+yk = n - k, so C(n - 1, k - 1).
    The function does not check n ≥ k; callers should do that when needed. -/
def stars_and_bars_count_pos (n k : Nat) : Nat :=
  if h : n >= k then Nat.choose (n - 1) (k - 1) else 0

/-- Compute numeric solution given a concrete count vector. -/
def solve_from_counts (counts : List Nat) : Nat :=
  let n := counts.sum
  let k := counts.length
  stars_and_bars_count n k

/-- Optional trace for teaching: same as `solve_from_counts` but left here
    so instructors can temporarily enable messaging while developing. -/
def solve_from_counts_trace (counts : List Nat) : Nat :=
  let n := counts.sum
  let k := counts.length
  -- trace! "Stars (n): {n}, Bars (k-1): {k-1}"
  stars_and_bars_count n k

/- Small constructors helpers -/
/-- Create canonical `count_form` for a concrete list of counts. -/
def by_tuple (counts : List Nat) : count_form counts counts.sum :=
  { sum_eq := rfl }

/-- Create canonical `count_form` for symbolic counts with an explicit proof. -/
def by_tuple_symbolic (counts : List Nat) (n : Nat) (h : counts.sum = n) : count_form counts n :=
  { sum_eq := h }

/- Relate the concrete solver with the closed-form numeric helper. This is
   a trivial definitional equality in our setup (both use the same choose
   expression), but it is helpful as a documented contract for students and
   for tactics that rewrite between the two. -/
theorem solve_from_counts_eq (counts : List Nat) :
  solve_from_counts counts = stars_and_bars_count counts.sum counts.length :=
by rfl

end StarsAndBars
