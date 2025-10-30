
/-
Developer Notes:

This file is guided by the following two questions:

1. How could we write a theorem like n-choose-k or stars and bars in Lean
2. How do we imagine students writing a good proof about n-choose-k, stars and bars, etc in Lean?

We have to keep in mind that CS22 is an introductory logic, discrete math, and probability course.
CS22 is not meant to requiring vast Lean knowledge, but rather Lean should be a learning tool.
Thus, these theorems/proofs/problems can't be too hard. They may also require us making new libraries
-/

----------------------------------------------------------------------------------------------------
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs

/-
  Now that we've spent some time using n-choose-k in written problems,
  let's explore how we can define the formula in Lean and then prove things
  about it. This exploration is meant to help you understand why the
  n-choose-k formula makes sense, and how we can use it.

  This Lean portion of the homework has three parts:
    1. Reviewing factorials
    2. Defining and proving properties about nCk
    3. ( Optional)Proving harder equalities, additional Lean exploration
-/




-------------------------
/- PART 1: Factorials -/
-------------------------

/- We can define our own factorial method-/
def fact : ℕ → ℕ
  | 0 => 1
  | (n + 1 ) => (n + 1) * fact n

/- We can test that it works, 5! = 120 -/
#eval fact 5

/-
   Exercise 1a: Prove that factorial is always positive
   Hints:
    1. Consider using the Lean tactic basic_induction for this proof.
    2. There is a tactic in Lean called "mul_pos". One can use it like
    so:
        Say we wish to prove a * b > 0. We could do so by proving:
          a > 0
          b > 0
        By using "apply mul_pos" on a * b > 0, Lean splits it into
        the two smaller goals above.
-/
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

/-
  Exercise 1b: Prove that fact (n + 1) = n + 1 * fact(n)
  Hint: if this seems "simple" or intuitive, your instinct is correct!
  We can prove this in one line. Think about how you would prove this
  on paper, then consider which Lean tactic corresponds to that.
-/
theorem fact_succ (n : ℕ) : fact (n + 1) = (n + 1) * fact n := by
    dsimp fact -- unfolding definition is enough







-------------------------
/- PART 2: Defining nCk -/
-------------------------

/- Recall, n choose k counts how many ways there are to choose
k items from n. We'll write it as nCk, and define it using
the factorial formula we've seen before:

       nCk = n! / (k! * (n - k)!)

Now we'll write this in Lean and check a few examples:
-/

def nCk (n k : ℕ) : ℕ :=
  if k ≤ n then fact n / (fact k * fact (n-k))
  else 0

#eval nCk 5 2 -- should be 10
#eval nCk 4 0 -- should be 1
#eval nCk 4 5 -- should be 0

/-
  Exercise 2a.
  Prove that n-choose-zero always results in 1.
  Logically, this makes sense beacuse there's only 1 way
  to choose 0 objects from n objects -- namely, by not choosing
  any objects. We want to formalize the logic using the definition
  of nCk here.
-/

theorem nCk_zero (n : ℕ): nCk n 0 = 1 := by
  dsimp nCk
  simp
  dsimp fact
  simp
  have hpos : 0 < fact n := fact_pos n
  rw [Nat.div_self hpos] -- new tactic

/-
Exercise 2b.
Prove that n-choose-n always results in 1.
Logically, this makese sense because there's only 1 way
to choosing all n items from n items -- namely, by choosing
all of them. We want to formalize the logic using the definition
  of nCk here.
-/
theorem nCk_self (n : ℕ) : nCk n n = 1 := by
  dsimp nCk
  simp
  dsimp fact
  simp
  have hpos : 0 < fact n := fact_pos n
  rw [Nat.div_self hpos] -- new tactic
/-
Exercise 2c.
Prove that "choosing k items" is the same as "leaving out n − k items"
That is, show the symmetry of nCk.
-/
theorem nCk_symm (n k : ℕ) (hk : k ≤ n) :
    nCk n k = nCk n (n - k) := by
  dsimp nCk
  simp
  split_ifs
  -- these are equal, need to learn Lean syntax


/-
  Note: the only thing we don't include now that we could
  is explictly proving why the n-choose-k formula is correct overall.
  However, we kind of do this with an induction-y vibe above:
    base case of n choose 0
    upper bound n choose n
    and symmtery proofs
  This, at least in my eyes, helps me see why the n-choose-k formula
  makes sense, which is the goal of this Lean exploration. These proofs
  are already moderately difficult, so I fear that a fully
  n-choose-k proof would be even more difficult.
-/

-------------------------
/- PART 3: Optional nCk Extensions -/
-------------------------

/-
  This is borrowed from existing Sprint 2025 HW8, could
  prove it here instead of in latex
  Prove that nCk 2n 2 = 2 ncK n 2 + n^2
-/
theorem nCk_two_element_subsets (n k : ℕ) :
    nCk (2*n) (2) = 2 * nCk n 2 + n^2 := by
  sorry

/-
(Optional, ChatGPT suggested this as possible extension)
Prove a lemma showing how nCk changes when we increase n.
Hint: try to express nCk (n+1) (k+1) in terms of nCk n k.
-/
theorem nCk_succ_simplify (n k : ℕ) (hk : k ≤ n) :
    nCk (n + 1) (k + 1) = (n + 1) * nCk n k / (k + 1) := by
  sorry










-- Below here is probably superfluous/too complicated from my last attemtp --


/- Here's a different way of defining n choose k
   using Pascal's recursion -/
def n_choose_k : ℕ → ℕ → ℕ
  | n, 0 => 1
  | 0, k+1 => 0
  | n+1, k+1 => n_choose_k n k + n_choose_k n (k+1)

#eval n_choose_k 5 2

theorem choose_pascal (n k : ℕ) :
    n_choose_k (n+1) (k+1) = n_choose_k n k + n_choose_k n (k+1) := by
    dsimp n_choose_k -- unfolding definition is enough


theorem choose_formula (hk : ∀ n: ℕ, ∀ k: ℕ, k ≤ n) :
    choose n k = fact n / (fact k * fact (n - k)) := by
    -- basic_induction
    sorry
    -- ok, this might be impossible haha


/-
If interested, Lean also has built in
n-choose-k definitions and factorial functions
-/
open Nat
#check Nat.choose
#check Nat.factorial
#check Nat.choose_eq_factorial_div_factorial
#eval Nat.choose 5 2


/- This is hard coded into mathlib, but where's the fun in that-/
theorem choose_factorial_formula (n k : ℕ) (hk : k ≤ n) :
    Nat.choose n k = n.factorial / (k.factorial * (n - k).factorial) := by
  exact Nat.choose_eq_factorial_div_factorial hk
