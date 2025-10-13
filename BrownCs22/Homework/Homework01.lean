import BrownCs22.Library.Tactics
import BrownCs22.Library.TruthTables
import AutograderLib

/-

# Welcome to the Lean section of HW1!

Some general guidelines, before we get started.

* When you're doing Lean homework assignments, including this one,
  do *not* edit any of the `import` statements above the
  opening comment. This will most likely break our autograder.

* Speaking of: you'll submit this file on Gradescope to the "tex and
  Lean" Homework 1 assignment. If you're not using LaTeX to write
  the rest of your assignment, you can ignore the "tex" part of that,
  and upload a PDF to the "PDF" Homework 1 assignment. Starting at
  Homework 3, you'll only be able to upload a .lean and a .tex file.

  In Codespaces, you can download this file by right clicking on its
  name in the "Explorer" tab to the left. (Click the "Files" icon at
  the top left if you don't see the "Explorer" tab.)

* Your goal in this assignment is to replace the `sorry`s in each
  part with completed proofs.

  For example, suppose the original problem looks like this:
-/

theorem example_1 (p : Prop) : p → p → p := by
  sorry
  done

/-

  Notice that, with the `sorry`, `example_1` is highlighted with a
  yellow warning. If you delete the `sorry`, a red error message
  appears at `done`: the proof is not complete!

  A solution is complete if it has no warnings and no error messages:

-/

theorem example_1' (p : Prop) : p → p → p := by
  assume hp1
  assume hp2
  assumption
  done




/-
Let's get started!
-/

variable (p q r s : Prop)

/-

## Problem 1

Fill in the `sorry` in the proof below.
The elimination and introduction rules we talked about in Lecture 4
will be very helpful here!


-/

@[autograded 3]
theorem problem_1 : (p ∧ q) ∧ (q ∧ r) → (p ∧ r) := by
  sorry
  done



/-

## Problem 2

Consider what the theorem below is saying!
"If the truth of `p` implies the truth of `q`,
 then it can't be the case that `p` is true and `q` is false."

Does that seem like a reasonable statement?
What do the truth tables of `p → q` and `¬ (p ∧ ¬ q)` look like?
(You do not need to write an answer, but think about it for a moment.
 Try the `#truth_table` command if you want.)


Again, your task is to fill in the `sorry` below to prove this statement.

-/


@[autograded 3]
theorem problem_2 : (p → q) → ¬ (p ∧ ¬ q) := by
  sorry
  done


/-
## Problem 3

This one's a little tricky! Let's reason through it in natural language.

We want to prove that, if we know `((p ∨ q) ∧ (p → r) ∧ (q → s))`,
then we know `r ∨ s`.
So suppose that we know `((p ∨ q) ∧ (p → r) ∧ (q → s))`.
Our goal is to show that `r ∨ s` follows.

From that long statement, we know three facts: `p ∨ q`, `p → r`, and `q → s`.
We'll reason by cases on `p ∨ q`.

First, if we know `p`, then we know `r`, because `p → r`.
And if we know `r` then we know `r ∨ s`.

Second, if we know `q`, then we know `s`, because `q → s`.
And if we know `s` then we know `r ∨ s`.

That completes our proof!

Your task: translate this argument to Lean.

-/

@[autograded 4]
theorem problem_3 : ((p ∨ q) ∧ (p → r) ∧ (q → s)) → (r ∨ s) := by
  sorry
  done
