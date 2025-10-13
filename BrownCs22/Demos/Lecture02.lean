import BrownCs22.Library.Defs

namespace Demo1
open BrownCs22.Nat

/-

# Welcome to Lean!

We'll get a more detailed introduction later.
For now, meet our new friend, the `#check` command.

`#check <expression>` tells us what "kind of thing" `<expression>` is.

-/

#check 1 + 4

#check 5

/-

Read `1 : ℕ` as saying, "`1` is a natural number."

-/

#check 2 + 3 = 5

#check 1 + 1 = 3

/-

How could I translate
  "every action has an equal but opposite reaction"?

...

-/




/-

We can write things with quantifiers (`∀` and `∃`):

-/

--
#check ∃ n : ℕ, n^2 % 10 = 6

#check ∀ n : ℕ, Prime (n^2 + n + 41)


/-

`Prime` is a *predicate*.
So is `isOdd`.
-/

#check isOdd

#check isOdd 5

#check isOdd 10


/-
How do I write "the sum of any two odd numbers is even"?
-/

#check ∀ x : ℕ, ∀ y : ℕ, isOdd x ∧ isOdd y → isEven (x + y)


def PerfectSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, n = k * k       -- `n` is a perfect square


#check PerfectSquare 22

#check ∀ n : ℕ, PerfectSquare n

#check ∃ n : ℕ, PerfectSquare n


-- ignore this line for now!
variable (n : ℕ)




#check PerfectSquare (n + 1)



-- It doesn't make sense for us to ask about PerfectSquare (n) + 1

-- #check PerfectSquare (n) + 1




end Demo1
