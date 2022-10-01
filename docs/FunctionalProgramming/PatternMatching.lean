import Mathlib.Init.Data.Nat.Basic
/-!
## Pattern Matching Expressions

Pattern matching is possible not only at the top level of a `def` command but also
deeply within terms, via a `match` expression. The construct has the following general syntax:

```lean
match term₁, . . ., termm with
| pattern₁₁, . . ., pattern₁ₘ => result₁
.
.
.
| patternn₁, . . ., patternₙₘ => resultₙ
```

The patterns may contain variables, constructors, and nameless
placeholders (_). The `resultᵢ` expressions may refer to the variables introduced
in the corresponding patterns.

The following function definition demonstrates the syntax of pattern matching
within expressions:
-/
def bcount {α : Type} (p : α → Bool) : List α → ℕ
| [] => 0
| (x :: xs) =>
  match p x with
  | true => (bcount p xs) + 1
  | false => bcount p xs

#eval bcount (λ x : Nat => x >= 5) (List.range 10) -- 5

/-!
The `bcount` function counts the number of elements in a list that satisfy the given
predicate `p`. The predicate’s codomain is `Bool`. As a general rule, we will use type
`Bool`, of Booleans, within programs and use the type `Prop`, of propositions, when
stating properties of programs.

Here's an example that shows how to match on two variables:
-/
def extract  {α : Type} : List α → ℕ → List α
  | _, 0 => []
  | [], _ => []
  | (x :: xs), i + 1 => x :: (extract xs i)

#eval extract (List.range 10) 3  -- [0, 1, 2]

/-!

Notice that the variables are extracted in order from the return type.
This example also shows how to use an induction technique matching `i + 1` so that
the count is decremented by one on each recursive call.

You can write this with full match expression if you prefer to name the arguments for
documentation reasons:
-/
def extract₂ {α : Type} (xs : List α) (count : ℕ) : List α :=
  match xs, count with
    | _, 0 => []
    | [], _ => []
    | (x :: xs), i + 1 => x :: (extract xs i)
/-!
The connectives are called `or` (infix: `||`), `and` (infix: `&&`), and `not` (`¬`) or (`!`).

BUGBUG: the book also adds `xor` but I couldn't find that in Lean, I only found HXor.hXor?

The following diagram shows the interpretations of `bool` and `Prop`:

![diagram](diagram.svg)

Dots represents elements, circles represents types, and the group represents
a type of types. We see that `bool` are interpreted as a set with two values, whereas
`Prop` consists in an infinite number of propositions (the types), each of which has
zero or more proofs (the elements). We will refine this picture in Chapter 5.

We cannot match on a proposition of type `Prop`, but we can use `if–then–else`
instead. For example, the `min` operator on natural numbers operator can be defined as follows:

-/
def minimum (a b : ℕ) : ℕ :=
  if a ≤ b then a else b

#eval minimum 5 9   -- 5

/-!
This works only for propositions that are decidable (i.e., executable). This is the
case for `≤`: Given concrete values for the arguments, such as `35` and `49`, Lean can
reduce `35 ≤ 49` to true. Lean keeps track of decidability using a mechanism called
type classes, which will be explained below.
-/