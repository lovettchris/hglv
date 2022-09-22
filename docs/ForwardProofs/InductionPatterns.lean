import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases

/-!
## Induction by Pattern Matching

In [Proofs by Mathematical Induction](../BackwardProofs/Induction.lean.md), we reviewed the use of
the induction’ tactic to perform proofs by induction. An alternative, more flexible style relies on
pattern matching and the Curry–Howard correspondence.

Recall the definition of the reverse of a list from [Function Definitions](../Basics/FunctionDefinitions.lean.md):

-/
def reverse {α : Type} : List α → List α
| [] => []
| (x :: xs) => reverse xs ++ [x]

/-!
In fact, `reverse` exists in Lean’s standard library, as `List.reverse`, but our definition is
optimized for reasoning. A useful property to prove is that `reverse` is its own inverse: `reverse
(reverse xs) = xs` for all lists `xs`. However, if we try to prove it by induction, we quickly run
into an obstacle. The induction step is
```lean
ih : ∀xs, reverse (reverse xs) = xs ⊢ reverse (reverse xs ++ [x]) = x :: xs
```
What is unpleasant about this subgoal is the presence of `++ [x]` inside the double
`reverse` sandwich. We need a way to “distribute” the outer `reverse` over `++` to
obtain a term that matches the induction hypothesis’s left-hand side. The trick is
to prove and use the following lemma:
-/
lemma reverse_append {α : Type} :
  ∀ xs ys : List α, reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [], ys => by simp [reverse]
  | (x :: xs), ys => by simp [reverse, reverse_append xs, List.append_assoc]

/-!
In the proof of the lemma, the patterns on the left, `[]` and `x :: xs`, correspond to
the two constructors of the ∀-quantified variable `xs :: List α`. On the right-hand
side of each `=>` symbol is a proof for the corresponding case.

Inside the induction step’s proof, the induction hypothesis is available under
the same name as the lemma we are proving (`reverse_append`). We explicitly
pass `xs` as argument to the induction hypothesis. This is useful as documentation,
and it also prevents Lean from accidentally invoking the induction hypothesis in
a circular fashion on `x :: xs`. Lean’s termination checker would notice that the
argument is ill-founded and raise an error.

For reference, the corresponding tactical proof is as follows:
-/
lemma reverse_append₂ {α : Type} (xs ys : List α) :
  reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  induction' xs
  case nil => simp [reverse]
  case cons x xs ih => simp [reverse, ih, List.append_assoc]
/-!
which can also be written
-/

lemma reverse_append₃ (as bs : List α) :
  (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih => simp [ih, List.append_assoc]

/-!
The lemma would also be provable, and useful, if we put `[y]` instead of `ys`. But it is a good
habit to state lemmas as generally as possible. This results in more reusable libraries. Moreover,
this is often necessary to obtain a strong enough induction hypothesis in a proof by induction. In
general, finding the right inductions and lemmas can be diffcult, requiring thought and creativity.

Simultaneous pattern matching on multiple variables is supported (e.g., `xs` and `ys` above). The
patterns are then separated by spaces. This explains why Lean requires us to put parentheses around
complex patterns, even when we match on a single variable. The general format is

```lean
lemma name (params₁ : type1₁) . . . (paramsₘ : typeₘ) :
statement
| patterns₁ := proof₁
.
.
.
| patternsₙ := proofₙ
```
Notice the strong similarity with the syntax of `def` (Section 1.3). The two commands are, in fact,
almost the same, the main exception being that `lemma` considers the defined term or the proof opaque,
whereas `def` keeps it transparent. Since the actual proofs are irrelevant once a lemma is proven
(Section 11), there is no need to expand them later. A similar distinction exists between `let` and
`have`.

By the Curry–Howard correspondence, a proof by induction by pattern matching is the same as a
recursive proof term. When we invoke the induction hypothesis, we are really just invoking a
recursive function recursively. This explains why the induction hypothesis has the same name as the
lemma we prove. Lean’s termination checker is used to establish well-foundedness of the proof by
induction.

With the reverse_append lemma in place, we can return to our initial goal:
-/
lemma reverse_reverse {α : Type} :
  ∀ xs : List α, reverse (reverse xs) = xs
  | [] => by rfl
  | (x :: xs) =>
  by simp [reverse, reverse_append, reverse_reverse xs]

/-!
Induction by pattern matching is highly popular among Lean users. Its main advantages are its
convenient syntax and its support for well-founded induction and not only structural induction, as
provided by the [induction’ tactic](../BackwardProofs/InductionTactic.lean.md). However, in this
guide, we will not need the full power of well-founded induction. Furthermore, for subtle logical
reasons, induction by pattern matching is not available for inductive predicates, which are the
topic of Chapter 5.

--BUGBUG: is this still true in lean4?
-/

