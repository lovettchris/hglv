import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Init.Data.Nat.Basic

/-!
## Lists

Lean provides a rich library of functions on finite lists. In this section, we will review some of
them, and we will define some of our own; these are good exercises to familiarize ourselves with
functional programming in Lean.

In the first example, we show how to exploit injectivity of constructors. The
`cases` tactic can be used to apply injectivity on equations in which both sides
have the same constructor applied. In the proof below, the equation on which
injectivity is applied is `x :: xs = y :: ys`:

-/
lemma injection_example {α : Type} (x y : α) (xs ys : List α)
    (h : List.cons x xs = List.cons y ys) :
  x = y ∧ xs = ys := by
  cases h
  simp
/-!
As a result of the case distinction, `y` is replaced by `x` and `ys` is replaced by `xs`
throughout the goal, yielding the subgoal
```
h : x :: xs = x :: xs ⊢ x = x ∧ xs = xs
```
The `cases` tactic is also useful when the constructors are different, to detect
the impossible case:
-/
lemma distinctness_example {α : Type} (y : α) (ys : List α)
  (h : [] = y :: ys) :
  false :=
  by cases h
/-!
The first operation we define is a `map` function: a function that applies its
argument f—which is itself a function—to all elements stored in a container.
-/
def map {α β : Type} (f : α → β) : List α → List β
| [] => []
| (x :: xs) => f x :: map f xs

#eval map Nat.succ [1, 2, 3]  -- [2, 3, 4]
/-!
This could also be written using match on multiple parameters as follows:
-/
def map₂ {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, (x :: xs) => f x :: map₂ f xs
/-!
A basic property of map functions is that they have no effect if their argument
is the identity function (`λ x => x`, or `id`):
-/
lemma map_ident {α : Type} (xs : List α) :
    map (λ x => x) xs = xs := by
  induction' xs
  case nil => rfl
  case cons x xs ih =>
    simp [map, ih]
/-!
Another basic property is that successive maps can be compressed into a single map, whose argument
is the composition of the functions involved:
-/
lemma map_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    map g (map f xs) = map (λ x => g (f x)) xs := by
  induction' xs
  case nil => rfl
  case cons y ys ih =>
   simp [map, ih]
/-!
When introducing new operations, it is useful to show how these behave when
used in combination with other operations. Here is an example that proves
that `map` distributes over `append`:
-/
lemma map_append {α β : Type} (f : α → β) (xs ys : List α) :
    map f (xs ++ ys) = map f xs ++ map f ys := by
  induction' xs
  case nil => rfl
  case cons y ys ih =>
    simp [map, ih]
/-!
Remarkably, the last three proofs are textually identical. These are typical
`induction'–refl–simp` proofs.

The next list operation removes the first element of a list, returning the tail:
-/
def tail {α : Type} : List α → List α
| [] => []
| (_ :: xs) => xs

/-!
For an empty list `[]`, we simply return `[]` as its own tail.

The counterpart of tail is a function that extracts the first element of a list.
We already reviewed one solution in [Section 4.6](TypeClasses.lean.md).
Another possible definition uses an option wrapper:
-/
def head_opt {α : Type} : List α → Option α
| [] => Option.none
| (x :: _) => Option.some x

/-!
The type `Option α` is equipped with two constructors: `Option.none` and
`Option.some a`, where `a : α`. We use `Option.none` when we have no meaningful value
to return and `Option.some` otherwise. We can think of `Option.none` as the `null`
pointer of functional programming, but unlike `null` pointers (and `null` references),
the type system guards against unsafe dereferences. To obtain the value stored
in an option, we must use pattern matching. Schematically:
```lean
match head_opt xs with
| option.none => handle_the_error
| option.some x => do_something_with_value x
```
We cannot simply write `do_something_with_value (head_opt xs)`, because this would be
type-incorrect. The type system forces us to think about error handling. Using the power of
dependent types, another way to implement a partial function is to specify a precondition. The
callee must then pass a proof that the precondition is satisfied as argument:
-/
def head_le {α : Type} : ∀xs : List α, xs ≠ [] → α
| [], hxs => absurd rfl hxs
| (x :: _), _ => x

/-!
The `head_le` function takes two explicit arguments. The first argument, `xs`, is a
list. The second argument, `hxs`, is a proof of `xs ≠ []`. Since the type (`xs ≠ []`) of
the second argument depends on the first argument, we must use the dependent
type syntax `∀xs : list α`, rather than `List α` to name the first argument. The
result of the function is a value of type α; thanks to the precondition, there is no
need for an option wrapper.

The precondition `hxs` is used to rule out the case where `xs` is `[]`. In that case, `hxs` is a
proof of `[] ≠ []`, which is impossible. The absurd tactic derives the contradiction and exploits it
to derive an arbitrary α. From a contradiction, we can derive anything, even an inhabitant of α.

We can then invoke the function as follows using the `simp` tactic to prove that `[3, 1, 4] ≠ []`:
-/
#eval head_le [3, 1, 4] (by simp)   -- 3
/-!
Let us move on. Given two lists `[x₁, . . ., xₙ]` and `[y₁, . . ., yₙ]` of the same
length, the `zip` operation constructs a list of pairs `[(x₁, y₁), . . ., (xₙ, yₙ)]`:
-/
def zip {α β : Type} : List α → List β → List (α × β)
| (x :: xs), (y :: ys) => (x, y) :: zip xs ys
| [], _ => []
| (_ :: _), [] => []
/-!
Remember that `(α × β)` is the type of pairs of values of types `α` and `β` and `(a, b)`
is an instance of that pair where `a : α` and `b : β`.

The function is also defined if one list is shorter than the other. For example,
`zip [a, b, c] [x, y] = [(a, x), (b, y)]`. Notice that the recursion, with three cases,
deviates slightly from the structural recursion schema.

The length of a list is defined by recursion:
-/
def length {α : Type} : List α → ℕ
| [] => 0
| (_ :: xs) => length xs + 1
/-!
We can say something interesting about the length of `zip`’s result—namely, it is
the minimum of the lengths of the two input lists:
-/
lemma min_add_add (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l := by
  cases Classical.em (m ≤ n)
  case inl h =>
    simp [min] at h
  case inr h =>
    simp [min] at h

lemma length_zip {α β : Type} (xs : List α) (ys : List β) :
    length (zip xs ys) = min (length xs) (length ys) := by
induction' xs
case nil => rfl
case cons x xs' ih =>
  cases ys
  case nil => rfl
  case cons y ys' =>
    simp [zip, length, min_add_add] at ih ys'

-- BUGBUG still broken
/-!
The proof above teaches us yet another trick. The induction hypothesis is
```lean
ih : ∀{β} ys : List β, length (zip xs ys) = min (length xs) (length ys)
```
The syntax `∀{β}` is new but suggestive: It indicates that the type `β` is an implicit
argument of `ih`. In contrast, `ys` is explicit—and from it, `β` can be inferred.

The presence of ∀-quantifiers is explained as follows. The `induction’` tactic
automatically generalized the lemma statement so that the induction hypothesis
is not restricted to same fixed `β` and `ys` as the proof goal but can be used for
arbitrary values of `β` and `ys`. Such flexibility is rarely needed for types (e.g., `β`),
but here we need it for `ys`, because we want to instantiate the quantifier with `ys`’s
tail (called `ys'`) and not with `ys` itself.

The proof relies on a helper lemma `min_add_add` which shows the min function
distributes over addition.

Recall the definition `min a b = (if a ≤ b then a else b)`. To reason about `min`, we
often need to perform a `case` distinction on the condition `a ≤ b`. This is achieved
using `cases Classical.em (a ≤ b)`. This creates two subgoals: one with `a ≤ b` as
a hypothesis and one with `¬ a ≤ b`.

Here are two different ways to perform a case distinction on a proposition in
a structured proof:

-/
lemma min_add_add2 (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  match Classical.em (m ≤ n) with
  | Or.inl h => by simp [min, h]
  | Or.inr h => by simp [min, h]

lemma min_add_add3 (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  if h : m ≤ n then
    by simp [min, h]
  else
    by simp [min, h]
/-!
We see again that the mechanisms that are available to write functional programs,
such as `match` and `if–then–else`, are also available for writing structured proofs
(which are, after all, terms). We can now add a few rows to the table presented at
the end of Section 3.7:


| Tactical proofs | Structured proofs | Raw proof terms |
|-----------------|-------------------|-----------------|
| cases t         | match t with _    |  match t with _ |
| cases Classical.em Q | if Q then _ else _ | if Q then _ else _ |

We conclude with a distributivity law about `map` and `zip`, expressed using the
`Prod.fst` and `Prod.snd` selectors on pairs:

-/
lemma map_zip {α α' β β' : Type} (f : α → α') (g : β → β') :
  ∀xs ys, map (λab : α × β => (f (ab.1), g (ab.2))) (zip xs ys) =
    zip (map f xs) (map g ys)
  | (x :: xs), (y :: ys) => by simp [zip, map, map_zip]
  | [], _ => by rfl
  | (_ :: _), [] => by rfl
/-!
The patterns on the left correspond exactly to the patterns used in the definition of
zip. This is simpler than performing the induction on `xs` and the case distinction
on `ys` separately, as we did when we proved `length_zip`. Good proofs often follow
the structure of the definitions they are based on.

In the definition of `zip` and in the proof of `map_zip`, we were careful to specify
three non-overlapping patterns. It is also possible to write equations with overlapping patterns, as in
```lean
def f {α : Type} : List α → · · ·
| [] => . . .
| xs => . . . xs . . .
```
Since the patterns are applied sequentially, the above command defines the same
function as
```lean
def f2 {α : Type} : List α → · · ·
| [] => . . .
| (x :: xs) => . . . (x :: xs) . . .
```
We generally recommend the latter, more explicit style, because it leads to fewer
surprises, especially in proofs.
-/