import Mathlib.Tactic.Basic
import Mathlib.Init.Data.Nat.Basic
/-!
## Dependent Inductive Types

The inductive types `List α` and `BTree α` fall within the simply typed fragment of
Lean. Inductive types may also depend on (non-type) terms. A typical example is
the type of lists of length _n_, or _vectors_:
-/
inductive Vec (α : Type u) : ℕ → Type u where
  | nil : Vec α 0
  | cons {n} (head : α) (tail : Vec α n) : Vec α (n+1)
  deriving Repr

/-!
Thus, the term `Vec.cons 3 (Vec.cons 1 Vec.nil)` has type `Vec ℕ 2`. By encoding the vector length
in the type, we can provide more precise information about the result of functions. A function such
as `Vec.reverse`, which reverses a vector, would map a value `Vec α n` to another value of the same
type, with the same `n`. And `Vec.zip` could require its two arguments to have the same length.
Fixed-length vectors and matrices are also useful in mathematics.

Unfortunately, this more precise information comes at a cost. Dependent inductive types cause
difficulties when the terms they depend on are provably equal but not syntactically equal up to
computation (e.g., `m + n` vs. `n + m`). In this guide, we will generally avoid dependent inductive
types. They are briefly covered in this section for completeness. To put it unambiguously: This is
not exam material.

The definitions below introduce conversions between lists and vectors:
-/
def listOfVec {α : Type} : ∀{n : ℕ}, Vec α n → List α
| _, Vec.nil => []
| _, (Vec.cons a v) => a :: listOfVec v

def vecOfList {α : Type} :
∀xs : List α, Vec α (List.length xs)
| [] => Vec.nil
| (x :: xs) => Vec.cons x (vecOfList xs)

#eval vecOfList [1,2,3] -- Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))

#check vecOfList [1,2,3] -- Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))

#eval listOfVec (vecOfList [1,2,3]) -- Vec ℕ (List.length [1, 2, 3])

/-!
The `listOfVec` conversion takes a type `α`, a length `n`, and a vector of length `n` over `α` as
arguments and returns a list over `α`. Although we do not care about the length `n`, it still needs
to be an argument because it appears in the type of the third argument. The first two arguments are
implicit, which is reasonable since they can be inferred from the type of the third argument.

The `vecOfList` conversion takes a type `α` and a list over `α` as arguments and returns a vector of
the same length as the list. Lean’s type checker is strong enough to determine that the two
right-hand sides have the desired type.

By the [Curry–Howard correspondence](../ForwardProofs/CurryHoward.lean.md), proofs are analogous to
function definitions. Let us verify that converting a vector to a list preserves its length:
-/
lemma lengthListOfVec {α : Type} :
  ∀{n : ℕ} (v : Vec α n), List.length (listOfVec v) = n
| _, Vec.nil => by rfl
| _, Vec.cons a v =>
  by simp [listOfVec, lengthListOfVec v]
/-!
To prove a goal `v : Vec α n ⊢ P[v]` by structural induction on `v`, we might
naively think that it suffices to show the following two sub-goals:
```
⊢ P[Vec.nil]
m : N, a : α, u : Vec α m, ih : P[u] ⊢ P[Vec.cons a u]
```
This is naive because the sub-goals are not even type-correct: The hole in `P[ ]` has
type `Vec α n` (the type of its original dweller, `v`), so we cannot simply plug `Vec.nil`,
`u`, or `Vec.cons a u`—which have types `Vec α 0`, `Vec α m`, and `Vec α (m + 1)`—into
that hole. We must massage `P` each time, replacing `n` with `0`, `m`, or `m + 1`. Using the
notation `Pₜ[ ]` for the variant of `P[ ]` where all occurrences of `n` are replaced by
term `t`, we get
```
⊢ P₀[Vec.nil]
m : N, a : α, u : Vec α m, ih : Pₘ[u] ⊢ Pₘ₊₁[Vec.cons a u]
```
Proofs by case distinction using the `cases'` tactic are similar, but without the
induction hypothesis. Often, the length `n` will be not a variable but a complex
term. Then the replacement of `n` in `P[ ]` might not be intuitively meaningful. With
`cases'`, the corresponding sub-goal is silently eliminated. Thus, a case distinction
on a value of type `Vec α 0` will yield only one sub-goal, of the form `⊢ P[Vec.nil]`,
since `0` could never be equal to a term of the form `m + 1`.

Dependently typed pattern matching is subtle, because the type of the value
we match on may change according to the constructor. Given `v : Vec α n`, we might
be tempted to write

```lean
match v with
| Vec.nil => . . .
| Vec.cons a u => . . .
```
but this is just as naive as our first induction proof attempt above. Because the
term `n` in the type `Vec α n` may change depending on the constructor, we must
pattern-match on it as well:

```lean
match n, v with
| 0, Vec.nil => . . .
| m + 1, Vec.cons a u => . . .
```
-/
def vecHead (v : Vec α n) : Option α :=
match n, v with
| 0, Vec.nil => Option.none
| m + 1, Vec.cons a u => Option.some a

#eval vecHead (vecOfList [5,6,7]) -- some 5

set_option pp.explicit true
#print vecHead

def vecHeadₑ : {α : Type u_1} → {n : ℕ} → Vec α n → Option α :=
fun {α} {n} v =>
  match n, v with
  | 0, @Vec.nil α => @none α
  | Nat.succ m, @Vec.cons α .(m) a u => @some α a

/-!
Lean reports a bunch of unused variables in `vecHead` and so you can put
placeholders (`_`) there instead:
-/
def vecHead₂ (v : Vec α n) : Option α :=
match n, v with
| _, Vec.nil => Option.none
| _, Vec.cons a _ => Option.some a

/-!
It may seem paradoxical to pattern-match on `n` only to ignore the result, but without it Lean cannot
infer the second implicit argument to `Vec.cons`. In this respect, `cases'` is more user-friendly than
match.

--BUGBUG - is this still true in Lean 4?

Incidentally, Lean’s core libraries define a type of fixed-length vectors, called
`Vector α n`, as a subtype of `List α`:

-- BUGBUG - does it? I'm not finding it...
-/
def Vector (α : Type) (n : ℕ) :=
  { xs : List α // List.length xs = n }
/-!
In other words, the type `Vector α n` consists of the values `xs` of type `List α` such
that `xs` is of length `n`. This makes it possible to reuse Lean’s extensive list library.
Subtyping will be explained in Chapter 11.
-/
