import Mathlib.Tactic.Basic
import Mathlib.Init.Data.Nat.Basic
/-!
## Dependent Types

Dependent types are the defining feature of the _dependent type theory_ family of
logics. Although you may not be familiar with the terminology, you are likely to
be familiar with the concept in some form or other.

Consider a function `pick` that takes a natural number `n` (i.e, a value from
`ℕ = {0, 1, 2, . . .}`) and that returns a natural number between `0` and `n`.
Intuitively, `pick n` should have the type `{0, 1, . . ., n}` (i.e., the type consisting
of all natural numbers `i ≤ n`). In Lean, this is written `{i : N // i ≤ n}`.
This would be the type of `pick n`. Mathematically inclined readers might want to
think of `pick` as an ℕ-indexed family of terms
```
(pick n : {i : ℕ // i ≤ n})ₙ
```
--BUGBUG : markdown won't let me subscript `n:ℕ` like the book has.

in which the type of each term depends on the index—e.g.,
`pick 5 : {i : ℕ // i ≤ 5}`. But what would be the type of `pick` itself? We would like to express that
`pick` is a function that takes an argument `n : ℕ` and that returns a value of type
`{i : ℕ // i ≤ n}`. To capture this, we can write
-/
def pick : (n : ℕ) → {i : ℕ // i ≤ n} :=
  sorry
/-!
This is a dependent type: The type of the result depends on the value of the
argument `n`. The variable name `n` is immaterial.

Unless otherwise specified, a _dependent type_ means a type depending on a (non-type) term, as above,
with `n : ℕ` as the term and `{i : ℕ // i ≤ n}` as the type that depends on it. This is what we mean
when we claim that simple type theory does not support dependent types. But a type may also depend
on another type— for example, the type constructor `List`, its η-expanded variant `λ α : Type => List α`,
or the polymorphic type `λ α : Type => α → α` of functions with the same domain and codomain. A term may
depend on a type—for example, the polymorphic identity function `λ α : Type => λ x : α => x`. And of course,
a term may also depend on a term— for example, `λ n : ℕ => n + 2`. In summary, there are four cases for
`λ x => t`:

| Body (t)  |                 | Argument (x) | Description                         |
|-----------|-----------------|--------------|-------------------------------------|
| A term    | depending on    | a term       |Simply typed λ-expression            |
| A type    | depending on    | a term       |Dependent type (in the narrow sense) |
| A term    | depending on    | a type       |Polymorphic term                     |
| A type    | depending on    | a type       |Type constructor                     |

The last three rows correspond to the three axes of [Henk Barendregt’s λ-cube](https://en.wikipedia.org/wiki/Lambda_cube).

The APP and LAM rules presented in [Type Checking and Type Inference](TypesAndTerms.lean.md#type-checking-and-type-inference)
must be generalized to work with dependent types:

\\( \cfrac{C ⊢ t : (x : σ) → τ[x] \quad C ⊢ u : σ }{C ⊢ t\enspace{u} : τ[u]} {\large{A}}{\normalsize{PP'}} \\)

\\( \cfrac{C, x : σ ⊢ t : τ[x] }{C ⊢ (λ\enspace{x} : σ => t) : (x : σ) → τ[x]} {\large{L}}{\normalsize{AM'}} \\)

The notation `τ[x]` stands for a type that may contain `x`, and `τ[u]` stands for the
same type where all occurrences of `x` have been replaced by `u`.

The simply typed case arises when `x` does not occur in `τ[x]`. Then, we can
simply write `σ →` instead of `(x : σ) →`. The familiar notation `σ → τ` is equivalent
to `(_ : σ) → τ`. It is easy to check that APP' and LAM' coincide with APP and LAM
when `x` does not occur in `τ[x]`. The example below demonstrates APP':


\\( \cfrac{pick : (n : ℕ) → i : ℕ // i ≤ n \quad 5 : ℕ }{⊢ pick\enspace{5} : i : ℕ // i ≤ 5} {\large{A}}{\normalsize{PP'}} \\)

The next example demonstrates LAM':

\\( \cfrac{
      \cfrac {α : Type, x : α ⊢ x : α} {α : Type ⊢ (λ\enspace{x} : α => x) : α → α} {\large{L}}{\normalsize{AM}}\enspace{or}\enspace{\large{L}}{\normalsize{AM'}}
    }
    {⊢ (λ\enspace{α} : Type => λ\enspace{x} : α => x) : (α : Type) → α → α}
    {\large{L}}{\normalsize{AM'}} \\)

The picture is incomplete because we only check that the terms—the entities on the left-hand side of a
colon (:)—are well typed. The types—the entities on the right-hand side of a colon—must also be
checked, using the same type system, but this time as terms. For example, the type of `Nat.succ` is
`ℕ → ℕ`, whose type is `Type`. Types of types, such as `Type` and `Prop`, are called universes. We will study
them more closely in Chapter 11.

Regrettably, the intuitive syntax `(x : σ) → τ` used above is not available in Lean. Instead, we
must write `∀x : σ, τ`. The familiar notation `σ → τ` is supported as syntactic sugar for `∀ _ : σ, τ`. The
∀ syntax emphasizes that `x` is a bound variable. As an alias for ∀, we can also write Π. The two
symbols are interchangeable.

In [Type Definitions](../Basics/TypeDefinitions.lean.md), we saw the commands:
-/
#check List.nil
#check List.cons
/-!
and their output
```
[] : List ?m.26
List.cons : ?m.28 → List ?m.28 → List ?m.28
```
We can now make sense of the Π-type: `List.nil` is a function that takes a type `α`
as argument and that returns a value of type `List α`.

-- BUGBUG : lean4 no longer shows `List.nil : Π(α : Type), list α` - is there a better example
we can use here instead?
-/
