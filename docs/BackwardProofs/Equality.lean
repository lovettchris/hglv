import Mathlib.Tactic.Basic
/-!
## Reasoning about Equality

Equality (`=`) is also a basic logical constant. It is characterized by the following
introduction and elimination rules:

```lean
Eq.refl : ∀a, a = a
Eq.symm : ?a = ?b → ?b = ?a
Eq.trans : ?a = ?b → ?b = ?c → ?a = ?c
Eq.subst : ?a = ?b → ?p ?a → ?p ?b
```

The first three lemmas are introduction rules specifying that `=` is an equivalence
relation. The fourth lemma is an elimination rule that allows us to replace equals
for equals in an arbitrary context, represented by the higher-order variable `?p`.

An example will show how this works. Below, we apply `Eq.subst` to rewrite
`f a b` to `f a' b`, using the equation `a = a'`:
-/
theorem cong_fst_arg {α : Type} (a a' b : α)
(f : α → α → α) (ha : a = a') : f a b = f a' b := by
  apply Eq.subst ha
  apply Eq.refl

-- BUGBUG doesn't work.

/-!
The `Eq.subst` instance we use has `?a := a`, `?b := a'`, and `?p := (λ x, f a b = f x b)`:
```lean
a = a' → (λx, f a b = f x b) a → (λx, f a b = f x b) a'
```
In β-reduced form:
```lean
a = a' → f a b = f a b → f a b = f a' b
```
The lemma's first assumption matches the hypothesis `ha : a = a'`, which is passed as an argument in the
first apply invocation. The lemma's second assumption is a trivial equality that can be proved by
apply `Eq.refl` or `rfl`. The lemma's conclusion matches the goal’s target. Notice how a higher-order
variable (e.g., `?p`) can represent an arbitrary context (e.g., `f . . . b`) around a term (e.g.,
`a` or `a'`). This works because `apply` unifies up to computation, including β-conversion.

The `Eq.subst` lemma can be applied several times in sequence, as follows:
-/
lemma cong_two_args {α : Type} (a a' b b' : α)
  (f : α → α → α) (ha : a = a') (hb : b = b') :
f a b = f a' b' := by
  apply Eq.subst ha
  apply Eq.subst hb
  apply Eq.refl

-- BUGBUG doesn't work.

/-!
Since rewriting in this way is such a common operation, Lean provides a `rw` tactic
to achieve the same result. The tactic will also notice if `rfl` is applicable:
-/
lemma cong_two_args₂ {α : Type} (a a' b b' : α)
  (f : α → α → α) (ha : a = a') (hb : b = b') :
f a b = f a' b' := by
  rw [ha]
  rw [hb]

/-!
A note on parsing: Equality binds more tightly than the logical connectives.
Thus, `a = a' ∧ b = b'` should be read as (a = a') ∧ (b = b').

-/