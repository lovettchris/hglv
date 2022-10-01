import Mathlib.Tactic.Basic
import Mathlib.Init.Data.Nat.Basic
import InductivePredicates.IntroductoryExamples
/-!
## Rule Induction

In the same way that we can perform an induction on a term of inductive type, we can perform an
induction on a proof of an inductive predicate. For example, given the goal `h : Even n ⊢ p n`, we
can invoke `induction’ h` and get two subgoals, for `Even.zero` and `Even.add_two`. This is called
_induction on the structure of the derivation of `h`_ or simply _rule induction_, because the induction is
on the predicate’s introduction rules (i.e., the constructors of the proof term).

There are two ways to look at rule induction: the “least-predicate-such-that view” and the “PAT
view.” To understand the least-predicate-such-that view, recall that an inductive definition
introduces a symbol as the least (i.e., the most false) predicate satisfying the introduction rules.
Accordingly, `Even` is the least predicate `q` such that the properties `q 0` and `∀k, q k → q (k + 2)`
hold. Therefore, if we can show that `p 0` and `∀k, p k → p (k + 2)` hold for some predicate `p`, then `p`
is either `Even` itself or greater than (i.e., more true than) `Even`. As a result, `Even n` implies `p n`,
which is exactly what we need to prove the goal `h : Even n ⊢ p n`.

The least-predicate-such-that view gives a nice intuitive account of rule induction that can be used
in informal arguments, such as the following proof that `Even n` implies `n % 2 = 0` for all `n`:

- The proof is by rule induction on the hypothesis `Even n`.
- Case `Even.zero`: We must show `0 % 2 = 0`. This follows by computation.
- Case `Even.add_two k`: The induction hypothesis is `k % 2 = 0`. We must
show `(k + 2) % 2 = 0`. This follows by basic arithmetic reasoning. <span class="qed"></span>

The Lean proof has the same structure:
-/
lemma mod_two_eq_zero_of_even (n : ℕ) (h : Even n) :
    n % 2 = 0 := by
  induction' h
  case zero => rfl
  case add_two k hk ih => simp [ih]
/-!
The PAT principle gives us another fruitful way to look at rule induction. The
key idea is that rule induction on `h` in a goal such as `h : Even n ⊢ P[h]` is perfectly
analogous to structural induction on a value of a dependent inductive type such
as `Vec α n` (Section 4.10). Writing `Pᵤ[ ]` for the variant of `P[ ]` where `n` is replaced
by some term `u`, we get the subgoals
```lean
⊢ P₀[Even.zero : Even 0]
k : ℕ, hk : Even k, ih : Pₖ[hk] ⊢ Pₖ₊₂[Even.add_two k hk : Even (k + 2)]
```
These are precisely the subgoals produced by `induction’ h` with `k hk ih`.

Regardless of the inductive predicate `q`, the procedure to compute the subgoals is always the same:

1. Replace `h` in `P[h]` with each possible introduction rule applied to fresh variables (e.g.,
`Even.add_two k hk`), massaging `P[ ]` to make it type-correct. This yields as many subgoals as
there are introduction rules.
1. Add these new variables (e.g., `k`, `hk`) to the local context.
1. Add induction hypotheses for all new hypotheses that assert `q` . . .

Notice the presence of `hk : Even k` among the hypotheses above. It was absent
in the least-predicate-such-that view and is not essential because it can always
be recovered by strengthening `P` to be of the form `Even n ∧ · · ·`.

In nearly all practical cases, `h` will not occur in `P[h]`. We can then simply write
```
⊢ P₀   k : ℕ, hk : Even k, ih : Pₖ ⊢ Pₖ₊₂
```

In rare cases, `h` will occur in `P[h]`. Proofs may appear as subterms in arbitrary
terms, as we saw when we tried to extract the head of a list in
[Section 4.7](../FunctionalProgramming/Lists.lean.md)

When the argument to `Even` in `h` is not a variable, performing an induction will
destroy its structure. Fortunately, `induction’` (with a prime) notices this situation
and preserves the information in a hypothesis called `index_eq`. Thus, given the
goal `h : Even (2 * n + 1) ⊢ false`, invoking `induction’ h` with `k hk ih` produces
the induction step
```
k : ℕ, h : Even k, n : ℕ, index_eq : k + 1 = 2 * n, ih : ∀n, ¬ k = 2 * n + 1
⊢ false
```
for `Even.add_two`. The trivial base case `¬ Even 1` is eliminated automatically by
basic constructor reasoning.

The hypothesis `index_eq` records the equality between `Even`’s argument in the
initial goal (i.e., `2 * n + 1`) and `Even`’s argument in the `Even.add_two` rule
(i.e., `k + 2`). Notice that the equation is simplified by subtracting 1 from both sides. To
continue the proof, we need to instantiate `n` in the induction hypothesis with `n - 1`.
Here is the complete proof:
-/
lemma not_even_two_mul_add_one (n : ℕ) :
    ¬ Even (2 * n + 1) := by
  intro h
  induction' h
  apply ih (n - 1)
  cases' n
  case zero => { simp_arith }
  case succ => {
    simp [Nat.succ_eq_add_one] at *
    simp_arith }

--BUGBUG error: index in target's type is not a variable (consider using the `cases` tactic instead)
--BUGBUG the book used tactic linarith, but it doesn't seem to be defined
/-!

We use the lemma `Nat.succ_eq_add_one` to rewrite terms of the form `Nat.succ n` to `n + 1` and the
`simp_arith` tactic to perform simple arithmetic reasoning. The lemma is very useful when we face a
mixture of `Nat.succ` and addition.

The reflexive transitive closure `Star r` is similar to `Even`. Given a goal
`h : Star r x y ⊢ P`, rule induction on `h` produces the following subgoals, where `Pa,b` denotes
the variant of `P` where `x` and `y` are replaced by `a` and `b`, respectively:

```lean
a b : α, hab : r t u ⊢ Pa,b
a : α ⊢ Pa,a
a b c : α, hab : star r a b, hbc : star r b c, ihab : Pa,b, ihbc : Pb,c ⊢ Pa,c
```
Notice these three subgoals match the introduction rules for `Start`, namely `base`, `refl` and `trans`.

-- BUGBUG: book has Pa,b written using subscripts, but unicode doesn't seem to define those
so is the book using a custom font for that?

This is where the “assistant” aspect of “proof assistant” comes into play. One of
the key properties of `Star` is idempotence—applying `Star` to `Star r` has no effect.
This can be proved as follows in Lean, using rule induction for the → direction of
the equivalence:
-/
lemma star_star_iff_star {α : Type} (r : α → α → Prop)
    (a b : α) : Star (Star r) a b ↔ Star r a b := by
  apply Iff.intro
  { intro h
    induction' h
    case base a b hab => exact hab
    case refl a => apply Star.refl
    case trans a b c hab hbc ihab ihbc =>
      apply Star.trans a b
      exact ihab
      exact ihbc }
  { intro h
    apply Star.base
    exact h }
/-!
We use the `case` tactic both to document which cases we are focusing on and to give intuitive names
to the emerging variables. It is easy to get lost in goals containing long, automatically generated
names. The cleanup tactics introduced in [Section 2.8](../BackwardProofs/CleanupTactics.lean.md) can
also be a great help when facing large goals.

We can state the idempotence property more standardly in terms of equality
instead of as an equivalence:

-/
lemma star_star_eq_star {α : Type}
    (r : α → α → Prop) : Star (Star r) = Star r := by
  apply funext
  intro a
  apply funext
  intro b
  apply propext
  apply star_star_iff_star

/-!
The proof requires two lemmas that are available because Lean’s logic is classical:
```
funext : (∀x, ?f x = ?g x) → ?f = ?g
propext : (?a ↔ ?b) → ?a = ?b
```

Functional extensionality (`funext`) states that if two functions yield equal results for all
inputs, then the two functions must be equal. Propositional extensionality (`propext`) states that
equivalence of propositions coincides with equality. In these phrases, extensionality means
something like “what you see is what you get.” These properties may seem obvious, and yet there
exist proof assistants built on weaker, intuitionistic logics in which the properties do not
generally hold.

In [Chapter 4](../FunctionalProgramming/PatternMatching.lean.md), we saw a diagram depicting the
interpretation of bool and Prop side by side. The diagram suggested the existence of an infinite
number of propositions, but we now know that there are exactly two propositions: false and true.
Moreover, the latter admits any number of proofs. Here is a revised diagram (with only five proofs
shown):

![diagram](diagram.svg)

We register the lemma `star_star_eq_star` as a `simp` rule using:
-/
attribute [simp] star_star_eq_star
/-!
because viewed as a left-to-right rewrite rule, it genuinely replaces a complex term by a simpler
term. It is hard to imagine a situation where we would not want `simp` to rewrite `Star (Star . . .)`
to `Star . . .`.

For rule induction, we normally use the `induction'` tactic. For subtle logical
reasons that will become clearer in Chapter 11, rule induction by pattern matching
is generally not possible.
-/