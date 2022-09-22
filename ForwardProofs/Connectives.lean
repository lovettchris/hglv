import Mathlib.Tactic.Basic
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Int.Basic
/-!
## Forward Reasoning about Connectives and Quantifiers

Reasoning about the logical connectives and quantifiers in a forward fashion uses
the same introduction and elimination rules as in [tactic mode](../BackwardProofs/ConnectivesAndQuantifiers.lean.md).
A few examples will show the flavor. Let us start with conjunction:
-/
lemma and_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
λ hab : a ∧ b =>
  have ha : a := And.left hab
  have hb : b := And.right hab
  show b ∧ a from And.intro hb ha
/-!
Even readers who do not know what `And.left` etc. means can understand that we extract `a` and `b` from
`a ∧ b` and put them back together as `b ∧ a`. Mathematicians would probably have an easier time making
sense of this proof than of its tactical counterpart:

-/
lemma and_swap₂ (a b : Prop) :
  a ∧ b → b ∧ a := by
  intro hab
  apply And.intro
  apply And.right
  exact hab
  apply And.left
  exact hab

/-!
On the other hand, the tactical proof is easier to derive mindlessly.

In general, backward proofs are easier to find, and most of the automation provided by proof
assistants works backwards. The reason is simple: Pretend that you are Miss Marple or Hercule Poirot
on a murder investigation. A backward investigation would start from the crime scene and try to
extract clues that potentially connect a handful of suspects to the crime. In contrast, a forward
investigation might start by questioning as many as seven billion people to determine whether they
have an alibi. Which approach is more likely to succeed?

Our next examples concern _one-point rules_. These are lemmas that can be used to eliminate a
quantifier when the bound variable can effectively take only one value. For example, the proposition
`∀ n, n = 666 → beast ≥ n` can be simplified to `beast ≥ 666`. The following lemma justifies this
simplification:

-/
lemma forall.one_point {α : Type} (t : α) (p : α → Prop) :
  (∀x, x = t → p x) ↔ p t :=
Iff.intro (
  λ (hall : ∀ (x : α), x = t → p x) =>
    show p t by
      apply hall t
      rfl
) (
  λ (hp : p t) (x : α) =>
    show x = t → p x by
      intro heq
      rw [heq]
      exact hp
)

/-!
The proof may look intimidating, but it was not hard to develop. The key was to
proceed one step at a time. At first, we observed that the goal is an equivalence,
so we wrote
```
Iff.intro (_) (_)
```
The two placeholders are important to make this proof well formed. We already
put parentheses because we strongly suspect that these will be nontrivial proofs.
Because proofs are basically terms, which are basically programs, the advice we
gave in Section 1.1.4 applies here as well:

> The key idea is that the [proof] should be syntactically correct at all times. The only red
underlining we should see in Visual Studio Code should appear under the placeholders. In general, a
good principle for software development is to start with a program that compiles, perform the smallest
change possible to obtain a new compiling program, and repeat until the program is complete.

Hovering over the first placeholder makes the corresponding subgoal appear. We
can see that Lean expects a proof of `⊢ (∀ (x : α), x = t → p x) → p t`, so we provide
a suitable skeleton. Remember that an implication is the same as a function, so
a structured proof of an implication consists of a lambda that introduces the
assumption followed by a show:
```lean
Iff.intro
  (λ hall : ∀ (x : α), x = t → p x =>
  show p t by
  _)
  (_)
```
What we need to show now is the simpler term `p t` which can by done using the `apply` tactic
using the `hall` hypothesis. The result of this is the goal `t = t` which can be easily
solved using `rfl` or `exact` in this case would also work.

The second part of the `Iff.intro` has to prove the inverse implication, namely,
that `p t → ∀ (x : α), x = t → p x`.  For this proof we need to fix the variable `x`
in that ∀ quantificaiton. We can do that simply by adding it as a parameter in our lambda
function, so we can create the hypothesis `hp` and fix the value of `x` with `λ (hp : p t) (x : α)`.
This leaves us with having to prove the subgoal `x = t → p x`.  Using `intro heq` takes off
the first part of this implication `x = t` and makes it a hypothesis, which leaves us with
the goal `p x`.  The `rw` tactic can use the fact that `x = t` to rewrite this goal as `p t`
and the `exact` tactic can match this exactly with the hypothesis `hp`.

Notice that each of placeholders we started with can be filled in with a structured proof or by a
tactical proof. To fill these placeholders, interpreted each implication as the function arrow
using a λ to introduce the hypothesis and variables that are bound by a quantifier.

Let us check that the rule actually works on our motivating example:
-/
lemma beast_666 (beast : ℕ) :
  (∀ n : ℕ, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  forall.one_point _ _
/-!
It works (we know because there are no red squiggles!). Matching `forall.one_point t p` against the
statement of `beast_666` yields the instantiation `t := 666` and `p := (λ m => beast = m)`. Indeed, if we
substitute these values in `forall.one_point` and β-reduce, we get the statement of `beast_666`.

Finally, the one-point rule for ∃ demonstrates how to use the introduction and
elimination rules for ∃ in a structured proof:
-/
lemma exists.one_point {α : Type} (t : α) (p : α → Prop) :
  (∃x : α, x = t ∧ p x) ↔ p t :=
Iff.intro
  (λ hex : ∃x, x = t ∧ p x =>
    Exists.elim hex
    (λ (x : α) (hand : x = t ∧ p x) =>
      show p t by
      cc))
  (λ hp : p t =>
    show ∃ x : α, x = t ∧ p x from
    Exists.intro t
    (show t = t ∧ p t by
      cc))

-- BUGBUG: cc is missing.
/-!
Notice how we use `Exists.elim hex` to obtain an `x` such that `x = t ∧ p x`. This
admittedly is a bit cumbersome
-/
