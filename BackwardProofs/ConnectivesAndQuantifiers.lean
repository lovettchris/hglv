import Mathlib.Tactic.Basic
import BackwardProofs.BasicTactics
/-!
## Reasoning about Connectives and Quantifiers

Before we learn to reason about natural numbers, lists, or other data types, we
must first learn to reason about the logical connectives and quantifiers of Lean’s
logic. Let us start with a simple example: commutativity of conjunction (`∧`).
-/
lemma and_swap (a b : Prop) :
a ∧ b → b ∧ a := by
  intro hab
  apply And.intro
  apply And.right
  exact hab
  apply And.left
  exact hab
/-!
At this point, we recommend that you move the cursor over each line in the above example to see the
sequence of proof states. By putting the cursor over each bubble at the end of the line, you can see
the effect of the command on that line. At the end of the last line Lean simply reports “goals
accomplished 🎉” meaning that no subgoals remain to be proved.

The proof is a typical `intro–apply–exact` mixture. It uses the lemmas

```
And.intro : ?a → ?b → ?a ∧ ?b
And.left : ?a ∧ ?b → ?a
And.right : ?a ∧ ?b → ?b
```
where the question marks (?) indicate variables that can be instantiated—for example, by matching
the goal’s target against the conclusion of a lemma.

The three lemmas above are the introduction rule and the two elimination
rules associated with conjunction. An introduction rule for a symbol (e.g., `∧`) is
a lemma whose conclusion contains that symbol. Dually, an elimination rule has
the symbol in an assumption. In the above proof, we apply the introduction rule
associated with `∧` to prove the goal `⊢ b ∧ a`, and we apply the two elimination
rules to extract `b` and `a` from the hypothesis `a ∧ b`.

Question marks can also arise in goals. They indicate variables that can be
instantiated arbitrarily. In the middle of the proof above, right after the tactic
apply `And.right`, we have the goal

```lean
a b : Prop, hab : a ∧ b ⊢ ?left.a ∧ b
```
The tactic exact `hab` matches `?left.a` (in the target) with `a` (in `hab`). Because variables can
occur both in the hypothesis or lemma that is `apply`d and in the target, in general the procedure
used to instantiate variables to make two terms syntactically equal is called _unification_. Matching
is a special case of unification where one of the two terms contains no variables. In practice,
goals with variables are rare, so Lean’s unification usually amounts to matching.

    -- BUGBUG: no idea what most of that paragraph means.

In Lean, unification is performed up to computation. For example, the terms
`(λ x => ?left.a) a` and `b` can be unified by taking `?left.a := b`,
because `(λ x => b) a` and `b` are syntactically equal up to β-conversion.

The following is an alternative proof of the lemma `and_swap`:
-/
lemma and_swap2 :
∀ a b : Prop, a ∧ b → b ∧ a := by
  intros a b hab
  apply And.intro
  { exact And.right hab }
  { exact And.left hab }
/-!
The lemma is stated differently, with `a` and `b` as ∀-quantified variables instead of
parameters of the lemma. Logically, this is equivalent, but in the proof we must
then introduce `a` and `b` in addition to `hab`.

Another difference is the use of curly braces `{ }`. When we face two or more goals to prove, it is
generally good style to put each proof in its own block enclosed in curly braces. The `{ }` tactic
combinator focuses on the first subgoal; the tactic inside must prove it. In our example, the
`apply And.intro` tactic creates two subgoals, `⊢ b` and `⊢ a`.

A third difference is that we now apply, by juxtaposition, `And.right` and
`And.left` directly to the hypothesis `a ∧ b` to obtain `b` and `a`, respectively,
instead of waiting for the lemmas’ assumptions to emerge as new subgoals. This
is a small forward step in an otherwise backward proof. The same syntax is used
both to discharge (i.e., prove) a hypothesis and to instantiate a ∀-quantifier. One
benefit of this approach is that we avoid the potentially confusing `?left.a` variable.

The introduction and elimination rules for disjunction (∨) are as follows:
```lean
Or.intro_left : ∀ b : Prop, ?a → ?a ∨ b
Or.intro_right : ∀ b : Prop, ?a → b ∨ ?a
Or.elim : ?a ∨ ?b → (?a → ?c) → (?b → ?c) → ?c
```

--BUGBUG: what are all these question marks? Are they supposed to look like
unresolved metavariables?

The ∀-quantifiers in `Or.intro_left` and `Or.intro_right` can be instantiated
directly by applying the lemma name to the value we want to instantiate with,
via simple juxtaposition. Thus, `Or.intro_left false` corresponds to the lemma
`?a → ?a ∨ false`. This is the forward style.

Alternatively, we can invoke apply `Or.intro_left` on a goal of the form
`. . . ⊢ c ∨ d`. This instantiates the lemma with `?a := c` and `b := d`.
The new subgoal is `. . . ⊢ c`. This is the backward style.

Both `Or.intro_left` and `Or.intro_right` are unsafe: If you apply the wrong
one of the two, or either of them too early in a proof, you might end up with an
unprovable subgoal. This is easy to see if you consider the provable goal
`⊢ true ∨ false`: applying `Or.intro_right` yields the unprovable subgoal
`⊢ false`.

The `Or.elim` rule may seem counterintuitive at a first glance. In essence, it
states that if we have `a ∨ b`, then to prove an arbitrary `c`, it suffices to prove `c`
when `a` holds and when `b` holds. You can think of `(?a → ?c) → (?b → ?c) → ?c`
as a clever trick to express the concept of disjunction using only implication.

The introduction and elimination rules for equivalence (`↔`) are as follows:

```lean
Iff.intro : (?a → ?b) → (?b → ?a) → (?a ↔ ?b)
Iff.mp : (?a ↔ ?b) → ?a → ?b
Iff.mpr : (?a ↔ ?b) → ?b → ?a
```
The introduction and elimination rules for existential quantification (`∃`) are

```lean
Exists.intro : ∀ w, (?p w → (∃x, ?p x))
Exists.elim : (∃ x, ?p x) → (∀a, ?p a → ?c) → ?c
```
The introduction rule for `∃` can be used to instantiate an existential quantifier
with a witness. For example:
-/
lemma nat_exists_double_iden :
  ∃ n : ℕ, double n = n := by
  apply Exists.intro 0
  rfl
/-!
Again, we instantiate a ∀-quantifier in a forward fashion: `Exists.intro 0` is the
lemma `?p 0 → (∃x, ?p x)`. The rule is unsafe: Choosing the wrong witness for `x`
will result in an unprovable goal. For example, if the goal is `⊢ ∃ n, n > 5` and we
take 3 as the witness, we end up with the unprovable subgoal `⊢ 3 > 5`.

The elimination rule for `∃` is reminiscent of `∨`. Indeed, a fruitful way to think
of a quantification `∃ n, ?p n` is as a possibly infinitary disjunction `?p 0 ∨ ?p 1 ∨ · · · `.
Similarly, `∀ n, ?p n` can be thought of as `?p 0 ∧ ?p 1 ∧ · · · `.
For truth (`true`), there is only an introduction rule:

```lean
True.intro : true
```
Truth holds no information whatsoever. If it appears as a hypothesis, it is completely useless, and
there is no elimination rule that will succeed at extracting any information from it. The `clear`
tactic, described in Section 2.8 below, can be used to remove such useless hypotheses.

Dually, for falsehood (`false`), there is only an elimination rule

```lean
False.elim : false → ?a
```
There is no way to prove falsehood, but if we somehow have it from somewhere
(e.g., from a hypothesis), then we can derive `?a`nything.

Negation (`not`) is defined in terms of implication and falsehood:
`¬ a` abbreviates `a → false`. Lean’s logic is classical, with support for the law of excluded
middle and proof by contradiction:

-- BUGBUG is this still true statemetn or is classical lean just one option now as per:
  https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html?highlight=classical#classical-logic

```lean
Classical.em : ∀ a : Prop, a ∨ ¬ a
Classical.byContradiction : (¬ ?a → false) → ?a
```

Finally, implication (`→`) and universal quantification (`∀`) are the proverbial dogs
that did not bark. For both of them, the `intro` tactic is the introduction principle,
and application is the elimination principle. For example, given the lemmas
`hab : a → b` and `ha : a`, the juxtaposition `hab ha` is a lemma stating `b`.

For proving logic puzzles involving connectives and quantifiers, we advocate
a “mindless,” “video game” style of reasoning that relies mostly on basic tactics
such as `intro`(s) and `apply`. Here are some strategies that often work:

- If the goal’s target is an implication `P → Q`, invoke `intro hP` to move `P` into your
  hypotheses: `. . ., hP : P ⊢ Q`.

- If the goal’s target is a universal quantification `∀ x : σ, Q`, invoke `intro x` to move `x` into
  the local context: `. . ., x : σ ⊢ Q`.

- Look for a lemma or hypothesis whose conclusion has the same shape as the goal’s target (possibly
  containing variables that can be matched), and apply it. For example, if the goal’s target is `Q`
  and you have a lemma or hypothesis of the form `hPQ : P → Q`, try `apply hPQ`.

- A negated goal `⊢ ¬ P` is syntactically equal to `⊢ P → false` up to computation, so you can
  invoke `intro hP` to produce the subgoal `hP : P ⊢ false`. Expanding negation’s definition by
  invoking `rw not_def` (described in Section 2.5) is often a good strategy.

- Sometimes you can make progress by replacing the goal by `false`, by entering apply `False.elim`. As
  next step, you would typically apply a lemma or hypothesis of the form `P → false` or `¬ P`.

- When you face several choices (e.g., between `Or.intro_left` and `Or.intro_right`), remember which
  choices you have made, and backtrack when you reach a dead end or have the impression you are not
  making any progress.

- If you suspect that you might have reached a dead end, check whether the goal actually is provable
  under the given assumptions. Even if you started with a provable lemma statement, the current goal
  might be unprovable (e.g., if you used unsafe rules such as `Or.intro_left`)

-/
