import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.Basic

/-!
## Basic Tactics

We already saw the `intros` and `apply` tactics. These are the staples of tactical
proofs. Other basic tactics include `rfl`, `exact`, `assumption`, and `cc`. These tactics
can go a long way, if we are patient enough to carry out the reasoning using them,
without appealing to stronger proof automation. They can also be used to solve
various logic puzzles.

Below, the square brackets [] enclose optional syntax

**intro(s)**

```
    intro [ name ]
    intros [ name₁ ... nameₙ ]
```

The `intro` tactic moves the leading ∀-quantified variable or the leading assumption `a →` from the
goal’s target to the local context. The tactic takes as an optional argument the name to give to the
variable or to the assumption in the context, overriding the default name. The plural variant intros
can be used to move several variables or assumptions at once.

**rfl**

The `rfl` tactic proves goals of the form `⊢ l = r`, where the two sides `l` and `r` are
syntactically equal up to computation. Computation means expansion of definitions, reduction of an
application of a λ-expression to an argument, and more.

These _conversions_ have traditional names. The main conversions are listed below together with
examples, in a global context containing `def double (n : ℕ) : ℕ := n + n`:

| name         | effect                               |
|--------------|--------------------------------------|
| α-conversion | `(λx, f x) = (λy, f y)`              |
| β-conversion | `(λx, f x) a = f a`                  |
| δ-conversion | `double 5 = 5 + 5`                   |
| ζ-conversion | `(let n : N := 2 in n + n) = 4`      |
| η-conversion | `(λx, f x) = f`                      |
| ι-conversion | `prod.fst (a, b) = a`                |

Applying a conversion repeatedly as left-to-right rewrite rules is called _reduction); applying it
once in reverse is called _expansion_. Since much of Lean’s machinery treats terms that are
syntactically equal up to computation uniformly, it usually makes sense to tell Lean’s
pretty-printer to aggressively β-reduce its output. This is what the the command
```
set_option pp.beta true   -- BUGBUG: https://github.com/leanprover/lean4/issues/715
```
near the top of the files accompanying this guide achieves.
-/

lemma α_example {α β : Type} (f : α → β) :
  (λ x => f x) = (λ y => f y) :=
  by
   rfl

lemma α_example₂ {α β : Type} (f : α → β) :
  (λx => f x) = (λy => f y) :=
by rfl

lemma β_example {α β : Type} (f : α → β) (a : α) :
  (λx => f x) a = f a :=
by rfl

def double (n : ℕ) : ℕ := n + n

lemma δ_example :
  double 5 = 5 + 5 :=
by rfl

lemma ζ_example :
  (let n : ℕ := 2; n + n) = 4 :=
by rfl

lemma η_example {α β : Type} (f : α → β) :
  (λ x => f x) = f :=
by rfl

lemma ι_example {α β : Type} (a : α) (b : β) :
  Prod.fst (a, b) = a :=
by rfl
/-!

**apply**
```
    apply lemma-or-hypothesis
```

The `apply` tactic matches the goal’s target with the conclusion of the specified lemma or
hypothesis and adds the lemma or hypothesis’s assumptions as new goals. The matching is performed up
to computation.

We must invoke apply with care, because it can transform a provable goal into
an unprovable subgoal. For example, if the goal is `⊢ 2 + 2 = 4` and we apply the
lemma `false → ?a`, the variable `?a` is matched against `2 + 2 = 4`, and we end up
with the unprovable subgoal `⊢ false`. We say that `apply` is unsafe. In contrast,
`intro` always preserves provability and is therefore safe.

**exact**
    ```
    exact lemma-or-hypothesis
    ```

The `exact` tactic matches the goal’s target with the specified lemma or hypothesis,
closing the goal. We can often use `apply` in such situations, but `exact` communicates
our intentions better. In the example from Section 2.1, we could have used
`exact ha` instead of `apply ha`.

**assumption**

The `assumption` tactic finds a hypothesis from the local context that matches the
goal’s target and applies it to prove the goal. In the example from Section 2.1, we
could have used `assumption` instead of `apply ha`

**cc**

The `cc` tactic implements an algorithm known as [congruence closure](../bib.md#31) to derive new
equalities from those that are present in the goal. For example, if the goal contains `b = a` and
`f b ≠ f a` as hypotheses, the algorithm will derive `f b = f a` from `b = a` and discover a contradiction
with `f b ≠ f a`. The `cc` tactic is also suitable for more pedestrian work, such as proving
`hb : b ⊢ a ∨ b ∨ c` or discovering a contradiction among the goal’s hypotheses.

In addition, `cc` can be used to reason up to associativity (e.g., `(a + b) + c = a + (b + c)`) and
commutativity (e.g, `a + b = b + a`). This works for binary operations that are registered as
associative and commutative, such as `+` and `*` on arithmetic types, and `∪` and `∩` on sets. We will see
an example in Section 2.6.

At this point, you might wonder, “So what does `cc` do exactly?” Of course, you could look up the
[reference](../bib.md#31) given above to the scientific paper that describes its underlying algorithm, or even
read the source code. But this might not be the most efficient use of your time. In truth, even expert
users of proof assistants do not fully understand the behavior of the tactics they use daily. The
most successful users adopt a relaxed, sporty attitude, trying tactics in sequence and studying the
emerging subgoals, if any, to see if they are on the right path.

As you keep on using `cc` and other tactics, you will develop some intuition about what kinds of
goal they work well on. This is one of the many reasons why interactive theorem proving can only be
learned by doing. Often, you will not understand exactly what Lean does—why a tactic succeeds, or
fails. Theorem proving can be very frustrating at times. The advice printed in large, friendly
letters on the cover of _The Hitchhiker’s Guide to the Galaxy_ applies here: DON'T PANIC.

**sorry**

The `sorry` proof command we encountered in [Theorem Statements](../Basics/TheoremStatements.lean.md)
is also available as a tactic. It “proves” the current goal without actually proving it. This is
normally used as a placeholder for a proof that is not yet available or an exercise left to the reader.

-/
