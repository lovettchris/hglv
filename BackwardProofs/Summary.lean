import Mathlib.Tactic.Basic

/-!
## Summary of New Lean Constructs

**Commands**

| name | description |
|------|-------------|
| `set_option` | changes or activates tracing, syntax output, etc. |

**Attribute**


| name | description |
|------|-------------|
| `@[simp]` | adds a lemma to the simp set |

**Proof Commands**


| name | description |
|------|-------------|
| `by` | applies a single tactic |

**Tactics**

| name | description |
|------|-------------|
| apply      | matches the goal’s target with the lemma’s conclusion and replaces the goal with the lemma’s hypotheses |
| assumption | proves the goal using a hypothesis |
| cc         | propagates equalities up to to associativity and commutativity |
| clear      | removes a variable or hypothesis from the goal |
| exact      | proves the goal using the specified lemma |
| induction’ | performs structural induction on a variable of an inductive type |
| intro(s)   | moves ∀-quantified variables into the goal’s hypotheses |
| refl       | proves l = r where l and r are equal up to computation |
| rename     | renames a variable or hypothesis |
| rewrite    | applies the given rewrite rule once |
| simp       | applies a set of preregistered rewrite rules exhaustively |
| sorry      | stands for a missing proof or definition |

**Tactic Combinator**

| name | description |
|------|-------------|
| `{ . . . }` | focuses on the first subgoal; needs to prove that goal |
-/