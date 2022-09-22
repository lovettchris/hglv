import Mathlib.Tactic.Basic
import Basics.FunctionDefinitions
/-!
## Structured Constructs

The previous section presented the main commands for writing structured proofs: `fun`, `have`,
and `show`. We now review the components of structured proofs more systematically.

**Lemma or Hypothesis**

The simplest structured proof, apart from `sorry`, is the name of a lemma or hypothesis. If we have
-/
lemma two_add_two_eq_four :
  2 + 2 = 4 :=
-- . . .
/-!
then the lemma name `two_add_two_eq_four` can be used as a proof of `2 + 2 = 4` later.
For example:
-/
lemma this_time_with_feelings :
  2 + 2 = 4 :=
two_add_two_eq_four

/-!
We can pass arguments to lemmas to instantiate ∀-quantifiers and discharge assumptions. Suppose the
lemma `add_comm (m n : ℕ) : add m n = add n m` is available, and suppose we want to prove its instance
`add 0 n = add n 0`. This can be achieved neatly using the name of the lemma and two arguments:
-/
axiom add_comm (m n : ℕ) : add m n = add n m

lemma add_comm_zero_left (n : ℕ) :
  add 0 n = add n 0 :=
  add_comm 0 n
/-!
This has the same effect as the tactical proof `by exact add_comm 0 n`, but is more concise. The `exact`
tactic can be seen as the inverse of `by`. Why enter tactic mode if only to leave it immediately?

Like with `exact` and `apply`, the lemma or hypothesis’s statement is matched with the current goal up
to computation. This gives some flexibility.

**fun**

```lean
fun (names₁ [: type₁]) . . . (namesₙ [: typeₙ]) =>
```

A lambda `fun` moves ∀-quantified variables from the goal’s target to the local
context. It can be seen as a structured version of the `intros` tactic.

**have**

```lean
have name : proposition := proof
```
The `have` command lets us state and prove an intermediate lemma, which may refer to names
introduced previously. The proof can be tactical or structured. Generally, we tend to use structured
proofs to sketch the main argument and resort to tactical proofs for proving subgoals or
uninteresting intermediate steps. Another kind of mixture arises when we pass arguments to lemma
names. For example, given `hab : a → b` and `ha : a`, the tactic `exact hab ha` will prove the goal
`⊢ b`. Here, `hab ha` is a proof term nested inside a tactic. So the earlier line
`have hb : b := hab ha` can also be written using a tactic as `have hb : b := by exact hab ha`.

**let**
```
let name [: type] := term
```
Just as with a normal `def` the `let` command introduces a new local definition. It can be used to
name a complex object that occurs several times in the proof afterwards. It is similar to `have` but
is designed for computable data, not proofs. Expanding or introducing a let corresponds to
ζ-conversion (Section 2.2).

**show**
```lean
show proposition from proof
show proposition by tactic proof
```
The `show` command lets us repeat the goal to prove, which can be useful as documentation. It also
allows us to rephrase the goal in a syntactically equal form up to computation. Instead of the
syntax `show proposition from proof`, we can simply write `proof` if we do not want to repeat the goal
and do not need to rephrase it. The proof can also be tactical if you write `show proposition by ...`


-/