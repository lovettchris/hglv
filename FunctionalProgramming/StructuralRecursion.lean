import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Init.Data.Nat.Basic
/-!
## Structural Recursion

_Structural recursion_ is a form of recursion that allows us to peel off one constructor from the
value on which we recurse. The factorial function below is structurally recursive:
-/
def fact : ℕ → ℕ
| 0 => 0
| (n + 1) => (n + 1) * fact n
/-!
The constructor we peel off here is `Nat.succ` (written `+ 1`). Such functions are guaranteed to
call themselves only finitely many times before the recursion stops; for example, `fact 12345` will
call itself 12345 times. This is a prerequisite for establishing that the function terminates, an
important property to ensure both logical consistency and termination of evaluation.

With structural recursion, there are as many equations as there are constructors. Novices are often
tempted to supply additional, redundant cases, as in the following example:
-/
def fact₁ : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 1) => (n + 1) * fact n
/-!
It is in your own best interest to resist this temptation. The more cases you have in your
definitions, the more work it will be to reason about them. Keep in mind the saying that one good
definition is worth three theorems.

For structurally recursive functions, Lean can automatically prove termination. For more general
recursive schemes, the termination check may fail. Sometimes it does so for a good reason, as in the
following example:
-/
-- fails saying: fail to show termination for `illegal`
def illegal : ℕ → ℕ
| n => illegal n + 1
/-!
If Lean were to accept this definition, we could exploit it to prove that `0 = 1`, by subtracting
`illegal n` on each side of the equation `illegal n = illegal n + 1`. From `0 = 1`, we could derive `false`,
and from `false`, we could derive anything, including the three-color theorem. Clearly, we do not want
that.

If we had used a variable and axiom, nothing could have saved us:
-/
constant immoral : ℕ → \N

axiom immoral_eq (n : ℕ) : immoral n = immoral n + 1

lemma proof_of_false :
false := by
  have h1 : immoral 0 = immoral 0 + 1 :=
    immoral_eq 0
  have h2 : immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 :=
    by rfl
  have h3 : 0 = 1 := by simp [*] at *
  show false
    by rfl

-- BUGBUG: failed to synthesize instance...
/-!
Another reason for preferring `def` is that the defining equations are used to compute. Tactics such
as `rfl` that unify up to computation become stronger each time we introduce a definition, and the
diagnosis commands `#eval` and `#reduce` can be used on defined constants.

-- BUGBUG: what to use instead of 'constants' in the above example ?

The observant reader will have noticed that the above definitions of factorial are mathematically
wrong: `fact` shockingly returns `0` regardless of the argument, and `fact₂ 0` should give `1`, not
`0`. We quite literally facted up. These embarrassing mistakes remind us to test our definitions and
prove some properties about them. Although flawed axioms arise now and then, what is much more
common are definitions that fail to capture the intended concepts. Just because a function is called
`fact` does not mean that it actually computes factorials.
-/
