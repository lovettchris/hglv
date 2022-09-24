import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Init.Data.Nat.Basic
/-!
## Structural Induction

_Structural induction_ is a generalization of mathematical induction to arbitrary inductive types.
To prove a goal `n : ℕ ⊢ P[n]` by structural induction on `n`, it suffces to show two subgoals,
traditionally called the base case and the induction step:
```lean
⊢ P[0]
k : ℕ,ih : P[k] ⊢ P[k + 1]
```
We can of course also write `Nat.zero` and `Nat.succ k`.

In general, the situation is more complex. The goal might contain some extra hypotheses (e.g., `Q`)
that do not depend on `n` and others (e.g., `R[n]`) that do. Assuming we have one hypothesis of each
kind, this gives the initial goal
```lean
hQ : Q, n : N, hR : R[n] ⊢ S[n]
```
Structural induction on `n` then produces the two subgoals
```lean
hQ : Q, hR : R[0] ⊢ S[0]
hQ : Q, k : N, ih : R[k] → S[k], hR : R[k + 1] ⊢ S[k + 1]
```
The hypothesis `Q` is simply carried over unchanged from the initial goal, whereas
`R[n] ⊢ S[n]` is treated almost the same as if the goal’s target had been
`R[n] → S[n]`. This is easy to check by taking `P[n] := R[n] → S[n]` in the first example
above. Since this general format is very verbose and hardly informative (now that
we understand how it works), from now on we will present goals in the simplest
form possible, without extra hypotheses.

For lists, given a goal `xs : List α ⊢ P[xs]`, structural induction on `xs` yields
```lean
⊢ P[[]]
y : α, ys : List α, ih : P[ys] ⊢ P[y :: ys]
```
We can of course also write `List.nil` and `List.cons y ys`. There is no induction hypothesis
associated with `y`, because `y` is not of List type.

For arithmetic expressions, the base cases are
```
i : ℤ ⊢ P[Aexp.num i]                    x : string ⊢ P[Aexp.var x]
```
and the induction steps for `add`, `sub`, `mul` and `div` are
```
e₁ e₂ : Aexp, ih₁ : P[e₁], ih₂ : P[e₂] ⊢ P[Aexp.add e₁ e₂]
e₁ e₂ : Aexp, ih₁ : P[e₁], ih₂ : P[e₂] ⊢ P[Aexp.sub e₁ e₂]
e₁ e₂ : Aexp, ih₁ : P[e₁], ih₂ : P[e₂] ⊢ P[Aexp.mul e₁ e₂]
e₁ e₂ : Aexp, ih₁ : P[e₁], ih₂ : P[e₂] ⊢ P[Aexp.div e₁ e₂]
```
Notice the two induction hypotheses, about e₁ and e₂.

In general, structural induction produces one subgoal per constructor. In each subgoal, induction
hypotheses are available for all constructor arguments of the type we are performing the induction
on.

Regardless of the inductive type `τ`, the procedure to compute the subgoals is
always the same:

1. Replace the hole in `P[ ]` with each possible constructor applied to fresh
variables (e.g., `y :: ys`), yielding as many subgoals as there are constructors.
2. Add these new variables (e.g., `y`, `ys`) to the local context.
3. Add induction hypotheses for all new variables of type `τ`.

As an example, we will prove that `Nat.succ n ≠ n` for all `n : ℕ`. We start with
an informal proof, because these require us to understand what we are doing:

The proof is by structural induction on `n`.

`Case 0`: We must show `Nat.succ 0 ≠ 0`. This follows from the “no confusion” property
of the constructors of inductive types.

`Case Nat.succ k`: The induction hypothesis is `Nat.succ k ≠ k`. We
must show `Nat.succ (Nat.succ k) ≠ Nat.succ k`. By the injectivity of
`Nat.succ`, we have that `Nat.succ (Nat.succ k) = Nat.succ k` is equivalent to
`Nat.succ k = k`. Thus, it suffces to prove `Nat.succ k ≠ k`,
which corresponds exactly to the induction hypothesis. <span class=qed></span>

Notice the main features of this informal proof, which you should aim to reproduce in your own
informal arguments:

- The proof starts with an unambiguous announcement of the type of proof we are carrying out (e.g.,
  which kind of induction and on which variable).
- The cases are clearly identified, and for each case, both the goal’s target and the hypotheses are
  stated.
- The key lemmas on which the proof relies are explicitly invoked (e.g., injectivity of `Nat.succ`).

Now let us carry out the proof in Lean:
-/
lemma nat.succ_neq_self (n : ℕ) :
  Nat.succ n ≠ n := by
  induction' n with n ih  -- ih: Nat.succ n ≠ n
  { simp }           -- ⊢ Nat.succ Nat.zero ≠ Nat.zero
  { simp [ih] }      -- ⊢ Nat.succ (Nat.succ n) ≠ Nat.succ n
/-!
The routine reasoning about constructors is all carried out by `simp` automatically,
which is usually what we want.

We can supply our own names, and reorder the cases, by using the case tactic
in front of each case, together with the case’s name and the desired names for
the variables and hypotheses introduced by `induction’`. For example:
-/
lemma nat.succ_neq_self2 (n : ℕ) :
  Nat.succ n ≠ n := by
  induction' n with m IH
  case succ  => { simp [IH] }
  case zero => { simp }
/-!
Instead of `n` and `ih`, we chose the names `m` and `IH` and we moved the zero
case to the end.
-/
