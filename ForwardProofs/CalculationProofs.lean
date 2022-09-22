import Mathlib.Tactic.Basic
import Mathlib.Init.Data.Nat.Basic
/-!
## Calculation Proofs

In informal mathematics, we often express proofs as transitive chains of equalities, inequalities,
or equivalences (e.g., `a = b = c`, `a ≥ b ≥ c`, or `a ↔ b ↔ c`). In Lean, such _calculational proofs_ are
supported by the `calc` command. It provides a lightweight syntax and takes care of applying
transitivity lemmas for preregistered relations, such as equality and the arithmetic comparison
operators.

The general syntax is as follows:

```lean
calc
  term₀ op₁ term₁ : proof1
  _     op₂ term₂ : proof₂
  .
  .
  .
  _     opₙ termₙ : proofₙ
```

Each _proofᵢ_ justifies the statement _termᵢ-₁ opᵢ termᵢ_.
The operators _opᵢ_ need not be identical, but they must be compatible.
The underscore (_) is a placeholder for the previous term.
For example, =, <, and ≤ are compatible with each other, whereas > and < are not.

A simple example follows:
-/
axiom two_mul (n : ℕ) : 2 * n = n + n

lemma two_mul_example (m n : ℕ) :
  2 * m + n = m + n + m :=
  calc
    2 * m + n = (m + m) + n := by rw [two_mul]
    _ = m + n + m := by rw [Nat.add_right_comm]

/-!
Mathematicians (assuming they would condescend to offer a justification for such
a trivial result) could have written the above proofs roughly as follows:

```
2 * m + n
= (m + m) + n       (since 2 * m = m + m)
= m + n + m         (by associativity and commutativity of +)
```

In the Lean proof, the underscore stands for the prior term₁ `(m + m) + n`, which we
would have had to repeat had we written the proof without `calc`:

-/
lemma two_mul_example2 (m n : ℕ) :
2 * m + n = m + n + m :=
  have h1 : 2 * m + n = (m + m) + n :=
  by rw [two_mul]
  have h2 : m + m + n = m + n + m :=
  by rw [Nat.add_right_comm]
  show _ from
  Eq.trans h1 h2
/-!
Notice that with `have`s, we also need to explicitly invoke `Eq.trans` and to give
names to the two intermediate steps.

-/