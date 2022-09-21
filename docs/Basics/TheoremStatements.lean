import Basics.FunctionDefinitions
/-!
## Theorem Statements

What makes Lean a proof assistant and not only a programming language is that we can state theorems
about the types and constants we define and prove that they hold. We will use the terms theorem,
lemma, corollary, fact, property, and true statement more or less interchangeably. Similarly,
propositions, logical formulas, and statements will all mean the same.

In Lean, propositions are simply terms of type `Prop`. This stands in contrast with most
descriptions of first-order logic, where terms and formulas are separate syntactic entities. A
proposition that can be proved is called a theorem (or lemma, corollary, etc.); otherwise it is a
nontheorem or false statement. Mathematicians sometimes use the term “proposition” as a synonym for
theorem (e.g., “Proposition 3.14”), but in formal logic propositions can also be false. Here are
examples of true statements that can be made about the addition, multiplication, and list reversal
operations defined in [Function Definitions](./FunctionDefinitions.lean.md):

-/
theorem add_comm (m n : Nat) :
  add m n = add n m :=
  sorry

theorem add_assoc (l m n : Nat) :
  add (add l m) n = add l (add m n) :=
  sorry

theorem mul_comm (m n : Nat) :
  mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : Nat) :
  mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : Nat) :
  mul l (add m n) = add (mul l m) (mul l n) :=
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
  reverse (reverse xs) = xs :=
  sorry
/-!
The general format is
```lean
theorem name (params1 : type1) . . . (paramsm : typem) :
  statement :=
  proof
```
The `:=` symbol separates the theorem’s statement and its proof. The syntax of theorem is very
similar to that of a `def` command without pattern matching, with `statement` instead of `type` and
`proof` instead of `result`. In the examples above, we put the marker `sorry` as a placeholder for
the actual proof. The marker is quite literally an apology to future readers and to Lean for the
absence of a proof. It is also a reason to _worry_, until we manage to eliminate it. In Chapters 2
and 3, we will see how to achieve this.

The intuitive semantic of a theorem command with a `sorry` proof is, “This proposition should be
provable, but I have not carried out the proof yet—sorry.” Sometimes, we want to express a related
idea, namely, “Let us assume this proposition holds.” Lean provides the axiom command for this,
which is often used in conjunction with constant(s). For example:
-/
axiom a_less_b (a b : ℤ) : a < b

/-!
Here we have no information about a and b beyond their type. The axiom specifies the desired
property about them. The general format of the command is
```lean
axiom name (params₁ : type₁) . . . (paramsₘ : typeₘ) :
  statement
```
Axioms are dangerous, because they rapidly can lead to an inconsistent logic, in which we can derive
false. For example, if we added a second axiom stating that `a = b`, we could easily derive `b < b`,
from which we could derive `false` is true. The history of interactive theorem proving is paved with
inconsistent axioms. An anecdote among many: At the 2020 edition of the Certified Programs and
Proofs (CPP) conference, a submitted paper was rejected due to a flawed axiom, from which one of the
peer reviewers derived `false`. Therefore, we will generally avoid axioms, preferring the benign
combination of `def` and `theorem` to the more dangerous `axiom`.
-/