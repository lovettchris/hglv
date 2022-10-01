import Mathlib.Tactic.Basic
import Mathlib.Init.Data.Nat.Basic
namespace hidden
/-!
## Logical Symbols

Although `Even` is the first openly inductive predicate in this guide, the earlier chapters already
presented other inductive predicates clandestinely. The very first of these is equality (`=`),
introduced in Chapter 1, followed by the logical symbols `∧`, `∨`, `↔`, `∃`, `true`, and `false`. Their
definitions are worth studying closely
-/

inductive And (a b : Prop) : Prop where
| intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
| inl : a → Or a b
| inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
| intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} (p : α → Prop) : Prop where
| intro : ∀a : α, p a → Exists p

inductive True : Prop where
| intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
| refl : ∀a : α, Eq a a
/-!
(Strictly speaking, in Lean, some of the above definitions are actually structures and not inductive
predicates, but the difference is unimportant: Structures are essentially single-constructor
inductive predicates with some syntactic sugar.)

The traditional notations `∃x : α, p` and `x = y` are syntactic sugar for `Exists (λx : α => p)` and
`Eq x y`. Notice how `λ` acts as an all-purpose binder. Notice also that there is no constructor for
false. There are no proofs of `False`, just like there is no proof of `Even 1`.

> With inductive predicates, we only state the rules we want to be true.

The symbol `∀`, including its special case `→`, is built directly into the logic and is not defined as
inductive predicates. Nor does it have explicit introduction or elimination rules. The introduction
principle is `λ-expression λx => _`, and the elimination principle is function application `_ u`.

-- BUGBUG I assume this comment about `∀` is still true in Lean 4?

As for any inductive predicates, only the introduction rules are specified. The elimination rules
presented in [Sections 2.3](../BackwardProofs/ConnectivesAndQuantifiers.lean.md) and
[Section 2.4](../BackwardProofs/Equality.lean.md) must be derived manually.

-/