import Mathlib.Tactic.Basic

/-!
## The Curry–Howard Correspondence

You will likely have noticed that the same symbol `→` is used both for implication
(e.g., `false → true`) and as the type constructor of functions (e.g., `ℤ → ℕ`).
Similarly, ∀ is used both as a quantifier and to specify dependent types. Without
context, we cannot tell whether `a → b` refers to the type of a function with domain
`a` and codomain `b` or to the proposition “`a` implies `b`,” and similarly,
`∀x : a, b[x]` can denote a proposition or a dependent type.

It turns out that not only the two pairs of concepts look the same, they are the
same. This is called the _Curry–Howard correspondence_. It is also called the
_PAT principle_, where PAT is a double mnemonic:

> PAT = propositions as types&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;PAT = proofs as terms

Furthermore, because types are also terms, we also have that propositions are
terms. However, PAT is not a quadruple mnemonic (<span style="text-decoration:line-through">PAT = proofs as types</span>).

Haskell Curry and William Alvin Howard noticed that for some logics, propositions are isomorphic to
types, and proofs are isomorphic to terms. Hence, in dependent type theory, we _identify_ proofs with
terms as well as propositions with types, a considerable economy of concepts. The question “Is `H` a
proof of `P`?” becomes equivalent to “Does the term `H` have type `P`?” As a result, inside of Lean, there
is no proof checker, only a type checker.

Let us go through the dramatis personae one by one. We use the metavariables `σ`, `τ` for types;
`P`, `Q` for propositions; `t`, `u`, `x` for terms; and `h`, `G`, `H`, for proofs. Starting with
“propositions as types,” for types, we have the following:

1. `σ → τ` is the type of (total) functions from `σ` to `τ`.
2. `∀x : σ, τ[x]` is the dependent function type from `x : σ` to `τ[x]`.

In contrast, for propositions, we have the following:
1. `P → Q` can be read as “`P` implies `Q`,” or as the type of functions mapping proofs
of `P` to proofs of `Q`.
2. `∀x : σ, Q[x]` can be read as “for all `x, Q[x]`,” or as the type of functions
mapping values `x` of type `σ` to proofs of `Q[x]`.

Continuing with “proofs as terms,” for terms, we have the following:

1. A constant is a term.
2. A variable is a term.
3. `t u` is the application of function `t` to argument `u`.
4. `λ x => t[x]` is a function mapping `x` to `t[x]`.

In contrast, for proofs (i.e., proof terms), we have the following:

1. The name of a lemma or hypothesis is a proof.
2. `H t`, which instantiates the leading parameter or quantifier of proof `H`’s statement with term
   `t`, is a proof.
3. `H G`, which discharges the leading assumption of `H`’s statement with proof `G`, is a proof.
   This operation is called modus ponens.
4. `λ h : P => H[h]` is a proof of `P → Q`, assuming `H[h]` is a proof of `Q` for `h : P`.
5. `λ x : σ => H[x]` is a proof of `∀x : σ, Q[x]`, assuming `H[x]` is a proof of `Q[x]` for `x : σ`.

The last two cases are justified by the LAM' rule. In a structured proof, as opposed to a raw proof
term, we would write assume or fix instead of λ, and we would probably want to repeat the conclusion
using show for readability, as follows:

```lean
lemma case_4 (H : P → Q):
  P → Q :=
λ h : P =>
  show Q from
  H h

lemma case_5 :
∀ x : σ, Q x :=
λ x =>
  show Q x from
  H x
```
Some commands are provided in Lean under two different names but are really
the same as per the Curry–Howard correspondence. This is the case for
`axiom`.

There are also pairs with slightly different behavior, such as `def` and `lemma` or
`let` and `have`. The fundamental difference is this: When we define some function
or data, we care not only about the type but also about the body—the behavior. On
the other hand, once we have proved a lemma, the proof becomes _irrelevant_. All
that matters is that there is a proof. We will return to the topic of proof irrelevance
in Chapter 11.

The following correspondence table summarizes the differences between tactical proofs, structured
proofs, and raw proof terms:

| Tactical proofs | Structured proofs | Raw proof terms |
|-----------------|-------------------|-----------------|
| `intro x`         | `λ x =>`          | `λ x =>`          |
| `intro h`         | `λ h =>`            | `λ h =>`          |
| `have k := H`     | `have k := H`       | `(λ k => . . .) H`|
| `let x := t`      | `let x := t`        | `let x := t`      |
| `exact (H : P)`   | `show P from H`     | `H : P`          |
| `calc . . .`      | `calc . . .`        | `calc . . .`      |

-- BUGBUG: I made some changes to this table, it needs close review.

The terminology of dependent type theory can be quite confusing, because some words have a narrow
and a broad sense. The following diagram captures the various meanings of important words:

-- BUGBUG nice latex chart goes here...

According to the broad senses, any expression is a term, any expression that may occur on the
right-hand side of a typing judgment is a type, and any expression that may occur on the right-hand
side of a typing judgment with a type on its left-hand side is a universe. This is consistent with the
reading of `t : u` as “`t` has type `u`” and the notion that universes are types of types.


-/