import Mathlib.Tactic.Basic
import Mathlib.Init.Data.Nat.Basic

/-!
## Introductory Examples

Unless you have been exposed to Prolog or logic programming, you will probably wonder what inductive
predicates are and why they are useful. We start by reviewing three examples that demonstrate the
variety of uses: even numbers, tennis games, and the reflexive transitive closure.

### Even Numbers

Mathematicians often define sets as the smallest set that meets some criteria.
Consider this definition:

The set `E` of _even natural numbers_ is defined as the smallest set `S`
closed under the following rules:

1. 0 ∈ S;
2. for every k ∈ ℕ, if k ∈ S, then k + 2 ∈ S.

Such a set exists by the Knaster–Tarski theorem.

(The last sentence is often left implicit.) It is easy to convince ourselves that `E`
contains all the even numbers and only those. Let us put on our mathematician’s
hat and prove that 4 is even:

- By rule (1), we have 0 ∈ E.
- Hence, by rule (2) (with k := 0), we have 2 ∈ E.
- Thus, by rule (2) (with k := 2), we have 4 ∈ E, as desired. <span class="qed"></span>

By contrast, computer scientists might use a formal system consisting of two
derivation rules to specify the same set:

\\( \cfrac
      {}
      {0 ∈ E}
      {\large{Z}}{\normalsize{ERO}}  \quad \quad
    \cfrac
      {k ∈ E}
      {k + 2 ∈ E}
      {\large{A}}{\normalsize{DD}}{\large{Z}}{\normalsize{ERO}}  \\)

A proof is then a derivation tree:

\\( \cfrac
      { \cfrac
        { \cfrac
          {}
          {0 ∈ E}
          {\large{Z}}{\normalsize{ERO}}
        }
        {2 ∈ E}
        {\large{A}}{\normalsize{DD}}{\large{Z}}{\normalsize{ERO₀}}
      }
      {4 ∈ E}
      {\large{A}}{\normalsize{DD}}{\large{Z}}{\normalsize{ERO₁}}  \\)


The proof is forward if we read it downwards and backward if we read it upwards.
Inductive predicates are the logicians’ way to achieve the same result. In Lean,
instead of a set, we would define a characteristic predicate inductively:

-/

inductive Even : ℕ → Prop
| zero : Even 0
| add_two : ∀k : ℕ, Even k → Even (k + 2)
/-!
This should look familiar. We have used the exact same syntax, except with `Type`
instead of `Prop`, to define inductive types.
Inductive types and inductive predicates are the same mechanism in Lean.

The command above defines a unary predicate even as well as two introduction rules
`Even.zero` and `Even.add_two` that can be used to prove goals of the form
`⊢ Even . . . .` Recall that an introduction rule for a symbol (e.g., `Even`) is
a lemma whose conclusion contains that symbol (Section 3.3). By
the PAT principle, `Even n` can be viewed as a dependent inductive type like
`Vec α n` (Section 4.10), and `Even.zero` and `Even.add_two` as constructors like
`Vec.nil` and `Vec.cons`.

If we translate the Lean definition back into English, we get something similar
to the Knaster–Tarski-style definition above:

The following clauses define the even numbers.

1. 0 is even;
2. any number of the form k + 2 is even, if k is even.

Any other number is not even.

It is worth nothing that inductively defined symbols have no definition. Thus, we cannot unfold
their definition using `simp`, any more than we can unfold the definition of an inductive type such as
`List`. The only reasoning principles available are introduction and elimination.

As a warm-up exercise, here is a proof of even 4:
-/
lemma even_4 : Even 4 :=
  have even_0 : Even 0 := Even.zero
  have even_2 : Even 2 := Even.add_two _ even_0
  show Even 4 from Even.add_two _ even_2
/-!
For example, the proof term `Even.add_two _ even_0` has type `Even (0 + 2)`, which
is syntactically equal to `Even 2` up to computation and hence equal from the type
checker’s point of view. The underscore stands for `0`.

Thanks to the “no junk” guarantee of inductive definitions, `Even.zero` and `Even.add_two` are the only
two ways to construct proofs of `⊢ even . . . .` By inspection of the conclusions `Even 0` and `Even (k + 2)`,
we see that there is no danger of ever proving that 1 is `Even`.

> We could cheat and add an axiom stating `Even 1`, but this would be inconsistent. Alternatively,
we could add an assumption `Even 1` to our lemma and use it to prove `Even 1`, but this would be
tautological and hence pointless.

Another way to view the inductive definition above is as follows: The first line
introduces a predicate, whereas the second and third lines introduce axioms we
want the predicate to satisfy. Accordingly, we could have written
-/
variable (Even₂ : ℕ → Prop)
axiom Even₂.zero : Even₂ 0
axiom Even₂.add_two : ∀k : ℕ, Even₂ k → Even₂ (k + 2)
/-!
replacing `inductive` by `variable` and `|` by `axiom`. But this axiomatic version, apart from being
dangerous, does not give us any information about when `Even` is false. We cannot use it to prove `¬
Even 1` or `¬ Even 17`. For all we know, `Even` could be true for all natural numbers. In contrast,
the inductive definition guarantees that we obtain the least (i.e., the most false) predicate that
satisfies the introduction rules `Even.zero` and `Even.add_two`, and provides elimination and
induction principles that allow us to prove `¬ Even 1`, `¬ Even 17`, or `¬ Even (2 * n + 1)`.

Why should we bother with inductive predicates when we can define recursive functions? Indeed, the
following definition is perfectly legitimate:
-/
def Even₃ : ℕ → Bool
| 0 =>  true
| 1 => false
| (k + 2) => Even₃ k
/-!
Each style has its strengths and weaknesses. The recursive version forces us to specify a false case
(the second equation), and it forces us to worry about termination. On the other hand, because it is
equational and computational, it works well with `rfl`, `simp`, `#reduce`, and `#eval`. The inductive
version is arguably more abstract and elegant. Each introduction rule is stated independently. We
can add or remove rules without having to think about termination or executability.

Yet another way to define even is as a nonrecursive definition, using the modulo operator (`%`):
-/
def Even₄ (k : ℕ) : Bool := k % 2 = 0
/-!
Mathematicians would likely prefer this version. But the inductive version is a
convenient “Hello, World!” example that resembles many realistic inductive definitions.
It might be a toy, but it is a useful toy.

### Tennis Games

Transition systems consists of transition rules that connect a “before” and an “after” state. As a
specimen of a transition system, we consider the possible transitions in a game of tennis, starting
from `0–0` (“Love all”). Tennis games are also a toy, but in Chapter 8, we will define the semantics
of an imperative programming language as a transition system in a similar style.

The scoring rules for tennis from the International Tennis Federation’s Rules of Tennis are
reproduced below.

A standard game is scored as follows with the server’s score being called first:

| Point | Score |
|-------|-------|
| No point      | “Love”|
| First point   | “15”  |
| Second point  | “30”  |
| Third point   | “40”  |
| Fourth point  | “Game”|

except that if each player/team has won three points, the score is “Deuce.” After “Deuce,” the score
is “Advantage” for the player/team who wins the next point. If that same player/team also wins the
next point, that player/team wins the “Game”; if the opposing player/team wins the next point, the
score is again “Deuce.” A player/team needs to win two consecutive points immediately after “Deuce”
to win the “Game.”

We first define an inductive type to represent scores:
-/
inductive Score : Type
| vs : ℕ → ℕ → Score
| adv_srv : Score
| adv_rcv : Score
| game_srv : Score
| game_rcv : Score
deriving Repr
/-!
A score such as `30–15` is represented as `Score.vs 30 15`, abbreviated to `30–15`. We ignore some
of the most frivolous aspects of the scoring rules, writing `0` for “Love” and `40–40` for “Deuce.”
If we really cared, we could introduce aliases such as `def love : ℕ := score.vs 0 0`.

The next stage is to introduce a binary predicate `Step` that determines whether a transition is
possible:
-/

-- create convenient operator for constructing a Score.vs by writing `(n-m)`.
infixr:10 (priority := high) " - "  => Score.vs

inductive Step : Score → Score → Prop
| srv_0_15 : ∀n, Step (0-n) (15-n)
| srv_15_30 : ∀n, Step (15-n) (30-n)
| srv_30_40 : ∀n, Step (30-n) (40-n)
| srv_40_game : ∀n, n < 40 → Step (40-n) Score.game_srv
| srv_40_adv : Step (40-40) Score.adv_srv
| srv_adv_40 : Step Score.adv_srv (40-40)
| srv_adv_game : Step Score.adv_srv (40-40)
| rcv_0_15 : ∀n, Step (n-0) (n-15)
| rcv_15_30 : ∀n, Step (n-15) (n-30)
| rcv_30_40 : ∀n, Step (n-30) (n-40)
| rcv_40_game : ∀n, n < 40 → Step (n-40) Score.game_rcv
| rcv_40_adv : Step (40-40) Score.adv_rcv
| rcv_adv_40 : Step Score.adv_rcv (40-40)
| rcv_adv_game : Step Score.adv_rcv Score.game_rcv
/-!
> The little infix operator we defined here simply makes it easier to construct a score
so you can write `0-15` instead of `Score.vs 0 15`.

Let `s ⇒ t` abbreviate `Step s t`. A game is a chain `s₀ ⇒ s₁ ⇒ s₂ ⇒ · · · ⇒ sₙ` where
`s₀ = 0–0` and no transition is possible from `sₙ`. The `Step` predicate allows nonsensical
transitions such as `15–99 ⇒ 30–99` using `n=99` in `| srv_15_30 : ∀n, Step (15-n) (30-n)`,
but since the `Score 15–99` cannot be reached from `0–0`, these transitions are harmless.

Equipped with a formal definition, we can ask, and formally answer, questions such as: Do games have
a maximal length? How many different final scores are possible? Is the score 15–99 reachable from
“Love all”? And can the score ever return to 0–0 after at least one step?
Let us use Lean to disprove the last claim:
-/
lemma no_step_to_0_0 (s : Score) :
¬ Step s (0-0) := by
  intro h
  cases h
/-!
The diagram below summarizes which scores are reachable from which scores:

![diagram](tennis.svg)

### Reflexive Transitive Closure

Are there any convincing non-toy applications of inductive predicates? The answer
is yes. Consider the reflexive transitive closure _r*_ of a binary relation _r_.
The star (`*`) operator is often defined as a formal system:


\\( \cfrac
      {(a,b) ∈ r}
      {(a,b) ∈ r*)}
      {\large{B}}{\normalsize{ASE}}  \quad \quad
    \cfrac
      {}
      {(a,a) ∈ r*}
      {\large{R}}{\normalsize{EFL}}  \quad \quad
    \cfrac
      {(a,b) ∈ r*) \quad (b,c) ∈ r*)}
      {(a,c) ∈ r*}
      {\large{T}}{\normalsize{RANS}}  \quad \quad  \\)

These rules define _r*_ as the smallest relation that contains _r_ (by BASE) and that is reflexive
(by REFL) and transitive (by TRANS). If we wanted to define the transitive closure _r*_ instead, we
would simply omit the REFL rule. If we wanted the reflexive symmetric closure, we would replace the
TRANS rule by a SYMM rule. With a formal system, we simply declare the properties we want to be
true, without giving a thought to termination or executability.

It is straightforward to translate the above derivation rules into introduction rules of an
inductive predicate:
-/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
| base (a b : α) : r a b → Star r a b
| refl (a : α) : Star r a a
| trans (a b : α) : ∀ c : α, Star r a b → Star r b c → Star r a c
/-!
We represent relations as binary predicates rather than sets of pairs, writing `r a b`
for `(a, b) ∈ r`. The reflexive transitive closure of `r` is written `Star r`. Inside the
definition, `r` is omitted since it is declared as a parameter, on the left of a colon
(`:`). Notice that `a`, `b`, and `c` are declared as parameters of the introduction rules,
on the left of the colons. We could also have written
```
| base : ∀a b : α, r a b → Star a b
```
or at the other extreme
```
| base (a b : α) (hab : r a b) : star a b
```
and similarly for `Star.refl` and `Star.trans`. All these forms are logically and
operationally equivalent.

The general format of inductive predicates is as follows:
```lean
inductive predicate-name (params₁ : type₁) . . . (paramsₖ : typeₖ) :
    typeₖ₊₁ → · · · → typeₗ → Prop
  | rule-name₁ (params₁₁ : type₁₁) . . . (params₁ₘ : type₁ₘ) : proposition₁
  ...
  | rule-nameₙ (paramsₙ₁ : typen₁) . . . (paramsₙₘ : typeₙₘ) : propositionₙ
```

where the conclusion of each propositionⱼ must be an application of the defined predicate
predicate-name to some arguments. These arguments may be arbitrary terms; they do not need to be
constructor patterns. We can also use curly braces `{ }` instead of parentheses `( )` if we wanted
to make the arguments corresponding to the parameters implicit.

The above definition of `Star` is truly elegant. If you still doubt this, try implementing it as a
recursive function:
```lean
def star_rec {α : Type} (r : α → α → Bool) : α → α → Bool :=
```
To summarize, each introduction rule of an inductive predicate `p` consists of the following
components:

- an application of `p` to some arguments, forming a _pattern_;
- zero or more conditions that must be fulfilled, which may apply `p` recursively;
- variables that may appear in the pattern and the conditions.

Thus, for rule `Star.base`, the pattern is `Star r a b`, the condition is `r a b`, and the
variables are `a` and `b`.

### A Nonexample

Not all inductive definitions admit a least solution. The simplest nonexample is
```lean
-- fails
inductive illegal₂ : Prop
| intro : ¬ illegal₂ → illegal₂
```
If Lean accepted this definition, we could use it to prove the equivalence illegal₂
↔ ¬ illegal₂, from which we could easily derive false. Fortunately, Lean rejects
the definition:
```
(kernel) arg #1 of 'illegal₂.intro' has a non positive occurrence of the datatypes being declared
```
The nonpositive occurrence it complains about is the occurrence of illegal2 under a negation.
Mathematicians would reject the definition on the ground that the monotonicity condition of the
Knaster–Tarski theorem is not satisfied.
-/