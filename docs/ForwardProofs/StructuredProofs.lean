import Mathlib.Tactic.Basic

/-!
## Structured Proofs

As a first example, consider the following structured proof:
-/
lemma t1 : ∀ a b : Prop, a → b → a :=
  fun {a b : Prop} (ha : a) (hb : b) =>
  show a from ha

/-!
Each variable bound by a ∀-quantifier and each assumption of an implication is introduced explicitly
in the proof using a lambda function with parameters. Several variables or hypotheses can be introduced
simultaneously. We will often omit the types of variables, especially when they can be guessed from
their names; however, we will usually spell out the propositions and put them one per line, to
increase readability—which is, after all, one of the main potential advantages of the structured
style. The `show . . . from` command at the end repeats the proposition to prove, for the sake of
readability, and gives the proof after the keyword `from`. The goal at this point is
`a b : Prop, ha : a, hb : b ⊢ a`.

Informally, we could write the proof as follows:

- Given some propositions `a` and `b`.
- And given `(ha) a` and `(hb) b` are true.
- We must show `a`. This follows trivially from `ha`.<span class="qed"></span>

Some authors would insert some qualifiers such as “arbitrary but fixed” in front
of “propositions,” especially in textbooks for first-year bachelor students, or they
would write “Let `a` and `b` be some propositions.” All these variants are equivalent.
And instead of “∎” some authors would write “QED” to conclude the proof.

The Lean proof above is atypical in that the goal’s target appears among the hypotheses. Usually, we
must perform some intermediate reasoning steps, essentially of the form “from such-and-such, we have
so-and-so.” In Lean, each intermediate step takes the form of a `have` command, as in the following
example:

-/
lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
  fun (ha : a) =>
  have hb : b :=
  hab ha
  have hc : c :=
  hbc hb
  show c from
  hc
/-!
Informally:

- Assume `(ha) a` is true.
- From `ha` and `hab`, we have `(hb) b`.
- From `hb` and `hbc`, we have `(hc) c`.
- We must show `c`. This follows trivially from `hc`.

Notice that this is a forward proof: It progresses one theorem at a time from the hypothesis `a` to
the desired theorem `c`.

In general, the above proof skeleton simply repeats the lemma’s statement. In between, as many
`have` commands as desired may appear, depending on how detailed we want the argument to be. Details
can increase readability, but providing too many details can overwhelm even the most persistent
reader.

The `have` command has a similar syntax to `lemma` but appears inside a structured proof.
We can think of a `have` as a definition. In `have hb : b := hab ha`, the
right-hand side `hab ha` is a proof term for `b`, and the left-hand side `hb` is defined
as a synonym for that proof term. From that point on, `hb` and `hab ha` can be used
interchangeably. Since `hb` and `hc` are used only once and their proofs are very
short, experts would tend to inline their proofs, replacing `hc` by `hbc hb` and `hb` by
`hab ha`, yielding

-/
lemma prop_comp₂ (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
fun (ha : a) =>
show c from
  hbc (hab ha)
/-!

-- BUGBUG : delete the following?

A typical structured proof has the following fix–assume–have–show format:
```lean
lemma l :
∀(c1 : σ1) . . . (cl : σl), P1 → · · · → Pm → R :=
fix (c1 : σ1) . . . (cl : σl),
assume h1 : P1,
...
assume hm : Pm,
have k1 : Q1 :=
. . .,
...
have kn : Qn :=
. . .,
show R, from
. . .
```
-/


