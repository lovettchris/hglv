import Mathlib.Tactic.Basic

/-!
## Tactic Mode

In Chapter 1, whenever a proof was required, we simply put a `sorry` placeholder.
For a tactical proof, we will now write `by` to enter tactic mode. In this mode,
we can apply a sequence of tactics, separated by semicolons or new lines.

Tactics operate on the goal, which consists of the proposition `Q` that we want to
prove and of a local context `C`. The local context consists of variable declarations
of the form `c : τ` and hypotheses of the form `h : P`. We write `C ⊢ Q` to denote a
goal, where `C` is a list of variables and hypotheses and `Q` is the goal’s target.

To make things more concrete, consider the following Lean example:

-/

lemma fst_of_two_props :
  ∀ a b : Prop, a → b → a := by
  intros a b
  intros ha hb
  apply ha

/-!
Note that the implication arrow `→` is right-associative; this means that `a → b → a`
is the same as `a → (b → a)`. Intuitively speaking, it has the meaning “`a` implies
that `b` implies `a`,” or equivalently “`a` and `b` imply `a`.” In the example, three tactics
are invoked, each on its own line. Let us trace their behavior:

1. Initially, the goal is simply the lemma statement:
    ```lean
    ⊢ ∀ a b : Prop, a → b → a
    ```

2.  The `intros a b` tactic tells Lean to fix two free variables, `a` and `b`,
corresponding to the two bound variables of the same names. Offen, we name the free
variables after the bound variables. The tactic mimics how mathematicians
work on paper: To prove a ∀-quantified proposition, it suffices to prove it for
some arbitrary but fixed value of the bound variable. The goal becomes
    ```lean
    a b : Prop ⊢ a → b → a
    ```

3. The `intros ha hb` tactic tells Lean to move the assumptions `a` and `b` to the
local context and to call these hypotheses `ha` and `hb`. Indeed, to prove an
implication, it suffices to take its left-hand side as hypothesis and prove its
right-hand side. The goal becomes
    ```lean
    a b : Prop, ha : a, hb : b ⊢ a
    ```

4. The `apply ha` tactic tells Lean to match the hypothesis `a`, called `ha`, against
the goal `⊢ a`. Since `a` is syntactically equal to `a`, we have a match, and this
completes the proof.

Informally, in a style reminiscent of pen-and-paper mathematics, we could
write the proof as follows:

- Let `a` and `b` be propositions.
- Assume `(ha) a` and `(hb) b` are true.
- To prove `a`, we use hypothesis `ha`.

(Mathematicians would probably use numeric tags such as (1) and (2) for the hypotheses
instead of informative names.)

Going back to the Lean proof, we can avoid the `intros` invocations by declaring
the variables and hypotheses as parameters of the lemma, as follows:
-/
lemma fst_of_two_props₂ (a b : Prop) (ha : a) (hb : b) :
  a := by
  apply ha
/-!
Here is an example with multiple `apply`s in sequence:
-/
lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c := by
  intro ha
  apply hbc
  apply hab
  apply ha
/-!
Putting on our mathematician’s hat, we can verbalize the last proof as follows:

- Assume `(ha) a` is true.
- To prove `c`, by hypothesis `hbc` it suffices to prove `b`.
- To prove `b`, by hypothesis `hab` it suffices to prove `a`.
- To prove `a`, we use hypothesis `ha`.
-/