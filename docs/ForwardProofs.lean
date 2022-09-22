import ForwardProofs.StructuredProofs
/-!
# Forward Proofs

Tactics are a backward proof mechanism. They start from the goal and break it down. Often it makes
sense to work in a forward fashion: to start with what we already know and proceed step by step
towards our goal. _Structured proofs_ are a style that supports this kind of reasoning. It can be
combined with the tactical style. Tactical proofs tend to be easier to write but harder to read; it
is, after all, easier to destruct things than to construct them. Most users combine the two styles,
using whichever seems the most appropriate for the situation. The higher readability of structured
proofs make them popular with some users, especially in mathematical circles.

Structured proofs are syntactic sugar sprinkled over Lean’s _proof terms_. They are built using
keywords such as `assume`, `have`, and `show` that mimic pen-and-paper proofs. All Lean proofs,
whether tactical or structured, are reduced internally to proof terms. We have seen some specimens
already, in Chapter 2: Given hypotheses `ha : a` and `hab : a → b`, the term `hab ha` is a proof
term for the proposition `b`, and we write `hab ha : b`. The names of lemmas and hypotheses, such as
`ha` and `hab`, are also proof terms. Pushing this idea further, given `hbc : b → c`, we can build
the proof term `hbc (hab ha)` for the proposition `c`. We can think of `hab` as a function that
converts a proof of `a` to a proof of `b`, and similarly for `hbc`.

Structured proofs are the default in Lean. They can be used outside tactic
mode (with no `by` keyword).

The concepts covered here are described in more detail in Chapters 2 to 4
of [Theorem Proving in Lean](.bib.md#1). [Nederpelt and Geuvers’s textbook](./bib.md#24) and
[Van Raamsdonk’s lecture notes](./bib.md#29) are other useful references.
-/