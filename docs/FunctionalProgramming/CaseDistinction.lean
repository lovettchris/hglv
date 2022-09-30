import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
/-!
## Case Distinction and Induction Tactics

The following tactics are useful when performing case distinctions, with or without
induction hypotheses.

**cases'**
```
  cases' term [with name₁ . . . nameₙ]
```
The `cases'` tactic performs a case distinction on the specified term. This gives
rise to as many sub-goals as there are constructors in the definition of the term’s
type. The tactic behaves roughly the same as `induction’` except that it does not
produce induction hypotheses and it eliminates impossible cases.

The optional names `name₁ . . . nameₙ` are used for any emerging variables or
hypotheses, to override the default names.

Note that the standard Lean tactic for case distinction is called `cases`. The
primed variant is provided by `Mathlib`. It is more user-friendly.
```
cases' hypothesis-of-the-form-l-equals-r
```
The `cases'` tactic can also be used on a hypothesis `h` of the form `l = r`. It matches
`r` against `l` and replaces all occurrences of the variables occurring in `r` with the
corresponding terms in `l` everywhere in the goal. The remaining hypothesis `l = l`
can be removed using `clear h` if desired. If `r` fails to match `l`, no sub-goals emerge;
the proof is complete.
```
cases' Classical.em (proposition) [with name₁ name₂]
```
The `cases'` tactic can also be used to perform a case distinction on a proposition.
Two cases emerge: one in which the proposition is true and one in which it is false.
The optional names `name₁` and `name₂` are used for hypotheses in the true and false
cases, respectively.


**case**
```
case name [: name₁ . . . nameₙ] => ...
```

The `case` tactic (with no s) can be used in tandem with `cases'` or `induction'` to
select a sub-goal corresponding to the constructor called `name` and focus on it.
The optional names `name₁ . . . nameₙ` are used for any emerging variables or
hypotheses, to override the default names.

You can lits multiple names separated by '|' to apply the same proof to
a number of case names.  `case tag₁ | tag₂ => tac`.
This is equivalent to `(case tag₁ => tac); (case tag₂ => tac)`.

-/
