import Mathlib.Tactic.Basic

/-!
## Cleanup Tactics

The following tactics help us clean up the goal by allowing us to give more meaningful names to
variables or hypotheses or to remove useless hypotheses. We did not need them so far, but they can
be helpful during proof exploration.

**rename**
```
rename variable-or-hypothesis new-name
```

The rename tactic changes the name of a variable or hypothesis.

**clear**
```
clear variable-or-hypothesis₁ . . . variable-or-hypothesisₙ
```

The clear tactic removes the specified variables and hypotheses, as long as they
are not used anywhere else in the goal.

-/