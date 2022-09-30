import Mathlib.Tactic.Basic
/-!
## Summary of New Lean Constructs

**Declaration**

| declaration | description |
| :--- | :--- |
| structure | introduces a structure type and its selectors |
| class | declares a structure type as a type class |
| instance | registers a structure value as a type class instance |

**Term Language**

| term | description |
| :--- | :--- |
| `if ... then ... else ...` | performs a case distinction on a decidable proposition |
 `match ... with ...` | performs pattern matching |

**Tactics**

| tactic | description |
| :--- | :--- |
| `case` | focuses on a sub-goal and names its variables and hypotheses |
| `cases'` | performs a case distinction |
-/