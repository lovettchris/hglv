import Mathlib.Tactic.Basic
/-!
## Summary of New Lean Constructs

**Proof Commands**

| command | description |
| :--- | :--- |
| λ x =>             |  introduces assumptions            |
| calc               |  combines proofs by transitivity   |
| have               |  states an intermediate lemma      |
| let . . .          |  introduces a local definition     |
| show . . .  from   |  states the target                 |

**Tactics**

| tactic | description |
| :--- | :--- |
| calc | combines proofs by transitivity |
| have | states an intermediate lemma |
| let  | introduces a local definition |
| case | handles a inductive case |

-/