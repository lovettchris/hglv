import Mathlib.Tactic.Basic

/-!
## Forward Reasoning with Tactics

Many users, including most of the mathematicians that form the majority of Lean’s user community,
prefer the tactic mode. But even in tactic mode, it can be useful to reason in a forward fashion,
mixing forward and backward reasoning steps.

The structured proof commands `have`, `let`, and `calc` are also available as tactics,
making this possible.

The following example demonstrates the `have` and `let` tactics on a lemma we
have seen several times already:
-/
lemma prop_comp3 (a b c : Prop) (hab : a → b) (hbc : b → c) :
a → c := by
  intro ha
  have hb : b :=
  hab ha
  let c' := c
  have hc : c' :=
  hbc hb
  exact hc
/-!
**have**
```
have [[name :] proposition] :=
    proof
```
The `have` tactic lets us state and prove an intermediate lemma in tactic mode.
Afterwards, the lemma is available as a hypothesis in the goal state.

**let**
```
let name [: type] := term
```
The `let` tactic lets us introduce a local definition in tactic mode. Afterwards, the
defined symbol and its definition are available in the goal state.

**calc**

```lean
calc
  term₀ op₁ term₁ : proof1
  _     op₂ term₂ : proof₂
  ...
  _     opₙ termₙ : proofₙ
```

The `calc` tactic lets us enter a [calculational proof](./CalculationProofs.lean.md) in tactic mode.
The tactic has the same syntax as the structured proof command of the same name. We can regard
`apply calc . . . `, where `calc` is a tactic, as an alias for `apply (exact calc . . .)`,
where `calc` is the structured proof command described above.

-/