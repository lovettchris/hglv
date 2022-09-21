<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-wsp"><span class="alectryon-token"><span class="kn">import</span> Mathlib.Tactic.Basic</span></span></pre>

## Induction Tactic

**induction'**

```
induction’ term [with name₁ . . . nameₙ]
```

The `induction’` tactic performs structural induction on the specified term. This gives rise to as
many subgoals as there are constructors in the definition of the term’s type. Induction hypotheses
are available as hypotheses in the subgoals corresponding to recursive constructors (e.g., `Nat.succ`
or `List.cons`). The optional names `name₁, . . . , nameₙ` are used for any emerging variables or
hypotheses. Note that the standard Lean tactic for structural induction is called `induction`. The
primed variant is provided by `mathlib`. It is more user-friendly and is the only one we will use.



