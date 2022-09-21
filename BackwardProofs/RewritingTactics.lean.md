<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-wsp"><span class="alectryon-token"><span class="kn">import</span> Mathlib.Tactic.Basic</span></span></pre>

## Rewriting Tactics

The rewriting tactic `rw` and its relative `simp` replace equals for equals. Unlike `cc`,
they use equations as left-to-right rewrite rules. By default, they operate on the
goal’s target, but they can also be used to rewrite hypotheses specified using the
`at` keyword:

| at | description |
|----|-------------|
|`at ⊢` | applies to the target (the default) |
| `at h₁ . . . hₙ` | applies to the specified hypotheses |
| `at *` | applies to all hypotheses and the target |

**rw**
```
rw lemma-or-constant [at position]
```

The rw tactic applies a single equation as a left-to-right rewrite rule. It searches for the first
subterm that matches the rule’s left-hand side; once found, all occurrences of that subterm are
replaced by the right-hand side of the rule. If the rule contains variables, these are instantiated
as necessary. To apply a lemma as a right-to-left rewrite rule, put a short left arrow (`←`) in front
of the lemma’s name.

Given the lemma `l : ∀x, g x = f x` and the goal `⊢ h (f a) (g b) (g c)`, the
tactic `rw l` produces the subgoal `⊢ h (f a) (f b) (g c)`, whereas `rw ←l` produces the subgoal
`⊢ h (g a) (g b) (g c)`.

Instead of a lemma, we can also specify the name of a constant. This will attempt to
use one of the constant’s defining equations as rewrite rules. For technical reasons, this does not
work with not (`¬`), and we must use `rw not_def` instead.

**simp**
```
simp [at position]
```

The simp tactic applies a standard set of rewrite rules, called the _simp_ set, exhaustively. The simp
set can be extended by putting the `@[simp]` attribute on lemmas. Unlike `rw`, `simp` can rewrite terms
containing bound variables (e.g., occurrences of `x` in the body of `λx => . . .`, `∀x, . . .`, or
`∃x, . . .`).

```
simp [lemma-or-constant₁, . . . , lemma-or-constantₙ] [at position]
```
For the above `simp` variant, the specified lemmas are temporarily added to the simp set. In the
lemma list, an asterisk (`*`) can be use to represent all hypotheses. The minus sign (`-`) in front
of a lemma name temporarily removes the lemma from the simp set. A powerful incantation that both
simplifies the hypotheses and uses the result to simplify the goal’s target is `simp [*] at *`.

Given the `lemma l : ∀x, g x = f x` and the goal `⊢ h (f a) (g b) (g c)`, the tactic `simp [l]`
produces the subgoal `⊢ h (f a) (f b) (f c)`, where both `g b` and `g c` have been rewritten. Instead of a
lemma, we can also specify the name of a constant. This temporarily adds the constant’s defining
equations to the simp set.

To find out what simp does, you can enable tracing via the command
```lean
set_option trace.simplify.rewrite true              -- this was lean3
set_option trace.Meta.Tactic.simp.rewrite true      -- BUGBUG: is this the correct lean4 option?
```


