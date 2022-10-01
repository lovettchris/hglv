import InductivePredicates.IntroductoryExamples
import InductivePredicates.LogicalSymbols
/-!
# Inductive Predicates

Inductive predicates, or inductively defined propositions, are a convenient way to
specify functions of type `· · · → Prop`. They are reminiscent of formal systems and
of Prolog-style logic programming. But Lean offers a much stronger logic than
Prolog, so we need to do some work to establish theorems instead of just running
the Prolog interpreter. A possible view of Lean:
```
Lean = functional programming + logic programming + more logic
```
-/