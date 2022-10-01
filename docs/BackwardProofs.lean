import BackwardProofs.TacticMode
import BackwardProofs.BasicTactics
import BackwardProofs.ConnectivesAndQuantifiers
import BackwardProofs.Equality
import BackwardProofs.RewritingTactics
-- import BackwardProofs.Induction
import BackwardProofs.InductionTactic
import BackwardProofs.CleanupTactics
import BackwardProofs.Summary

/-!
# Backward Proofs

In this chapter, we see how to prove Lean lemmas using tactics, and we review the most important
Lean tactics. A _tactic_ is a procedure that operates on the goal— the proposition to prove—and
either fully proves it or produces new subgoals (or fails). When we state a lemma, the lemma
statement is the initial goal. A proof is complete once all (sub)goals have been eliminated using
suitable tactics. The tactics described here are documented in more detail in Chapter 5 of [Theorem
Proving in Lean](./bib.md#1) and Chapter 6 of [The Lean Reference Manual](./bib.md/#3). Tactics
are a backward proof mechanism. They start from the goal and work backwards towards the already
proved lemmas. Consider the lemmas `a, a → b`, and `b → c` and the goal `⊢ c`. An informal backward
proof is as follow:

- To prove `c`, by `b → c` it suffices to prove `b`.
- To prove `b`, by `a → b` it suffices to prove `a`.
- To prove `a`, we use `a`.  <span class="qed"></span>

The telltale sign of a backward proof is the phrase “it suffices to.” Notice how we
progress from one goal to another ( `⊢ c`, `⊢ b`, `⊢ a`) until no goal is left to prove. By
contrast, a forward proof would start from the lemma `a` and progress, one theorem
at a time, towards the desired theorem `c`:

- From `a` and `a → b`, we have `b`.
- From `b` and `b → c`, we have `c`, as desired. <span class="qed"></span>

A forward proof only manipulates theorems, not goals. We will study forward
proofs more deeply in Chapter 3.
-/
