## Summary of New Lean Constructs

At the end of this and most other chapters, we include a brief summary of the constructs introduced
in the chapter. Some syntaxes have multiple meanings, which will be introduced gradually. We refer
to [The Lean Reference Manual](../bib.md#3), the [Theorem Proving in Lean](../bib.md#1) tutorial, and
the [mathlib documentation](https://leanprover-community.github.io/mathlib_docs/) for details.

**Diagnosis Commands**

| Command | Description |
| --- | --- |
| #check   | checks and prints type of a term |                 |
| #eval    | executes a term using an optimized interpreter     |
| #print   | prints the definition of a constant                |
| #reduce  | executes a term using Lean’s inference kernel      |


**Declarations**


| Declaration | Description |
| --- | --- |
| axiom           | states an axiom                           |
| def             | defines a new constant                    |
| inductive       | introduces a type and its constructors    |
| theorem         | states a theorem and its proof            |
| namespace . . . | end collects declarations in a named scope  |


**Proof Commands**

| Command | Description |
| --- | --- |
| sorry   | stands for a missing proof or definition


TODO : need to review closely how I removed "contants" from this chapter,
since we are generally hiding that term in Lean 4.  I instead jumped straight
to "def".
