/-!
# Definitions and Statements

We start our journey by studying the basics of Lean, without carrying out any
proofs yet. We review how to define new types and functions and how to state
their expected properties as lemmas.

Lean’s logical foundation is a rich formalism called the calculus of inductive
constructions, which supports dependent types. In this chapter, we restrict our
attention to its simply (i.e., nondependently) typed fragment. It is inspired by
the λ-calculus and resembles typed functional programming languages such as
Haskell, OCaml, and Standard ML. Even if you have not been exposed to these
languages, you will recognize many of the concepts from modern languages (e.g.,
Python, C++11, Java 8). In a first approximation:

> Lean = functional programming + logid

If your background is in mathematics, you probably already know most of
the key concepts underlying functional programming, sometimes under different
names. For example, the Haskell program:

```haskell
fib 0 = 0
fib 1 = 1
fib n = fib (n - 2) + fib (n - 1)
```

closely matches the mathematical definition:

\\( fib(n) = \\begin{cases} 0 & \\text{if } n = 0 \\\\ 1 & \\text{if } n = 1 \\\\ fib(n - 2) + fib(n - 1) & \\text{if } n ≥ 2 \\end{cases} \\)

and which can be written in Lean as:
-/
def fib : Nat → Nat
| 0     => 0
| 1     => 1
| (n+2) => fib n + fib (n+1)

#eval fib 10    -- 55