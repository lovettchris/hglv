import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Int.Basic
/-!
## Types and Terms

_Simple type theory_ (also called higher-order logic) corresponds roughly to the
[simply typed λ-calculus](../bib.md#5) extended with an equality operator (=). It is an abstract,
extremely simplified version of a programming language with a function-calling
mechanism that prefigures functional programming. It can also be viewed as a
generalization of first-order logic (also called predicate logic).

### Types

Types are either basic types such as `ℤ`, `ℚ`, and bool or total functions `σ → τ`, where
`σ` and `τ` are themselves types. Types indicate which values an expression may
evaluate to. They introduce a discipline that is followed somewhat implicitly in
mathematics. In principle, nothing prevents a mathematician from stating `1 ∈ 2`,
but a typing discipline would mark this as the error it likely is.

Semantically, types can be viewed as sets. We would normally define the types
`ℤ`, `ℚ`, and `bool` so that they faithfully capture the mathematicians’ `ℤ` and `ℚ` and
the computer scientists’ Booleans, and similarly for the function arrow (`→`). But
despite their similarities, Lean and mathematics are distinct languages. Lean’s
types may be interpreted as sets, but they are not sets.

Higher-order types are types containing left-nested `→` arrows. Values of such
types are functions that take other functions as arguments. Accordingly, the type
`(ℤ → ℤ) → ℚ`  is the type of unary functions that take a function of type `ℤ → ℤ` as
argument and that return a value of type `ℚ`.

### Terms

The _terms_, or expressions, of simple type theory consist of

- _constants_ c;
- _variables_ x;
- _applications_ t u;
- _λ-expressions_ λx => t.

Above, `t` and `u` denote arbitrary terms. We can also write `t : σ` to indicate that the
term `t` has the type `σ`.

A constant `c : σ` is a symbol of type `σ` whose meaning is fixed in the current
global context. For example, an arithmetic theory might contain constants such
as `0 : ℤ`, `1 : ℤ`, `abs : ℤ → ℕ`, `square : ℕ → ℕ`, and `prime : ℕ → Bool`. Constants
include functions (e.g., `abs`) and predicates (e.g., `prime`).

A variable `x : σ` is either bound or free. A bound variable refers back to the
input of a λ-expression `λ x : σ => t` enclosing it. In `λ x : ℤ => square (abs x)`
the second `x` is a variable that refers back to the λ binder’s input `x`. By contrast, a free
variable is declared in the local context&mdash;a concept that will be explained below.

An application `t u`, where `t : σ → τ` and `u : σ`, is a term of type `τ` denoting the
result of applying the function `t` to the argument `u`—e.g., `abs 0`. No parentheses
are needed around the argument, unless it is a complex term—e.g., `prime (abs 0)`.

Given a term `t : τ`, a λ-expression `λ x : σ => t` denotes the total function of type
`σ → τ` that maps each input value `x` of type `σ` to the function body `t`, where `t` may
contain `x`. For example, `λ x : ℤ => square (abs x)` denotes the function that maps
(the value denoted by) `0` to (the value denoted by) `square (abs 0)`, that maps `1` to
`square (abs 1)`, and so on. A more intuitive syntax might have been
`x ↦ square (abs x)`, but this is not supported by Lean.

Applications and λ-expressions mirror each other: A λ-expression “builds” a
function; an application “destructs” a function. Although our functions are unary
(i.e., they take one argument), we can build _n_-ary functions by nesting λs, using
an ingenious technique called _currying_. For example, `λ x : σ => (λ y : τ => x)` denotes
the function of type `σ → (τ → σ)` that takes two arguments and returns the first
one. Strictly speaking, `σ → (τ → σ)` takes a single argument and returns a function,
which in turn takes an argument. Applications work in the same way: If
`K := (λx : ℤ => (λ y : Z => x))`, then `K 1 = (λ y : Z => 1)` and `(K 1) 0 = 1`.
The function `K` in `K 1`, which is applied to a single argument, is said to be _partially applied_.

Currying is so useful a concept that we will omit most parentheses, writing

- `σ → τ → υ` for `σ → (τ → υ)`
- `t u v` for `(t u) v`
- `λ x : σ => λ y : τ => t` for `λ x : σ => `(λ y : τ => t)`

and also

- `λ (x : σ) (y : τ) => t` for `λ x : σ => λ y : τ => t`
- `λ x y : σ => t` for `λ (x : σ) (y : σ) => t`

In mathematics, it is customary to write binary operators in infix syntax—e.g.,
`x + y`. Such notations are also possible in Lean, as syntactic sugar for `Add.add x y`.
Partial application is possible with this syntax. For example,  `Add.add 1`
denotes the unary function that adds one to its argument. Other ways to write
this function are `λ x => Add.add 1 x` and `λ x => 1 + x`.

No we can move some of this into the Lean language, declaring some simple
typed values and functions using the `def` command as follows:
-/
-- These are defined in Mathlib:
-- notation "ℤ" => Int   -- associates the notation ℤ with Integer type.
-- notation "ℕ" => Nat   -- associates the notation ℕ with Nat type for natural numbers.

def a : ℤ := 1
def b : ℤ := 2
def f : ℤ → ℤ  := λ x => x + 1
def g : ℤ → ℤ → ℤ := λ x y => x + y

#check λ x : ℤ => g (f (g a x)) (g x b)   -- ℤ → ℤ
#check λ x => g (f (g a x)) (g x b)       -- ℤ → ℤ

/-!
The first two lines declare tow constants (a, b), both of type Integer with
the respective value of 1 and 2.  The definition for `f` defines a funciton
of type `ℤ → ℤ` implemented by a lambda expression that adds 1 to its argument.
The definition for `g` defines a function of type `ℤ → ℤ → ℤ` implemented by a
lambda expression that takes two arguments and adds them together.

The last two lines use the `#check` command to type-check some terms and
show their types. The # prefix identifies interactive commands: commands that are
useful for debugging but that we would normally not keep in a Lean program.

The `abbrev` command can be used to define a new name for an existing type:
-/
abbrev foo := Int

#check foo -- foo : Type

#check (5 : foo)    -- 5 : foo

#reduce (5 : foo)   -- Int.ofNat 5
/-!
Here we see that `foo` is a `Type` and it is synonymous for the type `Int`.

### Type Checking and Type Inference

When Lean parses a term, it checks whether the term is well typed. In the process,
it tries to infer the types of bound variables if those are omitted—e.g., the type of
`x` in `λ x => 1 + x`. Type inference lightens notations and saves some typing.

For simple type theory, type checking and type inference are decidable problems.
Advanced features such as overloading (the possibility to reuse the same
name for several constants—e.g., `0 : ℕ`  and `0 : ℝ`) can lead to [undecidability](../bib.md#30).
Lean takes a pragmatic, computer-science-oriented approach and assumes that
numerals `0, 1, 2, . . .` are of type `Nat` if several types are possible.

Lean’s type system can be expressed as a formal system. A formal system
consists of judgments and of (derivation) rules for producing judgments. A typing
judgment has the form `C ⊢ t : σ`, meaning that term `t` has type `σ` in local context `C`.
The local context gives the types of the variables in `t` that are not bound by a `λ`.
The local context is used to keep track of the variables bound by λ’s outside `t`.
For a function definition, it will consist of the function’s parameters. For example,
in Lean, the right-hand side of the last equation of fib’s above would be type-checked
in a local context consisting of `n : ℕ`.

For simple type theory, there are four typing rules, one per kind of term:

\\( \cfrac{}{C ⊢ c : σ} {\large{C}}{\normalsize{ST}} \quad \\text{if c is declared with type σ } \\)

\\( \cfrac{}{C ⊢ x : σ} {\large{V}}{\normalsize{AR}} \quad \\text{if x : σ is the last occurrence of x in C } \\)

\\( \cfrac{C ⊢ t : σ → τ \quad C ⊢ u : σ }{C ⊢ t\enspace{u} : τ} {\large{A}}{\normalsize{PP}} \\)

\\( \cfrac{C, x : σ ⊢ t : τ }{C ⊢ (λ\enspace{x} : σ => t) : σ → τ} {\large{L}}{\normalsize{AM}} \\)

Each rule has zero or more premises (above the horizontal bar), a conclusion
(below the bar), and possibly a side condition. The premises are typing judgments,
whereas the side conditions are arbitrary mathematical conditions on the mathematical
variables occurring in the rule. To discharge the premises, we need to
continue performing a derivation upward, as we will see in a moment. As for the
side conditions, we can use the entire arsenal of mathematics to show that they
are true.

The first two rules, labeled `CST` and `VAR`, have no premises, but they have side
conditions that must be satisfied for the rules to apply. The last two rules take
one or two judgments as premises and produce a new judgment. `LAM` is the only
rule that modifies the local context: As we enter the body `t` of a λ-expression, we
need to record the existence of the bound variable `x` and its type to be ready when
we meet `x` in `t`

We can use this rule system to prove that a given term is well typed by working our way backwards
(i.e., upwards) and applying the rules, building a formal derivation of a typing judgment. Like
natural trees, derivation trees are drawn with the root at the bottom. The derived judgment appears
at the root, and each branch ends with the application of a premise-less rule. Rule applications are
indicated by a horizontal bar and a label. The following typing derivation establishes that the term
`λ x : ℤ => abs x` has type `ℤ → ℕ`  in an arbitrary local context `C`:

\\( \cfrac{
      \cfrac{}{C, x : ℤ ⊢ abs : ℤ → ℕ} {\large{C}}{\normalsize{ST}}
      \quad 
      \cfrac{}{C, x : ℤ ⊢ x : ℤ } {\large{V}}{\normalsize{AR}}
    }
    {
      \cfrac{C, x : ℤ ⊢ abs\enspace{x} : ℕ}{C ⊢ (λ\enspace{x} : ℤ => abs\enspace{x}): ℤ → ℕ} {\large{C}}{\normalsize{ST}}
    }
    {\large{A}}{\normalsize{PP}}\\)

Reading the proof from the root upwards, notice how the local context is threaded
through and how it is extended by the `LAM` rule. The rule moves the variable bound
by the λ-expression to the local context, making an application of `VAR` possible
further up the tree. If the variable `x` is already declared in `C`, it becomes shadowed
by `x : ℤ` after entering the λ-expression.

The above type system only checks that terms are well typed. It does not check
that types are well formed. For example, `List ℤ`  is well formed, whereas `ℤ List`
and `List List` are ill-formed. For simple type theory, well-formedness is easy
to check: Only declared type constructors should be used, and each _n_-ary type
constructor should be passed exactly _n_ type arguments.

As a side note, type inference is a generalization of type checking where the
types on the right-hand side of the colon (`:`) in judgments may be replaced by
placeholders. Lean’s type inference is based on an algorithm due to [Hindley](../bib.md#15)
and [Milner](../bib.md#25), which also forms the basis of Haskell, OCaml, and Standard ML.
The algorithm generates type constraints involving type variables `?α, ?β, ?γ, . . .`,
and attempts to solve them using a type unification procedure. For example, when
inferring the type `?α` of `λ x => abs x`, Lean would perform the following schematic
type derivation:

\\( \cfrac{
      \cfrac{}{x :\thinspace{?β} ⊢ abs :\thinspace{?β} → γ} {\large{C}}{\normalsize{ST}}
      \quad 
      \cfrac{}{x :\thinspace{?β} ⊢ x :\thinspace{?β}} {\large{V}}{\normalsize{AR}}
    }
    {
      \cfrac{x :\thinspace{?β} ⊢ abs\enspace{x}:\thinspace{?γ}}{⊢ (λ\enspace{x} => abs\enspace{x}) :\thinspace{?α}} {\large{C}}{\normalsize{ST}}
    }
    {\large{A}}{\normalsize{PP}}\\)

In addition, Lean would generate the following constraints to ensure that all the
rule applications are legal:

1. For the application of `LAM`, the type of `λ x => abs x` must be of the form `?β → ?γ`,
for some types `?β` and `?γ`. Thus, Lean would generate the constraint `?α = ?β → ?γ`
2. For the application of `CST`, the type of `abs` must correspond to the declaration as `ℤ → ℕ`.
Thus, Lean would generate the constraint `?β → ?γ = ℤ → ℕ`

Solving the two constraints yields `?α := ℤ → ℕ`, which is indeed the type that Lean
infers for `λ x => abs x`.

### Type Inhabitation

Given a type `σ`, the type inhabitation problem consists of finding an “inhabitant”
of that type—a term of type `σ`—within the empty local context. It may seem like a
pointless exercise, but as we will see in Chapter 3, this problem is closely related
to that of finding a proof of a proposition. Seemingly silly exercises of the form
“find a term of type `σ`” are good practice towards mastery of theorem proving.

To create a term of a given type, start with the placeholder _ and recursively
apply a combination of the following two steps:

1. If the type is of the form `σ → τ`, a possible inhabitant is an anonymous function,
of the form `λ x : σ => _`, where `_` is a placeholder for a missing term of
type `τ`. Lean will mark `_` as an error; if you hover over it in Visual Studio
Code, a tooltip will show the missing term’s type as well as any variables
declared in the local context.

2. Given a type `σ` (which may be a function type), you can use any constant `c`
or variable `x : τ₁ → · · · → τₙ → σ` to build a term of that type. For each
argument, you need to put a placeholder, yielding `c _ . . . _` or `x _ . . . _`

The placeholders can be eliminated recursively using the same procedure.
As an example, we will apply the procedure to find a term of type
`(α → β → γ) → ((β → α) → β) → α → γ`.

Initially, only step 1 is applicable, with `σ := α → β → γ` and `τ := ((β → α) → β) → α → γ`.
(Recall that `→` is right-associative: `σ → τ → υ` stands for `σ → (τ → υ)`.)
This results in the term `λ f => _`, which has the right type but has a placeholder left.
Since the argument `f` has type `σ`, a function type, it makes sense to use the name
`f` for it. Then we continue recursively with the placeholder, of type `τ`. Again, only
step 1 is possible, so we end up with the term `λ f => λ g => _`, where `g` has type
`(β → α) → β` and the placeholder has type `α → γ`. A third application of step 1 yields
`λ f => λ g => λ a => _`, where `a` has type `α` and the placeholder has type `γ`.

At this point, step 1 is no longer possible. Let us see if step 2 is applicable. The
context surrounding the placeholder contains the following variables:
```lean
f : α → β → γ
g : (β → α) → β
a : α
```

Recall that we are trying to build a term of type `γ`. The only variable we can use
to achieve this is `f`: It takes two arguments and returns a value of type `γ`. So
we replace the placeholder with the term `f _ _`, where the two new placeholders
stand for the two missing arguments. Putting everything together, we now have
the term `λ f => λ g => λ a => f _ _`.

Following f’s type, the placeholders are of type `α` and `β`, respectively. The first
placeholder is easy to fill, using step 2 again, by simply supplying `a`, of type `α`, with
no arguments. For the second placeholder, we apply step 2 with the variable `g`,
which is the only source of βs. Since `g` takes an argument, we must supply a
placeholder. This means our current term is `λ f => λ g => λ a => f a (g _)`.

We are almost done. The only placeholder left has type `β → α`, which is g’s
argument type. Applying step 1, we replace the placeholder with `λ b => _`, where `_`
has type `α`. Here, we can simply supply `a`. Our final term is
`λ f => λ g => λ a => f a (g (λ b => a))`—i.e., `λ f g a => f a (g (λ b => a))`.

The above derivation was tedious but deterministic: At each point, either step
1 or 2 was applicable, but not both. In general, this will not always be the case.
For some other types, we might encounter dead ends and need to backtrack. We
might also fail altogether, with nowhere to backtrack to. Notably, with an empty
local context, it is impossible to supply a witness for `α`.

The key idea is that the term should be syntactically correct at all times. The
only red underlining we should see in Visual Studio Code should appear under the
placeholders. In general, a good principle for software development is to start
with a program that compiles, perform the smallest change possible to obtain a
new compiling program, and repeat until the program is complete.
-/