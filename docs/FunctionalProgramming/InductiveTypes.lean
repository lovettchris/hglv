namespace func
/-!
## Inductive Types

Inductive types are modeled after the data types of typed functional programming languages (e.g.,
Haskell, ML, OCaml). They are also reminiscent of sealed classes in Scala. Already in [Chapter
1](../Basics/Definitions.lean.md), we saw some basic inductive types: the natural numbers, the finite
lists, and a type of arithmetic expressions. In this chapter, we revisit the lists and study binary
trees. We also take a brief look at vectors of length _n_, a dependent type.

Recall the definition of natural numbers as an inductive type:
-/
inductive Nat : Type
| zero : Nat
| succ : Nat → Nat
/-!
This definition introduces three constants, which could have been declared as
follows:
-/
#check Nat       -- Type
#check Nat.zero  -- Nat
#check Nat.succ  -- Nat
/-!
In addition, the inductive definitions asserts some properties about `Nat.zero` and `Nat.succ`,
which is why we use the inductive command. It also introduces further constants that are used
internally to support induction and recursion.

As we saw in [Section 1.2](../Basics/TypeDefinitions.lean.md), an inductive type is a type whose
members are all the values that can be built by a finite number of applications of its constructors,
and only those. Mottos:

- _No junk_: The type contains no values beyond those expressible using the constructors.
- _No confusion_: Values built using a different combination of constructors are different.

For natural numbers, “no junk” means that there exist no special values such as −1, ε, ∞, or `NaN`
that cannot be expressed using a finite combination of `Nat.zero` and `Nat.succ`,¹ and “no
confusion” ensures that `Nat.zero ≠ Nat.succ n` for all `n` and that `Nat.succ` is injective. In
addition, values of inductive types are always finite.

> ¹ We could try to cheat and axiomatize special constants using constant and axiom, but the result
would be either tautological (i.e., useless) or contradictory (i.e., positively harmful). A safer
but equally pointless alternative would be to locally assume the existence of such a value; this
would be pointless because the assumption could never be discharged.

The infinite term
```
nat.succ (nat.succ (nat.succ (nat.succ . . .)))
```

is not a value. Nor does there exist a value `n` such that `Nat.succ n = n`, as we will
show below.

Inductive types are very convenient to use, because they support induction and recursion and their
constructors are well behaved, but not all types can be defined as an inductive type. In particular,
mathematical types such as ℚ (the rationals) and ℝ (the real numbers) require more elaborate
constructions, based on quotienting and subtyping. These will be explained in Chapters 11 and 13.

-/