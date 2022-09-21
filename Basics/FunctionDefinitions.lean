import Basics.TypeDefinitions
/-!
## Function Definitions

If all we want is to declare a function, we can use the `def` command.
Going back to the arithmetic expression example from [Typoe Definitions](./TypeDefinitions.lean.md), if we wanted to
implement an eval function in Java, we would probably add it as part of AExp’s
interface and implement it in each subclass. For Add, Sub, Mul, and Div, we would
recursively call eval on the left and right objects.

In Lean, the syntax is very compact. We define a single function and use pattern
matching to distinguish the six cases:
-/
def eval (env: String → Int) : aexp → Int
| (aexp.num i) => i
| (aexp.var x) => env x
| (aexp.add e₁ e₂) => eval env e₁ + eval env e₂
| (aexp.sub e₁ e₂) => eval env e₁ - eval env e₂
| (aexp.mul e₁ e₂) => eval env e₁ * eval env e₂
| (aexp.div e₁ e₂) => eval env e₁ / eval env e₂

/-!
The keyword `def` introduces the definition. The general format of definitions by
pattern matching is:

```lean
def name (params₁ : type₁) . . . (paramsₘ : typeₘ) : type
| patterns₁ := result₁
.
.
.
| patternsₙ := resultₙ
```

The parentheses ( ) around the parameters can also be curly braces { } if we want
to make them implicit arguments. The parameters cannot be subjected to pattern
matching, only the remaining arguments (e.g., the `aexp` argument of `eval`).

Patterns may contain variables, which are then visible in the corresponding
right-hand side, as well as constructors. For example, in the second case in eval’s
definition, the variable `x` can be used in the right-hand side `env x`.

Some definitions do not need pattern matching. For these, the syntax is simply

```lean
def name (params₁ : type₁) . . . (paramsₘ : typeₘ) : type :=
  result
```

We can have pattern matching without recursion (e.g., in the `aexp.num` and `aexp.var` cases above),
and we can have recursion without pattern matching.

The basic arithmetic operations on natural numbers, such as addition, can be
defined by recursion:

-/
def add : Nat → Nat → Nat
| m, Nat.zero => m
| m, (Nat.succ n) => Nat.succ (add m n)
/-!
We pattern-match on two arguments at the same time, distinguishing the case where the second
argument is zero and the case where it is nonzero. Each recursive call to add peels off one `Nat.succ`
constructor from the second argument. Instead of `Nat.zero` and `Nat.succ n`, Lean also allows us to
write `0` and `n + 1` as syntactic sugar.

-/
def add₂ : Nat → Nat → Nat
| m, 0 => m
| m, (n + 1) => (m + n) + 1
/-!
We can evaluate the result of applying add to numbers using `#eval` or `#reduce`:
-/
#eval add 2 7
#reduce add 2 7

/-!
Both commands print 9, as expected. `#eval` employs an optimized interpreter,
whereas `#reduce` uses Lean’s inference kernel, which is less effcient.

Perhaps you are worried about division by zero in the definition of eval above.
Let us see what `#eval` has to say about it:

-/
#eval eval (λ x => 7) (aexp.div (aexp.var "x") (aexp.num 0))
/-!
The output is 0. In Lean, division is conveniently defined as a total function that
returns zero when the denominator is zero. For a lucid explanation of why this is
not dangerous, see [Buzzard’s blog](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/).

It is good practice to provide a few tests each time we define a function, to
ensure that it behaves as expected. You can even leave the `#eval` or `#reduce`
calls in your Lean files as documentation.

The definition of multiplication is similar to that of addition and we can reuse our
`add` function here:
-/
def mul : Nat → Nat → Nat
| _, Nat.zero => Nat.zero
| m, (Nat.succ n) => add m (mul m n)

/-!
The underscore (`_`) stands for an unused variable. We could have put a name (e.g., `m`),
but `_` documents our intentions better.

The #eval command below prints 14, as expected:
-/
#eval mul 2 7
/-!
The power operation (“_m_ to the power of _n_”) can be defined in various ways.
Our first proposal is structurally identical to the definition of multiplication:
-/
def power : Nat → Nat → Nat
| _, Nat.zero => 1
| m, (Nat.succ n) => mul m (power m n)
/-!
Since the first argument, `m`, remains unchanged in the recursive call, `power m n`, we
can factor it out and put it next to the function’s name, as a parameter, before the
colon introducing the type of the function (excluding the parameter `m`):
-/
def power₂ (m : Nat) : Nat → Nat
| Nat.zero => 1
| (Nat.succ n) => mul m (power₂ m n)

#eval power₂ 2 7    -- 128
/-!
Yet another definition is possible by first introducing a general-purpose iterator
that applies a function recursively over the Nat values:
-/
def iter (z : α) (f : α → α) : Nat → α
| Nat.zero => z
| (Nat.succ n) => f (iter z f n)

def power₃ (m n : Nat) : Nat :=
  iter 1 (λ l => m * l) n

#eval power₃ 2 7    -- 128

/-!
Notice that the `power₃` is not recursive since the recursion is done by `iter`.

Recursive functions on lists can be defined in a similar way:
-/
def append (α : Type): List α → List α → List α
| xs, List.nil => xs
| List.nil, ys => ys
| (List.cons x xs), ys => List.cons x (append _ xs ys)

#check append
#eval append _ [3, 1] [4, 1, 5]   -- [3, 1, 4, 1, 5]
/-!
This append function takes three arguments: a type `α` and two lists of type `List α`
and it produces a resulting list of type `List α`.
By passing the placeholder `_`, we leave it to Lean to infer the type α from the type
of the other two arguments.

To make the type argument α implicit, we can put it in curly braces `{ }`
-/
def append₂ {α : Type} : List α → List α → List α
| xs, List.nil => xs
| List.nil, ys => ys
| (List.cons x xs), ys => List.cons x (append₂ xs ys)

#check append₂
#eval append₂ [3, 1] [4, 1, 5]    -- [3, 1, 4, 1, 5]
/-!
The at sign (`@`) can be used to make the implicit arguments explicit.
This is useful for debugging and occasionally necessary to guide Lean’s parser:
-/
#check @append₂
#eval @append₂ _ [3, 1] [4, 1, 5]
/-!
We can use syntactic sugar in the definition, both in the patterns on the left-hand sides of `=>` and in the right-hand sides:
-/
def append₃ {α : Type} : List α → List α → List α
| [], ys => ys
| (x :: xs), ys => x :: append₃ xs ys

#eval append₃ [3, 1] [4, 1, 5]    -- [3, 1, 4, 1, 5]
/-!
In Lean’s standard library, the append function has an infix operator called `++`.
We can use it to define a function that reverses a list:
-/
def reverse {α : Type} : List α → List α
| [] => []
| (x :: xs) => reverse xs ++ [x]

#eval reverse [1,2,3]   -- [3, 2, 1]
