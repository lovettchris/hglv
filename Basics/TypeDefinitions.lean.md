
## Type Definitions

A distinguishing feature of Lean’s calculus of inductive constructions is its built-in
support for inductive types. An _inductive type_ is a type whose values are built by
applying special constants called _constructors_. Inductive types are a concise way
of representing acyclic data in a program. You may know them under some other,
largely synonymous names, including algebraic data types, inductive data types,
freely generated data types, recursive data types, and data types.

### Natural Numbers

The “Hello, World!” example of inductive types is the type `Nat` natural numbers.
In Lean, it can be defined as follows:

<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-wsp"><span class="alectryon-token"><span class="kn">namespace</span></span><span class="alectryon-token"> my_nat

</span><span class="alectryon-token"><span class="kd">inductive</span></span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Nat</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">Nat</span></span><span class="alectryon-token"> </span><span class="alectryon-token"><span class="k">where</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>zero</var><b>: </b><span>Nat</span></span></div></blockquote></div></small></div>zero</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Nat</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">Nat</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>succ</var><b>: </b><span>Nat → Nat</span></span></div></blockquote></div></small></div>succ</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Nat</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">Nat</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Nat</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">Nat</span></span><span class="alectryon-token">

</span><span class="alectryon-token"><span class="kd">end</span></span><span class="alectryon-token"> my_nat</span></span></pre>

Note: we are placing this in a new nameapce `my_nat` so it does not conflict with the
built-in type.

The first line of the `inductive` type announces to the world that we are introducing a new type
called `Nat`, intended to represent the natural numbers. The second and third line declare two new
constructors, `Nat.zero` which is of type `Nat` and `Nat.succ` which has the function type `Nat →
Nat`, that can be used to build values of type `Nat`. Following an established convention in
computer science and logic, counting starts at zero. The second constructor is what makes this
inductive definition interesting—it requires an argument of type `Nat` to produce a value of type
`Nat`. The terms
```lean
Nat.zero
Nat.succ Nat.zero
Nat.succ (Nat.succ Nat.zero)
...
```
denote the different values of type nat—zero, its successor, its successor’s successor, and so on.
This notation is called _unary_, or _Peano_, after the logician Giuseppe Peano. For an alternative
explanation of Peano numbers in Lean (and some groovy video game graphics), see Kevin Buzzard’s
article [Can computers prove theorems?](http://chalkdustmagazine.com/features/can-computers-prove-theorems/).

The general format of type declarations is
```lean
inductive type-name (params₁ : type₁) . . . (paramsₖ : typeₖ) : Type
| constructor-name₁ : constructor-type₁
.
.
.
| constructor-nameₙ : constructor-typeₙ
```
For the natural numbers, it is possible to convince Lean to use the familiar name `ℕ` by declaring
notation for it as follows:

<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-wsp"><span class="alectryon-token"><span class="kd">notation</span></span><span class="alectryon-token"> <span class="s2">&quot;ℕ&quot;</span> <span class="bp">=&gt;</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Nat</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div>Nat</span><span class="alectryon-token">
</span><span class="alectryon-token"><span class="kd">notation</span></span><span class="alectryon-token"> <span class="s2">&quot;ℤ &quot;</span> <span class="bp">=&gt;</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Int</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div>Int</span><span class="alectryon-token"></span></span></pre>

You can also use literals `0, 1, 2, . . .` and Lean will be able to infer that they are of type `Nat`
when they are used in that context.

We can inspect an earlier definition at any point in Lean by using the `#print` command. For example,
`#print Nat` within the `my_nat` namespace displays the following information:

<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-sentence"><input class="alectryon-toggle" id="TypeDefinitions-lean-chk0" style="display: none" type="checkbox"><label class="alectryon-input" for="TypeDefinitions-lean-chk0"><span class="alectryon-token"><span class="k">#print</span></span></label><small class="alectryon-output"><div><div class="alectryon-messages"><blockquote class="alectryon-message"><span class="kd">inductive</span> my_nat.Nat : <span class="kt">Type</span>
number of <span class="kd">parameters</span>: <span class="mi">0</span>
constructors:
my_nat.Nat.zero : my_nat.Nat
my_nat.Nat.succ : my_nat.Nat <span class="bp">→</span> my_nat.Nat</blockquote></div></div></small></span><span class="alectryon-wsp"><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>my_nat.Nat</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div>my_nat.Nat</span><span class="alectryon-token"></span></span></pre>

```
inductive my_nat.Nat : Type
number of parameters: 0
constructors:
my_nat.Nat.zero : my_nat.Nat
my_nat.Nat.succ : my_nat.Nat → my_nat.Nat
```

The focus on natural numbers is one of the many features of this guide that reveal a bias towards
computer science. Number theorists would be more interested in the integers `ℤ` and the rational
numbers `ℚ`; analysts would want to work with the real numbers `ℝ` and the complex numbers `ℂ`. But the
natural numbers are ubiquitous in computer science and enjoy a very simple definition as an
inductive type. They can also be used to build other types, as we will see in Chapter 13.

### Arithmetic Expressions

If we were to specify a calculator program or a programming language, we would
likely need to define a type to represent arithmetic expressions. The next example
shows how this could be done in Lean:

<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-wsp"><span class="alectryon-token"><span class="kd">inductive</span></span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token">  </span><span class="alectryon-token"><span class="k">where</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>num</var><b>: </b><span>ℤ → aexp</span></span></div></blockquote></div></small></div>num</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Int</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div>Int</span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>var</var><b>: </b><span>String → aexp</span></span></div></blockquote></div></small></div>var</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>String</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div>String</span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>add</var><b>: </b><span>aexp → aexp → aexp</span></span></div></blockquote></div></small></div>add</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>sub</var><b>: </b><span>aexp → aexp → aexp</span></span></div></blockquote></div></small></div>sub</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>mul</var><b>: </b><span>aexp → aexp → aexp</span></span></div></blockquote></div></small></div>mul</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token">
<span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>div</var><b>: </b><span>aexp → aexp → aexp</span></span></div></blockquote></div></small></div>div</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token"> <span class="bp">→</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">aexp</span></span><span class="alectryon-token">

</span></span><span class="alectryon-sentence"><input class="alectryon-toggle" id="TypeDefinitions-lean-chk1" style="display: none" type="checkbox"><label class="alectryon-input" for="TypeDefinitions-lean-chk1"><span class="alectryon-token"><span class="k">#check</span></span></label><small class="alectryon-output"><div><div class="alectryon-messages"><blockquote class="alectryon-message">aexp.num <span class="mi">1</span> : aexp</blockquote></div></div></small></span><span class="alectryon-wsp"><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>aexp.num</var><b>: </b><span>ℤ → aexp</span></span></div></blockquote></div></small></div>aexp.num</span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>1</var><b>: </b><span>ℤ</span></span></div></blockquote></div></small></div><span class="mi">1</span></span><span class="alectryon-token">     <span class="c1">-- aexp.num 1 : aexp</span></span></span></pre>

Mathematically, this definition is equivalent to defining the type `aexp` inductively
by the following formation rules:

1. For every integer `i`, we have that `aexp.num i` is an `aexp` value.
2. For every character string `x`, we have that `aexp.var x` is an `aexp` value.
3. If `e1` and `e2` are `aexp` values, then so are `aexp.add e1 e2`, `aexp.sub e1 e2`,
`aexp.mul e1 e2`, and `aexp.div e1 e2`.

The above definition is exhaustive. The only possible values for `aexp` are those built using
formation rules 1 to 3. Moreover, `aexp` values built using different formation rules are distinct.
These two properties of inductive types are captured by the motto “No junk, no confusion,” due to
Joseph Goguen.

### Comparison with Java

It may be instructive to compare the concise Lean specification of `aexp` above with a Java program
that achieves the same. The program consists of one interface and six classes that implement it,
corresponding to the `aexp` type and its six constructors:

```java
public interface AExp { }
public class Num implements AExp {
  public int num;
  public Num(int num) { this.num = num; }
}
public class Var implements AExp {
  public String var;
  public Var(String var) { this.var = var; }
}
public class Add implements AExp {
  public AExp left;
  public AExp right;
  public Add(AExp left, AExp right)
  { this.left = left; this.right = right; }
}
public class Sub implements AExp {
  public AExp left;
  public AExp right;
  public Sub(AExp left, AExp right)
  { this.left = left; this.right = right; }
}
public class Mul implements AExp {
  public AExp left;
  public AExp right;
  public Mul(AExp left, AExp right)
  { this.left = left; this.right = right; }
}
public class Div implements AExp {
  public AExp left;
  public AExp right;
  public Div(AExp left, AExp right)
  { this.left = left; this.right = right; }
}
```

### Comparison with C

In C, the natural counterpart of an inductive type is a tagged union. The type
declarations would be as follows:

```C
#include <stddef.h>
#include <stdlib.h>
enum AExpKind {
  AET_NUM, AET_VAR, AET_ADD, AET_SUB, AET_MUL, AET_DIV
};
struct aexp;
struct aexp_num {
  int num;
};
struct aexp_var {
  char var[1024];
};
struct aexp_binop {
  struct aexp *left;
  struct aexp *right;
};
struct aexp {
  enum AExpKind kind;
  union {
    struct aexp_num anum;
    struct aexp_var avar;
    struct aexp_binop abinop;
  } data;
};
```
Corresponding to each constructor in Lean, we would need to write a function
to allocate an `aexp` object of the right size in memory. Here is the definition of the
function corresponding to the first constructor, `aexp.num`:

```C
struct aexp *create_num(int num)
{
  struct aexp *res = malloc(offsetof(struct aexp, data) +
  sizeof(struct aexp_num));
  res->kind = AET_NUM;
  res->data.anum.num = num;
  return res;
}
```

The subtle pointer arithmetic for the `malloc` call is needed to allocate exactly the
right amount of memory.

### Lists

The next type we consider is that of finite lists (shown here in a temporary namespace
so it doesn't conflict with the same built-in type):

<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-wsp"><span class="alectryon-token"><span class="kn">namespace</span></span><span class="alectryon-token"> my_list

</span><span class="alectryon-token"><span class="kd">inductive</span></span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>List</var><b>: </b><span>Type → Type</span></span></div></blockquote></div></small></div><span class="nv">List</span></span><span class="alectryon-token"> (</span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>α</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">α</span></span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Type</var><b>: </b><span>Type 1</span></span></div></blockquote></div></small></div><span class="kt">Type</span></span><span class="alectryon-token">) </span><span class="alectryon-token"><span class="k">where</span></span><span class="alectryon-token">
  <span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>nil</var><b>: </b><span>{α : Type} → List α</span></span></div></blockquote></div></small></div>nil</span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>List</var><b>: </b><span>Type → Type</span></span></div></blockquote></div></small></div><span class="nv">List</span></span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>α</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">α</span></span><span class="alectryon-token">
  <span class="bp">|</span> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>cons</var><b>: </b><span>{α : Type} → α → List α → List α</span></span></div></blockquote></div></small></div>cons</span><span class="alectryon-token"> (</span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>head</var><b>: </b><span>α</span></span></div></blockquote></div></small></div><span class="nv">head</span></span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>α</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">α</span></span><span class="alectryon-token">) (</span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>tail</var><b>: </b><span>List α</span></span></div></blockquote></div></small></div><span class="nv">tail</span></span><span class="alectryon-token"> : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>List</var><b>: </b><span>Type → Type</span></span></div></blockquote></div></small></div><span class="nv">List</span></span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>α</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">α</span></span><span class="alectryon-token">) : </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>List</var><b>: </b><span>Type → Type</span></span></div></blockquote></div></small></div><span class="nv">List</span></span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>α</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div><span class="nv">α</span></span><span class="alectryon-token">

</span><span class="alectryon-token"><span class="kd">end</span></span><span class="alectryon-token"> my_list</span></span></pre>

The type is _polymorphic_: It is parameterized by a type α, which we can instantiate with concrete
types. For example, `List ℤ`  is the type of lists over integers, and `List (List ℝ)` is the type of
lists of lists of real numbers. The type constructor `List` takes a type as argument and returns a
type. Polymorphism is related to generics (in Java) and templates (in C++). The general idea in all
cases is to have parameterized types.

The following commands display the constructors’ types:

<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-sentence"><input class="alectryon-toggle" id="TypeDefinitions-lean-chk2" style="display: none" type="checkbox"><label class="alectryon-input" for="TypeDefinitions-lean-chk2"><span class="alectryon-token"><span class="k">#check</span></span></label><small class="alectryon-output"><div><div class="alectryon-messages"><blockquote class="alectryon-message">[] : List <span class="bp">?</span>m.4805</blockquote></div></div></small></span><span class="alectryon-wsp"><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>List.nil</var><b>: </b><span>{α : Type u_1} → List α</span></span></div></blockquote></div></small></div>List.nil</span><span class="alectryon-token">       <span class="c1">-- [] : List ?m.6639</span>
</span></span><span class="alectryon-sentence"><input class="alectryon-toggle" id="TypeDefinitions-lean-chk3" style="display: none" type="checkbox"><label class="alectryon-input" for="TypeDefinitions-lean-chk3"><span class="alectryon-token"><span class="k">#check</span></span></label><small class="alectryon-output"><div><div class="alectryon-messages"><blockquote class="alectryon-message">List.cons : <span class="bp">?</span>m.4807 <span class="bp">→</span> List <span class="bp">?</span>m.4807 <span class="bp">→</span> List <span class="bp">?</span>m.4807</blockquote></div></div></small></span><span class="alectryon-wsp"><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>List.cons</var><b>: </b><span>{α : Type u_1} → α → List α → List α</span></span></div></blockquote></div></small></div>List.cons</span><span class="alectryon-token">      <span class="c1">-- List.cons : ?m.6641 → List ?m.6641 → List ?m.6641</span></span></span></pre>

Informally:
- The `nil` constructor takes a type α as argument and produces a result of type
`List α`. The type was not defined here so you see `?m.6639` which represents
an unresolved metavariable in the Lean compilation.
- The `cons` constructor takes an element (the _head_) of some arbitrary type
`?m.6641` as argument and a list over `?m.6641` (the tail) and produces a result of
type list `?m.6641`. Unlike for nil, there is no need to pass a type argument to
cons—the type is inferred from the first argument. If we want to pass the type
argument explicitly, we need to write an at sign (@) in front of the constant:
`@List.cons`.

<pre class="alectryon-io type-info-hidden highlight"><!-- Generator: Alectryon --><span class="alectryon-sentence"><input class="alectryon-toggle" id="TypeDefinitions-lean-chk4" style="display: none" type="checkbox"><label class="alectryon-input" for="TypeDefinitions-lean-chk4"><span class="alectryon-token"><span class="k">#check</span></span></label><small class="alectryon-output"><div><div class="alectryon-messages"><blockquote class="alectryon-message">List.cons : ℕ <span class="bp">→</span> List ℕ <span class="bp">→</span> List ℕ</blockquote></div></div></small></span><span class="alectryon-wsp"><span class="alectryon-token"> <span class="bp">@</span></span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>List.cons</var><b>: </b><span>{α : Type} → α → List α → List α</span></span></div></blockquote></div></small></div>List.cons</span><span class="alectryon-token"> </span><span class="alectryon-token"><div class="alectryon-type-info-wrapper"><small class="alectryon-type-info"><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span class="hyp-type"><var>Nat</var><b>: </b><span>Type</span></span></div></blockquote></div></small></div>Nat</span><span class="alectryon-token">   <span class="c1">-- List.cons : ℕ → List ℕ → List ℕ</span></span></span></pre>

Even if we try to restrict ourselves to a fragment of Lean’s language, Lean often
exposes us to more advanced constructs in the output, such as `?m.6641` above, `Sort u`,
or `Type 1`. Our advice is to adopt a sporty attitude: Do not worry if you do not
always understand everything the first time. Use your common sense and your
imagination. And, above all, do not hesitate to ask.

Lean’s built-in lists offer syntactic sugar for writing lists:

- `[]` for `List.nil`
- `x :: xs` for `List.cons x xs`
- `[x₁, . . ., xₙ]` for `x₁ :: . . . :: xₙ :: []`

The `::` operator, like all other binary operators, binds less tightly than function
application. Thus, `f x :: reverse ys` is parsed as `(f x) :: (reverse ys)`. It is good
practice to avoid needless parentheses. They can quickly impair readability. In
addition, it is important to put spaces around infix operators, to suggest the right
precedence; it is all too easy to misread `f x::reverse ys` as `f (x::reverse) ys` otherwise.

Functional programmers often use plural names such as `xs`, `ys`, `zs` for lists
(or more generally collections). A list contains many elements, so a plural form is natural.
A list of `cat` objects might be called `cats`; a list of list of `cat` objects, `catss`.
When a nonempty list is presented as a head and a tail, we usually write, say, `x :: xs` or `cat :: cats`.
