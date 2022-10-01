import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
/-!
## Type Classes

Type classes are a mechanism that was popularized by Haskell and that is present
in several proof assistants. In Lean, a type class is a structure type combining
abstract constants and their properties. A type can be declared an instance of
a type class by providing concrete definitions for the constants and proving that
the properties hold. Based on the type, Lean retrieves the relevant instance.

A simple example is the type class inhabited, which requires only a constant
inhabited.default and no properties:
-/
class inhabited (α : Type) : Type where
  default : α
/-!
Lean has a built-in type class with this name in upper case `Inhabited`
so we'll switch to the `Inhabited` built-in type class from here on.

The syntax is the same as for structures, except with the keyword `class` instead
of `structure`. The parameter `α` represents an arbitrary type that could be a member of
this type class.

Any type that has at least one element can be registered as an instance of this class. For example,
we can register Nat as being inhabited by choosing an arbitrary number to be the default value:
-/
instance Nat.Inhabited : Inhabited ℕ :=
  { default := 0 }
/-!
The above example is using object syntax just to show the connection with structures.
Normally we use the nice `where` clause syntax instead and you don't need to provide
a name for it:
-/
instance : Inhabited ℤ where
  default := 0
/-!

This specifies a structure value called `Nat.Inhabited` of type `Inhabited ℕ`. In addition, the
structure value is registered as _the_ canonical instance to use whenever a structure of type
`Inhabited ℕ` is desired.

--BUGBUG: I removed mention of the global table of instances, is that ok?

For lists, the empty list is an obvious default value that can be constructed
even if α itself is not Inhabited:
-/
instance : Inhabited (List α) where
  default := []

/-!
Sometimes we may want to supply several instances of a given type class for
the same type. Lean will then choose the first matching instance it finds.

--BUGBUG I'm not following this part...

As an example, recall that finite functions of type `α → β` can be represented
by their function tables, of type `β × · · · × β` (with `|α|` copies of `β`). Accordingly,
`|α → β| = |β|^|α|`. To make this ∅, we must have both `|β| = ∅` and `|α| ≠ ∅`. In
other words, the type `α → β` is inhabited if either (1) β is inhabited or (2) α is _not_
inhabited. Case (1) is easy:
-/
instance {α β : Type} [Inhabited β] : Inhabited (α → β) where
  default := λ (_ : α) => default

/-!
The instance relies itself on an instance of the same type class but on a different
type. This frequently occurs and is part of the reason why we speak of type class
_search_ rather than _lookup_.

For case (2), there is a type class for uninhabitedness, but we know that the
type `Empty` is not inhabited, so it will do:
-/
instance {β : Sort v} [Inhabited β] : Inhabited (Empty → β) where
  default := fun _ : Empty => default
/-!
Notice the function can never be called, because no value of type `empty` exists to pass as
argument. The definition of `empty` has zero introduction rules.

Finally, the type `α × β` of pairs, also called product type, contains values of
the form `(a, b)`, where `a : α` and `b : β`. Given a pair x, the first and second components
can be extracted by writing `prod.fst x` and `prod.snd x`. To provide an
inhabitant of `α × β`, we need both an inhabitant of `α` and an inhabitant of `β`:
-/
instance {α β : Type} [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

def foo {α β : Type} [Inhabited α] [Inhabited β] :=
  ((default, default) : α × β)

#eval foo (α := ℕ) (β := ℤ) -- (0, 0)

/-!
Lean will search for an instance for `Inhabited ℕ` and will find `Nat.Inhabited`, the
instance we declared above. In that declaration, we set default to be `0` and hence
this is what `#eval` prints.

If multiple instances are applicable and Lean chooses the wrong one, we can name them and use the @
syntax to transform type class arguments into explicit arguments and supply the desired type class
instance. This is the main reason why we give names to the type class instances.

For example you can see how `foo` was wired together using some compiler generated names
if you turn on the verbose pretty printer like this:
-/
set_option pp.all true
#print foo

-- you will see this output:
def foo₁ : {α β : Type} → [inst : Inhabited.{1} α] → [inst : Inhabited.{1} β] → Prod.{0, 0} α β :=
fun {α β : Type} [inst : Inhabited.{1} α] [inst_1 : Inhabited.{1} β] =>
  @Prod.mk.{0, 0} α β (@Inhabited.default.{1} α inst) (@Inhabited.default.{1} β inst_1)

/-!
Notice how you can name the instances with `name :` like `inst` and `inst_1` above.
Notice also that Lean generated the name `instInhabitedProd_1` for our instance
since we didn't provide one.

So if you ever have to be explicit about which instance you are using it is easier if you add
names:
-/

instance InhabitedProd {α β : Type} [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

def foo₂ {α β : Type} [i1: Inhabited α] [i2: Inhabited β] : α × β :=
  (@InhabitedProd α β i1 i2).default

#eval foo₂ (α := ℕ) (β := ℤ) -- (0, 0)
/-!
Now we know for sure we are using our `InhabitedProd` instance rather than leaving it
up to Lean to find the right matching instance.

Using the `Inhabited` type class, we can define the head operation on lists: the
function that returns the first element of a list. Because an empty list contains no
elements, there is no meaningful value we can return in that case. Given a type
that belongs to the `Inhabited` type class, we can simply return the default value:
-/
def head {α : Type} [Inhabited α] : List α → α
| [] =>  default
| (x :: _) => x

/-!
We require that `α` belongs to `Inhabited` by writing `[Inhabited α]`. This allows us
to access `Inhabited.default` in the definition.

The syntax `[Inhabited α]` adds an implicit argument to the `head` definition. But
unlike for other implicit arguments, Lean performs not only type inference but
also a type class search through all declared instances to determine the value of
this argument. Thus, when running the command
-/
#eval head ([] : List ℕ) -- result : 0

/-!

Note the actual `List.head` function is defined different, it has a pre-requisite
that the list is not empty, so `List.head` function is not defined for empty lists.

In practice, almost all types are nonempty (with the notable exceptions of `empty` and `false`), so the
`Inhabited` restriction is hardly an issue. Regardless, lists over empty types are uninteresting—the
only possible value is `[]`.

We can prove abstract lemmas about the `Inhabited` type class, such as
-/
lemma head_head {α : Type} [Inhabited α] (xs : List α) :
  head [head xs] = head xs := sorry
/-!
Note we use `sorry` to indicate that the proof is left to the reader.

The assumption `[inhabited α]` is needed to use the operator head on lists of
type `List α`. If we omit this assumption, Lean will raise an error telling us that
type class synthesis failed.

There are more type classes with only a constant but no properties, including

-/
namespace hidden

class Add (α : Type u) where
  add : α → α → α

class Sub (α : Type u) where
  sub : α → α → α

class Mul (α : Type u) where
  mul : α → α → α

class Neg (α : Type u) where
  neg : α → α

/-!
`Add.add` computes the sum of `a` and `b`.
`Sub.sub` computes the difference of `a` and `b`.
`Mul.mul` computes the product of `a` and `b`.
`Neg.neg` computes the negative or opposite of `a`.

These all have homogeneous types α, there are also type classes for heterogeneous operations, named
`HAdd`, `HSub`, and `HMul`.

And Mathlib defines the following additional type classes:
-/
class Zero (α : Type u) where
  zero : α

class One (α : Type u) where
  one : α

class Inv (α : Type u) where
  inv : α → α

end hidden
/-!

These syntactic type classes introduce constants that are used in many different
contexts with different semantics.

The main purpose of these type classes is to form the foundation for a rich hierarchy of algebraic
type classes (groups, monoids, ring, fields, etc.) and to allow the overloading of common
mathematical symbols such as `+`, `-`, `*`, `!`, and so on.

Syntactic type classes do not impose serious restrictions on the types that can be declared
instances, except that α in type class `Zero` and `One` must be `Inhabited`. In contrast, the
semantic type classes contain properties that restrict how the given constants behave.

--BUGBUG : I don't like the use of the term `constants` here since we are kind of hiding that term
in lean4 now, I think it is refering to the type class functions like `zero`, `one`, `inv` in the
above, so can this be replaced with `definitions` or `functions` ?

In [Proofs by Mathematical Induction](../ForwardProofs/Induction.lean.md), we defined a lemma
proving Nat is commutative under addition, we named this lemma `add_comm`.
We can now use this in a type class as follows:
-/
class is_commutative (α : Type) (f : α → α → α) where
  comm : ∀a b, f a b = f b a

class is_associative (α : Type) (f : α → α → α) where
  assoc : ∀a b c, f (f a b) c = f a (f b c)

instance add.is_commutative : is_commutative ℕ Add.add where
  comm := add_comm

instance add.is_associative : is_associative ℕ Add.add where
  assoc := add_assoc

/-!
This time, the associations are not from a type to a constant, but from a type _and a function_ to a
property. Lean does not mind the abuse: Although they are called type classes, Lean’s type classes
are very flexible and can be used to express all sorts of constraints.

Conceptually, `is_commutative` is a dependent type of triples (`α`, `f`, `comm`), and similarly for
`is_associative`. The type of `f` depends on `α`, and the type of `comm` depends on `α` and `f`.
Although they are parameters, `α` and `f` are also stored along with `comm`. But the type class
mechanism treats the parameters differently from the fields: The parameters are treated as _input_ to
the type class search, whereas the fields are _output_.

Whenever we try to access `is_commutative.comm ℕ Add.add`, we obtain `add_comm`,
and similarly for `is_associative.assoc ℕ Add.add`. The `cc` tactic tries to look up the
`comm` and `assoc` properties for all binary operators in the problem and exploits
the properties whenever they are present.

The general syntax to define a type class is as follows:
```lean
class class-name (params₁ : type₁) . . . (paramsₖ : typeₖ)
  extends structure₁, . . ., structureₘ
where
  (constant-names₁ : constant-type₁)
  ...
  (constant-namesnₙ : constant-typeₙ)
  (property-names₁ : proposition₁)
  ...
  (property-namesₚ : propositionₚ)
```

The general syntax to instantiate a type class is as follows:

```lean
instance [instance-name] : type-class-name arguments where
  constant₁ := definition₁
  ...
  constantₙ := definitionₙ,
  property₁ := proof₁
  ...
  propertyₚ := proofₚ

-/
