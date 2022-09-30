import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Init.Data.Nat.Basic

/-!
## Structures

Lean provides a convenient syntax for defining records, or _structures_ as they are
also called. These are essentially nonrecursive, single-constructor inductive types,
but with some syntactic sugar.

The definition below introduces a structure called `rgb` with three fields of type
Nat called `red`, `green`, and `blue`:
-/
structure rgb where
  (red green blue : ℕ)
  deriving Repr
/-!
The additional `deriving Repr` clause tells Lean to automatically generate a
`repr` function for this structure so that `#eval` can print the structure.

This definition has roughly the same effect as the following commands:
-/
inductive rgb₁ : Type
| mk : ℕ → ℕ → ℕ → rgb₁

def rgb₁.red : rgb₁ → ℕ
| (rgb₁.mk r _ _) => r

def rgb₁.green : rgb₁ → ℕ
| (rgb₁.mk _ g _) => g

def rgb₁.blue : rgb₁ → ℕ
| (rgb₁.mk _ _ b) => b

/-!
We can define a new structure as the extension of an existing structure. The
definition below extends `rgb` with a fourth field, called `alpha`:
-/
structure rgba extends rgb where
  (alpha : ℕ)
  deriving Repr
/-!
The general syntax to define structures is
```lean
structure structure-name (params₁ : type₁) . . . (paramsₖ : typeₖ )
  [extends structure₁, . . ., structureₘ] where
  [constructor ::]
  <fields>
```
Where each fields is either
```
(field-names₁ : field-type₁) ... (field-namesₙ : field-typeₙ)
```
Or one field per line where you can drop the parens:
```
  field-names₁ : field-type₁
  ...
  field-namesₙ : field-typeₙ
```
So `rgb` can also be defined like this:
-/
structure rgb₂ where
  red : ℕ
  green : ℕ
  blue : ℕ
/-!
The parameters `params₁, . . . , paramsₖ` are effectively additional fields, but unlike
the fields `field-names₁, . . . , field-namesₙ`, they are also stored in the type, as
arguments to the type constructor (structure-name).

Values can be created using a variety of syntaxes:
-/
def black : rgb := rgb.mk 0 0 0
/-!
Notice the structure has a default constructor named 'mk'.  You can rename this by
providing a name before the fields followed by `::` then the fields, for example:
-/
structure rgb₃ where
  foo :: (red green blue : ℕ)
  deriving Repr

#eval rgb₃.foo 1 2 3 -- { red := 1, green := 2, blue := 3 }
/-!

The special brackets `⟨ ... ⟩` is general notation that means call the default constructor,
and in this case there is only one contructor, so it knows what to do:
-/
def red : rgb := ⟨255, 0, 0⟩
def red₃ : rgb₃ := ⟨255, 0, 0⟩
/-!
You can also construct object using an object syntax where you name the fields:
-/
def green  : rgb := { red := 0, green := 255, blue := 0 }

def blue  : rgb := { black with blue := 255 }

def yellow := { red := 255, green := 255, blue := 0 : rgb }

def semitransparent_red : rgba := { red with alpha := 0x7f }
/-!

Notice that the `with` clause allows you to copy the values from another object and override
just a subset of fields that you want to change and this works with base types
as shown in `semitransparent_red`.

Values can be also extracted using dot notation:
-/
#eval yellow.green   -- 255
/-!
Next, we define an operation called shuffle:
-/
def shuffle (c : rgb) := {
  c with
    red := c.green,
    green := c.blue,
    blue := c.red
}

#eval shuffle yellow  -- { red := 255, green := 0, blue := 255 }
/-!
Applying shuffle three times in a row is the same as not applying it at all:
-/
lemma shuffle_shuffle_shuffle (c : rgb) :
  shuffle (shuffle (shuffle c)) = c := by
    cases c
    rfl

/-!
The proof relies on the `cases` tactic, a close relative of `induction`. It performs a
case distinction on its argument, but it does not generate induction hypotheses.
For `rgb`, the invocation `cases c` transforms a goal `⊢ P[c]` into a subgoal
`r g b : ℕ ⊢ P[rgb.mk r g b]`. We could also have used `induction c`.

In a structured proof, we can use `match` expressions to perform a case distinction.
For example:
-/
lemma shuffle_shuffle_shuffle₂ (c : rgb) :
  shuffle (shuffle (shuffle c)) = c :=
  match c with
  | rgb.mk _ _ _ => Eq.refl _

/-!
Recall from [Section 2.4](../BackwardProofs/Equality.lean.md) that `Eq.refl` is the property
`∀a, a = a`.
-/
