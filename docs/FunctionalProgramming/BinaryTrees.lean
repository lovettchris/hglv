import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Init.Data.Nat.Basic

/-!
## Binary Trees

Inductive types with constructors taking several recursive arguments define treelike objects.
_Binary trees_ have nodes with at most two children. A possible definition of binary trees follows:
-/
inductive BTree (α : Type) : Type
| empty : BTree α
| node : α → BTree α → BTree α → BTree α
deriving Repr
/-!

-- BUGBUG - can you do this in lean4?  lean3 example had `| empty {} : BTree`

(The `{}` annotation is often used with nullary constructors of polymorphic types.
Here, it indicates that the type `α` should be implicitly derived from the context
around `BTree.empty`. We can then write `BTree.empty` instead of `BTree.empty N`,
`tree.empty _`, etc.)

With binary trees, structural induction gives rise to two induction hypotheses:
one for the left subtree of an inner node and one for the right subtree. To prove a
goal `t : tree α ⊢ P[t]` by structural induction on `t`, we need to show the sub-goals

```lean
⊢ P[tree.empty]
a : α, l r : tree α, ih_l : P[l], ih_r : P[r] ⊢ P[tree.node a l r]
```

The tree counterpart to list reversal is the mirror operation:
-/
def mirror {α : Type} : BTree α → BTree α
| BTree.empty => BTree.empty
| (BTree.node a l r) => BTree.node a (mirror r) (mirror l)

/-!
Mirroring can be defined directly, without appealing to some append operation. As a result,
reasoning about `mirror` is simpler than reasoning about `reverse`, as we can see below:
-/
lemma mirror_mirror {α : Type} (t : BTree α) :
  mirror (mirror t) = t := by
  induction t with
  | empty => rfl
  | node a l r ih_l ih_r =>
    simp [mirror, ih_l, ih_r]
/-!
A more detailed informal proof would be as follows:

- The proof is by structural induction on t.
- Case `tree.empty`: We must show that
`mirror (mirror tree.empty) = tree.empty`.
This follows directly from the definition of `mirror`.

- Case `tree.node a l r`: The induction hypotheses are
`(ih_l) mirror (mirror l) = l` and `(ih_r) mirror (mirror r) = r`
- We must show `mirror (mirror (tree.node a l r)) = tree.node a l r`.
- We have
```
mirror (mirror (tree.node a l r))
= mirror (tree.node a (mirror r) (mirror l)) (by def. of mirror)
= tree.node a (mirror (mirror l)) (mirror (mirror r)) (ditto)
= tree.node a l (mirror (mirror r)) (by ih_l)
= tree.node a l r (by ih_r)
```
<span class="qed"></span>

To achieve the same level of detail in the Lean proof, we could use a calculational
block ([Section 3.4](../ForwardProofs/CalculationProofs.lean.md)) instead of `simp`:

-/
lemma mirror_mirror2 {α : Type} :
    ∀t : BTree α, mirror (mirror t) = t
| BTree.empty => by rfl
| (BTree.node a l r) =>
calc mirror (mirror (BTree.node a l r))
  = mirror (BTree.node a (mirror r) (mirror l)) :=
    by rfl
  _ = BTree.node a (mirror (mirror l)) (mirror (mirror r)) :=
    by rfl
  _ = BTree.node a l (mirror (mirror r)) :=
    by rw [mirror_mirror2 l]
  _ = BTree.node a l r :=
    by rw [mirror_mirror2 r]

/-!

So now you can see all the work that the `simp` tactic is doing for you, all it
needed was the hint _use mirror, ih_l, ih_r_.

The following lemma will be useful in Chapter 5, it simply states that the
mirror of a tree is empty iff the tree is empty.
-/
lemma mirror_eq_empty_iff {α : Type} :
∀t : BTree α, mirror t = BTree.empty ↔ t = BTree.empty
| BTree.empty => by rfl
| (BTree.node _ _ _) => by simp [mirror]

