## 4.3. Structural Recursion

First example the zero case for fact should return 1.

Turns out this mistake was deliberate - which I find frustrating to the reader, do we really have to do that?
It's the sort of thing you might do in a class room to see how many students are awake, but not like this.

## 4.7 Lists

This is referring to undefined tactic in the preceeding proof:
> The clear h tactic removes the useless hypothesis h : x :: xs = x :: xs.
It doesn't use clear it uses cc, but it could just use simp.

Also this seems like a typo `map_zip xs ys` in `map_zip` deleting `xs ys` solves it

## 4.8 Binary Trees

Paragraph has "tree.empty instead of tree.empty N" and "tree.empty _" but I think
it means to use "btree" instead here.