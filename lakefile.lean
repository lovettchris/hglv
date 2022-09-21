import Lake
open Lake DSL

package hitchikersGuide {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[defaultTarget]
lean_lib Basics {
  -- add library configuration options here
}

lean_lib BackwardProofs {
  -- add library configuration options here
}
