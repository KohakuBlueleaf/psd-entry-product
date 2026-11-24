import MatrixIneq.Basic

/-!
# The reduced form for `n ≤ 1`

`reducedAt_zero`, `reducedAt_one`: the trivial sizes, which the general argument (`2 ≤ n`) does not cover.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

theorem reducedAt_zero : ReducedAt 0 := by
  intro A _; simp

theorem reducedAt_one : ReducedAt 1 := by
  intro A _; simp


end MatrixIneq
