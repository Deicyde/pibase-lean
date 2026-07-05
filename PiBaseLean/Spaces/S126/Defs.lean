module

public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S126

/- Space 126: Punctured Knaster-Kuratowski fan.
See https://topology.pi-base.org/spaces/S000126.
π-Base S125 (the Knaster-Kuratowski fan) with the apex removed. For `a ∈ [0,1]` let
`L(a)` be the line segment from `(a, 0)` to `p = (1/2, 1/2)`. Let `C` be the middle-thirds
Cantor set in `[0,1]`; let `E` be the endpoints of the intervals removed in the
construction of `C` (obtained, just like `C` itself, as the union over `n` of the finite
sets of "corner" points reachable from `{0,1}` by `n` applications of `x ↦ x/3` and
`x ↦ (2+x)/3`); let `F = C \ E`. Put `A = {(x,y) ∈ L(c) | c ∈ E, y ∈ ℚ}` and
`B = {(x,y) ∈ L(c) | c ∈ F, y ∉ ℚ}`. This space is `X = (A ∪ B) \ {p} ⊆ ℝ × ℝ`, with the
subspace topology. -/

/-- For `a : ℝ`, the line segment `L(a)` from `(a, 0)` to the apex `p = (1/2, 1/2)`,
inside `ℝ × ℝ`. -/
def S126.L (a : ℝ) : Set (ℝ × ℝ) := segment ℝ (a, (0 : ℝ)) ((1 / 2 : ℝ), (1 / 2 : ℝ))

/-- The `n`-th finite stage of the "endpoints of removed intervals" construction: the
corner points reachable from the seed `{0, 1}` by `n` applications of the two maps
`x ↦ x / 3` and `x ↦ (2 + x) / 3` used to build the Cantor set. Mirrors
`preCantorSet` (whose seed is `[0, 1]` instead of `{0, 1}`). -/
def S126.preEndpoints : ℕ → Set ℝ
  | 0 => {0, 1}
  | n + 1 => (· / 3) '' S126.preEndpoints n ∪ (fun x => (2 + x) / 3) '' S126.preEndpoints n

/-- `E`, the endpoints of the intervals removed in the construction of the Cantor set:
the union, over all finite stages, of the corner points introduced at that stage. -/
def S126.E : Set ℝ := ⋃ n, S126.preEndpoints n

/-- `F = C \ E`, the points of the Cantor set that are not endpoints of a removed
interval. -/
def S126.F : Set ℝ := cantorSet \ S126.E

/-- `A = {(x, y) ∈ L(c) | c ∈ E, y ∈ ℚ}`. -/
def S126.A : Set (ℝ × ℝ) := {q : ℝ × ℝ | ∃ c ∈ S126.E, q ∈ S126.L c ∧ ¬ Irrational q.2}

/-- `B = {(x, y) ∈ L(c) | c ∈ F, y ∉ ℚ}`. -/
def S126.B : Set (ℝ × ℝ) := {q : ℝ × ℝ | ∃ c ∈ S126.F, q ∈ S126.L c ∧ Irrational q.2}

/-- The apex `p = (1/2, 1/2)` of the fan, removed to form the punctured space. -/
noncomputable def S126.apex : ℝ × ℝ := (1 / 2, 1 / 2)

/-- The carrier set of the punctured Knaster-Kuratowski fan: `X = (A ∪ B) \ {p}`,
as a subset of `ℝ × ℝ`. -/
def S126Set : Set (ℝ × ℝ) := (S126.A ∪ S126.B) \ {S126.apex}

/-- Punctured Knaster-Kuratowski fan (pi-Base S126): the Knaster-Kuratowski fan
(pi-Base S125) with its apex removed, as a subspace of `ℝ × ℝ`. -/
noncomputable def S126 : Type := S126Set

instance : TopologicalSpace S126 := inferInstanceAs (TopologicalSpace S126Set)

end S126
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S126 as a bundled `Space` (carrier + topology). -/
noncomputable def S126 : Space := ⟨PiBase.Spaces.S126.S126, inferInstance⟩

end PiBase.Formal
