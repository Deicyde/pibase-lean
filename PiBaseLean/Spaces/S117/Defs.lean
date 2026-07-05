module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology
open scoped Convex

namespace PiBase.Spaces
namespace S117

/- Space 117: Closed infinite broom.
See https://topology.pi-base.org/spaces/S000117.
The carrier is `⋃ n, [ (0,0) -[ℝ] (1, 1/(n+1)) ] ∪ [ (0,0) -[ℝ] (1,0) ] ⊆ ℝ × ℝ`
(the closed line segments `L_n` from `(0,0)` to `(1, 1/(n+1))` for `n : ℕ`, together
with `L_∞ = [0,1] × {0}`, the segment from `(0,0)` to `(1,0)`); topologized as a
subspace of the plane `ℝ × ℝ` with its product topology. -/

/-- The carrier of the closed infinite broom (pi-Base S117): the union of the closed
segments from `(0,0)` to `(1, 1/(n+1))` for each `n : ℕ`, together with the closed
segment `L_∞` from `(0,0)` to `(1,0)`, sitting inside the plane `ℝ × ℝ`. -/
def S117.carrier : Set (ℝ × ℝ) :=
  (⋃ n : ℕ, [(0, 0) -[ℝ] (1, 1 / (n + 1))]) ∪ [(0, 0) -[ℝ] (1, 0)]

/-- Closed infinite broom (pi-Base S117). -/
def S117 : Type := S117.carrier

instance : TopologicalSpace S117 := instTopologicalSpaceSubtype

end S117
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S117 as a bundled `Space` (carrier + topology). -/
noncomputable def S117 : Space := ⟨PiBase.Spaces.S117.S117, inferInstance⟩

end PiBase.Formal
