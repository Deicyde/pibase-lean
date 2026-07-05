module

public import Mathlib.Topology.Order
public import Mathlib.Topology.Instances.Real.Lemmas

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S133

/- Space 133: Real line with post office metric.
See https://topology.pi-base.org/spaces/S000133.
The carrier is `ℝ` with distinguished point `0`; every point `x ≠ 0` is isolated
(its singleton is a basic open set), while the basic neighborhoods of `0` are the
Euclidean open intervals `(-ε, ε)` around it — matching the topology induced by the
post office metric `d(x, y) = ‖x‖ + ‖y‖` (for `x ≠ y`), for which a ball of radius
`ε < 2 * |x|` around any `x ≠ 0` is `{x}`, while a ball of radius `ε` around `0` is
exactly `(-ε, ε)`. -/

/-- Real line with the post office metric topology (pi-Base S133). -/
def S133 : Type := ℝ

instance S133_top : TopologicalSpace S133 :=
  TopologicalSpace.generateFrom
    ({s : Set ℝ | ∃ x ≠ (0 : ℝ), s = {x}} ∪ {s : Set ℝ | ∃ ε > (0 : ℝ), s = Set.Ioo (-ε) ε})

end S133
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S133 as a bundled `Space` (carrier + topology). -/
noncomputable def S133 : Space := ⟨PiBase.Spaces.S133.S133, PiBase.Spaces.S133.S133_top⟩

end PiBase.Formal
