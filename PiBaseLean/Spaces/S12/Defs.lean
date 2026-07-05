module

public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S12

/- Space 12: Excluded Point Topology on a Countably Infinite Set.
See https://topology.pi-base.org/spaces/S000012.
Carrier `X = ℕ`; the closed sets are `∅` and the sets containing the excluded
point `0`, so a set `U ⊆ X` is open iff `U = X` or `0 ∉ U`. -/

/-- Excluded Point Topology on a Countably Infinite Set (pi-Base S12). -/
def S12 : Type := ℕ

instance : TopologicalSpace S12 :=
  TopologicalSpace.generateFrom {s : Set S12 | s = Set.univ ∨ (0 : ℕ) ∉ s}

end S12
end PiBase.Spaces
