module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

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

instance S12_top : TopologicalSpace S12 :=
  TopologicalSpace.generateFrom {s : Set S12 | s = Set.univ ∨ (0 : ℕ) ∉ s}

end S12
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S12 as a bundled `Space` (carrier + topology). -/
noncomputable def S12 : Space := ⟨PiBase.Spaces.S12.S12, PiBase.Spaces.S12.S12_top⟩

end PiBase.Formal
