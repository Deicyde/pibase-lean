module

public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S8

/- Space 8: Particular point topology on a countably infinite set.
See https://topology.pi-base.org/spaces/S000008.
On `X = ℕ` (pi-Base's `ω`), a set is open iff it contains the particular point `0`
or is empty. -/

/-- Particular point topology on a countably infinite set (pi-Base S8). -/
def S8 : Type := ℕ

instance : TopologicalSpace S8 :=
  TopologicalSpace.generateFrom {s : Set S8 | (Nat.zero : S8) ∈ s ∨ s = ∅}

end S8
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S8 as a bundled `Space` (carrier + topology). -/
noncomputable def S8 : Space := ⟨PiBase.Spaces.S8.S8, inferInstance⟩

end PiBase.Formal
