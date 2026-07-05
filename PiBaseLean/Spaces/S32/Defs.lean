module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S32

/- Space 32: Hilbert cube $[0,1]^\omega$.
See https://topology.pi-base.org/spaces/S000032.
The countable product of copies of the unit interval `unitInterval` (S158), carried by
`ℕ → unitInterval` with the product topology. -/

/-- The Hilbert cube $[0,1]^\omega$ (pi-Base S32). -/
def S32 : Type := ℕ → unitInterval

instance : TopologicalSpace S32 := Pi.topologicalSpace

/-- The Hilbert cube is compact, by Tychonoff's theorem (pi-Base P16). -/
instance : CompactSpace S32 := inferInstanceAs (CompactSpace (ℕ → unitInterval))

end S32
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S32 as a bundled `Space` (carrier + topology). -/
noncomputable def S32 : Space := ⟨PiBase.Spaces.S32.S32, inferInstance⟩

end PiBase.Formal
