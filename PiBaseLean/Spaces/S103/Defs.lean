module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S103

/- Space 103: Continuum power of $[0,1]$.
See https://topology.pi-base.org/spaces/S000103.
The Tychonoff cube of weight continuum $I^I$, i.e. all functions `unitInterval → unitInterval`,
carried by `unitInterval → unitInterval` with the product topology. -/

/-- The continuum power of $[0,1]$, i.e. $I^I$ (pi-Base S103). -/
def S103 : Type := unitInterval → unitInterval

instance S103_top : TopologicalSpace S103 := Pi.topologicalSpace

/-- $I^I$ is compact, by Tychonoff's theorem (pi-Base P16). -/
instance : CompactSpace S103 := inferInstanceAs (CompactSpace (unitInterval → unitInterval))

end S103
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S103 as a bundled `Space` (carrier + topology). -/
noncomputable def S103 : Space := ⟨PiBase.Spaces.S103.S103, PiBase.Spaces.S103.S103_top⟩

end PiBase.Formal
