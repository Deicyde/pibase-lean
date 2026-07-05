module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import PiBaseLean.Spaces.S23.Defs

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S165

/- Space 165: One-point compactification of the Arens-Fort space.
See https://topology.pi-base.org/spaces/S000165.
The carrier is `OnePoint S23`, i.e. the Arens-Fort space (S23) together with a
single extra point `∞`; a set is open iff its preimage in `S23` is open, and if
it contains `∞` then the complement of that preimage is compact. -/

/-- One-point compactification of the Arens-Fort space (pi-Base S165). -/
def S165 : Type := OnePoint S23

instance : TopologicalSpace S165 := inferInstanceAs (TopologicalSpace (OnePoint S23))

end S165
end PiBase.Spaces
