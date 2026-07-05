module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Instances.Rat

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S31

/- Space 31: Square of one-point compactification of ℚ.
See https://topology.pi-base.org/spaces/S000031.
The product `OnePoint ℚ × OnePoint ℚ`, where `OnePoint ℚ` (π-Base S29) carries the
Alexandroff one-point compactification topology of ℚ and the square carries the
product topology. -/

/-- Square of one-point compactification of ℚ (pi-Base S31). -/
def S31 : Type := OnePoint ℚ × OnePoint ℚ

instance : TopologicalSpace S31 := inferInstanceAs (TopologicalSpace (OnePoint ℚ × OnePoint ℚ))

end S31
end PiBase.Spaces
