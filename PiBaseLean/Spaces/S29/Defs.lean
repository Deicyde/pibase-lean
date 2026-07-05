module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S29

/- Space 29: One-point compactification of ℚ.
See https://topology.pi-base.org/spaces/S000029.
The carrier is `ℚ ∪ {∞}`; the open sets are the open subsets of ℚ together with the
sets `X \ C` (containing `∞`) for `C` compact in ℚ -- the Alexandroff one-point
compactification of ℚ (with its usual order/metric topology). -/

/-- One-point compactification of ℚ (pi-Base S29). -/
def S29 : Type := OnePoint ℚ

instance : TopologicalSpace S29 := inferInstanceAs (TopologicalSpace (OnePoint ℚ))

end S29
end PiBase.Spaces
