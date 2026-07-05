module

public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S20

/- Space 20: Fort space on a countably infinite set.
See https://topology.pi-base.org/spaces/S000020.
Carrier `X = ℕ ∪ {∞}`; a set `U ⊆ X` is open iff its complement is finite or `∞ ∈ U`
(equivalently, `∞ ∉ X \ U`). This is exactly the one-point compactification of the
discrete space `ℕ`, so we take it as `OnePoint ℕ` with its standard instance. -/

/-- Fort space on a countably infinite set (pi-Base S20), realized as the
one-point compactification of the discrete space `ℕ`. -/
def S20 : Type := OnePoint ℕ

instance : TopologicalSpace S20 := inferInstanceAs (TopologicalSpace (OnePoint ℕ))

end S20
end PiBase.Spaces
