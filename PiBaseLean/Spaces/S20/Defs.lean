module

public import Mathlib.Topology.Compactification.OnePoint.Basic

public import PiBaseLean.Spaces.Bundled.Defs

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

instance S20_top : TopologicalSpace S20 := inferInstanceAs (TopologicalSpace (OnePoint ℕ))

end S20
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S20 as a bundled `Space` (carrier + topology). -/
noncomputable def S20 : Space := ⟨PiBase.Spaces.S20.S20, PiBase.Spaces.S20.S20_top⟩

end PiBase.Formal
