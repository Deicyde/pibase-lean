module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S195

/- Space 195: Join of cofinite and left-ray topologies on ω₁.
See https://topology.pi-base.org/spaces/S000195.
The set of ordinals below the least uncountable ordinal ω₁, with the topology generated
by the sets `[0,α) \ F = {x | x < α} \ F` for `α < ω₁` and `F ⊆ ω₁` finite — the join, in
the lattice of topologies, of the cofinite topology and the left-ray (initial-segment)
topology. -/

/-- Join of cofinite and left-ray topologies on ω₁ (pi-Base S195): the ordinals below the
least uncountable ordinal. -/
def S195 : Type 1 := {o : Ordinal.{0} // o < ω₁}

noncomputable instance : LinearOrder S195 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω₁})

instance S195_top : TopologicalSpace S195 :=
  TopologicalSpace.generateFrom
    {s : Set S195 | ∃ (a : S195) (F : Finset S195), s = {x : S195 | x < a} \ ↑F}

end S195
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S195 as a bundled `Space` (carrier + topology). -/
noncomputable def S195 : Space := ⟨PiBase.Spaces.S195.S195, PiBase.Spaces.S195.S195_top⟩

end PiBase.Formal
