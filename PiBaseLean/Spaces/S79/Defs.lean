module

public import PiBaseLean.Spaces.S78.Defs

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology OnePoint Ordinal

namespace PiBase.Spaces

/- Space 79: Deleted Tychonoff plank.
See https://topology.pi-base.org/spaces/S000079.
The Tychonoff plank `[0, ω₁] × [0, ω]` (S78) with its corner point `(ω₁, ∞)` removed,
carrying the subspace topology. -/

/-- The corner point `(ω₁, ∞)` of the Tychonoff plank (S78) that gets deleted. -/
noncomputable def S79.corner : S78 := (⟨ω₁, le_refl ω₁⟩, ∞)

/-- Deleted Tychonoff plank (pi-Base S79): the Tychonoff plank (S78) with its corner
point `(ω₁, ∞)` removed, as a subtype of `S78` with the subspace topology. -/
def S79 : Type 1 := {p : S78 // p ≠ S79.corner}

noncomputable instance S79_top : TopologicalSpace S79 :=
  inferInstanceAs (TopologicalSpace {p : S78 // p ≠ S79.corner})

end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S79 as a bundled `Space` (carrier + topology). -/
noncomputable def S79 : Space := ⟨PiBase.Spaces.S79, PiBase.Spaces.S79_top⟩

end PiBase.Formal
