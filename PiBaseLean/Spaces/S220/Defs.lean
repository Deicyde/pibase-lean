module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.UpperLowerSetTopology

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S220

/- Space 220: Right "closed-ray" topology on ω₁.
See https://topology.pi-base.org/spaces/S000220.
Carrier X = ω₁ = [0, ω₁) with its usual order; the open sets are exactly the
upward-closed ("upper") sets of (X, ≤) -- i.e. the upper set topology. -/

/-- The carrier `ω₁ = [0, ω₁)`, ordinals below the least uncountable ordinal
(pi-Base S220). -/
def S220 : Type 1 := {o : Ordinal.{0} // o < ω₁}

noncomputable instance : LinearOrder S220 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω₁})

/-- The right "closed-ray" topology: open sets are the upward-closed sets of
`(S220, ≤)`, i.e. `∅` and the "closed rays" `[α, →)`. -/
noncomputable instance : TopologicalSpace S220 := Topology.upperSet S220

end S220
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S220 as a bundled `Space` (carrier + topology). -/
noncomputable def S220 : Space := ⟨PiBase.Spaces.S220.S220, inferInstance⟩

end PiBase.Formal
