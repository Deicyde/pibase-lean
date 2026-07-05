module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Data.Prod.Lex
public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S38

/- Space 38: Long ray.
See https://topology.pi-base.org/spaces/S000038.
The lexicographic order topology on X = ω₁ × [0,1), i.e. the order topology induced by the
lexicographic order on (the ordinals below the first uncountable ordinal ω₁) ×ₗ [0,1) ⊆ ℝ. -/

/-- The Long ray (pi-Base S38): the lexicographic order topology on
`{o : Ordinal // o < ω₁} ×ₗ [0,1)`.
(`Ordinal.{0} : Type 1`, so the carrier lives in `Type 1`, not `Type 0`.) -/
def S38 : Type 1 := { o : Ordinal.{0} // o < ω₁ } ×ₗ ↥(Set.Ico (0 : ℝ) 1)

noncomputable instance : LinearOrder S38 :=
  inferInstanceAs (LinearOrder ({o : Ordinal.{0} // o < ω₁} ×ₗ ↥(Set.Ico (0 : ℝ) 1)))

noncomputable instance S38_top : TopologicalSpace S38 := Preorder.topology S38

instance : OrderTopology S38 := ⟨rfl⟩

end S38
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S38 as a bundled `Space` (carrier + topology). -/
noncomputable def S38 : Space := ⟨PiBase.Spaces.S38.S38, PiBase.Spaces.S38.S38_top⟩

end PiBase.Formal
