module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Data.Prod.Lex
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval
public import Mathlib.Data.Real.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S173

/- Space 173: Product of long ray and continuum power of a closed interval.
See https://topology.pi-base.org/spaces/S000173.
The product of the long ray (S38), the lexicographic order topology on
`{o : Ordinal // o < ω₁} ×ₗ [0,1)`, and the continuum power of `[0,1]` (S103), i.e.
`unitInterval → unitInterval` with the product topology, itself given the product topology. -/

/-- The long ray factor (pi-Base S38): the lexicographic order topology on
`{o : Ordinal // o < ω₁} ×ₗ [0,1)`.
(`Ordinal.{0} : Type 1`, so this factor lives in `Type 1`, not `Type 0`.) -/
def S173.LongRay : Type 1 := { o : Ordinal.{0} // o < ω₁ } ×ₗ ↥(Set.Ico (0 : ℝ) 1)

noncomputable instance : LinearOrder S173.LongRay :=
  inferInstanceAs (LinearOrder ({o : Ordinal.{0} // o < ω₁} ×ₗ ↥(Set.Ico (0 : ℝ) 1)))

noncomputable instance : TopologicalSpace S173.LongRay := Preorder.topology S173.LongRay

instance : OrderTopology S173.LongRay := ⟨rfl⟩

/-- The continuum power of `[0,1]` factor (pi-Base S103), i.e. `I^I`, carried by
`unitInterval → unitInterval` with the product topology. -/
def S173.Cube : Type := unitInterval → unitInterval

instance : TopologicalSpace S173.Cube := Pi.topologicalSpace

/-- Product of long ray and continuum power of a closed interval (pi-Base S173). -/
def S173 : Type 1 := S173.LongRay × S173.Cube

noncomputable instance : TopologicalSpace S173 :=
  inferInstanceAs (TopologicalSpace (S173.LongRay × S173.Cube))

end S173
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S173 as a bundled `Space` (carrier + topology). -/
noncomputable def S173 : Space := ⟨PiBase.Spaces.S173.S173, inferInstance⟩

end PiBase.Formal
