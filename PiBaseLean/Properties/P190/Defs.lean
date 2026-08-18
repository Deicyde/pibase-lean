module

public import Mathlib.SetTheory.Ordinal.Topology
public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace Ordinal

universe u

namespace PiBase

/- 190. Ordinal space -/
class OrdinalSpace (X : Type u) [TopologicalSpace X] : Prop where
  homeo_ordinal : ∃ a : Ordinal.{u}, IsHomeo X (Iio a : Set Ordinal.{u})

end PiBase

namespace PiBase.Formal

def P190 : Property where
  toPred := OrdinalSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    rcases h.homeo_ordinal with ⟨a, ha⟩
    exact ⟨a, IsHomeo.trans ⟨φ.symm⟩ ha⟩

end PiBase.Formal
