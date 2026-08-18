module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P244.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.Set.Countable

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasCountablePiCharacter [HasCountablePiCharacter X] (f : X ≃ₜ Y) :
    HasCountablePiCharacter Y :=
  Formal.P244.well_defined f (inferInstance : HasCountablePiCharacter X)

theorem WellDefined.hasCountablePiCharacter : WellDefined HasCountablePiCharacter :=
  fun {_ _} _ _ h hX => Homeomorph.hasCountablePiCharacter h.some

end Meta

end PiBase
