module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P243.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.Set.Countable

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.hasCountablePiWeight [HasCountablePiWeight X] (f : X ≃ₜ Y) :
    HasCountablePiWeight Y :=
  Formal.P243.well_defined f (inferInstance : HasCountablePiWeight X)

theorem WellDefined.hasCountablePiWeight : WellDefined HasCountablePiWeight :=
  fun {_ _} _ _ h hX => Homeomorph.hasCountablePiWeight h.some

end Meta

end PiBase
