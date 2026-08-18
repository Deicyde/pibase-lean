module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P184.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.embeddableInEuclideanSpace [EmbeddableInEuclideanSpace X]
    (f : X ≃ₜ Y) : EmbeddableInEuclideanSpace Y :=
  Formal.P184.well_defined f ‹_›

theorem WellDefined.embeddableInEuclideanSpace : WellDefined EmbeddableInEuclideanSpace :=
  fun {_ _} _ _ h _ => Homeomorph.embeddableInEuclideanSpace h.some

end Meta

end PiBase
