module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P246.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem Homeomorph.collectionwiseHausdorffSpace
    [h : CollectionwiseHausdorffSpace X] (f : X ≃ₜ Y) :
    CollectionwiseHausdorffSpace Y :=
  PiBase.Formal.P246.well_defined f h

-- Transport via Homeomorph image: closed preimage via Homeomorph,
-- discrete via subtype homeomorph, open cover via isOpenMap, etc.
theorem WellDefined.collectionwiseHausdorffSpace : WellDefined CollectionwiseHausdorffSpace :=
  fun {_ _} _ _ h _ => Homeomorph.collectionwiseHausdorffSpace h.some

end Meta

end PiBase
