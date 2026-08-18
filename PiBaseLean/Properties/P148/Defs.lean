module

public import PiBaseLean.Properties.P141.Defs
public import PiBaseLean.Properties.P143.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 148. CWGH -/
class CWGH (X : Type u) [TopologicalSpace X] : Prop extends CompactlyGeneratedSpace X, WeakT2Space X

end PiBase

namespace PiBase.Formal

def P148 : Property where
  toPred := CWGH
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y)
      (h : CWGH X) := by
    have hCWGH_X : CWGH X := h
    have hCG_X : CompactlyGeneratedSpace X := inferInstance
    have hW_X : WeakT2Space X := inferInstance
    have hCG_Y : CompactlyGeneratedSpace Y := Formal.P141.well_defined φ hCG_X
    have hW_Y : WeakT2Space Y := Formal.P143.well_defined φ hW_X
    exact @CWGH.mk _ _ hCG_Y hW_Y

end PiBase.Formal
