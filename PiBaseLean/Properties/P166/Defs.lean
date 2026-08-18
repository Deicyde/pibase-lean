module

public import Mathlib.Topology.MetricSpace.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter TopologicalSpace

universe u v

namespace PiBase

/- 166. Has a coarser separable metrizable topology -/
class HasCoarserSeparableMetrizableTopology (X : Type u) [τ : TopologicalSpace X] : Prop where
  ex_coarser_metrizable_separable : ∃ m : MetricSpace X,
    τ ≤ m.toUniformSpace.toTopologicalSpace ∧ @SeparableSpace X m.toUniformSpace.toTopologicalSpace

end PiBase

namespace PiBase.Formal

theorem hasCoarserSeparableMetrizableTopology_of_homeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (h : HasCoarserSeparableMetrizableTopology X) :
    HasCoarserSeparableMetrizableTopology Y := by
  obtain ⟨mX, hm_le, hm_sep⟩ := h.ex_coarser_metrizable_separable
  let e : X ≃ Y := φ.toEquiv
  let mY : MetricSpace Y := MetricSpace.induced e.symm e.symm.injective mX
  refine ⟨⟨mY, ?_, ?_⟩⟩
  · have h_ind : mY.toUniformSpace.toTopologicalSpace =
        TopologicalSpace.induced (e.symm : Y → X) mX.toUniformSpace.toTopologicalSpace := rfl
    intro s hs
    rw [h_ind] at hs
    obtain ⟨u, hu, hus⟩ :=
      (isOpen_induced_iff (t := mX.toUniformSpace.toTopologicalSpace) (f := e.symm)).mp hs
    rw [← hus]
    exact (hm_le u hu).preimage φ.symm.continuous
  · let τX : TopologicalSpace X := mX.toUniformSpace.toTopologicalSpace
    let τY : TopologicalSpace Y := mY.toUniformSpace.toTopologicalSpace
    have hτY : τY = TopologicalSpace.induced (e.symm : Y → X) τX := rfl
    have h_cont_symm : @Continuous Y X τY τX (e.symm : Y → X) := by
      rw [hτY]
      exact continuous_induced_dom
    have h_cont : @Continuous X Y τX τY (e : X → Y) := by
      rw [hτY, continuous_induced_rng]
      simpa using (@continuous_id X τX)
    let hY : @Homeomorph X Y τX τY :=
      { toEquiv := e
        continuous_toFun := h_cont
        continuous_invFun := h_cont_symm }
    let : TopologicalSpace X := τX
    let : TopologicalSpace Y := τY
    let : SeparableSpace X := hm_sep
    exact hY.isQuotientMap.separableSpace

def P166 : Property where
  toPred := HasCoarserSeparableMetrizableTopology
  well_defined := hasCoarserSeparableMetrizableTopology_of_homeomorph

namespace P166

theorem well_defined {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (h : HasCoarserSeparableMetrizableTopology X) :
    HasCoarserSeparableMetrizableTopology Y :=
  hasCoarserSeparableMetrizableTopology_of_homeomorph φ h

end P166

end PiBase.Formal
