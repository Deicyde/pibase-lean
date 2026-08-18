module

public import PiBaseLean.AdditionalDefs.Meta
public import PiBaseLean.Properties.P9.Defs

@[expose] public section

namespace PiBase

open Topology Filter Set Function TopologicalSpace

section Meta

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem WellDefined.functionallyT2Space : WellDefined FunctionallyT2Space :=
  fun {X Y} _ _ φ h => by
    constructor
    rw [← EquivLike.pairwise_comp_iff φ.some]
    intro x y hxy
    rcases h.functionally_t2 hxy with ⟨f, f₀, f₁⟩
    refine ⟨f.comp (φ.some.symm : C(Y, X)), ?_, ?_⟩ <;> simpa

theorem Homeomorph.functionallyT2Space [FunctionallyT2Space X] (f : X ≃ₜ Y) : FunctionallyT2Space Y :=
  WellDefined.functionallyT2Space ⟨f⟩ inferInstance

end Meta

end PiBase
