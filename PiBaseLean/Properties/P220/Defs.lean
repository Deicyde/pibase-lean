module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

namespace PiBase

/- 220. Ultrametrizable -/
class UltraMetrizableSpace (X : Type*) [τ : TopologicalSpace X] : Prop where
  ex_ultrametric : ∃ (t : MetricSpace X),
    IsUltrametricDist X ∧ t.toUniformSpace.toTopologicalSpace = τ

end PiBase

namespace PiBase.Formal

def P220 : Property where
  toPred := UltraMetrizableSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    obtain ⟨mX, hUltraX, hTopX⟩ := h.ex_ultrametric
    -- Pull the ultrametric back along the injection `φ.symm : Y → X`.
    let mY : MetricSpace Y := MetricSpace.induced φ.symm φ.symm.injective mX
    have hUltraY : @IsUltrametricDist Y mY.toDist :=
      ⟨fun y₁ y₂ y₃ => hUltraX.dist_triangle_max (φ.symm y₁) (φ.symm y₂) (φ.symm y₃)⟩
    have hTopY : mY.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Y) := by
      have hcomap : mY.toUniformSpace.toTopologicalSpace =
          TopologicalSpace.induced φ.symm mX.toUniformSpace.toTopologicalSpace := rfl
      rw [hcomap, hTopX]
      exact φ.symm.induced_eq
    exact ⟨mY, hUltraY, hTopY⟩

end PiBase.Formal
