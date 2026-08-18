module

public import PiBaseLean.AdditionalDefs.Constructions
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Function Topology Set

namespace PiBase

/- 38. Injectively path connected -/
class InjPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  joined : IsInjPathConnected (Set.univ (α := X))

end PiBase

namespace PiBase.Formal

def P38 : Property where
  toPred := InjPathConnectedSpace
  well_defined φ h := by
    constructor
    intro x y hxy _ _
    have hxy' : φ.symm x ≠ φ.symm y := by
      intro heq
      apply hxy
      calc x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
        _ = φ (φ.symm y) := by rw [heq]
        _ = y := φ.apply_symm_apply y
    obtain ⟨p, hinj, _⟩ := h.joined hxy' trivial trivial
    refine ⟨⟨⟨fun t => φ (p t), φ.continuous.comp p.continuous⟩, ?_, ?_⟩, ?_, subset_univ _⟩
    · simp [p.source, Homeomorph.apply_symm_apply]
    · simp [p.target, Homeomorph.apply_symm_apply]
    · exact φ.injective.comp hinj

end PiBase.Formal
