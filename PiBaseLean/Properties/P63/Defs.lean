module

public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Topology.GDelta.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 63. Cech complete -/
class CechCompleteSpace (X : Type u) [TopologicalSpace X] : Prop extends T35Space X where
  is_gδ : IsGδ (range (stoneCechUnit (α := X)))

end PiBase

namespace PiBase.Formal

def P63 : Property where
  toPred := CechCompleteSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    have hT35X : T35Space X := h.toT35Space
    have hT35Y : T35Space Y := φ.symm.isEmbedding.t35Space
    refine ⟨?_⟩
    -- The Stone-Čech extensions of `stoneCechUnit ∘ φ` and `stoneCechUnit ∘ φ.symm`.
    have hcφ : Continuous ((stoneCechUnit : Y → StoneCech Y) ∘ φ) :=
      continuous_stoneCechUnit.comp φ.continuous
    have hcψ : Continuous ((stoneCechUnit : X → StoneCech X) ∘ φ.symm) :=
      continuous_stoneCechUnit.comp φ.symm.continuous
    obtain ⟨G, hcG, hGu⟩ : ∃ G : StoneCech X → StoneCech Y, Continuous G ∧
        ∀ x : X, G (stoneCechUnit x) = stoneCechUnit (φ x) :=
      ⟨stoneCechExtend hcφ, continuous_stoneCechExtend hcφ,
        fun x => stoneCechExtend_stoneCechUnit hcφ x⟩
    obtain ⟨H, hcH, hHu⟩ : ∃ H : StoneCech Y → StoneCech X, Continuous H ∧
        ∀ y : Y, H (stoneCechUnit y) = stoneCechUnit (φ.symm y) :=
      ⟨stoneCechExtend hcψ, continuous_stoneCechExtend hcψ,
        fun y => stoneCechExtend_stoneCechUnit hcψ y⟩
    have hGH : ∀ z : StoneCech Y, G (H z) = z := by
      have hcomp : G ∘ H = id :=
        stoneCech_hom_ext (hcG.comp hcH) continuous_id <| funext fun y => by
          simp only [Function.comp_apply, hHu, hGu, φ.apply_symm_apply, id_eq]
      exact fun z => congrFun hcomp z
    have hrange : range (stoneCechUnit (α := Y)) = H ⁻¹' range (stoneCechUnit (α := X)) := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨φ.symm y, (hHu y).symm⟩
      · rintro ⟨x, hx⟩
        refine ⟨φ x, ?_⟩
        calc stoneCechUnit (φ x) = G (stoneCechUnit x) := (hGu x).symm
          _ = G (H z) := by rw [hx]
          _ = z := hGH z
    rw [hrange]
    exact h.is_gδ.preimage hcH

end PiBase.Formal
