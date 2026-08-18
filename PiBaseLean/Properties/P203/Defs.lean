module

public import Mathlib.Topology.Order
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

namespace PiBase

/- 203. Almost discrete -/
class AlmostDiscreteSpace (X : Type*) [TopologicalSpace X] : Prop where
  ex_point : ∃ p : X, ∀ x : X, x ≠ p ↔ IsOpen {x}

end PiBase

namespace PiBase.Formal

def P203 : Property where
  toPred := AlmostDiscreteSpace
  well_defined φ h := by
    obtain ⟨p, hp⟩ := h.ex_point
    refine ⟨⟨φ p, fun x => ?_⟩⟩
    -- x ≠ φ p  ↔  φ.symm x ≠ p  (injectivity of φ.symm / φ)
    have h_ne_iff : x ≠ φ p ↔ φ.symm x ≠ p := by
      constructor
      · intro h_ne h_eq
        apply h_ne
        calc x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
          _ = φ p := by rw [h_eq]
      · intro h_ne h_eq
        apply h_ne
        calc φ.symm x = φ.symm (φ p) := by rw [h_eq]
          _ = p := φ.symm_apply_apply p
    -- IsOpen preservation for singletons via φ.symm
    have h_singleton_eq : φ.symm '' {x} = {φ.symm x} := Set.image_singleton
    have h_isOpen_iff : IsOpen {φ.symm x} ↔ IsOpen {x} := by
      have h_img := φ.symm.isOpen_image (s := {x})
      rw [h_singleton_eq] at h_img
      exact h_img
    calc x ≠ φ p ↔ φ.symm x ≠ p := h_ne_iff
      _ ↔ IsOpen {φ.symm x} := hp (φ.symm x)
      _ ↔ IsOpen {x} := h_isOpen_iff

end PiBase.Formal
