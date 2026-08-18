module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

set_option linter.style.haveILetI false

namespace PiBase

/- 133. Lots -/
class Lots (X : Type*) [TopologicalSpace X] : Prop where
  from_linear_order : ∃ (_ : LinearOrder X), OrderTopology X

end PiBase

namespace PiBase.Formal

def P133 : Property where
  toPred := Lots
  well_defined {X Y} _ _ φ h := by
    obtain ⟨loX, otX⟩ := h.from_linear_order
    letI : LinearOrder X := loX
    let loY : LinearOrder Y := LinearOrder.lift' φ.symm φ.symm.injective
    letI : LinearOrder Y := loY
    have hIoi : ∀ b : X, φ.symm ⁻¹' Set.Ioi b = Set.Ioi (φ b) := by
      intro b
      ext y
      simp only [Set.mem_preimage, Set.mem_Ioi]
      have hsym : φ.symm (φ b) = b := φ.symm_apply_apply b
      constructor
      · intro hb
        change φ.symm (φ b) < φ.symm y
        rw [hsym]
        exact hb
      · intro hy
        change φ.symm (φ b) < φ.symm y at hy
        rw [hsym] at hy
        exact hy
    have hIio : ∀ b : X, φ.symm ⁻¹' Set.Iio b = Set.Iio (φ b) := by
      intro b
      ext y
      simp only [Set.mem_preimage, Set.mem_Iio]
      have hsym : φ.symm (φ b) = b := φ.symm_apply_apply b
      constructor
      · intro hb
        change φ.symm y < φ.symm (φ b)
        rw [hsym]
        exact hb
      · intro hy
        change φ.symm y < φ.symm (φ b) at hy
        rw [hsym] at hy
        exact hy
    have hBasisEq :
        Set.preimage φ.symm '' {s : Set X | ∃ a : X, s = Set.Ioi a ∨ s = Set.Iio a}
        = {t : Set Y | ∃ a : Y, t = Set.Ioi a ∨ t = Set.Iio a} := by
      ext t
      constructor
      · rintro ⟨s, ⟨a, ha⟩, rfl⟩
        rcases ha with rfl | rfl
        · rw [hIoi a]
          exact ⟨φ a, Or.inl rfl⟩
        · rw [hIio a]
          exact ⟨φ a, Or.inr rfl⟩
      · rintro ⟨a, ha⟩
        rcases ha with rfl | rfl
        · refine ⟨Set.Ioi (φ.symm a), ⟨φ.symm a, Or.inl rfl⟩, ?_⟩
          rw [hIoi (φ.symm a), φ.apply_symm_apply]
        · refine ⟨Set.Iio (φ.symm a), ⟨φ.symm a, Or.inr rfl⟩, ?_⟩
          rw [hIio (φ.symm a), φ.apply_symm_apply]
    have hX_eq : (inferInstance : TopologicalSpace X) =
        TopologicalSpace.generateFrom
          {s : Set X | ∃ a : X, s = Set.Ioi a ∨ s = Set.Iio a} :=
      otX.topology_eq_generate_intervals
    have hInd : TopologicalSpace.induced φ.symm (inferInstance : TopologicalSpace X) =
        (inferInstance : TopologicalSpace Y) :=
      φ.symm.induced_eq
    have hY_eq : (inferInstance : TopologicalSpace Y) =
        TopologicalSpace.generateFrom
          {t : Set Y | ∃ a : Y, t = Set.Ioi a ∨ t = Set.Iio a} := by
      calc (inferInstance : TopologicalSpace Y)
          = TopologicalSpace.induced φ.symm (inferInstance : TopologicalSpace X) :=
            hInd.symm
        _ = TopologicalSpace.induced φ.symm
              (TopologicalSpace.generateFrom
                {s : Set X | ∃ a : X, s = Set.Ioi a ∨ s = Set.Iio a}) := by
              rw [hX_eq]
        _ = TopologicalSpace.generateFrom
              (Set.preimage φ.symm ''
                {s : Set X | ∃ a : X, s = Set.Ioi a ∨ s = Set.Iio a}) := by
              rw [induced_generateFrom_eq]
        _ = TopologicalSpace.generateFrom
              {t : Set Y | ∃ a : Y, t = Set.Ioi a ∨ t = Set.Iio a} := by
              rw [hBasisEq]
    constructor
    refine ⟨loY, ⟨hY_eq⟩⟩

end PiBase.Formal
