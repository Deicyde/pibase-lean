module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Homeomorph.Defs
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Function Set Filter Topology TopologicalSpace

namespace PiBase

/- 25. Exhaustlible by compacts -/
class ExhaustibleByCompacts (X : Type*) [TopologicalSpace X] : Prop where
  exhaustion : Nonempty (CompactExhaustion X)

end PiBase

namespace PiBase.Formal

def P25 : Property where
  toPred := ExhaustibleByCompacts
  well_defined φ h := by
    obtain ⟨K⟩ := h.exhaustion
    refine ⟨⟨⟨fun n => φ '' K n, fun n => (K.isCompact' n).image φ.continuous, fun n => ?_, ?_⟩⟩⟩
    · -- monotonicity via image_mono and φ.continuous / φ.image_interior
      have h1 : φ '' K n ⊆ φ '' interior (K (n + 1)) :=
        Set.image_mono (K.subset_interior_succ n)
      rw [φ.image_interior] at h1
      exact h1
    · -- union univ via image_iUnion and image_univ/surjective
      calc (⋃ n, φ '' K n : Set _) = φ '' (⋃ n, K n) := by
            rw [← Set.image_iUnion]
        _ = φ '' univ := by rw [K.iUnion_eq]
        _ = univ := Set.image_univ_of_surjective φ.surjective

end PiBase.Formal
