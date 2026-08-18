module

public import PiBaseLean.AdditionalDefs.AlphaTransport
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter Function

namespace PiBase

/- 211. α₁.₅ space -/
class α15Space (X : Type*) [TopologicalSpace X] : Prop where
  subset_converge {x : X} {S : ℕ → ℕ → X} (S_inj : ∀ n, Injective (S n))
    (S_disj : Pairwise (fun n m ↦ range (S n) ∩ range (S m) = ∅))
    (hS : ∀ n : ℕ, Tendsto (S n) atTop (𝓝 x)) : ∃ T : ℕ → X, Injective T ∧
      Tendsto T atTop (𝓝 x) ∧ range T ⊆ ⋃ n, range (S n) ∧
        {n | (range (S n) \ range T).Finite}.Infinite

end PiBase

namespace PiBase.Formal

def P211 : Property where
  toPred := α15Space
  well_defined {X Y} _ _ φ h := by
    constructor
    intro y S S_inj S_disj hS
    obtain ⟨T, hT_inj, hT_tend, hT_sub, hT_inf⟩ :=
      h.subset_converge (x := φ.symm y) (S := fun n => φ.symm ∘ S n)
        (fun n => φ.symm.injective.comp (S_inj n))
        (AlphaTransport.symm_pairwise_disjoint φ S S_disj)
        (fun n => AlphaTransport.tendsto_symm_comp φ (hS n))
    exact ⟨φ ∘ T, φ.injective.comp hT_inj, AlphaTransport.tendsto_comp_of_symm φ hT_tend,
      AlphaTransport.range_comp_subset φ S T hT_sub,
      AlphaTransport.infinite_setOf_finite_diff φ S T hT_inf⟩

end PiBase.Formal
