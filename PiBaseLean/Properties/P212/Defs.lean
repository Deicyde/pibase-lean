module

public import PiBaseLean.AdditionalDefs.AlphaTransport
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Filter Function

namespace PiBase

/- 212. α₂ space -/
class α2Space (X : Type*) [τ : TopologicalSpace X] : Prop where
  subset_converge {x : X} {S : ℕ → ℕ → X} (S_inj : ∀ n, Injective (S n))
    (hS : ∀ n : ℕ, Tendsto (S n) atTop (𝓝 x)) : ∃ T : ℕ → X, Injective T ∧
      Tendsto T atTop (𝓝 x) ∧ range T ⊆ ⋃ n, range (S n) ∧ ∀ n, (range (S n) ∩ range T).Infinite

end PiBase

namespace PiBase.Formal

def P212 : Property where
  toPred := α2Space
  well_defined {X Y} _ _ φ h := by
    constructor
    intro y S S_inj hS
    obtain ⟨T, hT_inj, hT_tend, hT_sub, hT_inf⟩ :=
      h.subset_converge (x := φ.symm y) (S := fun n => φ.symm ∘ S n)
        (fun n => φ.symm.injective.comp (S_inj n))
        (fun n => AlphaTransport.tendsto_symm_comp φ (hS n))
    exact ⟨φ ∘ T, φ.injective.comp hT_inj, AlphaTransport.tendsto_comp_of_symm φ hT_tend,
      AlphaTransport.range_comp_subset φ S T hT_sub,
      fun n => (AlphaTransport.infinite_inter_iff φ (S n) T).2 (hT_inf n)⟩

end PiBase.Formal
