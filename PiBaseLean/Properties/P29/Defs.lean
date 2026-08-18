module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Defs.Basic
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function TopologicalSpace

namespace PiBase

/- 29. Countable chain condition -/
class CountableChainCondition (X : Type*) [TopologicalSpace X] : Prop where
  countable_chain_condition : ∀ ⦃S : Set (Set X)⦄,
    S.PairwiseDisjoint id → (∀ s ∈ S, IsOpen s) → S.Countable

end PiBase

namespace PiBase.Formal

def P29 : Property where
  toPred := CountableChainCondition
  well_defined {X Y} _ _ φ h := by
    refine ⟨fun {S} hDisj hOpen => ?_⟩
    have hSurj : Surjective φ := φ.surjective
    have hPreInj : Injective (Set.preimage φ) :=
      (Set.preimage_injective).mpr hSurj
    let T := (Set.preimage φ) '' S
    have hT_disj : T.PairwiseDisjoint id := by
      intro t1 ht1 t2 ht2 hne
      rcases ht1 with ⟨s1, hs1, rfl⟩
      rcases ht2 with ⟨s2, hs2, rfl⟩
      have hs_ne : s1 ≠ s2 := fun heq => hne (by rw [heq])
      exact Disjoint.preimage _ (hDisj hs1 hs2 hs_ne)
    have hT_open : ∀ t ∈ T, IsOpen t := by
      intro t ht
      rcases ht with ⟨s, hs, rfl⟩
      exact φ.isOpen_preimage.mpr (hOpen s hs)
    have hT_countable : T.Countable :=
      h.countable_chain_condition hT_disj hT_open
    exact Set.countable_of_injective_of_countable_image hPreInj.injOn hT_countable

end PiBase.Formal
