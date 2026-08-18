module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.DiscreteSubset
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 168. Countable sets are discrete -/
class CountableSetsDiscrete (X : Type u) [TopologicalSpace X] : Prop where
  countable_discrete : ∀ ⦃s : Set X⦄, s.Countable → IsDiscrete s

end PiBase

namespace PiBase.Formal

def P168 : Property where
  toPred := CountableSetsDiscrete
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    refine ⟨fun {s} hs => ?_⟩
    have hdisc : IsDiscrete (φ ⁻¹' s) :=
      h.countable_discrete (hs.preimage φ.injective)
    have h1 : IsDiscrete (φ '' (φ ⁻¹' s)) := hdisc.image φ.isInducing
    rwa [φ.image_preimage] at h1

end PiBase.Formal
