module

public import Mathlib.Topology.Defs.Induced
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

open Topology Set Function Filter TopologicalSpace

namespace PiBase

/- 51. Scattered -/
class ScatteredSpace (X : Type*) [TopologicalSpace X] : Prop where
  scattered : ∀ s : Set X, s.Nonempty → ∃ x : s, IsOpen {x}

end PiBase

namespace PiBase.Formal

def P51 : Property where
  toPred := ScatteredSpace
  well_defined φ h := by
    constructor
    intro s hs
    -- pull nonempty subset s : Set Y back under φ to get nonempty preimage in X
    obtain ⟨⟨p, hp⟩, hp'⟩ := h.scattered (φ.toFun ⁻¹' s) <| hs.preimage φ.surjective
    -- transport singleton openness from preimage subtype point ⟨p, _⟩ to s subtype point ⟨φ p, _⟩
    refine ⟨⟨φ p, hp⟩, ?_⟩
    rw [isOpen_mk] at hp' ⊢
    obtain ⟨t, ht, tp⟩ := hp'
    rw [Set.ext_iff] at tp
    refine ⟨φ '' t, (Homeomorph.isOpen_image φ).mpr ht, ?_⟩
    ext ⟨z, zs⟩
    simp_all only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, mem_preimage, mem_singleton_iff,
      Subtype.forall, Subtype.mk.injEq, mem_image]
    refine ⟨fun hh ↦ ?_, fun hh ↦ ?_⟩
    · obtain ⟨r, rt, rz⟩ := hh
      rw [← rz, ((tp r) (rz.symm ▸ zs)).mp rt]
    exact ⟨p, (tp p <| hh.symm ▸ zs).mpr <| .refl p, hh.symm⟩

end PiBase.Formal
