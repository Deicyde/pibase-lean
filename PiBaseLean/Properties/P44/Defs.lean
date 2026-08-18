module

public import Mathlib.Topology.Connected.Basic
public import PiBaseLean.Properties.Bundled.Defs
public import PiBaseLean.AdditionalDefs.Meta

@[expose] public section

open Topology Set Function Filter TopologicalSpace

universe u

namespace PiBase

/- 44. Biconnected -/
class BiconnectedSpace (X : Type*) [TopologicalSpace X] extends PreconnectedSpace X where
  no_partition : ∀ s v : Set X,
    ConnectedSpace s → s.Nontrivial → ConnectedSpace v → v.Nontrivial → (s ∩ v).Nonempty

end PiBase

namespace PiBase.Formal

def P44 : Property where
  toPred := BiconnectedSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    have hpX : PreconnectedSpace X := h.toPreconnectedSpace
    have hpY : PreconnectedSpace Y := φ.surjective.denseRange.preconnectedSpace φ.continuous
    refine ⟨fun s v hCs hNs hCv hNv => ?_⟩
    have : ConnectedSpace s := hCs
    have : ConnectedSpace v := hCv
    have eS : (φ ⁻¹' s) ≃ₜ s := (IsHomeo.subset_preimage φ s).some
    have eV : (φ ⁻¹' v) ≃ₜ v := (IsHomeo.subset_preimage φ v).some
    have hCsX : ConnectedSpace (φ ⁻¹' s) :=
      eS.symm.surjective.connectedSpace eS.symm.continuous
    have hCvX : ConnectedSpace (φ ⁻¹' v) :=
      eV.symm.surjective.connectedSpace eV.symm.continuous
    obtain ⟨x, hxs, hxv⟩ :=
      h.no_partition _ _ hCsX (hNs.preimage φ.surjective) hCvX (hNv.preimage φ.surjective)
    exact ⟨φ x, hxs, hxv⟩

end PiBase.Formal
