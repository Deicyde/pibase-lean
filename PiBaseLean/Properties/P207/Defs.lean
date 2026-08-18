module

public import Mathlib.Data.Rel
public import Mathlib.Topology.Constructions.SumProd
public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

universe u

open Set

open scoped SetRel

namespace PiBase

/- 207. Strongly collectionwise normal -/
class StronglyCollectionwiseNormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  subset_diagonal {s : Set (X × X)} (ds : diagonal X ⊆ s) (hs : IsOpen s) :
    ∃ t : Set (X × X), diagonal X ⊆ t ∧ IsOpen t ∧ t ○ t ⊆ s

end PiBase

namespace PiBase.Formal

def P207 : Property where
  toPred := StronglyCollectionwiseNormalSpace
  well_defined {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (φ : X ≃ₜ Y) h := by
    constructor
    intro sY hsY_diag hsY_open
    -- Transport along the homeomorphism `φ ×ₜ φ` by taking preimages, which keeps both
    -- openness and membership computations definitional.
    have hg : Continuous (Prod.map (φ : X → Y) φ) := φ.continuous.prodMap φ.continuous
    have hf : Continuous (Prod.map (φ.symm : Y → X) φ.symm) :=
      φ.symm.continuous.prodMap φ.symm.continuous
    have hsX_diag : diagonal X ⊆ Prod.map (φ : X → Y) φ ⁻¹' sY :=
      diagonal_subset_iff.2 fun x => hsY_diag (mem_diagonal _)
    obtain ⟨tX, htX_diag, htX_open, htX_comp⟩ :=
      h.subset_diagonal hsX_diag (hg.isOpen_preimage _ hsY_open)
    refine ⟨Prod.map (φ.symm : Y → X) φ.symm ⁻¹' tX,
      diagonal_subset_iff.2 fun y => htX_diag (mem_diagonal _),
      hf.isOpen_preimage _ htX_open, ?_⟩
    rintro ⟨y₁, y₂⟩ ⟨y, hy₁, hy₂⟩
    have hmem : (φ.symm y₁, φ.symm y₂) ∈ Prod.map (φ : X → Y) φ ⁻¹' sY :=
      htX_comp ⟨φ.symm y, hy₁, hy₂⟩
    simpa using hmem

end PiBase.Formal
