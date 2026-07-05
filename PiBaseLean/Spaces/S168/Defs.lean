module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S168

/- Space 168: Real projective plane ℝP².
See https://topology.pi-base.org/spaces/S000168.
The quotient of the sphere `S² ⊆ EuclideanSpace ℝ (Fin 3)` (Euclidean subspace topology)
which identifies each point with its antipode. -/

/-- Identify a point of the sphere with itself or with its antipode `-x`. -/
def S168.r (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : Prop :=
  x = y ∨ (x : EuclideanSpace ℝ (Fin 3)) = -(y : EuclideanSpace ℝ (Fin 3))

theorem S168.r.equivalence : Equivalence S168.r where
  refl _ := Or.inl rfl
  symm h := h.elim (fun e => Or.inl e.symm) (fun e => Or.inr (by rw [e, neg_neg]))
  trans {a b c} hab hbc := by
    rcases hab with hab | hab
    · rcases hbc with hbc | hbc
      · exact Or.inl (hab.trans hbc)
      · exact Or.inr (by rw [hab, hbc])
    · rcases hbc with hbc | hbc
      · exact Or.inr (by rw [hbc] at hab; exact hab)
      · exact Or.inl (Subtype.ext (by rw [hab, hbc, neg_neg]))

instance S168.setoid : Setoid (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := ⟨S168.r, S168.r.equivalence⟩

/-- Real projective plane ℝP² (pi-Base S168): the quotient of the sphere `S²`
(Euclidean subspace topology) identifying antipodal points. -/
def S168 : Type := Quotient S168.setoid

instance : TopologicalSpace S168 := inferInstanceAs (TopologicalSpace (Quotient S168.setoid))

end S168
end PiBase.Spaces
