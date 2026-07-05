module

public import Mathlib.Topology.Order
public import Mathlib.SetTheory.Cardinal.Aleph

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology
open scoped Ordinal

namespace PiBase.Spaces
namespace S178

/- Space 178: Misra's subspace of E₀.
See https://topology.pi-base.org/spaces/S000178.
pi-Base describes S178 as the subspace of Misra's space E₀ (S177, Example 3.1 of
A. Misra, "A topological view of P-spaces", 1972) obtained by deleting the points
`b_{αβ}` and `b` from E₀. The primary source (Example 3.1) is not available to us; the
pi-Base database itself, however, records enough of the construction to fix the
remaining points and part of the topology (in its proof that S178 is Hausdorff, P48):
points are of the form `a_{αβ}` (α ranging over an index set, `β < ω₁`) or `c_γ`
(γ ranging over the same index set), each singleton `{a_{αβ}}` is clopen, and each
"column" `{c_γ} ∪ {a_{γβ} : β < ω₁}` is clopen. We take the index set for both α/γ and
β to be the ordinals below ω₁ (consistent with pi-Base's own recorded cardinality
`|S178| = ℵ₁`, property P114), and generate the topology from exactly these two
families of clopen sets. TODO: this reconstructs only the topological data pi-Base's
own text exposes; Example 3.1 may impose finer structure (relevant to the P-space /
scattered / non-semiregular traits P147 / P51 / ¬P10) that we cannot verify without
the primary source. -/

/-- The ordinals below the least uncountable ordinal `ω₁`, used as the index set for
both `α` (equivalently `γ`) and `β` in the point names `a_{αβ}`, `c_γ` of S178. -/
def S178.Omega1 : Type 1 := {o : Ordinal.{0} // o < ω₁}

/-- The points `a_{αβ}`, for `α` and `β` both ranging over the ordinals below `ω₁`. -/
def S178.APts : Type 1 := S178.Omega1 × S178.Omega1

/-- The points `c_γ`, for `γ` ranging over the ordinals below `ω₁`. -/
def S178.CPts : Type 1 := S178.Omega1

/-- Misra's subspace of E₀ (pi-Base S178): the points `a_{αβ}` together with the points
`c_γ` (E₀ with the points `b_{αβ}` and `b` deleted). -/
def S178 : Type 1 := S178.APts ⊕ S178.CPts

/-- The "column" at `γ`: the point `c_γ` together with all points `a_{γβ}` (`β < ω₁`).
Recorded by pi-Base (proof of P48) as a clopen set. -/
def S178.column (γ : S178.Omega1) : Set S178 :=
  {p : S178 | (∃ β : S178.Omega1, p = Sum.inl (γ, β)) ∨ p = Sum.inr γ}

/-- The generating open sets for S178: the singletons `{a_{αβ}}` and the columns
`{c_γ} ∪ {a_{γβ} : β < ω₁}`, exactly as recorded in pi-Base's proof that S178 is
Hausdorff (P48). -/
def S178.generators : Set (Set S178) :=
  {s | ∃ α β : S178.Omega1, s = {Sum.inl (α, β)}} ∪ {s | ∃ γ : S178.Omega1, s = S178.column γ}

instance : TopologicalSpace S178 := TopologicalSpace.generateFrom S178.generators

end S178
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S178 as a bundled `Space` (carrier + topology). -/
noncomputable def S178 : Space := ⟨PiBase.Spaces.S178.S178, inferInstance⟩

end PiBase.Formal
