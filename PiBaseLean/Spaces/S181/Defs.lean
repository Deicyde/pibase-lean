module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Constructions

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S181

/- Space 181: Countable σ-product σ(ω₁+1)^ω.
See https://topology.pi-base.org/spaces/S000181.
The subspace of the countable product (ω₁+1)^ω of the ordinal space ω₁+1 (S36),
consisting of all functions ω → (ω₁+1) with finite support (non-zero on only
finitely many inputs), with the subspace topology inherited from the Pi/product
topology on (ω₁+1)^ω, where each factor carries the order topology. -/

/-- The ordinal space ω₁+1 (pi-Base S36): ordinals at most the least uncountable
ordinal ω₁, carrying the order topology. Reproduced here (rather than imported)
so this file is self-contained. -/
def S181.Factor : Type 1 := {o : Ordinal.{0} // o ≤ ω₁}

noncomputable instance : LinearOrder S181.Factor :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o ≤ ω₁})

noncomputable instance : TopologicalSpace S181.Factor := Preorder.topology S181.Factor

instance : OrderTopology S181.Factor := ⟨rfl⟩

/-- The basepoint `0` of the factor space, used to define finite support. -/
noncomputable instance : Zero S181.Factor := ⟨⟨0, bot_le⟩⟩

/-- Countable σ-product σ(ω₁+1)^ω (pi-Base S181): the subspace of the countable
product (ω₁+1)^ω consisting of all functions `ω → (ω₁+1)` with finite support,
i.e. those non-zero on only finitely many inputs. -/
def S181 : Type 1 := {f : ℕ → S181.Factor // (Function.support f).Finite}

noncomputable instance S181_top : TopologicalSpace S181 :=
  inferInstanceAs (TopologicalSpace {f : ℕ → S181.Factor // (Function.support f).Finite})

end S181
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S181 as a bundled `Space` (carrier + topology). -/
noncomputable def S181 : Space := ⟨PiBase.Spaces.S181.S181, PiBase.Spaces.S181.S181_top⟩

end PiBase.Formal
