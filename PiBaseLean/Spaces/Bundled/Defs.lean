module

public import PiBaseLean.Properties.Bundled.Defs

@[expose] public section

namespace PiBase.Formal

universe u

/-- A topological space in π-Base: a carrier type together with its topology.
The dual of `Property`. π-Base considers spaces up to homeomorphism — exactly the
invariance guaranteed by `Property.well_defined`, so `Sat` below is a homeomorphism
invariant. -/
structure Space where
  /-- The underlying set of points. -/
  carrier : Type u
  /-- Its topology. -/
  top : TopologicalSpace carrier

attribute [instance] Space.top

/-- `s ⊨ p` : the space `s` has the property `p`. Homeomorphism-invariant, since
`p` is (`Property.well_defined`). -/
def Space.Sat (s : Space) (p : Property) : Prop := p.toPred s.carrier

@[inherit_doc Space.Sat] scoped infix:50 " ⊨ " => Space.Sat

end PiBase.Formal
