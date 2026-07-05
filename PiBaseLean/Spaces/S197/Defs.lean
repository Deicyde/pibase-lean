module

public import Mathlib.Topology.Basic

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S197

/- Space 197: Rudin's nonmetrizable manifold.
See https://topology.pi-base.org/spaces/S000197.
Constructed in section 1 of M. E. Rudin, "Two nonmetrizable manifolds"
(Topology Appl. 35 (1990), 137-152, doi:10.1016/0166-8641(90)90099-N), built from a
Van Douwen line construction; it is a (non-metrizable, non-second-countable) 2-manifold.

TODO: the carrier/topology below are honestly incomplete. Unlike most π-Base spaces, the
π-Base entry for S197 does not spell out a carrier set or generating open sets at all -- it
only cites Rudin's paper and names the building block ("a Van Douwen line construction").
Faithfully reconstructing the actual manifold requires reading section 1 of that paper: it
glues copies of a Van Douwen-style long-line space together (an ordinal-indexed, non-second-
countable analogue of the long line/plane construction) to produce a connected, Hausdorff,
locally-Euclidean surface that is not metrizable. That gluing data is not available in the
π-Base source used here, and Mathlib has no packaged "Van Douwen line" object to anchor a
faithful parametrized stub to (contrast S109/Novak space, where the ambient `StoneCech ℕ`
was at least given). Presenting a concrete carrier/topology here would fabricate structure
that is nowhere stated in the source, so no `def`/`instance` is given; this file records the
gap instead of a wrong answer. -/

end S197
end PiBase.Spaces
