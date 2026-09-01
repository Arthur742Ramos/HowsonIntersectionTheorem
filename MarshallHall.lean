import MarshallHall.Hall
import MarshallHall.GrushkoGeneral
import MarshallHall.GrushkoReduction
import MarshallHall.GrushkoFold
import MarshallHall.GrushkoGraph
import MarshallHall.GrushkoFoldStep
import MarshallHall.GrushkoRose
import MarshallHall.GrushkoEdge
import MarshallHall.GrushkoUnfold
import MarshallHall.GrushkoInvariant
import MarshallHall.GrushkoReductionChain
import MarshallHall.GrushkoFull

/-!
# Marshall Hall's theorem through finite cores

The finite-core completion developed in `MarshallHall.Hall` proves the
inclusion-compatible free-factor form of Marshall Hall's theorem.  The same
repository also contains the LERF consequence, the binary and finite-indexed
free-group Grushko rank calculations, and the factorwise infrastructure for
the arbitrary-factor theorem.
-/

universe u

open Monoid.Coprod

namespace MarshallHall

/-! ### Arbitrary-factor Grushko--Neumann -/

/-- The rank of a free product of two finitely generated groups is additive.

The proof is the finite labelled-graph reduction: a minimal null path yields
either a safe fold or, after source-unfolding, a safe fold followed by an
explicit monochromatic-vertex contraction.  The resulting strict decrease in
the finite graph supplies the strong induction on the number of vertices.
-/
theorem rank_freeProduct_eq_add {G H : Type u} [Group G] [Group H]
    [Group.FG G] [Group.FG H] :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H :=
  GeneralGrushko.rank_coprod_eq_add

end MarshallHall
