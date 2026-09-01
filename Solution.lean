import MarshallHall

noncomputable section

open Monoid.Coprod

universe u

/-!
# Checked Grushko--Neumann solution

The public theorem is the arbitrary-factor binary rank-additivity statement.
Its proof is supplied by the finite labelled-graph reduction in
`MarshallHall.GrushkoFull`.
-/

theorem rank_freeProduct_eq_add {G H : Type u} [Group G] [Group H]
    [Group.FG G] [Group.FG H] :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H := by
  exact MarshallHall.rank_freeProduct_eq_add
