import Howson

/-!
# Checked Howson solution

The public theorem is supplied by the explicit finite-core/Hall/Kurosh
construction in `Howson.Intersection`.
-/

theorem HowsonChallenge.howson_intersection_fg
    {α : Type*} [Finite α]
    (H K : Subgroup (FreeGroup α))
    [Group.FG H] [Group.FG K] :
    Group.FG (H ⊓ K : Subgroup (FreeGroup α)) := by
  exact Howson.howson_intersection_fg H K
