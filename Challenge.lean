import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.Finiteness

/-!
# Howson's theorem

The Challenge exposes the finite-rank free-group intersection theorem.  The
finite-core, Hall, and Kurosh arguments belong to the Solution and library
modules, so this file remains a small Mathlib-only statement surface.
-/

theorem HowsonChallenge.howson_intersection_fg
    {α : Type*} [Finite α]
    (H K : Subgroup (FreeGroup α))
    [Group.FG H] [Group.FG K] :
    Group.FG (H ⊓ K : Subgroup (FreeGroup α)) := by
  sorry
