import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.Finiteness

noncomputable section

/-!
# Subgroup separability of finitely generated free groups

The challenge is the LERF form of Marshall Hall's theorem.  The theorem is
deliberately stated using only Mathlib's free-group and finite-generation
interfaces; the finite-core and completion argument belongs in the solution.
-/

theorem freeGroup_subgroup_separable
    {α : Type*} [Finite α]
    (H : Subgroup (FreeGroup α))
    [Group.FG H]
    (g : FreeGroup α)
    (hg : g ∉ H) :
    ∃ K : Subgroup (FreeGroup α),
      H ≤ K ∧ K.index ≠ 0 ∧ g ∉ K := by
  sorry
