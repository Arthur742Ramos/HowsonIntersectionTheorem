import MarshallHall.Separation

noncomputable section

/-!
# Checked solution

The public theorem is a short LERF statement.  Its proof is supplied by the
finite-core completion construction in `MarshallHall.Separation`.
-/

theorem freeGroup_subgroup_separable
    {α : Type*} [Finite α]
    (H : Subgroup (FreeGroup α))
    [Group.FG H]
    (g : FreeGroup α)
    (hg : g ∉ H) :
    ∃ K : Subgroup (FreeGroup α),
      H ≤ K ∧ K.index ≠ 0 ∧ g ∉ K := by
  exact MarshallHall.freeGroup_subgroup_separable_proved H g hg
