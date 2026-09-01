import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Rank

noncomputable section

open Monoid.Coprod
open Function Set

universe u

namespace MarshallHall

variable {G H : Type*} [Group G] [Group H]

structure MarshallHallWitness {F : Type u} [Group F] (H : Subgroup F) where
  K : Subgroup F
  hHK : H ≤ K
  finiteIndex : K.index ≠ 0
  complement : Type u
  [complementGroup : Group complement]
  equiv : H ∗ complement ≃* K
  inclusion : ∀ h : H, equiv (Monoid.Coprod.inl h) = ⟨h.1, hHK h.2⟩

theorem marshallHall
    {α : Type u} [finite : Finite α]
    (H : Subgroup (FreeGroup α))
    [fg : Group.FG H] :
    Nonempty (MarshallHallWitness H) := by
  sorry

namespace GeneralGrushko

instance coprod_fg [Group.FG G] [Group.FG H] : Group.FG (G ∗ H) := by
  rcases Group.fg_iff.mp (show Group.FG G from inferInstance) with ⟨S, hS, hSf⟩
  rcases Group.fg_iff.mp (show Group.FG H from inferInstance) with ⟨T, hT, hTf⟩
  refine Group.fg_iff.mpr ⟨inl '' S ∪ inr '' T, ?_, hSf.image _ |>.union (hTf.image _)⟩
  have hleftSub : Subgroup.closure ((inl : G →* G ∗ H) '' S) =
      MonoidHom.range (inl : G →* G ∗ H) := by
    rw [← MonoidHom.map_closure, hS, MonoidHom.range_eq_map]
  have hrightSub : Subgroup.closure ((inr : H →* G ∗ H) '' T) =
      MonoidHom.range (inr : H →* G ∗ H) := by
    rw [← MonoidHom.map_closure, hT, MonoidHom.range_eq_map]
  have hrangeleft : Subgroup.closure (Set.range (inl : G →* G ∗ H)) =
      MonoidHom.range (inl : G →* G ∗ H) := by
    rw [← MonoidHom.coe_range, Subgroup.closure_eq]
  have hrangeright : Subgroup.closure (Set.range (inr : H →* G ∗ H)) =
      MonoidHom.range (inr : H →* G ∗ H) := by
    rw [← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [← closure_range_inl_union_inr]
  rw [Subgroup.closure_union, Subgroup.closure_union,
    hleftSub, hrightSub, hrangeleft, hrangeright]

end GeneralGrushko
end MarshallHall

/-!
# Grushko--Neumann rank additivity for free products

The challenge exposes the arbitrary-factor binary Grushko theorem.  It uses
only Mathlib's group, free-product, and finite-generation interfaces; the
finite labelled-graph reduction belongs in the solution.
-/

theorem rank_freeProduct_eq_add {G H : Type u} [Group G] [Group H]
    [Group.FG G] [Group.FG H] :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H := by
  sorry
