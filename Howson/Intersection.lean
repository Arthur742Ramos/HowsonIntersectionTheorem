import Howson.KuroshFG
import Mathlib.GroupTheory.Schreier

/-!
# Howson's theorem

The finite-index free-factor theorem turns one finitely generated subgroup
into a factor of a finite-index overgroup.  The other subgroup pulls back to a
finitely generated subgroup by Schreier.  Kurosh then makes the intersection
with the selected factor a finitely generated factor, and the explicit
inclusion maps identify its image with the original intersection.
-/

noncomputable section

open Set Function
open Monoid
open Monoid.Coprod
open GraphCoveringTheory GraphCoveringTheory.Kurosh

namespace Howson

universe u

def intersectionSideEquiv {F : Type u} [Group F]
    (A B : Subgroup F) : A.subgroupOf B ≃* B.subgroupOf A :=
  { toFun := fun x =>
      ⟨⟨(x : F), by exact Subgroup.mem_subgroupOf.mp x.property⟩,
        by exact x.1.property⟩
    invFun := fun x =>
      ⟨⟨(x : F), by exact Subgroup.mem_subgroupOf.mp x.property⟩,
        by exact x.1.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_mul' := by intro x y; rfl }

theorem howson_intersection_fg
    {α : Type u} [Finite α]
    (H K : Subgroup (FreeGroup α))
    [Group.FG H] [Group.FG K] :
    Group.FG (H ⊓ K : Subgroup (FreeGroup α)) := by
  classical
  obtain ⟨w⟩ := MarshallHall.marshallHall H
  let L : Subgroup (FreeGroup α) := w.K
  let Q := w.complement
  letI : Group Q := w.complementGroup
  have hL : L.FiniteIndex := by
    apply Subgroup.finiteIndex_iff.mpr
    exact w.finiteIndex
  letI : L.FiniteIndex := hL
  letI : (L.subgroupOf K).FiniteIndex := inferInstance
  letI : Group.FG (L.subgroupOf K) := inferInstance
  have hM : Group.FG (K.subgroupOf L) := by
    exact Group.fg_of_surjective
      (f := (intersectionSideEquiv L K).toMonoidHom)
      (intersectionSideEquiv L K).surjective
  let A := binaryFamily H Q
  letI : ∀ i, Group (A i) := binaryFamilyGroup H Q
  let b : FreeProduct A ≃* (H ∗ Q) :=
    binaryIndexedEquiv (A := H) (B := Q)
  let e : FreeProduct A ≃* L := b.trans w.equiv
  let M : Subgroup L := K.subgroupOf L
  let N : Subgroup (FreeProduct A) := M.comap e.toMonoidHom
  let eN : N ≃* M :=
    { toFun := fun x => ⟨e x.1, x.property⟩
      invFun := fun y =>
        ⟨e.symm y.1, by
          change e (e.symm y.1) ∈ M
          simpa using y.property⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact e.map_mul x.1 y.1 }
  letI : Group.FG M := hM
  let hN : Group.FG N :=
    Group.fg_of_surjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  letI : Group.FG N := hN
  let J : Subgroup N := intersectionFactorInH N false (1 : FreeProduct A)
  have hJ : Group.FG J := fg_intersection_factor N false 1
  letI : Group.FG J := hJ
  have factor_mem_H : ∀ x : J, ((e x.1.1 : L) : FreeGroup α) ∈ H := by
    intro x
    have hxI : x.1.1 ∈ intersectionFactor N false (1 : FreeProduct A) :=
      x.property
    have hxR : x.1.1 ∈ MonoidHom.range (factorInclusion A false) := by
      have hxC := (mem_conjugateSubgroup_iff
        (MonoidHom.range (factorInclusion A false))
        (1 : FreeProduct A) x.1.1).1 hxI.2
      simpa using hxC
    rcases hxR with ⟨h, hh⟩
    have heq : e x.1.1 = ⟨(h : FreeGroup α), w.hHK h.property⟩ := by
      rw [← hh]
      change w.equiv (b (Monoid.CoprodI.of (M := A) (i := false)
        (show A false from h))) = _
      rw [binaryIndexedEquiv_of_false]
      exact w.inclusion h
    rw [heq]
    exact h.property
  have factor_mem_K : ∀ x : J, ((e x.1.1 : L) : FreeGroup α) ∈ K := by
    intro x
    have hxI : x.1.1 ∈ intersectionFactor N false (1 : FreeProduct A) :=
      x.property
    have hxN : x.1.1 ∈ N := hxI.1
    have hxM : e x.1.1 ∈ M := hxN
    exact Subgroup.mem_subgroupOf.mp hxM
  let φ : J →* (H ⊓ K : Subgroup (FreeGroup α)) :=
    { toFun := fun x =>
        ⟨(e x.1.1 : L), factor_mem_H x, factor_mem_K x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp [map_mul] }
  have hφ : Function.Surjective φ := by
    intro y
    let h : H := ⟨y.1, y.2.1⟩
    let a : FreeProduct A :=
      Monoid.CoprodI.of (M := A) (i := false) (show A false from h)
    have heq : e a = ⟨(h : FreeGroup α), w.hHK h.property⟩ := by
      change w.equiv (b (Monoid.CoprodI.of (M := A) (i := false)
        (show A false from h))) = _
      rw [binaryIndexedEquiv_of_false]
      exact w.inclusion h
    have haM : e a ∈ M := by
      change ((e a : L) : FreeGroup α) ∈ K
      rw [heq]
      exact y.2.2
    have haN : a ∈ N := by
      change e a ∈ M
      exact haM
    have haI : a ∈ intersectionFactor N false (1 : FreeProduct A) := by
      change a ∈ N ∧ a ∈ conjugateSubgroup
        (MonoidHom.range (factorInclusion A false)) (1 : FreeProduct A)
      refine ⟨haN, ?_⟩
      apply (mem_conjugateSubgroup_iff
        (MonoidHom.range (factorInclusion A false))
        (1 : FreeProduct A) a).2
      simpa using (show a ∈ MonoidHom.range (factorInclusion A false) from
        ⟨h, rfl⟩)
    let x : J := ⟨⟨a, haN⟩, haI⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (e a : L) = y.1
    rw [heq]
  exact Group.fg_of_surjective (f := φ) hφ

end Howson
