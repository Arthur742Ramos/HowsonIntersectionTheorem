import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Algebra.Group.ULift
import GraphCoveringTheory.KuroshTheorem

noncomputable section

universe u v

namespace GraphCoveringTheory.KuroshChallenge

/-!
# Palomar statement surface

This is the same repository-independent surface as `KuroshChallenge.lean`.
It is repeated here because the challenge and solution modules are compiled
in separate environments and therefore must not import one another.
-/

abbrev FreeProduct {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] := Monoid.CoprodI G

def factorInclusion {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) : G i →* FreeProduct G :=
  Monoid.CoprodI.of

def conjugateSubgroup {P : Type u} [Group P] (K : Subgroup P) (g : P) : Subgroup P :=
  K.map (MulAut.conj g)

def intersectionFactor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι)
    (g : FreeProduct G) : Subgroup (FreeProduct G) :=
  H ⊓ conjugateSubgroup (MonoidHom.range (factorInclusion G i)) g

def intersectionFactorInH {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) (i : ι)
    (g : FreeProduct G) : Subgroup H :=
  (intersectionFactor G H i g).comap H.subtype

def Component {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v)) :
    (J ⊕ PUnit.{1}) → Type (max (u + 1) (v + 1)) :=
  Sum.elim
    (fun j => ULift.{max (u + 1) (v + 1)} (A j))
    (fun _ => ULift.{max (u + 1) (v + 1)} (FreeGroup X))

instance componentGroup {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v))
    (q : J ⊕ PUnit.{1}) : Group (Component G H A X q) := by
  cases q with
  | inl j =>
      change Group (ULift.{max (u + 1) (v + 1)} (A j))
      infer_instance
  | inr q =>
      change Group (ULift.{max (u + 1) (v + 1)} (FreeGroup X))
      infer_instance

abbrev Product {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v)) :=
  Monoid.CoprodI (Component G H A X)

/-! The checked proof of the Kurosh Palomar statement. -/

theorem kurosh_bass_serre_decomposition_challenge {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∃ (J : Type (max u v)) (X : Type (max u v)) (A : J → Subgroup H),
      (∀ j, ∃ i : ι, ∃ g : FreeProduct G,
        A j = intersectionFactorInH G H i g) ∧
      Nonempty (Product G H A X ≃* H) := by
  let J := GraphCoveringTheory.Kurosh.KuroshActiveVertexIndex G H
  let X := IsFreeGroup.Generators (GraphCoveringTheory.Kurosh.KuroshFreePart G H)
  let A : J → Subgroup H := fun j =>
    GraphCoveringTheory.Kurosh.treeVertexStabilizer G H j.1

  have hfactor : ∀ j, ∃ i : ι, ∃ g : FreeProduct G,
      A j = intersectionFactorInH G H i g := by
    intro j
    rcases GraphCoveringTheory.Kurosh.kurosh_factor_is_conjugate_intersection
      G H j with ⟨i, g, h⟩
    refine ⟨i, g, ?_⟩
    simpa [A, intersectionFactorInH, intersectionFactor, conjugateSubgroup,
      factorInclusion, GraphCoveringTheory.Kurosh.intersectionFactorInH,
      GraphCoveringTheory.Kurosh.intersectionFactor,
      GraphCoveringTheory.Kurosh.conjugateSubgroup,
      GraphCoveringTheory.Kurosh.factorInclusion] using h

  let freeEquiv :
      ULift.{max (u + 1) (v + 1)} (FreeGroup X) ≃*
        ULift.{max (u + 1) (v + 1)} (GraphCoveringTheory.Kurosh.KuroshFreePart G H) :=
    (MulEquiv.ulift : ULift.{max (u + 1) (v + 1)} (FreeGroup X) ≃* FreeGroup X).trans
      (IsFreeGroup.toFreeGroup
        (GraphCoveringTheory.Kurosh.KuroshFreePart G H)).symm |>.trans
      (MulEquiv.ulift :
        ULift.{max (u + 1) (v + 1)} (GraphCoveringTheory.Kurosh.KuroshFreePart G H) ≃*
          GraphCoveringTheory.Kurosh.KuroshFreePart G H).symm

  let componentEquiv : ∀ q : J ⊕ PUnit.{1},
      Component G H A X q ≃*
        GraphCoveringTheory.Kurosh.KuroshActiveComponent G H q
    | Sum.inl j => by
        change ULift.{max (u + 1) (v + 1)} (A j) ≃*
          ULift.{max (u + 1) (v + 1)}
            (GraphCoveringTheory.Kurosh.treeVertexStabilizer G H j.1)
        exact MulEquiv.refl _
    | Sum.inr q => by
        change ULift.{max (u + 1) (v + 1)} (FreeGroup X) ≃*
          ULift.{max (u + 1) (v + 1)}
            (GraphCoveringTheory.Kurosh.KuroshFreePart G H)
        exact freeEquiv

  let forward : Product G H A X →*
      GraphCoveringTheory.Kurosh.KuroshActiveProduct G H :=
    Monoid.CoprodI.lift (fun q =>
      (Monoid.CoprodI.of :
        GraphCoveringTheory.Kurosh.KuroshActiveComponent G H q →*
          GraphCoveringTheory.Kurosh.KuroshActiveProduct G H).comp
        (componentEquiv q).toMonoidHom)
  let backward : GraphCoveringTheory.Kurosh.KuroshActiveProduct G H →*
      Product G H A X :=
    Monoid.CoprodI.lift (fun q =>
      (Monoid.CoprodI.of : Component G H A X q →* Product G H A X).comp
        (componentEquiv q).symm.toMonoidHom)

  have hforward : backward.comp forward = MonoidHom.id (Product G H A X) := by
    apply Monoid.CoprodI.ext_hom
    intro q
    apply MonoidHom.ext
    intro x
    change Monoid.CoprodI.of
        ((componentEquiv q).symm ((componentEquiv q) x)) =
      Monoid.CoprodI.of x
    rw [MulEquiv.symm_apply_apply]

  have hbackward : forward.comp backward =
      MonoidHom.id (GraphCoveringTheory.Kurosh.KuroshActiveProduct G H) := by
    apply Monoid.CoprodI.ext_hom
    intro q
    apply MonoidHom.ext
    intro x
    change Monoid.CoprodI.of
        ((componentEquiv q) ((componentEquiv q).symm x)) =
      Monoid.CoprodI.of x
    rw [MulEquiv.apply_symm_apply]

  let productEquiv : Product G H A X ≃*
      GraphCoveringTheory.Kurosh.KuroshActiveProduct G H :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro z
        exact congrArg (fun f : Product G H A X →* Product G H A X => f z)
          hforward
      right_inv := by
        intro z
        exact congrArg
          (fun f : GraphCoveringTheory.Kurosh.KuroshActiveProduct G H →*
            GraphCoveringTheory.Kurosh.KuroshActiveProduct G H => f z) hbackward
      map_mul' := forward.map_mul }

  rcases GraphCoveringTheory.Kurosh.kurosh_decomposition G H with ⟨activeEquiv⟩
  exact ⟨J, X, A, hfactor, ⟨productEquiv.trans activeEquiv⟩⟩

end GraphCoveringTheory.KuroshChallenge
