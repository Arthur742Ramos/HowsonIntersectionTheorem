import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Algebra.Group.ULift

noncomputable section

universe u v

namespace GraphCoveringTheory.KuroshChallenge

/-!
# Palomar statement surface for Kurosh's theorem

This file is deliberately independent of the repository implementation.  It
records the classical shape of the theorem using only Mathlib's free product
and subgroup primitives: a subgroup is a free product of a free group and
subgroups which are intersections with conjugates of the original factors.

The Bass--Serre construction proving this statement is kept in
`GraphCoveringTheory.KuroshTheorem.lean`; `KuroshSolution.lean` supplies the
bridge from that construction to this statement surface.
-/

/-! ## Free products and conjugate intersections -/

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

/-! ## The product displayed by the theorem -/

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

/-! The canonical maps from the displayed factors into `H`.  The non-free
components use the subtype inclusion, while the free component is supplied
by the decomposition witness. -/

def ComponentHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v))
    (freePartMap : ULift.{max (u + 1) (v + 1)} (FreeGroup X) →* H) :
    ∀ q : J ⊕ PUnit.{1}, Component G H A X q →* H
  | Sum.inl j => by
      change ULift.{max (u + 1) (v + 1)} (A j) →* H
      exact
        { toFun := fun x => x.down.1
          map_one' := by simp
          map_mul' := by intro x y; simp }
  | Sum.inr _ => freePartMap

/-! The homomorphism induced by the actual factor inclusions.  Thus an
isomorphism to `H` below is required to use the displayed subgroups as its
factors, rather than merely having the same abstract source type. -/

def inducedHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {J : Type (max u v)} (A : J → Subgroup H) (X : Type (max u v))
    (freePartMap : ULift.{max (u + 1) (v + 1)} (FreeGroup X) →* H) :
    Product G H A X →* H :=
  Monoid.CoprodI.lift (ComponentHom G H A X freePartMap)

/-! The challenge theorem exposes both the decomposition and the origin of
each non-free factor.  In particular, the factor family is not an arbitrary
family of groups: every factor is required to be an actual conjugate
intersection, and the displayed decomposition equivalence is required to be
the homomorphism induced by those inclusions (together with its free-part
map). -/

theorem kurosh_bass_serre_decomposition_challenge {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∃ (J : Type (max u v)) (X : Type (max u v)) (A : J → Subgroup H),
      (∀ j, ∃ i : ι, ∃ g : FreeProduct G,
        A j = intersectionFactorInH G H i g) ∧
      ∃ (freePartMap : ULift.{max (u + 1) (v + 1)} (FreeGroup X) →* H),
        ∃ (decomposition : Product G H A X ≃* H),
          decomposition.toMonoidHom = inducedHom G H A X freePartMap := by
  sorry

end GraphCoveringTheory.KuroshChallenge
