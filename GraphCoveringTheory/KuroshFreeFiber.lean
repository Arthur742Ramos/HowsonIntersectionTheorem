import GraphCoveringTheory.KuroshRawPathValue

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

universe u v

namespace GraphCoveringTheory.Kurosh

theorem test_coverFreeGroupoidPathHom_eq_quotient_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
    coverFreeGroupoidPathHom G H p =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H))).map p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      simp only [coverFreeGroupoidPathHom, Prefunctor.mapPath]
      rw [ih]
      cases e <;> rfl

theorem test_coverFreePath_exists {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (z : @Quiver.Hom (Quiver.FreeGroupoid (RawBassSerreOrbitVertex G H)) _
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a)
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b)) :
    ∃ p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a b,
      coverFreeGroupoidPathHom G H p = z := by
  obtain ⟨p, hp⟩ :=
    (CategoryTheory.Quotient.full_functor
      (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))).map_surjective z
  refine ⟨p, ?_⟩
  rw [test_coverFreeGroupoidPathHom_eq_quotient_map]
  exact hp

end GraphCoveringTheory.Kurosh
