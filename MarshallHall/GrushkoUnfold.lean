import MarshallHall.GrushkoEdge

/-!
## The local source unfold

This file formalizes the local graph move used in the last case of the
Stallings proof of Grushko's theorem.  Fix an oriented edge `e₀` leaving a
vertex `a`.  The source is split into an old copy and a new copy.  All
original arrows labelled in the colour of `e₀` remain attached to the old
copy, the other coloured arrows are attached to the new copy, and a second
copy of `e₀` is attached to the new copy.

The construction is intentionally local.  In particular, it does not yet
choose a new marking or perform the subsequent monochromatic-vertex
contraction.  The main certified fact here is that the old copy is
monochromatic, exactly the invariant needed by that contraction.
-/

open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type v} [Group G] [Group H]
  {V : Type u} [Fintype V] [Quiver V] [HasInvolutiveReverse V]
  [∀ a b : V, Fintype (a ⟶ b)]

/-! ### Split vertices and duplicated arrows -/

/-- A copy of `a` is added to the original vertex set.  `false` denotes the
old copy and `true` the new copy. -/
def UnfoldVertex (a : V) := {x : V // x ≠ a} ⊕ Bool

noncomputable instance unfoldVertexFintype (a : V) : Fintype (UnfoldVertex a) := by
  classical
  dsimp [UnfoldVertex]
  infer_instance

def unfoldOld (a : V) : UnfoldVertex a := Sum.inr false

def unfoldNew (a : V) : UnfoldVertex a := Sum.inr true

theorem unfoldOld_ne_new (a : V) : unfoldOld a ≠ unfoldNew a := by
  intro h
  cases h

theorem unfoldNew_ne_old (a : V) : unfoldNew a ≠ unfoldOld a := by
  exact (unfoldOld_ne_new a).symm

def unfoldEdgeColor (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e : AllArrow (V := V)) : Bool :=
  binarySumIndex (G := G) (H := H) (allArrowLabel L e)

def unfoldVertexAt (L : BinaryLabelling (G := G) (H := H) (V := V))
    (a : V) (e₀ : AllArrow (V := V)) (x : V) (c : Bool) :
    UnfoldVertex a :=
  by
    classical
    exact if h : x = a then
      Sum.inr (if c = unfoldEdgeColor L e₀ then false else true)
    else
      Sum.inl ⟨x, h⟩

theorem unfoldVertexAt_eq_old_iff
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (a : V) (e₀ : AllArrow (V := V)) (x : V) (c : Bool) :
    unfoldVertexAt L a e₀ x c = unfoldOld a ↔
      x = a ∧ c = unfoldEdgeColor L e₀ := by
  classical
  by_cases hx : x = a
  · subst x
    cases hcol : unfoldEdgeColor L e₀ <;> cases c <;>
      simp [unfoldVertexAt, unfoldOld, hcol] <;>
        exact (unfoldOld_ne_new a).symm
  · simp [unfoldVertexAt, unfoldOld, hx]

theorem unfoldVertexAt_eq_new_iff
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (a : V) (e₀ : AllArrow (V := V)) (x : V) (c : Bool) :
    unfoldVertexAt L a e₀ x c = unfoldNew a ↔
      x = a ∧ c ≠ unfoldEdgeColor L e₀ := by
  classical
  by_cases hx : x = a
  · subst x
    cases hcol : unfoldEdgeColor L e₀ <;> cases c <;>
      simp [unfoldVertexAt, unfoldNew, hcol] <;>
        exact unfoldOld_ne_new a
  · simp [unfoldVertexAt, unfoldNew, hx]

theorem unfoldVertexAt_of_ne
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (x : V) (c : Bool) (hx : x ≠ a) :
    unfoldVertexAt L a e₀ x c = Sum.inl ⟨x, hx⟩ := by
  classical
  simp [unfoldVertexAt, hx]

theorem unfoldEdgeColor_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e : AllArrow (V := V)) :
    unfoldEdgeColor L (allArrowReverse e) = unfoldEdgeColor L e := by
  simp only [unfoldEdgeColor, allArrowLabel_reverse,
    binarySumIndex_factorWordInv]

/-! ### The unfolded edge type and its quiver -/

/-- The old oriented edges together with the two orientations of a duplicated
edge.  The `Bool` component is the orientation of the duplicate. -/
abbrev UnfoldEdge (e₀ : AllArrow (V := V)) :=
  AllArrow (V := V) ⊕ Bool

noncomputable instance unfoldEdgeFintype (e₀ : AllArrow (V := V)) :
    Fintype (UnfoldEdge (V := V) e₀) := by
  dsimp [UnfoldEdge]
  infer_instance

def unfoldEdgeReverse {e₀ : AllArrow (V := V)} :
    UnfoldEdge (V := V) e₀ → UnfoldEdge (V := V) e₀
  | Sum.inl e => Sum.inl (allArrowReverse e)
  | Sum.inr false => Sum.inr true
  | Sum.inr true => Sum.inr false

@[simp] theorem unfoldEdgeReverse_reverse {e₀ : AllArrow (V := V)}
    (e : UnfoldEdge (V := V) e₀) :
    unfoldEdgeReverse (unfoldEdgeReverse e) = e := by
  cases e with
  | inl e => simp [unfoldEdgeReverse]
  | inr b => cases b <;> rfl

def unfoldEdgeSource
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    UnfoldEdge (V := V) e₀ → UnfoldVertex (allArrowSource e₀)
  | Sum.inl e =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowSource e) (unfoldEdgeColor L e)
  | Sum.inr false => unfoldNew (allArrowSource e₀)
  | Sum.inr true =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀)

def unfoldEdgeTarget
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    UnfoldEdge (V := V) e₀ → UnfoldVertex (allArrowSource e₀)
  | Sum.inl e =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e) (unfoldEdgeColor L e)
  | Sum.inr false =>
      unfoldVertexAt L (allArrowSource e₀) e₀
        (allArrowTarget e₀) (unfoldEdgeColor L e₀)
  | Sum.inr true => unfoldNew (allArrowSource e₀)

theorem unfoldEdgeSource_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (e : UnfoldEdge (V := V) e₀) :
    unfoldEdgeSource L e₀ (unfoldEdgeReverse e) =
      unfoldEdgeTarget L e₀ e := by
  cases e with
  | inl e =>
      simp [unfoldEdgeSource, unfoldEdgeTarget, unfoldEdgeReverse,
        unfoldEdgeColor_reverse]
  | inr b => cases b <;> rfl

theorem unfoldEdgeTarget_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (e : UnfoldEdge (V := V) e₀) :
    unfoldEdgeTarget L e₀ (unfoldEdgeReverse e) =
      unfoldEdgeSource L e₀ e := by
  cases e with
  | inl e =>
      simp [unfoldEdgeSource, unfoldEdgeTarget, unfoldEdgeReverse,
        unfoldEdgeColor_reverse]
  | inr b => cases b <;> rfl

@[reducible] def unfoldQuiver
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    Quiver (UnfoldVertex (allArrowSource e₀)) where
  Hom x y := {e : UnfoldEdge (V := V) e₀ //
    unfoldEdgeSource L e₀ e = x ∧ unfoldEdgeTarget L e₀ e = y}

noncomputable def unfoldQuiverHomFintype
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (x y : UnfoldVertex (allArrowSource e₀)) :
    Fintype (@Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) x y) := by
  classical
  change Fintype {e : UnfoldEdge (V := V) e₀ //
    unfoldEdgeSource L e₀ e = x ∧ unfoldEdgeTarget L e₀ e = y}
  infer_instance

noncomputable instance unfoldAllArrowFintype
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    Fintype (@AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  letI (x y : UnfoldVertex (allArrowSource e₀)) :
      Fintype (x ⟶ y) := by
    exact unfoldQuiverHomFintype L e₀ x y
  exact allArrowFintype

def unfoldReverseArrow
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    {x y : UnfoldVertex (allArrowSource e₀)}
    (e : @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) x y) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) y x := by
  refine ⟨unfoldEdgeReverse e.1, ?_, ?_⟩
  · rw [unfoldEdgeSource_reverse, e.2.2]
  · rw [unfoldEdgeTarget_reverse, e.2.1]

def unfoldHasReverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @Quiver.HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) :=
  @Quiver.HasInvolutiveReverse.mk
    (UnfoldVertex (allArrowSource e₀))
    (unfoldQuiver L e₀)
    (@Quiver.HasReverse.mk
      (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (fun {x y} e => unfoldReverseArrow L e₀ e))
    (by
      intro x y e
      apply Subtype.ext
      exact unfoldEdgeReverse_reverse e.1)

def unfoldEdgeLabel
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) : UnfoldEdge (V := V) e₀ → Sum G H
  | Sum.inl e => allArrowLabel L e
  | Sum.inr false => allArrowLabel L e₀
  | Sum.inr true => factorWordInv (allArrowLabel L e₀)

theorem unfoldEdgeLabel_reverse
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (e : UnfoldEdge (V := V) e₀) :
    unfoldEdgeLabel L e₀ (unfoldEdgeReverse e) =
      factorWordInv (unfoldEdgeLabel L e₀ e) := by
  cases e with
  | inl e =>
      simp [unfoldEdgeLabel, unfoldEdgeReverse, allArrowLabel_reverse]
  | inr b =>
      cases b
      · rfl
      · simp [unfoldEdgeLabel, unfoldEdgeReverse,
          factorWordInv_factorWordInv]

def unfoldLabelling
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @BinaryLabelling G H (UnfoldVertex (allArrowSource e₀)) _ _
      (unfoldQuiver L e₀) (unfoldHasReverse L e₀) := by
  exact @BinaryLabelling.mk G H (UnfoldVertex (allArrowSource e₀)) _ _
    (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
    (fun {x y} e => unfoldEdgeLabel L e₀ e.1)
    (by
      intro x y e
      exact unfoldEdgeLabel_reverse L e₀ e.1)

/-! ### The old copy is monochromatic -/

def unfoldOldIncident
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (e : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) : Prop :=
  e.1 = unfoldOld (allArrowSource e₀) ∨
    e.2.1 = unfoldOld (allArrowSource e₀)

theorem unfold_old_incident_color
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (e : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀))
    (h : unfoldOldIncident L e₀ e) :
    binarySumIndex (G := G) (H := H)
        (unfoldEdgeLabel L e₀ e.2.2.1) =
      unfoldEdgeColor L e₀ := by
  rcases e with ⟨x, y, e⟩
  rcases e with ⟨edge, hs, ht⟩
  change x = unfoldOld (allArrowSource e₀) ∨
    y = unfoldOld (allArrowSource e₀) at h
  cases edge with
  | inl e =>
      have hc : unfoldEdgeColor L e = unfoldEdgeColor L e₀ := by
        rcases h with h | h
        · have hsold :
              unfoldVertexAt L (allArrowSource e₀) e₀
                (allArrowSource e) (unfoldEdgeColor L e) =
              unfoldOld (allArrowSource e₀) := by
            exact hs.trans h
          exact (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
            (allArrowSource e) (unfoldEdgeColor L e)).mp hsold |>.2
        · have htold :
              unfoldVertexAt L (allArrowSource e₀) e₀
                (allArrowTarget e) (unfoldEdgeColor L e) =
              unfoldOld (allArrowSource e₀) := by
            exact ht.trans h
          exact (unfoldVertexAt_eq_old_iff L (allArrowSource e₀) e₀
            (allArrowTarget e) (unfoldEdgeColor L e)).mp htold |>.2
      exact hc
  | inr b =>
      cases b <;>
        simp [unfoldEdgeLabel, unfoldEdgeColor, binarySumIndex_factorWordInv]

def unfoldOriginalEdge
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀ x
        (unfoldEdgeColor L (allArrowOf e)))
      (unfoldVertexAt L (allArrowSource e₀) e₀ y
        (unfoldEdgeColor L (allArrowOf e))) :=
  ⟨Sum.inl (allArrowOf e), rfl, rfl⟩

theorem unfoldOriginalEdge_label
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y) :
    unfoldEdgeLabel L e₀ (Sum.inl (allArrowOf e)) = L.label e := by
  rfl

def unfoldOriginalEdgeAtColor
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y)
    (color : Bool) (hc : unfoldEdgeColor L (allArrowOf e) = color) :
    @Quiver.Hom (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)
      (unfoldVertexAt L (allArrowSource e₀) e₀ x color)
      (unfoldVertexAt L (allArrowSource e₀) e₀ y color) := by
  refine ⟨Sum.inl (allArrowOf e), ?_, ?_⟩
  · change unfoldVertexAt L (allArrowSource e₀) e₀ x
      (unfoldEdgeColor L (allArrowOf e)) =
        unfoldVertexAt L (allArrowSource e₀) e₀ x color
    rw [hc]
  · change unfoldVertexAt L (allArrowSource e₀) e₀ y
      (unfoldEdgeColor L (allArrowOf e)) =
        unfoldVertexAt L (allArrowSource e₀) e₀ y color
    rw [hc]

theorem unfoldOriginalEdgeAtColor_label
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) {x y : V} (e : x ⟶ y)
    (color : Bool) (hc : unfoldEdgeColor L (allArrowOf e) = color) :
    unfoldEdgeLabel L e₀
        (unfoldOriginalEdgeAtColor L e₀ e color hc).1 = L.label e := by
  rfl

def unfoldMonochromaticPath
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool) :
    ∀ {x y : V} (p : @Quiver.Path V _ x y),
      L.IsMonochromatic p color →
      @Quiver.Path (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)
        (unfoldVertexAt L (allArrowSource e₀) e₀ x color)
        (unfoldVertexAt L (allArrowSource e₀) e₀ y color)
  | _, _, Path.nil, _ =>
      @Quiver.Path.nil (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) _
  | _, _, Path.cons p e, hp => by
      have htail : L.IsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.pathLabels, List.mem_append]
          exact Or.inl hz)
      have hecolor : binarySumIndex (G := G) (H := H) (L.label e) = color := by
        exact hp (L.label e) (by
          simp only [BinaryLabelling.pathLabels, List.mem_append,
            List.mem_singleton]
          exact Or.inr trivial)
      have hecolor' : unfoldEdgeColor L (allArrowOf e) = color := by
        exact hecolor
      have edge := unfoldOriginalEdgeAtColor L e₀ e color hecolor'
      exact @Quiver.Path.cons
        (UnfoldVertex (allArrowSource e₀)) (unfoldQuiver L e₀)
        (unfoldVertexAt L (allArrowSource e₀) e₀ _ color) _
        (unfoldVertexAt L (allArrowSource e₀) e₀ _ color)
        (unfoldMonochromaticPath L e₀ color p htail) edge

theorem unfoldMonochromaticPath_read
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) (color : Bool)
    {x y : V} (p : @Quiver.Path V _ x y)
    (hp : L.IsMonochromatic p color) :
    (@BinaryLabelling.pathRead G H (UnfoldVertex (allArrowSource e₀))
      _ _ (unfoldQuiver L e₀) (unfoldHasReverse L e₀)
      (unfoldLabelling L e₀)
      _ _ (unfoldMonochromaticPath L e₀ color p hp)) =
      L.pathRead p := by
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  induction p with
  | nil =>
      simp [unfoldMonochromaticPath, BinaryLabelling.pathRead,
        BinaryLabelling.pathLabels, factorWordProd]
  | cons p e ih =>
      have htail : L.IsMonochromatic p color := by
        intro z hz
        exact hp z (by
          simp only [BinaryLabelling.pathLabels, List.mem_append]
          exact Or.inl hz)
      have hecolor : binarySumIndex (G := G) (H := H) (L.label e) = color := by
        exact hp (L.label e) (by
          simp only [BinaryLabelling.pathLabels, List.mem_append,
            List.mem_singleton]
          exact Or.inr trivial)
      simp only [unfoldMonochromaticPath]
      rw [← Path.comp_toPath_eq_cons, ← Path.comp_toPath_eq_cons,
        BinaryLabelling.pathRead_comp, ih htail,
        BinaryLabelling.pathRead_toPath]
      change L.pathRead p * separatedMap (L.label e) = L.pathRead (p.cons e)
      rw [← Path.comp_toPath_eq_cons, L.pathRead_comp,
        L.pathRead_toPath]

/-! ### Cardinal bookkeeping -/

theorem unfoldEdge_card
    (e₀ : AllArrow (V := V)) :
    Fintype.card (UnfoldEdge (V := V) e₀) =
      Fintype.card (AllArrow (V := V)) + 2 := by
  change Fintype.card (AllArrow (V := V) ⊕ Bool) =
    Fintype.card (AllArrow (V := V)) + 2
  rw [Fintype.card_sum, Fintype.card_bool]

def unfoldAllArrowEquivEdge
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀) ≃ UnfoldEdge (V := V) e₀ :=
  { toFun := fun e => e.2.2.1
    invFun := fun e =>
      ⟨unfoldEdgeSource L e₀ e, unfoldEdgeTarget L e₀ e,
        ⟨e, rfl, rfl⟩⟩
    left_inv := by
      intro e
      cases e with
      | mk x be =>
          cases be with
          | mk y e =>
              cases e with
              | mk edge h =>
                  cases h.1
                  cases h.2
                  rfl
    right_inv := by
      intro e
      rfl }

theorem unfoldAllArrow_card
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V)) :
    Fintype.card (@AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) =
      Fintype.card (AllArrow (V := V)) + 2 := by
  rw [Fintype.card_congr (unfoldAllArrowEquivEdge L e₀),
    unfoldEdge_card]

theorem unfoldVertex_card (a : V) :
    Fintype.card (UnfoldVertex a) = Fintype.card V + 1 := by
  classical
  have hcomp := Fintype.card_subtype_compl (fun x : V => x = a)
  have heq : Fintype.card {x : V // x = a} = 1 := by
    simpa using Fintype.card_subtype_eq a
  have hpos : 1 ≤ Fintype.card V := by
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  change Fintype.card ({x : V // x ≠ a} ⊕ Bool) =
    Fintype.card V + 1
  rw [Fintype.card_sum, Fintype.card_bool, hcomp, heq]
  omega

theorem unfold_euler_bound {n : ℕ}
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (hEuler : Fintype.card (AllArrow (V := V)) ≤
      2 * (n + Fintype.card V - 1)) :
    Fintype.card (@AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀)) ≤
      2 * (n + Fintype.card (UnfoldVertex (allArrowSource e₀)) - 1) := by
  calc
    Fintype.card (@AllArrow (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀)) = Fintype.card (AllArrow (V := V)) + 2 :=
      unfoldAllArrow_card L e₀
    _ ≤ 2 * (n + Fintype.card V - 1) + 2 := by
      exact Nat.add_le_add_right hEuler 2
    _ = 2 * (n + Fintype.card (UnfoldVertex (allArrowSource e₀)) - 1) := by
      rw [unfoldVertex_card]
      have hA : 1 ≤ n + Fintype.card V := by
        have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr
          ⟨allArrowSource e₀⟩
        omega
      have hsub : n + Fintype.card V - 1 + 1 =
          n + Fintype.card V := Nat.sub_add_cancel hA
      calc
        2 * (n + Fintype.card V - 1) + 2 =
            2 * (n + Fintype.card V - 1) + 2 * 1 := by simp
        _ = 2 * (n + Fintype.card V - 1 + 1) := by
          rw [Nat.mul_add]
        _ = 2 * (n + Fintype.card V) := by rw [hsub]
        _ = 2 * (n + (Fintype.card V + 1) - 1) := by
          congr 2

theorem unfold_allArrow_reverse_ne
    (L : BinaryLabelling (G := G) (H := H) (V := V))
    (e₀ : AllArrow (V := V))
    (hfree : ReverseFree (V := V)) :
    letI : Fintype (UnfoldVertex (allArrowSource e₀)) :=
      unfoldVertexFintype (allArrowSource e₀)
    letI : Quiver (UnfoldVertex (allArrowSource e₀)) :=
      unfoldQuiver L e₀
    letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
      unfoldHasReverse L e₀
    letI (x y : UnfoldVertex (allArrowSource e₀)) : Fintype (x ⟶ y) :=
      unfoldQuiverHomFintype L e₀ x y
    ∀ e : @AllArrow (UnfoldVertex (allArrowSource e₀))
      (unfoldQuiver L e₀), allArrowReverse e ≠ e := by
  letI : Fintype (UnfoldVertex (allArrowSource e₀)) :=
    unfoldVertexFintype (allArrowSource e₀)
  letI : Quiver (UnfoldVertex (allArrowSource e₀)) := unfoldQuiver L e₀
  letI : HasInvolutiveReverse (UnfoldVertex (allArrowSource e₀)) :=
    unfoldHasReverse L e₀
  letI (x y : UnfoldVertex (allArrowSource e₀)) : Fintype (x ⟶ y) :=
    unfoldQuiverHomFintype L e₀ x y
  intro e he
  rcases e with ⟨x, y, e⟩
  rcases e with ⟨edge, hs, ht⟩
  have hedge : unfoldEdgeReverse edge = edge := by
    have he' := congrArg
      (fun z : @AllArrow (UnfoldVertex (allArrowSource e₀))
        (unfoldQuiver L e₀) => z.2.2.1) he
    change unfoldEdgeReverse edge = edge at he'
    exact he'
  cases edge with
  | inl e =>
      apply hfree e
      simpa [unfoldEdgeReverse] using hedge
  | inr b => cases b <;> simp [unfoldEdgeReverse] at hedge

end GeneralGrushko
end MarshallHall
