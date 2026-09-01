import MarshallHall
import GraphCoveringTheory.KuroshTheorem

noncomputable section

open Monoid.Coprod

namespace Howson

universe u

abbrev binaryFamily (A B : Type u) : Bool → Type u
  | false => A
  | true => B

instance binaryFamilyGroup (A B : Type u) [Group A] [Group B] :
    ∀ i, Group (binaryFamily A B i) := by
  intro i
  cases i
  · change Group A
    infer_instance
  · change Group B
    infer_instance

def indexedLeft {A B : Type u} [Group A] [Group B] :
    A →* Monoid.CoprodI (binaryFamily A B) :=
  Monoid.CoprodI.of (M := binaryFamily A B) (i := false)

def indexedRight {A B : Type u} [Group A] [Group B] :
    B →* Monoid.CoprodI (binaryFamily A B) :=
  Monoid.CoprodI.of (M := binaryFamily A B) (i := true)

def binaryToIndexed {A B : Type u} [Group A] [Group B] :
    (A ∗ B) →* Monoid.CoprodI (binaryFamily A B) :=
  Monoid.Coprod.lift (indexedLeft (A := A) (B := B))
    (indexedRight (A := A) (B := B))

def indexedToBinaryFamily {A B : Type u} [Group A] [Group B] :
    (i : Bool) → binaryFamily A B i →* (A ∗ B)
  | false => Monoid.Coprod.inl
  | true => Monoid.Coprod.inr

def indexedToBinary {A B : Type u} [Group A] [Group B] :
    Monoid.CoprodI (binaryFamily A B) →* (A ∗ B) :=
  Monoid.CoprodI.lift (M := binaryFamily A B)
    (indexedToBinaryFamily (A := A) (B := B))

theorem binaryToIndexed_comp_indexedToBinary {A B : Type u} [Group A] [Group B] :
    (binaryToIndexed (A := A) (B := B)).comp
        (indexedToBinary (A := A) (B := B)) = MonoidHom.id _ := by
  classical
  apply Monoid.CoprodI.ext_hom
  intro i
  cases i
  · ext x
    change A at x
    change binaryToIndexed (indexedToBinary (indexedLeft x)) = indexedLeft x
    change binaryToIndexed
      ((Monoid.CoprodI.lift (M := binaryFamily A B)
        (indexedToBinaryFamily (A := A) (B := B)))
        (Monoid.CoprodI.of (M := binaryFamily A B) (i := false) x)) =
      indexedLeft x
    rw [Monoid.CoprodI.lift_of]
    rfl
  · ext x
    change B at x
    change binaryToIndexed (indexedToBinary (indexedRight x)) = indexedRight x
    change binaryToIndexed
      ((Monoid.CoprodI.lift (M := binaryFamily A B)
        (indexedToBinaryFamily (A := A) (B := B)))
        (Monoid.CoprodI.of (M := binaryFamily A B) (i := true) x)) =
      indexedRight x
    rw [Monoid.CoprodI.lift_of]
    rfl

theorem indexedToBinary_comp_binaryToIndexed {A B : Type u} [Group A] [Group B] :
    (indexedToBinary (A := A) (B := B)).comp
        (binaryToIndexed (A := A) (B := B)) = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · ext x
    change indexedToBinary (binaryToIndexed (Monoid.Coprod.inl x)) =
      Monoid.Coprod.inl x
    change indexedToBinary (indexedLeft x) = Monoid.Coprod.inl x
    change (Monoid.CoprodI.lift (M := binaryFamily A B)
      (indexedToBinaryFamily (A := A) (B := B)))
      (Monoid.CoprodI.of (M := binaryFamily A B) (i := false) x) =
      Monoid.Coprod.inl x
    rw [Monoid.CoprodI.lift_of]
    rfl
  · ext x
    change indexedToBinary (binaryToIndexed (Monoid.Coprod.inr x)) =
      Monoid.Coprod.inr x
    change indexedToBinary (indexedRight x) = Monoid.Coprod.inr x
    change (Monoid.CoprodI.lift (M := binaryFamily A B)
      (indexedToBinaryFamily (A := A) (B := B)))
      (Monoid.CoprodI.of (M := binaryFamily A B) (i := true) x) =
      Monoid.Coprod.inr x
    rw [Monoid.CoprodI.lift_of]
    rfl

def binaryIndexedEquiv {A B : Type u} [Group A] [Group B] :
    Monoid.CoprodI (binaryFamily A B) ≃* (A ∗ B) :=
  { toFun := indexedToBinary (A := A) (B := B)
    invFun := binaryToIndexed (A := A) (B := B)
    left_inv := by
      intro x
      have h := congrArg
        (fun f : Monoid.CoprodI (binaryFamily A B) →*
          Monoid.CoprodI (binaryFamily A B) => f x)
        (binaryToIndexed_comp_indexedToBinary (A := A) (B := B))
      exact h
    right_inv := by
      intro x
      have h := congrArg
        (fun f : (A ∗ B) →* (A ∗ B) => f x)
        (indexedToBinary_comp_binaryToIndexed (A := A) (B := B))
      exact h
    map_mul' := map_mul (indexedToBinary (A := A) (B := B)) }

@[simp]
theorem binaryIndexedEquiv_of_false {A B : Type u} [Group A] [Group B]
    (x : A) :
    binaryIndexedEquiv (A := A) (B := B)
        (Monoid.CoprodI.of (i := false) x) = Monoid.Coprod.inl x := by
  change indexedToBinary (Monoid.CoprodI.of (M := binaryFamily A B) (i := false) x) =
    Monoid.Coprod.inl x
  change (Monoid.CoprodI.lift (M := binaryFamily A B)
    (indexedToBinaryFamily (A := A) (B := B)))
    (Monoid.CoprodI.of (M := binaryFamily A B) (i := false) x) =
    Monoid.Coprod.inl x
  rw [Monoid.CoprodI.lift_of]
  rfl

@[simp]
theorem binaryIndexedEquiv_of_true {A B : Type u} [Group A] [Group B]
    (x : B) :
    binaryIndexedEquiv (A := A) (B := B)
        (Monoid.CoprodI.of (i := true) x) = Monoid.Coprod.inr x := by
  change indexedToBinary (Monoid.CoprodI.of (M := binaryFamily A B) (i := true) x) =
    Monoid.Coprod.inr x
  change (Monoid.CoprodI.lift (M := binaryFamily A B)
    (indexedToBinaryFamily (A := A) (B := B)))
    (Monoid.CoprodI.of (M := binaryFamily A B) (i := true) x) =
    Monoid.Coprod.inr x
  rw [Monoid.CoprodI.lift_of]
  rfl

end Howson
