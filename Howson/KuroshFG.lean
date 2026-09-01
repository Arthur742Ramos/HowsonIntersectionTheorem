import Howson.BinaryKurosh

/-!
# Finitely generated Kurosh factors

The Kurosh decomposition is a free product.  A factor of a free product is a
retract, so a finitely generated ambient group has finitely generated Kurosh
factors.  The auxiliary constructions in this file make that retract
explicit and then transport it across the Bass--Serre representatives.
-/

noncomputable section

open Set Function
open Monoid
open GraphCoveringTheory GraphCoveringTheory.Kurosh

namespace Howson

universe u v

abbrev ActiveIndex {ι : Type v} {G : ι → Type u} [∀ i, Group (G i)]
    (N : Subgroup (FreeProduct G)) :=
  @KuroshActiveComponentIndex.{u, v, 0} ι G _ N

abbrev ActiveComponent {ι : Type v} {G : ι → Type u} [∀ i, Group (G i)]
    (N : Subgroup (FreeProduct G)) (q : ActiveIndex N) :=
  KuroshActiveComponent G N q

abbrev ActiveProduct {ι : Type v} {G : ι → Type u} [∀ i, Group (G i)]
    (N : Subgroup (FreeProduct G)) :=
  @KuroshActiveProduct.{u, v, 0} ι G _ N

lemma stabilizerConj_mem {G : Type u} {X : Type u} [Group G] [MulAction G X]
    {x y : X} (g : G) (hxy : g • x = y)
    (a : MulAction.stabilizer G x) :
    g * a.1 * g⁻¹ ∈ MulAction.stabilizer G y := by
  change (g * a.1 * g⁻¹) • y = y
  rw [← hxy]
  have ha : a.1 • x = x := MulAction.mem_stabilizer_iff.mp a.property
  have ha' := congrArg (fun z => g • z) ha
  simpa [smul_smul, mul_assoc] using ha'

lemma stabilizerConj_mem_inv {G : Type u} {X : Type u} [Group G] [MulAction G X]
    {x y : X} (g : G) (hxy : g • x = y)
    (b : MulAction.stabilizer G y) :
    g⁻¹ * b.1 * g ∈ MulAction.stabilizer G x := by
  change (g⁻¹ * b.1 * g) • x = x
  have hb : b.1 • (g • x) = g • x := by
    rw [hxy]
    exact MulAction.mem_stabilizer_iff.mp b.property
  have hb' := congrArg (fun z => g⁻¹ • z) hb
  simpa [smul_smul, mul_assoc] using hb'

def stabilizerConjEquiv {G : Type u} {X : Type u} [Group G] [MulAction G X]
    {x y : X} (g : G) (hxy : g • x = y) :
    MulAction.stabilizer G x ≃* MulAction.stabilizer G y :=
  { toFun := fun a => ⟨g * a.1 * g⁻¹, stabilizerConj_mem g hxy a⟩
    invFun := fun b => ⟨g⁻¹ * b.1 * g, stabilizerConj_mem_inv g hxy b⟩
    left_inv := by
      intro a
      apply Subtype.ext
      simp [mul_assoc]
    right_inv := by
      intro b
      apply Subtype.ext
      simp [mul_assoc]
    map_mul' := by
      intro a b
      apply Subtype.ext
      simp [mul_assoc] }

def activeProjection {ι : Type v} {G : ι → Type u}
    [∀ i, Group (G i)] (N : Subgroup (FreeProduct G))
    (q : ActiveIndex N) :
    ActiveProduct N →* ActiveComponent N q :=
  by
    classical
    exact Monoid.CoprodI.lift (fun r =>
      dite (r = q)
        (fun h => h ▸ MonoidHom.id _)
        (fun _ =>
          { toFun := fun _ => 1
            map_one' := by simp
            map_mul' := by intro _ _; simp }))

@[simp]
theorem activeProjection_of {ι : Type v} {G : ι → Type u}
    [∀ i, Group (G i)] (N : Subgroup (FreeProduct G))
    (q : ActiveIndex N)
    (x : ActiveComponent N q) :
    activeProjection N q (Monoid.CoprodI.of x) = x := by
  simp [activeProjection]

theorem activeProjection_surjective {ι : Type v} {G : ι → Type u}
    [∀ i, Group (G i)] (N : Subgroup (FreeProduct G))
    (q : ActiveIndex N) :
    Function.Surjective (activeProjection N q) := by
  intro x
  exact ⟨Monoid.CoprodI.of x, activeProjection_of N q x⟩

theorem fg_active_component {ι : Type v} {G : ι → Type u}
    [∀ i, Group (G i)] (N : Subgroup (FreeProduct G))
    [Group.FG N] (q : ActiveIndex N) :
    Group.FG (ActiveComponent N q) := by
  let e : ActiveProduct N ≃* N := kuroshActiveEquivH G N
  have hprod : Group.FG (ActiveProduct N) :=
    Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  letI : Group.FG (ActiveProduct N) := hprod
  exact Group.fg_of_surjective (hG := hprod) (f := activeProjection N q)
    (activeProjection_surjective N q)

theorem fg_tree_vertex_stabilizer {ι : Type v} {G : ι → Type u}
    [∀ i, Group (G i)] (N : Subgroup (FreeProduct G))
    [Group.FG N] (a : RawBassSerreOrbitVertex G N) :
    Group.FG (treeVertexStabilizer G N a) := by
  let S := treeVertexStabilizer G N a
  by_cases hS : S = ⊥
  · letI : Subsingleton S := by
      constructor
      intro x y
      apply Subtype.ext
      have hx : (x : N) ∈ (⊥ : Subgroup N) := by
        rw [← hS]
        exact x.property
      have hy : (y : N) ∈ (⊥ : Subgroup N) := by
        rw [← hS]
        exact y.property
      have hx' : (x : N) = 1 := by simpa using hx
      have hy' : (y : N) = 1 := by simpa using hy
      exact hx'.trans hy'.symm
    apply Group.fg_iff.mpr
    refine ⟨{1}, ?_, Set.finite_singleton _⟩
    apply le_antisymm le_top
    intro x _
    have hx : x = (1 : S) := Subsingleton.elim _ _
    rw [hx]
    exact Subgroup.subset_closure (by simp)
  · let q : ActiveIndex N :=
      (Sum.inl ⟨a, hS⟩ : ActiveIndex N)
    have hfg : Group.FG (ActiveComponent N q) :=
      fg_active_component (G := G) N q
    change Group.FG (ULift.{max (u + 1) (v + 1)} S) at hfg
    let e : ULift.{max (u + 1) (v + 1)} S ≃* S := MulEquiv.ulift
    exact Group.fg_of_surjective (hG := hfg) (f := e.toMonoidHom) e.surjective

theorem fg_intersection_factor {ι : Type v} {G : ι → Type u}
    [∀ i, Group (G i)] (N : Subgroup (FreeProduct G))
    [Group.FG N] (i : ι) (g : FreeProduct G) :
    Group.FG (intersectionFactorInH N i g) := by
  let raw : RawBassSerreVertex G :=
    RawBassSerreVertex.factor i (factorCosetMk G i g)
  let a : RawBassSerreOrbitVertex G N :=
    actionOrbitMk N (RawBassSerreVertex G) raw
  let tree := rawTreeRepresentative G N a
  have horbit : actionOrbitMk N (RawBassSerreVertex G) tree =
      actionOrbitMk N (RawBassSerreVertex G) raw := by
    exact rawTreeRepresentative_orbit G N a
  obtain ⟨n, hn⟩ :=
    (actionOrbitMk_eq_iff N (RawBassSerreVertex G) tree raw).1 horbit
  have hS : Group.FG (treeVertexStabilizer G N a) :=
    fg_tree_vertex_stabilizer N a
  let eS : MulAction.stabilizer N tree ≃* MulAction.stabilizer N raw :=
    stabilizerConjEquiv n hn
  have htree : MulAction.stabilizer N tree = treeVertexStabilizer G N a := rfl
  have hraw : MulAction.stabilizer N raw = intersectionFactorInH N i g := by
    ext x
    change x.1 • raw = raw ↔ _
    exact rawBassSerre_factor_fixed_iff G N i g x
  have eT : treeVertexStabilizer G N a ≃*
      intersectionFactorInH N i g := by
    exact eS.trans (MulEquiv.subgroupCongr hraw)
  exact Group.fg_of_surjective (hG := hS) (f := eT.toMonoidHom) eT.surjective

end Howson
