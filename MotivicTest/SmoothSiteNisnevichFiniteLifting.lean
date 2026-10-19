/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteLifting
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of smooth-site finite-support lifting

These tests keep the actual scheme pullback, the actual residue-field map,
and the smooth, separated, finite-type structure of the new neighborhood.
They include empty fibers, nonreduced schemes, and disconnected finite support.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.SmoothSiteNisnevichFiniteLifting

/-- Over a field the neighborhood is an object of the same smooth site, with
its actual structure morphism smooth, separated, and of finite type. -/
theorem field_lift {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
    {Z V : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p] (x : X.left)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (hq : ∀ z : Z, p z = x → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X),
      Smooth U.hom ∧ IsSeparated U.hom ∧ LocallyOfFiniteType U.hom ∧
      QuasiCompact U.hom ∧ Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ Function.Bijective (g.left.residueFieldMap u) ∧
    ∃ b : pullback p g.left ⟶ V, b ≫ q = pullback.fst p g.left := by
  obtain ⟨U, g, hg, u, hu, hr, b, hb⟩ :=
    SmoothSite.exists_nisnevich_lift_of_isFinite X p x q hq
  exact ⟨U, g, inferInstance, inferInstance, inferInstance, inferInstance, hg,
    u, hu, (ConcreteCategory.isIso_iff_bijective _).mp hr, b, hb⟩

/-- An empty fiber is removed without leaving the smooth site. -/
theorem empty_fiber_gives_empty_support {S : Scheme.{u}} [IsAffine S]
    (X : SmoothSite S) {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
    (x : X.left) (hx : ∀ z : Z, p z ≠ x) :
    ∃ (U : SmoothSite S) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      IsEmpty (pullback p g.left : Scheme) := by
  obtain ⟨U, g, hg, u, hu, hr, b, _⟩ :=
    SmoothSite.exists_nisnevich_lift_of_isFinite X p x (initial.to Z)
      (fun z hz ↦ (hx z hz).elim)
  exact ⟨U, g, hg, u, hu, hr, ⟨fun z ↦ isEmptyElim (b z)⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A nonreduced support is preserved as the literal pullback scheme. -/
example {V : Scheme} (q : V ⟶ Spec (.of (ZMod 4))) [Etale q] [IsSeparated q]
    (hq : ∀ z : Spec (.of (ZMod 4)),
      ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) (x : Spec (.of (ZMod 4))) :
    ∃ (U : SmoothSite (Spec (.of (ZMod 4))))
      (g : U ⟶ SmoothSite.base (Spec (.of (ZMod 4)))), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ b : pullback (𝟙 (Spec (.of (ZMod 4)))) g.left ⟶ V,
      b ≫ q = pullback.fst (𝟙 _) g.left :=
  SmoothSite.exists_nisnevich_lift_of_isFinite (S := Spec (.of (ZMod 4)))
    (SmoothSite.base _) (𝟙 _) x q
    (fun z _ ↦ hq z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Two finite components over a field are lifted simultaneously. -/
example {k : Type u} [Field k] {V : Scheme.{u}}
    (q : V ⟶ Spec (.of (k × k))) [Etale q] [IsSeparated q]
    (hq : ∀ z : Spec (.of (k × k)), ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v))
    (x : Spec (.of k)) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ SmoothSite.base (Spec (.of k))),
      Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ b : pullback (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) g.left ⟶ V,
      b ≫ q = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k (k × k))))
        g.left := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  exact SmoothSite.exists_nisnevich_lift_of_isFinite (S := Spec (.of k))
    (SmoothSite.base _) p x q
    (fun z _ ↦ hq z)

/-- A finite common refinement retains actual morphism and point equations. -/
theorem finite_pointed_refinement {S : Scheme.{u}} [IsAffine S]
    (X : SmoothSite S) (x : X.left) (n : ℕ)
    (U : Fin n → SmoothSite S) (g : ∀ i, U i ⟶ X)
    (hg : ∀ i, Etale (g i).left) (u : ∀ i, (U i).left)
    (hu : ∀ i, (g i).left (u i) = x)
    (hr : ∀ i, IsIso ((g i).left.residueFieldMap (u i))) :
    ∃ (W : SmoothSite S) (h : W ⟶ X), Etale h.left ∧
    ∃ w : W.left, h.left w = x ∧ IsIso (h.left.residueFieldMap w) ∧
    ∃ a : ∀ i, W ⟶ U i, (∀ i, a i ≫ g i = h) ∧
      (∀ i, (a i).left w = u i) :=
  SmoothSite.exists_common_nisnevich_refinement X x n U g hg u hu hr

/-- No nonemptiness assumption on the finite family enters the refinement. -/
theorem empty_pointed_refinement {S : Scheme.{u}} [IsAffine S]
    (X : SmoothSite S) (x : X.left) :
    ∃ (W : SmoothSite S) (h : W ⟶ X), Etale h.left ∧
    ∃ w : W.left, h.left w = x ∧ IsIso (h.left.residueFieldMap w) := by
  obtain ⟨W, h, hh, w, hw, hr, _⟩ :=
    SmoothSite.exists_common_nisnevich_refinement X x 0
      (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
      (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  exact ⟨W, h, hh, w, hw, hr⟩

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_nisnevich_lift_of_isFinite,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_common_nisnevich_refinement,
      ``field_lift, ``empty_fiber_gives_empty_support,
      ``finite_pointed_refinement, ``empty_pointed_refinement] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.SmoothSiteNisnevichFiniteLifting
