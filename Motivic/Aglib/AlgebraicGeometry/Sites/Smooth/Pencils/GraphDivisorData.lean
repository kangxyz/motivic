/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Pencils.FamilyMaps
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.RegularProductSections

/-!
# Graph-divisor data for smooth-site pencils
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.SmoothSite.PolynomialPencil

universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil

variable {k : Type u} [Field k]

/-- Genuine geometric input only: two Cartesian ambient diagrams, four regular
sections, a diagonal ideal, and the actual finite-flat polynomial family.
No correspondence equality or endpoint identity is a field. -/
structure Data {X T V Y : SmoothSite (Spec (.of k))}
    (α : X ⟶ T) (β : X ⟶ V) (φ : X ⟶ Y) where
  /-- The first ambient scheme carrying the `a` and `b` line-bundle functionals. -/
  C : Scheme.{u}
  /-- The second ambient scheme carrying the `n` and `d` line-bundle functionals. -/
  E : Scheme.{u}
  /-- The common scheme in the two given Cartesian ambient diagrams over `X.left`. -/
  D : Scheme.{u}
  /-- The structure morphism from the first ambient scheme `C` to `T.left`. -/
  qA : C ⟶ T.left
  /-- The original target morphism from the first ambient scheme `C` to `Y.left`. -/
  rA : C ⟶ Y.left
  hA : qA ≫ T.hom = rA ≫ Y.hom
  /-- The structure morphism from the second ambient scheme `E` to `V.left`. -/
  qN : E ⟶ V.left
  /-- The original target morphism from the second ambient scheme `E` to `Y.left`. -/
  rN : E ⟶ Y.left
  hN : qN ≫ V.hom = rN ≫ Y.hom
  /-- The morphism from `D` to `C` in the first given Cartesian square. -/
  jA : D ⟶ C
  /-- The morphism from `D` to `E` in the second given Cartesian square. -/
  jN : D ⟶ E
  /-- The structure morphism from the common ambient scheme `D` to `X.left`. -/
  p : D ⟶ X.left
  squareA : IsPullback jA p qA α.left
  squareN : IsPullback jN p qN β.left
  /-- The common target morphism from `D` to `Y.left`, agreeing with both ambient target maps. -/
  g : D ⟶ Y.left
  targetA : jA ≫ rA = g
  targetN : jN ≫ rN = g
  base : p ≫ X.hom = g ≫ Y.hom
  /-- The numerator line bundle on the first ambient scheme `C`. -/
  A : LineBundle C
  /-- The denominator line bundle on the first ambient scheme `C`. -/
  B : LineBundle C
  /-- The numerator line bundle on the second ambient scheme `E`. -/
  N : LineBundle E
  /-- The denominator line bundle on the second ambient scheme `E`. -/
  M : LineBundle E
  /-- The chosen numerator functional from `A.val` to the unit module on `C`. -/
  a : A.val ⟶ SheafOfModules.unit C.ringCatSheaf
  /-- The chosen denominator functional from `B.val` to the unit module on `C`. -/
  b : B.val ⟶ SheafOfModules.unit C.ringCatSheaf
  /-- The chosen numerator functional from `N.val` to the unit module on `E`. -/
  n : N.val ⟶ SheafOfModules.unit E.ringCatSheaf
  /-- The chosen denominator functional from `M.val` to the unit module on `E`. -/
  d : M.val ⟶ SheafOfModules.unit E.ringCatSheaf
  /-- The given closed map `X.left ⟶ D`, with identity composite under `p` and composite
  `φ.left` under `g`. -/
  diagonal : X.left ⟶ D
  diagonal_closed : IsClosedImmersion diagonal
  diagonal_source : diagonal ≫ p = 𝟙 X.left
  diagonal_target : diagonal ≫ g = φ.left
  diagonal_line : IsLocallyRankOne D (Scheme.Hom.idealModule diagonal)
  alpha_flat : Flat α.left
  beta_flat : Flat β.left
  a_regular : Mono a
  b_regular : Mono b
  n_regular : Mono n
  d_regular : Mono d
  a_finite : IsFinite (Hom.zeroInclusion a ≫ qA)
  a_flat : Flat (Hom.zeroInclusion a ≫ qA)
  b_finite : IsFinite (Hom.zeroInclusion b ≫ qA)
  b_flat : Flat (Hom.zeroInclusion b ≫ qA)
  n_finite : IsFinite (Hom.zeroInclusion n ≫ qN)
  n_flat : Flat (Hom.zeroInclusion n ≫ qN)
  d_finite : IsFinite (Hom.zeroInclusion d ≫ qN)
  d_flat : Flat (Hom.zeroInclusion d ≫ qN)
  qA_smooth : Smooth (qA ≫ T.hom)
  qA_separated : IsSeparated (qA ≫ T.hom)
  qA_quasiCompact : QuasiCompact (qA ≫ T.hom)
  qN_smooth : Smooth (qN ≫ V.hom)
  qN_separated : IsSeparated (qN ≫ V.hom)
  qN_quasiCompact : QuasiCompact (qN ≫ V.hom)
  p_smooth : Smooth (p ≫ X.hom)
  p_separated : IsSeparated (p ≫ X.hom)
  p_quasiCompact : QuasiCompact (p ≫ X.hom)
  /-- The module isomorphism from the diagonal ideal tensored with both pulled-back denominator
  bundles to the tensor of the pulled-back numerator bundles. -/
  lineIso : (tensorLineBundle D ⟨Scheme.Hom.idealModule diagonal, diagonal_line⟩
    (tensorLineBundle D (pullbackLineBundle jA B) (pullbackLineBundle jN M))).val ≅
    (tensorLineBundle D (pullbackLineBundle jA A) (pullbackLineBundle jN N)).val
  pole_finite : IsFinite (Hom.zeroInclusion
    (Hom.productSection (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN)) ≫ p)
  pole_flat : Flat (Hom.zeroInclusion
    (Hom.productSection (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN)) ≫ p)
  family_finite : IsFinite (familySource p
    (tensorLineBundle D ⟨Scheme.Hom.idealModule diagonal, diagonal_line⟩
    (tensorLineBundle D (pullbackLineBundle jA B) (pullbackLineBundle jN M)))
    (Hom.productSection (Scheme.Hom.idealInclusion diagonal)
      (Hom.productSection (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN)))
    (lineIso.hom ≫ Hom.productSection (Hom.pullbackToUnit a jA) (Hom.pullbackToUnit n jN)))
  family_flat : Flat (familySource p
    (tensorLineBundle D ⟨Scheme.Hom.idealModule diagonal, diagonal_line⟩
    (tensorLineBundle D (pullbackLineBundle jA B) (pullbackLineBundle jN M)))
    (Hom.productSection (Scheme.Hom.idealInclusion diagonal)
      (Hom.productSection (Hom.pullbackToUnit b jA) (Hom.pullbackToUnit d jN)))
    (lineIso.hom ≫ Hom.productSection (Hom.pullbackToUnit a jA) (Hom.pullbackToUnit n jN)))

attribute [instance] Data.diagonal_closed
attribute [instance] Data.a_regular Data.a_finite Data.a_flat
attribute [instance] Data.b_regular Data.b_finite Data.b_flat
attribute [instance] Data.n_regular Data.n_finite Data.n_flat
attribute [instance] Data.d_regular Data.d_finite Data.d_flat
attribute [instance] Data.qA_smooth Data.qA_separated Data.qA_quasiCompact
attribute [instance] Data.qN_smooth Data.qN_separated Data.qN_quasiCompact
attribute [instance] Data.p_smooth Data.p_separated Data.p_quasiCompact
attribute [instance] Data.pole_finite Data.pole_flat Data.family_finite Data.family_flat


end AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil
