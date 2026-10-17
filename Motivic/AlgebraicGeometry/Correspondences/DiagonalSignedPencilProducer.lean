/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SignedPencilSourceEndpoints
public import Motivic.Aglib.AlgebraicGeometry.RegularProductSections

/-! # Actual section data producing both correcting-homotopy endpoints -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Motivic.SignedProductPencilEndpoints

universe u
namespace Motivic.DiagonalSignedPencilProducer

variable {k : Type u} [Field k]

/-- Genuine geometric input only: two Cartesian ambient diagrams, four regular
sections, a diagonal ideal, and the actual finite-flat polynomial family.
No correspondence equality or endpoint identity is a field. -/
structure Data {X T V Y : SmoothSite (Spec (.of k))}
    (α : X ⟶ T) (β : X ⟶ V) (φ : X ⟶ Y) where
  C : Scheme.{u}
  E : Scheme.{u}
  D : Scheme.{u}
  qA : C ⟶ T.left
  rA : C ⟶ Y.left
  hA : qA ≫ T.hom = rA ≫ Y.hom
  qN : E ⟶ V.left
  rN : E ⟶ Y.left
  hN : qN ≫ V.hom = rN ≫ Y.hom
  jA : D ⟶ C
  jN : D ⟶ E
  p : D ⟶ X.left
  squareA : IsPullback jA p qA α.left
  squareN : IsPullback jN p qN β.left
  g : D ⟶ Y.left
  targetA : jA ≫ rA = g
  targetN : jN ≫ rN = g
  base : p ≫ X.hom = g ≫ Y.hom
  A : LineBundle C
  B : LineBundle C
  N : LineBundle E
  M : LineBundle E
  a : A.val ⟶ SheafOfModules.unit C.ringCatSheaf
  b : B.val ⟶ SheafOfModules.unit C.ringCatSheaf
  n : N.val ⟶ SheafOfModules.unit E.ringCatSheaf
  d : M.val ⟶ SheafOfModules.unit E.ringCatSheaf
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

namespace Data
variable {X T V Y : SmoothSite (Spec (.of k))}
  {α : X ⟶ T} {β : X ⟶ V} {φ : X ⟶ Y} (P : Data α β φ)

/-- The original numerator-minus-pole correspondence on the first source. -/
def lam : Cor.mk T ⟶ Cor.mk Y :=
  Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.a ≫ P.qA) (Hom.zeroInclusion P.a ≫ P.rA)
      (by simp only [Category.assoc, P.hA]) -
    Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.b ≫ P.qA) (Hom.zeroInclusion P.b ≫ P.rA)
      (by simp only [Category.assoc, P.hA])

/-- The correction is pole-minus-numerator, with the sign needed by the consumer. -/
def psi : Cor.mk V ⟶ Cor.mk Y :=
  Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.d ≫ P.qN) (Hom.zeroInclusion P.d ≫ P.rN)
      (by simp only [Category.assoc, P.hN]) -
    Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.n ≫ P.qN) (Hom.zeroInclusion P.n ≫ P.rN)
      (by simp only [Category.assoc, P.hN])

/-- The full actual polynomial family minus the constant original product pole. -/
def correspondence : Cor.mk (SmoothSite.a1Cylinder (.of k) X) ⟶ Cor.mk Y :=
  signedCorrespondence P.p
    (tensorLineBundle P.D ⟨Scheme.Hom.idealModule P.diagonal, P.diagonal_line⟩
      (tensorLineBundle P.D (pullbackLineBundle P.jA P.B) (pullbackLineBundle P.jN P.M)))
    (Hom.productSection (Scheme.Hom.idealInclusion P.diagonal)
      (Hom.productSection (Hom.pullbackToUnit P.b P.jA) (Hom.pullbackToUnit P.d P.jN)))
    (P.lineIso.hom ≫
      Hom.productSection (Hom.pullbackToUnit P.a P.jA) (Hom.pullbackToUnit P.n P.jN))
    P.g P.base (Hom.productSection (Hom.pullbackToUnit P.b P.jA) (Hom.pullbackToUnit P.d P.jN))

/-- Both consumer endpoints follow from the original geometry and section algebra. -/
theorem endpoints :
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 0) ≫ P.correspondence =
        (Cor.graphFunctor k).map φ ∧
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 1) ≫ P.correspondence =
        (Cor.graphFunctor k).map α ≫ P.lam - (Cor.graphFunctor k).map β ≫ P.psi := by
  let : Flat α.left := P.alpha_flat
  let : Flat β.left := P.beta_flat
  constructor
  · let : Flat P.jA := MorphismProperty.of_isPullback P.squareA.flip P.alpha_flat
    let : Flat P.jN := MorphismProperty.of_isPullback P.squareN.flip P.beta_flat
    let : Mono P.b := P.b_regular
    let : Mono P.d := P.d_regular
    let : P.B.val.IsLocallyFree := lineBundle_isLocallyFree P.C P.B
    let : P.M.val.IsLocallyFree := lineBundle_isLocallyFree P.E P.M
    let : Mono (Hom.pullbackToUnit P.b P.jA) := by
      dsimp only [Hom.pullbackToUnit]
      infer_instance
    let : Mono (Hom.pullbackToUnit P.d P.jN) := by
      dsimp only [Hom.pullbackToUnit]
      infer_instance
    let := Hom.productSection_mono (pullbackLineBundle P.jA P.B) (pullbackLineBundle P.jN P.M)
      (Hom.pullbackToUnit P.b P.jA) (Hom.pullbackToUnit P.d P.jN)
    rw [← PencilA1Endpoints.endpointMorphism_eq_a1Section]
    exact signed_diagonal_zero P.p P.diagonal P.diagonal_source P.diagonal_line
      (tensorLineBundle P.D (pullbackLineBundle P.jA P.B) (pullbackLineBundle P.jN P.M))
      (Hom.productSection (Hom.pullbackToUnit P.b P.jA) (Hom.pullbackToUnit P.d P.jN))
      (P.lineIso.hom ≫
        Hom.productSection (Hom.pullbackToUnit P.a P.jA) (Hom.pullbackToUnit P.n P.jN))
      P.g φ P.diagonal_target P.base
  · exact SignedPencilSourceEndpoints.signed_one_source_graphs
      P.qA P.rA P.hA P.qN P.rN P.hN α β P.jA P.jN P.p P.squareA P.squareN
      P.A P.B P.N P.M P.a P.b P.n P.d P.g P.targetA P.targetN P.base
      _ _ P.lineIso

end Data
end Motivic.DiagonalSignedPencilProducer
