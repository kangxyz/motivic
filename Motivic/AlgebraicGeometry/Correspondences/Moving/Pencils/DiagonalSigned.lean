/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Pencils.GraphDivisorData

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.SignedSourceEndpoints
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.RegularProductSections

/-! # Actual section data producing both correcting-homotopy endpoints -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.SmoothSite.PolynomialPencil

universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil

variable {k : Type u} [Field k]
namespace Data
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLine
variable {X T V Y : SmoothSite (Spec (.of k))}
  {α : X ⟶ T} {β : X ⟶ V} {φ : X ⟶ Y} (P : Data α β φ)

/-- The original numerator-minus-pole correspondence on the first source. -/
def lam : _root_.Motivic.Cor.mk T ⟶ _root_.Motivic.Cor.mk Y :=
  _root_.Motivic.Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.a ≫ P.qA) (Hom.zeroInclusion P.a ≫ P.rA)
      (by simp only [Category.assoc, P.hA]) -
    _root_.Motivic.Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.b ≫ P.qA) (Hom.zeroInclusion P.b ≫
        P.rA)
      (by simp only [Category.assoc, P.hA])

/-- The correction is pole-minus-numerator, with the sign needed by the consumer. -/
def psi : _root_.Motivic.Cor.mk V ⟶ _root_.Motivic.Cor.mk Y :=
  _root_.Motivic.Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.d ≫ P.qN) (Hom.zeroInclusion P.d ≫ P.rN)
      (by simp only [Category.assoc, P.hN]) -
    _root_.Motivic.Cor.ofFiniteFlatSpan (Hom.zeroInclusion P.n ≫ P.qN) (Hom.zeroInclusion P.n ≫
        P.rN)
      (by simp only [Category.assoc, P.hN])

/-- The full actual polynomial family minus the constant original product pole. -/
def correspondence : _root_.Motivic.Cor.mk (a1Cylinder (.of k) X) ⟶ _root_.Motivic.Cor.mk Y :=
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
    (_root_.Motivic.Cor.graphFunctor k).map (a1Section (.of k) X 0) ≫ P.correspondence =
        (_root_.Motivic.Cor.graphFunctor k).map φ ∧
      (_root_.Motivic.Cor.graphFunctor k).map (a1Section (.of k) X 1) ≫ P.correspondence =
        (_root_.Motivic.Cor.graphFunctor k).map α ≫ P.lam - (_root_.Motivic.Cor.graphFunctor
            k).map β ≫ P.psi := by
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
    rw [← Endpoints.endpointMorphism_eq_a1Section]
    exact signed_diagonal_zero P.p P.diagonal P.diagonal_source P.diagonal_line
      (tensorLineBundle P.D (pullbackLineBundle P.jA P.B) (pullbackLineBundle P.jN P.M))
      (Hom.productSection (Hom.pullbackToUnit P.b P.jA) (Hom.pullbackToUnit P.d P.jN))
      (P.lineIso.hom ≫
        Hom.productSection (Hom.pullbackToUnit P.a P.jA) (Hom.pullbackToUnit P.n P.jN))
      P.g φ P.diagonal_target P.base
  · exact _root_.Motivic.SignedPencilSourceEndpoints.signed_one_source_graphs
      P.qA P.rA P.hA P.qN P.rN P.hN α β P.jA P.jN P.p P.squareA P.squareN
      P.A P.B P.N P.M P.a P.b P.n P.d P.g P.targetA P.targetN P.base
      _ _ P.lineIso

end Data
end AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil
