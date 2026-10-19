/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Basic
public import Motivic.Transfers.Cohomology.DegreeZero.Basic
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Cartier.ArbitraryTargetEndpoints

/-!
# HI actions of the actual whole Cartier endpoints

The literal polynomial parameter line of the finite-flat curve construction is
identified with the affine-line cylinder of the actual base object. Its scalar
evaluations are the images of the actual constant sections. Hence HI transfer
coefficients give equal actions of the whole endpoint correspondences of a
proper flat Cartier family, retaining all original multiplicities and an
arbitrary target map.

The same equality holds for the existing degree-zero ordinary cohomological
transfer action. This is a coefficient-action input to geometric splitting;
positive-degree affine-line cohomology vanishing is not asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Hom
open scoped Polynomial

universe w v u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- The original polynomial parameter line is the literal affine-line object. -/
theorem curveFamily_line_eq_affineLine :
    AffineLineField.line k = affineLine (.of k) := rfl

/-- The actual base cylinder is identified with the original curve parameter line
by its second projection, with the actual product lift as inverse. -/
def baseCylinderCurveLineIso :
    a1Cylinder (.of k) (base (Spec (.of k))) ≅ AffineLineField.line k where
  hom := productSnd (base (Spec (.of k))) (affineLine (.of k))
  inv := productLift
    (homMk (AffineLineField.line k).hom (Category.comp_id _)) (𝟙 _)
  hom_inv_id := by
    apply product_hom_ext
    · simp only [Category.assoc, productLift_fst, Category.id_comp]
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).symm.trans pullback.condition |>.symm
    · simp
  inv_hom_id := productLift_snd _ _

/-- The actual constant cylinder section becomes the original scalar evaluation map. -/
@[reassoc (attr := simp)]
theorem a1Section_baseCylinderCurveLineIso_hom (a : k) :
    a1Section (.of k) (base (Spec (.of k))) a ≫ (baseCylinderCurveLineIso k).hom =
      AffineLineField.evaluationPoint k a := by
  change productLift _ _ ≫ productSnd _ _ = _
  rw [productLift_snd]
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]

/-- HI identifies the endpoint actions of any signed correspondence from the original line. -/
theorem transfer_curveFamily_evaluations (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (Y : Cor k)
    (α : Cor.mk (AffineLineField.line k) ⟶ Y) (a b : k) :
    transfer P ((Cor.graphFunctor k).map (AffineLineField.evaluationPoint k a) ≫ α) =
      transfer P ((Cor.graphFunctor k).map (AffineLineField.evaluationPoint k b) ≫ α) := by
  simpa only [← Functor.map_comp_assoc, SmoothSite.a1Section_baseCylinderCurveLineIso_hom]
    using transfer_homotopy_endpoints P hP (SmoothSite.base (Spec (.of k))) Y
      ((Cor.graphFunctor k).map (SmoothSite.baseCylinderCurveLineIso k).hom ≫ α) a b

end Motivic.PresheafWithTransfers

namespace Motivic.RelativeCartierDivisor
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] {C U D : Scheme.{u}}
  (p : C ⟶ Spec (.of k[X])) [SmoothOfRelativeDimension 1 p]
  [IsSeparated p] [QuasiCompact p] (j : U ⟶ C) [IsOpenImmersion j]
  {Y : SmoothSite (Spec (.of k))} (i : D ⟶ C) [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (hAvoid : Set.range i ⊆ Set.range j) (g : U ⟶ Y.left)
  (hbase : j ≫ p ≫ (AffineLineField.line k).hom = g ≫ Y.hom)

/-- HI coefficients give equal actions of the actual whole Cartier endpoints at any scalars. -/
theorem transfer_endpoints_eq (P : PresheafWithTransfers.{v} k)
    (hP : PresheafWithTransfers.IsA1Invariant P) (a b : k) :
    P.transfer (endpointCorrespondence p i hI j hAvoid g hbase a) =
      P.transfer (endpointCorrespondence p i hI j hAvoid g hbase b) := by
  rw [← graph_evaluation_correspondence_of_separated_quasiCompact p j i hI hAvoid g hbase a,
    ← graph_evaluation_correspondence_of_separated_quasiCompact p j i hI hAvoid g hbase b]
  exact P.transfer_curveFamily_evaluations hP (Cor.mk Y) _ a b

variable [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The same original endpoints act equally on actual ordinary degree-zero cohomology. -/
theorem degreeZeroTransfer_endpoints_eq (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj) (a b : k) :
    F.degreeZeroTransfer (endpointCorrespondence p i hI j hAvoid g hbase a) =
      F.degreeZeroTransfer (endpointCorrespondence p i hI j hAvoid g hbase b) := by
  unfold SheafWithTransfers.degreeZeroTransfer
  rw [transfer_endpoints_eq p j i hI hAvoid g hbase F.obj hF a b]

end Motivic.RelativeCartierDivisor
