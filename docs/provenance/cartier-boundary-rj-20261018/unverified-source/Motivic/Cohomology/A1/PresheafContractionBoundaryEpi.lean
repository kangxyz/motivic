/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafBoundaryPolynomialImage
public import Motivic.Cohomology.A1.ContractionIntegralWholeZeroRefinement
public import Motivic.AlgebraicGeometry.SmoothSiteAffineLineZeroCoordinates
public import Motivic.AlgebraicGeometry.SmoothSiteAffineZeroPoint
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.PolynomialZeroOriginalEtalePresentation

/-! # The canonical original-presheaf contraction boundary is epimorphic

Over an infinite field, the two original section corrections give actual image
sieves on open neighborhoods of every closed point of each original zero fiber.
These opens form a genuine Jacobson open cover before passage to the Nisnevich
sieve. The coefficient presheaf is never replaced by its sheafification.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic.SmoothSiteAffineCoordinates

universe u

namespace Motivic.FiniteEtaleSite.OriginalPresheaf

variable {k : Type u} [Field k] [Infinite k]
attribute [local instance] sectionsAlgebra

/-- The actual canonical boundary morphism for every homotopy-invariant original
presheaf with transfers is epimorphic over an infinite field. -/
theorem contractionToBoundary_epi (X : SmoothSite (Spec (.of k)))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    Epi (contractionToBoundary X P) := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace
    (Y := Spec (.of k)) (show X.left ⟶ Spec (.of k) from X.hom)
  apply presheafBoundary_epi_of_closedPoint_generators
    ((PresheafWithTransfers.toPresheaf k).obj P)
    (SmoothSite.contractionOpen (.of k) X) (SmoothSite.a1Section (.of k) X 0)
    (contractionToBoundary X P)
  intro W d w hw
  obtain ⟨V₀, v₀, hV, hI, hv, hwV, E₀, e₀, q₀, a₀, z₀,
    hE, hq, hqc, hqs, H₀, haz, _hzq, hze⟩ :=
    exists_integral_whole_zero_neighborhood_refinement X W w
  let : IsAffine V₀.left := hV
  let : IsIntegral V₀.left := hI
  let : IsOpenImmersion v₀.left := hv
  let : IsAffine E₀.left := hE
  let : Etale q₀.left := hq
  let : QuasiCompact q₀.left := hqc
  let : IsSeparated q₀.left := hqs
  obtain ⟨t₀, ht₀⟩ := hwV
  have htClosed : IsClosed ({t₀} : Set V₀.left) := by
    have heq : v₀.left ⁻¹' ({w} : Set _) = {t₀} := by
      ext t
      change v₀.left t = w ↔ t = t₀
      rw [← ht₀]
      exact v₀.left.isOpenEmbedding.injective.eq_iff
    rw [← heq]
    exact hw.preimage v₀.left.continuous
  let B₀ := (toSmoothSite X).obj V₀
  let R := Γ(B₀.left, ⊤)
  let Y := (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj E₀
  let wR : Spec (.of R) := (affineIso B₀).inv.left t₀
  let xR : PrimeSpectrum (Polynomial R) :=
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) wR
  let : xR.asIdeal.IsMaximal := affineZeroPoint_isMaximal B₀ t₀ htClosed
  let qS := (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).map q₀ ≫
    (parameterProductUnderlyingIso X (SmoothSite.affineLine (.of k))).hom.app V₀
  let p : Y ⟶ RelativePolynomialOpenSpans.lineSite (k := k) (R := R) :=
    qS ≫ (affineLineIso B₀).inv
  have hpLeft : p.left = q₀.left ≫ (affineLineIso B₀).inv.left := by
    change (q₀.left ≫ 𝟙 _) ≫ (affineLineIso B₀).inv.left = _
    rw [Category.comp_id]
  let : IsIso (affineLineIso B₀).inv.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso
      (affineLineIso B₀)).inv)
  let : Etale p.left := by
    rw [hpLeft]
    infer_instance
  let sR := (affineIso B₀).hom.left ≫ a₀
  have HR : IsPullback sR (𝟙 _) p.left
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) := by
    rw [hpLeft]
    exact affineLineIso_wholeZero_isPullback B₀ q₀.left a₀ H₀
  have hsR : sR ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) :=
    HR.w.trans (Category.id_comp _)
  obtain ⟨presentation⟩ :=
    QuadraticIncidence.InfinityChart.nonempty_polynomialZero_originalEtalePresentation
      k R xR p.left sR hsR HR
  let vR := (affineIso B₀).hom ≫ (toSmoothSite X).map v₀
  let eR := (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).map e₀
  let : IsIso (affineIso B₀).hom.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of k))).mapIso (affineIso B₀)).hom)
  let : IsOpenImmersion vR.left := by
    change IsOpenImmersion ((affineIso B₀).hom.left ≫ v₀.left)
    infer_instance
  have hbase : vR ≫ toBase X ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W) =
      (affineIso B₀).hom ≫ toBase X V₀ := by
    change ((affineIso B₀).hom ≫ (toSmoothSite X).map v₀) ≫ _ = _
    rw [Category.assoc]
    congr 1
    exact MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w v₀)
  have hp : p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
      SmoothSite.a1Map (.of k)
        (vR ≫ toBase X ((baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W)) =
      eR ≫ toBase (SmoothSite.a1Cylinder (.of k) X) W := by
    have hpc : p ≫ (affineLineIso B₀).hom = qS := by
      simp only [p, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      _ = (p ≫ (affineLineIso B₀).hom) ≫ SmoothSite.a1Map (.of k) (toBase X V₀) := by
        simp only [hbase, SmoothSite.a1Map_comp, affineLineIso, Iso.trans_hom,
          cylinderIso, Category.assoc]
      _ = qS ≫ SmoothSite.a1Map (.of k) (toBase X V₀) := by rw [hpc]
      _ = _ := by
        apply MorphismProperty.Over.Hom.ext
        change (q₀.left ≫ 𝟙 _) ≫ ((cylinderNeighborhood X).obj V₀).hom = e₀.left ≫ W.hom
        rw [Category.comp_id, MorphismProperty.Over.w q₀, MorphismProperty.Over.w e₀]
  have haOriginal : a₀ ≫ e₀.left = v₀.left ≫
      pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left := by
    have hm : ((baseChange (SmoothSite.a1Section (.of k) X 0).left).map e₀).left ≫
        pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left =
      pullback.fst E₀.hom (SmoothSite.a1Section (.of k) X 0).left ≫ e₀.left :=
      pullback.lift_fst _ _ _
    calc
      _ = z₀.left ≫ pullback.fst E₀.hom
          (SmoothSite.a1Section (.of k) X 0).left ≫ e₀.left := by
        rw [← haz, Category.assoc]
      _ = z₀.left ≫ ((baseChange (SmoothSite.a1Section (.of k) X 0).left).map e₀).left ≫
          pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left := by rw [hm]
      _ = _ := congrArg (fun f => f.left ≫
        pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left) hze
  have hmark : sR ≫ eR.left = vR.left ≫
      pullback.fst W.hom (SmoothSite.a1Section (.of k) X 0).left := by
    change ((affineIso B₀).hom.left ≫ a₀) ≫ e₀.left =
      ((affineIso B₀).hom.left ≫ v₀.left) ≫ _
    rw [Category.assoc, haOriginal, Category.assoc]
  have hwR : vR.left wR = w := by
    change v₀.left (V₀.left.isoSpec.inv (V₀.left.isoSpec.hom t₀)) = w
    have ht := congrArg (fun f : V₀.left ⟶ V₀.left => f t₀) V₀.left.isoSpec.hom_inv_id
    change V₀.left.isoSpec.inv (V₀.left.isoSpec.hom t₀) = t₀ at ht
    rw [ht, ht₀]
  obtain ⟨V, v, hv, hw', hi⟩ := exists_polynomial_boundary_image_neighborhood
    X P hP W R p (PolynomialOpenQuotient.inclusion (Polynomial.X : Polynomial R))
    (PolynomialOpenQuotient.source (Polynomial.X : Polynomial R) ≫ sR)
    wR presentation sR hsR vR eR hp hmark d
  exact ⟨V, v, hv, hwR ▸ hw', hi⟩

end Motivic.FiniteEtaleSite.OriginalPresheaf
