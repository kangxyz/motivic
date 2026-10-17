/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.AffineLineEtaleCompactification
public import Motivic.Aglib.AlgebraicGeometry.Normalization.EtaleQuasiAffine
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.GraphBoundaryRestriction
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Diagonal
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # The actual smooth quasi-affine open of the constant compactified curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

/-- The literal polynomial affine line is smooth of relative dimension one. -/
theorem polynomialProjection_smooth_one (k : Type u) [CommRing k] :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap k (Polynomial k))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{u + 1} k) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial k PUnit.{u + 1}
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1})

variable (k : Type u) [Field k] {Y S : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (q : S ⟶ Spec (.of k))

abbrev curveProjection := p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
abbrev constantCurve := pullback q (curveProjection k p)
abbrev constantCompactification := pullback q (projection k p)

/-- The original retained curve embeds into the actual proper constant compactification. -/
def constantInclusion : constantCurve k p q ⟶ constantCompactification k p q :=
  (IsPullback.of_hasPullback q (projection k p)).flip.lift
    (pullback.snd _ _ ≫ inclusion k p) (pullback.fst _ _)
    (by rw [Category.assoc, inclusion_projection, ← pullback.condition])

omit [IsSeparated p] in
@[reassoc (attr := simp)]
theorem constantInclusion_fst : constantInclusion k p q ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (IsPullback.of_hasPullback q (projection k p)).flip.lift_snd _ _ _

omit [IsSeparated p] in
@[reassoc (attr := simp)]
theorem constantInclusion_snd : constantInclusion k p q ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ inclusion k p :=
  (IsPullback.of_hasPullback q (projection k p)).flip.lift_fst _ _ _

omit [IsSeparated p] in
theorem constantInclusion_isPullback :
    IsPullback (pullback.snd _ _) (constantInclusion k p q) (inclusion k p)
      (pullback.snd q (projection k p)) := by
  have H : IsPullback (pullback.snd q (curveProjection k p)) (pullback.fst _ _)
      (inclusion k p ≫ projection k p) q := by
    rw [inclusion_projection]
    exact (IsPullback.of_hasPullback q (curveProjection k p)).flip
  exact H.of_bot' (IsPullback.of_hasPullback q (projection k p)).flip

instance : IsOpenImmersion (constantInclusion k p q) :=
  MorphismProperty.of_isPullback (constantInclusion_isPullback k p q) inferInstance

instance : IsProper (pullback.fst q (projection k p)) := inferInstance

omit [QuasiCompact p] [IsSeparated p] in
/-- Only the actual retained curve, not the compactification, is asserted smooth. -/
theorem constantCurve_smooth :
    SmoothOfRelativeDimension 1 (pullback.fst q (curveProjection k p)) := by
  have := polynomialProjection_smooth_one k
  have : SmoothOfRelativeDimension 1 (curveProjection k p) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (curveProjection k p))
  exact MorphismProperty.pullback_fst _ _ inferInstance

/-- The actual constant retained curve is quasi-affine over every affine source. -/
theorem constantCurve_quasiAffine [IsAffine S] : (constantCurve k p q).IsQuasiAffine := by
  let π := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  let H := (IsPullback.of_hasPullback q π).flip
  let v := H.lift (pullback.snd q (curveProjection k p) ≫ p) (pullback.fst _ _)
    (by rw [Category.assoc, ← pullback.condition])
  have Hv : IsPullback (pullback.snd q (curveProjection k p)) v p (pullback.snd q π) :=
    (IsPullback.of_hasPullback q (p ≫ π)).flip.of_bot' H
  have : Etale v := MorphismProperty.of_isPullback Hv inferInstance
  have : QuasiCompact v := MorphismProperty.of_isPullback Hv inferInstance
  have : IsSeparated v := MorphismProperty.of_isPullback Hv inferInstance
  have : IsAffine (pullback q π) := isAffine_of_isAffineHom (pullback.fst q π)
  exact isQuasiAffine_of_etale_affine_target v

omit q [IsSeparated p] in
/-- The original graph lies in the actual smooth open, via the original map to Y. -/
theorem graph_mem_constantInclusion (r : S ⟶ Y) :
    Set.range (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p)) ⊆
      Set.range (constantInclusion k p ((r ≫ inclusion k p) ≫ projection k p)) := by
  let q' := (r ≫ inclusion k p) ≫ projection k p
  let l : S ⟶ constantCurve k p q' := pullback.lift (𝟙 S) r
    (by
      change 𝟙 S ≫ ((r ≫ inclusion k p) ≫ projection k p) = r ≫ curveProjection k p
      rw [Category.id_comp, Category.assoc, inclusion_projection])
  have hl : l ≫ constantInclusion k p q' =
      Hom.compactificationGraph (projection k p) (r ≫ inclusion k p) := by
    apply pullback.hom_ext <;> simp only [l, q', Hom.compactificationGraph, Category.assoc,
      constantInclusion_fst, constantInclusion_snd, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc]
  rintro x ⟨s, rfl⟩
  exact ⟨l s, congrArg (fun h => h s) hl⟩

/-- The chosen actual open subobject is smooth over the original affine source. -/
theorem constantInclusion_opensRange_smooth :
    SmoothOfRelativeDimension 1
      ((constantInclusion k p q).opensRange.ι ≫ pullback.fst q (projection k p)) := by
  rw [← (constantInclusion k p q).isoOpensRange_inv_comp, Category.assoc,
    constantInclusion_fst]
  have := constantCurve_smooth k p q
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

omit q in
/-- The original graph ideal is a line bundle, with its smooth neighborhood constructed. -/
theorem actualGraph_idealModule_isLocallyRankOne (r : S ⟶ Y) :
    Modules.Invertible.IsLocallyRankOne
      (pullback ((r ≫ inclusion k p) ≫ projection k p) (projection k p))
      (Hom.idealModule (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) := by
  let q' := (r ≫ inclusion k p) ≫ projection k p
  let U := (constantInclusion k p q').opensRange
  have : SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst q' (projection k p)) :=
    constantInclusion_opensRange_smooth k p q'
  exact Hom.graph_idealModule_isLocallyRankOne (r ≫ inclusion k p) (projection k p) U
    (graph_mem_constantInclusion k p r)
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
