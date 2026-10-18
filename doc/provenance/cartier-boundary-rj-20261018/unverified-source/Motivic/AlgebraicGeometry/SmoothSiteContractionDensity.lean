/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionComplement
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks
public import Motivic.Aglib.AlgebraicGeometry.CartierComplementDense
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Density of literal contraction punctures and their etale charts

The regular polynomial coordinate gives the dense principal open on the model.
The actual Cartesian squares and openness then give density on a chosen chart.
This is geometry only; no coefficient restriction or purity statement is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.SmoothSite

private theorem denseRange_fst_of_cartesian {D A B C : Scheme.{u}}
    {d : D ⟶ A} {e : D ⟶ B} {a : A ⟶ C} {i : B ⟶ C}
    (h : IsPullback d e a i) (ha : IsOpenMap a) (hi : DenseRange i) :
    DenseRange d := by
  have hr : Set.range d = a ⁻¹' Set.range i := by
    rw [← h.isoPullback_hom_fst]
    change Set.range ((pullback.fst a i) ∘ h.isoPullback.hom) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
      Set.image_univ, Scheme.Pullback.range_fst]
  change Dense (Set.range d)
  rw [hr]
  exact hi.preimage ha

/-- The actual Laurent-cylinder open is dense, including for disconnected
smooth bases. Only regularity of the polynomial variable is used. -/
theorem contractionOpen_denseRange (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) :
    DenseRange (contractionOpen R X).left := by
  have hd : DenseRange (torusInAffineLine R).left := by
    change Dense (Set.range (Scheme.PolynomialLaurent.laurentPlus R))
    rw [← Scheme.Hom.coe_opensRange, Scheme.PolynomialLaurent.laurentPlus_opensRange]
    exact PrimeSpectrum.dense_basicOpen_of_isRegular Polynomial.X Polynomial.isRegular_X
  let : Smooth (productSnd X (affineLine R)).left :=
    inferInstanceAs (Smooth (pullback.snd X.hom (affineLine R).hom))
  exact denseRange_fst_of_cartesian (productMap_right_isPullback X (torusInAffineLine R))
    (productSnd X (affineLine R)).left.isOpenMap hd

/-- A displayed etale chart square retains the dense actual puncture. In
particular the coefficient restriction Mono can be proved from dense-open
detection, rather than being supplied as a further mathematical input. -/
theorem contractionChartOpen_denseRange (R : CommRingCat.{u})
    (X : SmoothSite (Spec R)) {U E : SmoothSite (Spec R)}
    (b : E ⟶ a1Cylinder R X) [Etale b.left]
    (j : U ⟶ E) (q : U ⟶ torusCylinder R X)
    (hpb : IsPullback q j (contractionOpen R X) b) : DenseRange j.left :=
  denseRange_fst_of_cartesian
    ((forgetScheme (Spec R)).map_isPullback hpb.flip)
    b.left.isOpenMap (contractionOpen_denseRange R X)

end Motivic.SmoothSite
