/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RelativeCartierEndpoints
public import Motivic.Aglib.AlgebraicGeometry.FiniteTwoUnitPolynomialFamily

/-!
# Whole-fibre endpoint tests

The polynomial test retains two double sections. Its quotient has a nonzero
square-zero element and a nontrivial idempotent, so nonreduced and disconnected
sources genuinely occur. The endpoint equality uses the whole canonical fibre.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Polynomial
open AlgebraicGeometry.FiniteTwoUnitPolynomialFamily

universe u

namespace MotivicTest.FiniteFlatSpanEndpoints

variable {k : Type u} [Field k]

/-- The parameter and root have their actual common constant-field map. -/
theorem rootSpanBase (F : k[X][X]) :
    projection F ≫ (FiniteFlatCurveFamily.line k).hom =
      rootMap F ≫ (FiniteFlatCurveFamily.line k).hom := by
  change projection F ≫ Spec.map (CommRingCat.ofHom (C : k →+* k[X])) =
    rootMap F ≫ Spec.map (CommRingCat.ofHom (C : k →+* k[X]))
  rw [rootMap_structure, projection, ← Spec.map_comp]
  rfl

/-- Keeping both literal coordinates proves the joint embedding. -/
theorem rootSpanClosed (F : k[X][X]) (hF : F.Monic) :
    IsClosedImmersion (pullback.lift (projection F) (rootMap F) (rootSpanBase F)) :=
  closedImmersion_of_coordinates hF _ (pullback.fst _ _) (pullback.snd _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- Direct use of the actual span theorem for an arbitrary monic quotient. -/
theorem monicWholeEndpoint (F : k[X][X]) (hF : F.Monic) (a : k) :
    letI : IsFinite (projection F) := projection_finite hF
    letI : Flat (projection F) := projection_flat hF
    (Cor.graphFunctor k).map (FiniteFlatCurveFamily.evaluationPoint k a) ≫
        Cor.ofFiniteFlatSpan (X := FiniteFlatCurveFamily.line k)
          (Y := FiniteFlatCurveFamily.line k) (projection F) (rootMap F) (rootSpanBase F) =
      Cor.finiteFlatSpanEndpoint (Y := FiniteFlatCurveFamily.line k)
        (projection F) (rootMap F) (rootSpanBase F) a := by
  have : IsFinite (projection F) := projection_finite hF
  have : Flat (projection F) := projection_flat hF
  have : IsClosedImmersion (pullback.lift (projection F) (rootMap F) (rootSpanBase F)) :=
    rootSpanClosed F hF
  exact Cor.graph_evaluation_ofFiniteFlatSpan (Y := FiniteFlatCurveFamily.line k)
    (projection F) (rootMap F) (rootSpanBase F) a

/-- Two constant double sections, with their original quotient scheme. -/
def twoDoubleSections : ℚ[X][X] := (X * (X - C 1)) ^ 2

theorem twoDoubleSections_monic : twoDoubleSections.Monic :=
  (monic_X.mul (monic_X_sub_C (1 : ℚ[X]))).pow 2

/-- The family really contains a nonzero nilpotent. -/
theorem twoDoubleSections_squareZero :
    let n := AdjoinRoot.mk twoDoubleSections (X * (X - C 1))
    n ≠ 0 ∧ n ^ 2 = 0 := by
  refine ⟨AdjoinRoot.mk_ne_zero_of_natDegree_lt twoDoubleSections_monic
    (mul_ne_zero X_ne_zero (X_sub_C_ne_zero 1)) ?_, ?_⟩
  · simp only [twoDoubleSections, natDegree_pow,
      natDegree_mul (X_ne_zero (R := ℚ[X])) (X_sub_C_ne_zero (1 : ℚ[X])),
      natDegree_X, natDegree_X_sub_C]
    decide
  · rw [← map_pow]
    exact AdjoinRoot.mk_self

/-- A nontrivial idempotent separates the two double components. -/
theorem twoDoubleSections_idempotent :
    let e := AdjoinRoot.mk twoDoubleSections (3 * X ^ 2 - 2 * X ^ 3)
    IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · change _ * _ = _
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_sub, AdjoinRoot.mk_eq_zero]
    refine ⟨4 * X ^ 2 - 4 * X - 3, ?_⟩
    dsimp only [twoDoubleSections]
    simp only [map_one]
    ring
  · intro h
    have he := congrArg (AdjoinRoot.lift (RingHom.id ℚ[X]) 1
      (show eval₂ (RingHom.id ℚ[X]) 1 twoDoubleSections = 0 by
        norm_num only [twoDoubleSections, eval₂_pow, eval₂_mul, eval₂_sub,
          eval₂_X, eval₂_C, RingHom.id_apply])) h
    norm_num [AdjoinRoot.lift_mk] at he
  · intro h
    have he := congrArg (AdjoinRoot.lift (RingHom.id ℚ[X]) 0
      (show eval₂ (RingHom.id ℚ[X]) 0 twoDoubleSections = 0 by
        norm_num only [twoDoubleSections, eval₂_pow, eval₂_mul, eval₂_sub,
          eval₂_X, eval₂_C, RingHom.id_apply])) h
    norm_num [AdjoinRoot.lift_mk] at he

/-- The quotient algebra really is nonreduced. -/
theorem twoDoubleSections_not_reduced : ¬ IsReduced (AdjoinRoot twoDoubleSections) := by
  intro h
  have := h
  obtain ⟨hn, hn2⟩ := twoDoubleSections_squareZero
  exact hn (isNilpotent_iff_eq_zero.mp ⟨2, hn2⟩)

/-- The original family scheme really has disconnected underlying space. -/
theorem twoDoubleSections_not_preconnected :
    ¬ PreconnectedSpace (familyScheme twoDoubleSections) := by
  intro h
  have : PreconnectedSpace (PrimeSpectrum (AdjoinRoot twoDoubleSections)) := h
  let e := AdjoinRoot.mk twoDoubleSections (3 * X ^ 2 - 2 * X ^ 3)
  obtain ⟨he, h0, h1⟩ := twoDoubleSections_idempotent
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum _)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with hb | ht
  · apply h0
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.zero
    apply TopologicalSpace.Opens.ext
    simpa only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot] using hb
  · apply h1
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.one
    apply TopologicalSpace.Opens.ext
    simpa only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top] using ht

/-- The zero endpoint of this nonreduced, disconnected family. -/
theorem twoDoubleSections_zero :
    letI : IsFinite (projection twoDoubleSections) := projection_finite twoDoubleSections_monic
    letI : Flat (projection twoDoubleSections) := projection_flat twoDoubleSections_monic
    (Cor.graphFunctor ℚ).map (FiniteFlatCurveFamily.evaluationPoint ℚ 0) ≫
        Cor.ofFiniteFlatSpan (X := FiniteFlatCurveFamily.line ℚ)
          (Y := FiniteFlatCurveFamily.line ℚ) (projection twoDoubleSections)
          (rootMap twoDoubleSections) (rootSpanBase twoDoubleSections) =
      Cor.finiteFlatSpanEndpoint (Y := FiniteFlatCurveFamily.line ℚ)
        (projection twoDoubleSections) (rootMap twoDoubleSections)
        (rootSpanBase twoDoubleSections) 0 :=
  monicWholeEndpoint twoDoubleSections twoDoubleSections_monic 0

/-- The one endpoint of the same entire family. -/
theorem twoDoubleSections_one :
    letI : IsFinite (projection twoDoubleSections) := projection_finite twoDoubleSections_monic
    letI : Flat (projection twoDoubleSections) := projection_flat twoDoubleSections_monic
    (Cor.graphFunctor ℚ).map (FiniteFlatCurveFamily.evaluationPoint ℚ 1) ≫
        Cor.ofFiniteFlatSpan (X := FiniteFlatCurveFamily.line ℚ)
          (Y := FiniteFlatCurveFamily.line ℚ) (projection twoDoubleSections)
          (rootMap twoDoubleSections) (rootSpanBase twoDoubleSections) =
      Cor.finiteFlatSpanEndpoint (Y := FiniteFlatCurveFamily.line ℚ)
        (projection twoDoubleSections) (rootMap twoDoubleSections)
        (rootSpanBase twoDoubleSections) 1 :=
  monicWholeEndpoint twoDoubleSections twoDoubleSections_monic 1

section Cartier

open Scheme.Modules.Invertible Scheme.Hom

variable {Y : SmoothSite (Spec (.of k))} {C D U : Scheme.{u}}
  (p : C ⟶ Spec (.of k[X])) (i : D ⟶ C)
  [SmoothOfRelativeDimension 1 p] [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) [Flat (i ≫ p)] [IsProper (i ≫ p)]
  (j : U ⟶ C) [IsOpenImmersion j] (hAvoid : Set.range i ⊆ Set.range j)
  (g : U ⟶ Y.left) [IsClosedImmersion g]
  (hbase : j ≫ p ≫ (FiniteFlatCurveFamily.line k).hom = g ≫ Y.hom)

/-- A retained closed target supplies the embedding in the actual Cartier
endpoint theorem, with properness and divisor flatness still explicit. -/
theorem retainedTargetCartierEndpoint (a : k) :
    (Cor.graphFunctor k).map (FiniteFlatCurveFamily.evaluationPoint k a) ≫
        RelativeCartierDivisor.correspondence (X := FiniteFlatCurveFamily.line k)
          (Y := Y) p i hI j hAvoid g hbase =
      RelativeCartierDivisor.endpointCorrespondence p i hI j hAvoid g hbase a := by
  have : IsClosedImmersion (RelativeCartierDivisor.productMap
      (X := FiniteFlatCurveFamily.line k) (Y := Y) p i j hAvoid g hbase) :=
    RelativeCartierDivisor.productMap_closed_of_target_closed p i j hAvoid g hbase
  exact RelativeCartierDivisor.graph_evaluation_correspondence p i hI j hAvoid g hbase a

end Cartier

open Lean in
run_cmd do
  for name in #[``Cor.finiteFlatSpanFiber_base, ``Cor.finiteFlatSpanEndpoint,
      ``Cor.ofFiniteFlatSpan_eq_curveFundamental, ``Cor.graph_evaluation_ofFiniteFlatSpan,
      ``RelativeCartierDivisor.endpointCorrespondence,
      ``RelativeCartierDivisor.productMap_closed_of_target_closed,
      ``RelativeCartierDivisor.graph_evaluation_correspondence,
      ``RelativeCartierDivisor.graph_endpoints_correspondence,
      ``rootSpanBase, ``rootSpanClosed, ``monicWholeEndpoint,
      ``twoDoubleSections_squareZero, ``twoDoubleSections_idempotent,
      ``twoDoubleSections_not_reduced, ``twoDoubleSections_not_preconnected,
      ``twoDoubleSections_zero, ``twoDoubleSections_one, ``retainedTargetCartierEndpoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole-fibre endpoint compatibility uses only standard foundations."

end MotivicTest.FiniteFlatSpanEndpoints
