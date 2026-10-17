/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.RelativeCurveBaseOnlyLifting
public import Motivic.Aglib.AlgebraicGeometry.Normalization.RelativeFullBoundaryBaseFrames
public import Motivic.Aglib.AlgebraicGeometry.Normalization.EtaleDisjointBoundary
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantEtaleCurve
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleBoundaryIdeal

/-! # Whole affine-line correction from the actual normalized compactification -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
local instance (R : Type u) [CommRing R] : SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  AffineLineEtaleCompactification.polynomialProjection_smooth_one R
variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  {Y A T : Scheme.{u}} [IsAffine Y] [IsAffine A] [IsAffine T]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a]
  (B : Type u) [CommRing B] (z : Polynomial R →+* B)
  (s : Spec (.of B) ⟶ Y) [IsClosedImmersion s]
  (hs : s ≫ p = boundaryCoordinateMap R B z)
  (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z))
  [IsFinite (boundaryCoordinateMap R B z ≫ boundaryLineProjection R)]
  (ha : Disjoint (Set.range a) (Set.range (boundaryCoordinateMap R B z)))
  (v : T ⟶ compactification R p) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ projection R p)]
  (hc : ∀ c : compactification R p, c ∈ Set.range v ∨
    c ∈ Set.range (infinityInclusion R p) ∨ c ∈ Set.range (s ≫ inclusion R p))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ inclusion R p)

include hs H ha hc hφ in
/-- All compactification, finite generic boundary, global diagonal, and twist-frame
producers are consumed. The source parameter open is literally top: only the base shrinks. -/
theorem exists_wholeAffineLine_base_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      genericPoint (Spec (.of R)) ∈ V ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V),
        let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (boundaryBasePencilGraph k R (ULift.{u} (Fin 2)) t (boundaryLineProjection R)
            p a (toProjectiveLine R p) (inclusion R p) (inclusion_projection R p)
            ⊤ V v φ hφ)
          (boundaryBasePencilBeta k R (ULift.{u} (Fin 2)) t (boundaryLineProjection R)
            p a (toProjectiveLine R p) (inclusion R p) (inclusion_projection R p) ⊤ V)
          (boundaryBasePencilAlpha k R (ULift.{u} (Fin 2)) t (boundaryLineProjection R)
            p a (toProjectiveLine R p) (inclusion R p) (inclusion_projection R p) ⊤ V) := by
  let q := boundaryLineProjection R
  let j := inclusion R p
  let d := infinityInclusion R p
  have he : (s ≫ j) ≫ projection R p = boundaryCoordinateMap R B z ≫ q := by
    rw [Category.assoc, inclusion_projection, ← Category.assoc, hs]
  let : IsFinite ((s ≫ j) ≫ projection R p) := by rw [he]; infer_instance
  let : IsFinite (s ≫ j) := IsFinite.of_comp (s ≫ j) (projection R p)
  let : IsClosedImmersion (s ≫ j) :=
    IsClosedImmersion.of_isPreimmersion _ (s ≫ j).isClosedMap.isClosed_range
  let b := coprod.desc d (s ≫ j) ≫ projection R p
  have : IsProper b := inferInstanceAs
    (IsProper (coprod.desc (infinityInclusion R p) (s ≫ j) ≫ projection R p))
  have hfinite : (b ⁻¹' {genericPoint (Spec (.of R))}).Finite := by
    rw [show b = coprod.desc (d ≫ projection R p) ((s ≫ j) ≫ projection R p) from
      coprod.desc_comp _ _ _]
    apply finite_coprod_fiber
    · exact finite_generic_base_fiber_of_finite_projectiveLine R
        (infinityInclusion R p ≫ toProjectiveLine R p)
        (EtaleCompactification.infinity_avoids_generic _ (projectiveMap R p))
    · exact ((s ≫ j) ≫ projection R p).finite_preimage (Set.finite_singleton _)
  have hd : Disjoint (Set.range j) (Set.range d) := by
    rw [EtaleCompactification.range_infinityInclusion]
    exact disjoint_compl_right
  exact RelativeCurvePencil.exists_baseOnly_relativeCurve_lifting k R (ULift.{u} (Fin 2))
    1 Equiv.ulift t q p a (toProjectiveLine R p) j (inclusion_projection R p)
    (boundaryCoordinateMap R B z) s hs H ha d hd v hc φ hφ
    (genericPoint (Spec (.of R))) (boundaryCoordinateIdealIso R B z) hfinite P hP

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
