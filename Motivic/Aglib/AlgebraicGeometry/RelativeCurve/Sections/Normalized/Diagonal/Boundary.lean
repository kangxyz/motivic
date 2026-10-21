/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FullBoundaryProduct

/-! The original diagonal bundle and its prescribed boundary on the constructed compactification. -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y S : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (r : S ⟶ Y) [IsOpenImmersion r]

/-- The original graph ideal, proved invertible on its actual smooth neighborhood. -/
def actualIdealLineBundle : Invertible.LineBundle
    (pullback ((r ≫ inclusion k p) ≫ projection k p) (projection k p)) :=
  ⟨Hom.idealModule (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p)),
    actualGraph_idealModule_isLocallyRankOne k p r⟩

/-- The genuine divisor line bundle of the original graph. -/
def actualDivisorLineBundle := Invertible.dualLineBundle _ (actualIdealLineBundle k p r)

omit [IsOpenImmersion r] in
/-- Every original-source refinement remains disjoint from the constructed full infinity. -/
theorem refined_disjoint_infinity :
    Disjoint (Set.range (r ≫ inclusion k p)) (Set.range (infinityInclusion k p)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ hx
  have hI : Set.range (infinityInclusion k p) = (Set.range (inclusion k p))ᶜ :=
    EtaleCompactification.range_infinityInclusion _ (projectiveMap k p)
  rw [hI] at hx
  exact hx ⟨r y, rfl⟩

/-- The actual compactification and smooth neighborhood produce the full prescribed boundary
isomorphism with both literal component restrictions. No compactification or boundary-unit datum
is assumed. -/
theorem exists_actualFullBoundaryDivisorIso
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    (s : Spec (.of B) ⟶ S)
    (hs : s ≫ (r ≫ p) = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z)) :
    let L := (actualDivisorLineBundle k p r).val
    let a := Hom.infinityProductMap (projection k p) (r ≫ inclusion k p) (infinityInclusion k p)
    let b := Hom.graphBoundaryRestriction (projection k p) (r ≫ inclusion k p) s
    ∃ E : (Modules.pullback (coprod.desc a b)).obj L ≅
        SheafOfModules.unit ((pullback (pullback.snd ((r ≫ inclusion k p) ≫ projection k p)
          (projection k p)) (infinityInclusion k p) ⨿
          pullback ((r ≫ inclusion k p) ≫ projection k p)
            (s ≫ (r ≫ inclusion k p) ≫ projection k p))).ringCatSheaf,
      (Modules.restrictFunctor coprod.inl).map E.hom ≫ (restrictUnitIso _).hom =
        (coprodPullbackRestrictLeft a b).hom.app L ≫
          (Hom.infinityBoundaryDivisorIso (projection k p) (r ≫ inclusion k p)
            (infinityInclusion k p) (refined_disjoint_infinity k p r)
            (actualIdealLineBundle k p r).property).hom ∧
      (Modules.restrictFunctor coprod.inr).map E.hom ≫ (restrictUnitIso _).hom =
        (coprodPullbackRestrictRight a b).hom.app L ≫
          (Hom.compactificationBoundaryDivisorIso k B z (projection k p) (r ≫ inclusion k p)
            (r ≫ p) (by simp only [Category.assoc, inclusion_projection])
            s hs H (actualIdealLineBundle k p r).property).hom := by
  let q' := (r ≫ inclusion k p) ≫ projection k p
  let U := (constantInclusion k p q').opensRange
  have : SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst q' (projection k p)) :=
    constantInclusion_opensRange_smooth k p q'
  exact Hom.exists_fullBoundaryDivisorIso k B z (projection k p) (r ≫ inclusion k p)
    (r ≫ p) (by simp only [Category.assoc, inclusion_projection]) s hs H
    (infinityInclusion k p) (refined_disjoint_infinity k p r) U
    (graph_mem_constantInclusion k p r)
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
