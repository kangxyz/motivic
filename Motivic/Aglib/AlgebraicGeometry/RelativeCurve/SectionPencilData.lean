module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SectionPencilDataCore
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.FactorBoundaryGeometry
/-! # Boundary-prescribed sections construct all correcting-correspondence data -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] {S X Y A B Z C D V : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- No divisor regularity, finite-flat zero, or polynomial-family property is supplied. -/
def dataOfBoundarySections
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a ≫ q) π))
    (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (nS dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    (hA :
      let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
      pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
      tensorUnitSection (pullbackSectionMap zA bS)
        (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)
    (hN : pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS =
      (fixedProductBoundaryFrame q π a z e ha d).hom ≫
        pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) aS)]
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) bS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)]
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j) :
    DiagonalSignedPencilProducer.Data
      (relativeAlpha k t π j α) (relativeBeta k t q π j a α p hq β h)
      (relativeGraphMap k t π j α v φ hφ) := by
  let iA := retainedProductInclusion (j ≫ π) π v
  let iN := retainedProductInclusion (a ≫ q) π v
  let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
  let zN := psiBoundaryInclusion q π j p hq a z s hs d
  have : IsAffine (retainedProduct (j ≫ π) π v) := retainedProduct_affine (j ≫ π) π v
  have : IsAffine (retainedProduct (a ≫ q) π v) := retainedProduct_affine (a ≫ q) π v
  have : SmoothOfRelativeDimension 1 (iA ≫ pullback.fst (j ≫ π) π) :=
    retainedProduct_smooth (j ≫ π) π v
  have : SmoothOfRelativeDimension 1 (iN ≫ pullback.fst (a ≫ q) π) :=
    retainedProduct_smooth (a ≫ q) π v
  have hcA := lambdaBoundary_retained_cover π j s d v hc
  have hcN := psiBoundary_retained_cover q π j p hq a z s hs d v hc
  have hFa := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zA
    (pullback.fst (j ≫ π) π) iA hcA
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) aS
  have hFb := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zA
    (pullback.fst (j ≫ π) π) iA hcA T bS
  have hFn := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zN
    (pullback.fst (a ≫ q) π) iN hcN N nS
  have hFd := CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit zN
    (pullback.fst (a ≫ q) π) iN hcN N dS
  have hf := relativePencil_finite_flat k (commonProjection π j α ≫ t)
    q π j p hq a α β h z s hs H e ha d hd v hc T N aS bS nS dS hA hN
  have hfamily := retainedGraphFamily_finite_flat k (commonProjection π j α ≫ t)
    q π j p hq a α β h v φ hφ T N aS bS nS dS hf
  have hp := commonPole_finite_mono_flat q π j p hq a α β h z s hs d v hc T N bS dS
  have hpole := retainedPole_finite_flat q π j p hq a α β h v T N bS dS hp
  exact relativeSectionPencilDataOfSections k t q π j p hq a α β h v φ hφ
    T N aS bS nS dS hFa hFb hFn hFd hfamily hpole
end AlgebraicGeometry.Scheme.RelativeCurvePencil
