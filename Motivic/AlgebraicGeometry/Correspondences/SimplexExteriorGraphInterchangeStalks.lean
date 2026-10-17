/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraphInterchangeGeometry

/-!
# Actual Tor transversality for mixed graph and exterior incidence

The open coefficient chart transports one common diagonal equation list to
the original support-product stalk. Flatness is used only for the outer
smooth ambient schemes. The actual incidence coefficient module therefore
has no positive Tor and its Euler cycle is its full fundamental cycle.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.SimplexExteriorGraph

variable {k : Type u} [Field k] {X Y T T' : SmoothSite (Spec (.of k))}
  (u : T ⟶ T') (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  [GeometricallyIntegral T'.hom]
  (A : FiniteCorrespondenceGenerator (SmoothSite.product X T).hom
    (SmoothSite.product X T').hom)
  (hA : A.projection ≫ (SmoothSite.productMap (𝟙 X) u).left = A.targetProjection)

include hA

/-- Each actual mixed incidence point maps into the full literal mixed incidence. -/
def incidenceMixedMap : A.incidence (V.exteriorIdentityGenerator T') ⟶
    ProductGraph.support X.hom T'.hom V.projection u.left :=
  (ProductGraph.mixed_isPullback X.hom T'.hom V.projection u.left).lift
    (A.incidenceInclusion (V.exteriorIdentityGenerator T') ≫
      correspondenceTripleMiddle (SmoothSite.product X T).hom
        (SmoothSite.product X T').hom (SmoothSite.product Y T').hom)
    (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') ≫ coefficientChart u V A)
    (by
      calc
        _ = A.incidenceInclusion (V.exteriorIdentityGenerator T') ≫
            (correspondenceTripleMiddle (SmoothSite.product X T).hom
              (SmoothSite.product X T').hom (SmoothSite.product Y T').hom ≫
                pullback.diagonal (SmoothSite.product X T').hom) := Category.assoc _ _ _
        _ = A.incidenceInclusion (V.exteriorIdentityGenerator T') ≫
            (correspondenceTripleInclusion (SmoothSite.product X T).hom
              (SmoothSite.product X T').hom (SmoothSite.product Y T').hom ≫
                correspondenceMiddlePair (SmoothSite.product X T).hom
                  (SmoothSite.product X T').hom (SmoothSite.product Y T').hom) :=
          congrArg (A.incidenceInclusion (V.exteriorIdentityGenerator T') ≫ ·)
            (correspondenceTriple_isPullback (SmoothSite.product X T).hom
              (SmoothSite.product X T').hom (SmoothSite.product Y T').hom).w
        _ = (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') ≫
            A.supportProductInclusion (V.exteriorIdentityGenerator T')) ≫
              correspondenceMiddlePair (SmoothSite.product X T).hom
                (SmoothSite.product X T').hom (SmoothSite.product Y T').hom := by
          rw [← Category.assoc, A.incidence_ambient_comm]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') ≫ ·)
              (coefficientChart_middlePair u V A hA).symm)

@[reassoc (attr := simp)]
theorem incidenceMixedMap_middle :
    incidenceMixedMap u V A hA ≫ ProductGraph.supportMap X.hom T'.hom V.projection u.left =
      A.incidenceInclusion (V.exteriorIdentityGenerator T') ≫
        correspondenceTripleMiddle (SmoothSite.product X T).hom
          (SmoothSite.product X T').hom (SmoothSite.product Y T').hom :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem incidenceMixedMap_coefficient :
    incidenceMixedMap u V A hA ≫ ProductGraph.mixedEmbedding X.hom T'.hom V.projection u.left =
      A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') ≫ coefficientChart u V A :=
  IsPullback.lift_snd _ _ _ _

/-- The original middle diagonal point is the image of the actual open-chart coefficient point. -/
theorem incidenceMixedPoint_eq (w : A.incidence (V.exteriorIdentityGenerator T')) :
    pullback.diagonal (SmoothSite.product X T').hom
        (correspondenceTripleMiddle (SmoothSite.product X T).hom
          (SmoothSite.product X T').hom (SmoothSite.product Y T').hom
            (A.incidenceInclusion (V.exteriorIdentityGenerator T') w)) =
      ProductGraph.mixedPair X.hom T'.hom V.projection u.left
        (coefficientChart u V A (A.incidenceToSupportProduct
          (V.exteriorIdentityGenerator T') w)) := by
  have hd := congrArg (fun q => q w) (incidenceMixedMap_middle u V A hA)
  have hz := congrArg (fun q => q w) (incidenceMixedMap_coefficient u V A hA)
  have hr := congrArg (fun q => q (incidenceMixedMap u V A hA w))
    (ProductGraph.mixedEmbedding_mixedPair X.hom T'.hom V.projection u.left)
  simp only [Scheme.Hom.comp_apply] at hd hz hr
  rw [hd, hz] at hr
  exact hr.symm

/-- The full mixed chart supplies one regular list at the exact original incidence points. -/
theorem exists_common_regular_list_at_incidence
    (w : A.incidence (V.exteriorIdentityGenerator T')) :
    ∃ rs : List ((pullback (SmoothSite.product X T').hom
        (SmoothSite.product X T').hom).presheaf.stalk
      (pullback.diagonal (SmoothSite.product X T').hom
        (correspondenceTripleMiddle (SmoothSite.product X T).hom
          (SmoothSite.product X T').hom (SmoothSite.product Y T').hom
            (A.incidenceInclusion (V.exteriorIdentityGenerator T') w)))),
      IsRegular ((pullback (SmoothSite.product X T').hom
        (SmoothSite.product X T').hom).presheaf.stalk
        (pullback.diagonal (SmoothSite.product X T').hom
          (correspondenceTripleMiddle (SmoothSite.product X T).hom
            (SmoothSite.product X T').hom (SmoothSite.product Y T').hom
              (A.incidenceInclusion (V.exteriorIdentityGenerator T') w)))) rs ∧
      RingHom.ker ((pullback.diagonal (SmoothSite.product X T').hom).stalkMap
        (correspondenceTripleMiddle (SmoothSite.product X T).hom
          (SmoothSite.product X T').hom (SmoothSite.product Y T').hom
            (A.incidenceInclusion (V.exteriorIdentityGenerator T') w))).hom = Ideal.ofList rs ∧
      IsRegular ((ProductGraph.coefficient X.hom T'.hom V.projection u.left).presheaf.stalk
        (coefficientChart u V A (A.incidenceToSupportProduct
          (V.exteriorIdentityGenerator T') w)))
        (rs.map (StalkTransport.pointedMap
          (ProductGraph.mixedPair X.hom T'.hom V.projection u.left)
          (coefficientChart u V A (A.incidenceToSupportProduct
            (V.exteriorIdentityGenerator T') w)) _
          (incidenceMixedPoint_eq u V A hA w)).hom) := by
  let v := incidenceMixedMap u V A hA w
  have hd := congrArg (fun q => q w) (incidenceMixedMap_middle u V A hA)
  have hz := congrArg (fun q => q w) (incidenceMixedMap_coefficient u V A hA)
  simp only [Scheme.Hom.comp_apply] at hd hz
  have : Smooth (ProductGraph.middleHom X.hom T'.hom) :=
    inferInstanceAs (Smooth (SmoothSite.product X T').hom)
  have hc := ProductGraph.exists_common_regular_list X.hom T'.hom V.projection u.left v
  have ht := Graph.common_regular_list_congr_points
    (pullback.diagonal (ProductGraph.middleHom X.hom T'.hom))
    (ProductGraph.mixedPair X.hom T'.hom V.projection u.left)
    (ProductGraph.supportMap X.hom T'.hom V.projection u.left v) _
    (ProductGraph.mixedEmbedding X.hom T'.hom V.projection u.left v) _
    (pullback.diagonal (ProductGraph.middleHom X.hom T'.hom)
      (ProductGraph.supportMap X.hom T'.hom V.projection u.left v)) _
    hd hz (congrArg (pullback.diagonal (ProductGraph.middleHom X.hom T'.hom)) hd)
    rfl (congrArg (fun q => q v)
      (ProductGraph.mixedEmbedding_mixedPair X.hom T'.hom V.projection u.left)).symm
    rfl (incidenceMixedPoint_eq u V A hA w)
    (by simpa only [Graph.alignedStalkMap_rfl, ProductGraph.mixedDiagonalStalkMap] using hc)
  simpa [Graph.alignedStalkMap, StalkTransport.pointedMap, ProductGraph.middleHom,
    ProductGraph.productHom, SmoothSite.product_hom, pullback.diagonalObj] using ht

/-- The two genuine scalar-map paths through the chart agree. -/
theorem incidenceMixedDiagonalStalkMap_comp
    (w : A.incidence (V.exteriorIdentityGenerator T')) :
    Diagonal.baseChangeStalkMap (correspondenceTriple_isPullback
        (SmoothSite.product X T).hom (SmoothSite.product X T').hom
        (SmoothSite.product Y T').hom)
        (A.incidenceInclusion (V.exteriorIdentityGenerator T') w) ≫
      Intersection.coefficientStalkMap
        (correspondenceTripleInclusion (SmoothSite.product X T).hom
          (SmoothSite.product X T').hom (SmoothSite.product Y T').hom)
        (A.incidenceInclusion (V.exteriorIdentityGenerator T') w)
        (A.supportProductInclusion (V.exteriorIdentityGenerator T'))
        (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') w)
        (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback
          (V.exteriorIdentityGenerator T')) w) =
    StalkTransport.pointedMap
        (ProductGraph.mixedPair X.hom T'.hom V.projection u.left)
        (coefficientChart u V A (A.incidenceToSupportProduct
          (V.exteriorIdentityGenerator T') w)) _
        (incidenceMixedPoint_eq u V A hA w) ≫
      (coefficientChart u V A).stalkMap
        (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') w) := by
  change StalkTransport.pointedMap
      (correspondenceMiddlePair (SmoothSite.product X T).hom
        (SmoothSite.product X T').hom (SmoothSite.product Y T').hom) _ _
      (congrArg (fun q => q (A.incidenceInclusion (V.exteriorIdentityGenerator T') w))
        (correspondenceTriple_isPullback (SmoothSite.product X T).hom
          (SmoothSite.product X T').hom (SmoothSite.product Y T').hom).w) ≫
    StalkTransport.pointedMap (A.supportProductInclusion (V.exteriorIdentityGenerator T')) _ _
      (Intersection.point_eq _ _ _ _ (A.incidence_ambient_isPullback
        (V.exteriorIdentityGenerator T')) w) = _
  have hchart : (coefficientChart u V A).stalkMap
      (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') w) =
    StalkTransport.pointedMap (coefficientChart u V A)
      (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') w)
      (coefficientChart u V A (A.incidenceToSupportProduct
        (V.exteriorIdentityGenerator T') w)) rfl := by
    simp [StalkTransport.pointedMap]
  rw [hchart, StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _ (coefficientChart_middlePair u V A hA).symm _ _ _ _

/-- The literal ambient kernel list is regular on the actual mixed coefficient module. -/
theorem exists_incidence_regular_list [IsOpenImmersion A.projection]
    (w : A.incidence (V.exteriorIdentityGenerator T')) :
    ∃ s : List (A.incidenceAmbientStalk (V.exteriorIdentityGenerator T') w),
      RingHom.ker ((correspondenceTripleInclusion (SmoothSite.product X T).hom
        (SmoothSite.product X T').hom (SmoothSite.product Y T').hom).stalkMap
        (A.incidenceInclusion (V.exteriorIdentityGenerator T') w)).hom = Ideal.ofList s ∧
      IsRegular (A.incidenceAmbientStalk (V.exteriorIdentityGenerator T') w) s ∧
      IsWeaklyRegular (A.incidenceSupportStalkModule (V.exteriorIdentityGenerator T') w) s := by
  obtain ⟨rs, hrs, hker, hcoefficient⟩ := exists_common_regular_list_at_incidence u V A hA w
  obtain ⟨hregular, hkernel⟩ := Diagonal.mapped_equations_regular_kernel
    (correspondenceTriple_isPullback (SmoothSite.product X T).hom
      (SmoothSite.product X T').hom (SmoothSite.product Y T').hom)
    (A.incidenceInclusion (V.exteriorIdentityGenerator T') w) hrs hker
  refine ⟨_, hkernel, hregular, ?_⟩
  apply (Intersection.coefficientStalkModule_isWeaklyRegular_iff _ _ _ _ _ _).mpr
  have ht := StalkTransport.isWeaklyRegular_map_pointedMap_of_isOpenImmersion
    (coefficientChart u V A)
    (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') w) _ rfl
    hcoefficient.toIsWeaklyRegular
  have he := incidenceMixedDiagonalStalkMap_comp u V A hA w
  have hchart : StalkTransport.pointedMap (coefficientChart u V A)
      (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') w) _ rfl =
      (coefficientChart u V A).stalkMap
        (A.incidenceToSupportProduct (V.exteriorIdentityGenerator T') w) := by
    simp [StalkTransport.pointedMap]
  rw [hchart] at ht
  simp only [List.map_map] at ht ⊢
  convert ht using 1
  apply List.map_congr_left
  intro r _
  exact ConcreteCategory.congr_hom he r

/-- The actual mixed graph/exterior Tor cycle equals the full incidence fundamental cycle. -/
theorem incidenceTorCorrespondence_eq_fundamental [IsOpenImmersion A.projection] :
    A.incidenceTorCorrespondence k (V.exteriorIdentityGenerator T') =
      A.incidenceFundamentalCorrespondence k (V.exteriorIdentityGenerator T') := by
  choose s hker hs hT using fun x : genericPoints
    (A.incidence (V.exteriorIdentityGenerator T')) =>
      exists_incidence_regular_list u V A hA x.val
  exact A.incidenceTorCorrespondence_eq_fundamental_of_weaklyRegular k
    (V.exteriorIdentityGenerator T') s hker hs hT

end Motivic.SimplexExteriorGraph
