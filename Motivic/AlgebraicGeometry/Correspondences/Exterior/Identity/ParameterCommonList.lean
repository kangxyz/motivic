/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.RemainingIncidence

/-!
# One actual regular parameter list in ambient and coefficient stalks

The same smooth parameter-diagonal list is mapped through the ambient square
and its Cartesian coefficient pullback. The two pointed scalar routes agree.
Only this leading parameter block is regular on coefficients; no regularity
is asserted for the remaining middle equations after imposing supports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The actual ambient stalk at a point of the coefficient parameter quotient. -/
abbrev exteriorParameterAmbientStalk (z : A.exteriorParameterDiagonal T B) :=
  Intersection.ambientStalk (exteriorAmbientParameterInclusion X Y Z T)
    (A.exteriorCoefficientQuotientInclusion B T z)

/-- Its actual coefficient action includes the point equality of the Cartesian square. -/
abbrev exteriorParameterCoefficientStalkMap (z : A.exteriorParameterDiagonal T B) :=
  Intersection.coefficientStalkMap (exteriorAmbientParameterInclusion X Y Z T)
    (A.exteriorCoefficientQuotientInclusion B T z)
    ((A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T))
    (A.exteriorParameterDiagonalInclusion T B z)
    (Intersection.point_eq _ _ _ _ (A.exteriorCoefficientQuotientInclusion_isPullback B T) z)

/-- Pasting the actual squares gives the identical pointed action of the parameter stalk. -/
theorem exteriorParameterStalkMap_comp (z : A.exteriorParameterDiagonal T B) :
    Diagonal.baseChangeStalkMap (exteriorAmbientParameter_isPullback X Y Z T)
        (A.exteriorCoefficientQuotientInclusion B T z) ≫
      A.exteriorParameterCoefficientStalkMap B T z =
    Diagonal.baseChangeStalkMap
      ((A.exteriorCoefficientQuotientInclusion_isPullback B T).paste_horiz
        (exteriorAmbientParameter_isPullback X Y Z T)) z := by
  change StalkTransport.pointedMap (exteriorAmbientParameterPair X Y Z T) _ _
      (congrArg (fun m => m (A.exteriorCoefficientQuotientInclusion B T z))
        (exteriorAmbientParameter_isPullback X Y Z T).w) ≫
      StalkTransport.pointedMap
        ((A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T))
        _ _ (Intersection.point_eq _ _ _ _
          (A.exteriorCoefficientQuotientInclusion_isPullback B T) z) =
    StalkTransport.pointedMap
      ((A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T) ≫
        exteriorAmbientParameterPair X Y Z T) _ _
      (congrArg (fun m => m z)
        ((A.exteriorCoefficientQuotientInclusion_isPullback B T).paste_horiz
          (exteriorAmbientParameter_isPullback X Y Z T)).w)
  exact StalkTransport.pointedMap_comp _ _ _ _ _ _ _

/-- One literal parameter list generates both actual kernels and is regular
in the ambient and after the actual coefficient action. -/
theorem exteriorParameter_exists_common_regular_list (z : A.exteriorParameterDiagonal T B) :
    ∃ t : List (A.exteriorParameterAmbientStalk B T z),
      IsRegular (A.exteriorParameterAmbientStalk B T z) t ∧
      RingHom.ker ((exteriorAmbientParameterInclusion X Y Z T).stalkMap
        (A.exteriorCoefficientQuotientInclusion B T z)).hom = Ideal.ofList t ∧
      IsRegular (((A.exteriorIdentityGenerator T).supportProduct
        (B.exteriorIdentityGenerator T)).presheaf.stalk
          (A.exteriorParameterDiagonalInclusion T B z))
        (t.map (A.exteriorParameterCoefficientStalkMap B T z).hom) ∧
      RingHom.ker ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom =
        Ideal.ofList (t.map (A.exteriorParameterCoefficientStalkMap B T z).hom) := by
  let sq := (A.exteriorCoefficientQuotientInclusion_isPullback B T).paste_horiz
    (exteriorAmbientParameter_isPullback X Y Z T)
  have : Flat
      ((A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T) ≫
        exteriorAmbientParameterPair X Y Z T) := by
    rw [A.exteriorCoefficientParameterPair_ambient B T]
    infer_instance
  obtain ⟨t, ht, hker⟩ := Diagonal.exists_regular_kernel_of_smooth T.hom
    (pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T)
      (A.exteriorCoefficientQuotientInclusion B T z))
  obtain ⟨hambient, hkernel⟩ := Diagonal.mapped_equations_regular_kernel
    (exteriorAmbientParameter_isPullback X Y Z T)
    (A.exteriorCoefficientQuotientInclusion B T z) ht hker
  obtain ⟨hcoeff, hcoeffker⟩ := Diagonal.mapped_equations_regular_kernel sq z ht hker
  have hlists :
      (t.map (Diagonal.baseChangeStalkMap (exteriorAmbientParameter_isPullback X Y Z T)
        (A.exteriorCoefficientQuotientInclusion B T z)).hom).map
          (A.exteriorParameterCoefficientStalkMap B T z).hom =
      t.map (Diagonal.baseChangeStalkMap sq z).hom := by
    simp only [List.map_map]
    congr 1
    funext r
    exact ConcreteCategory.congr_hom (A.exteriorParameterStalkMap_comp B T z) r
  refine ⟨_, hambient, hkernel, ?_, ?_⟩
  · simpa only [hlists] using hcoeff
  · simpa only [hlists] using hcoeffker

end Motivic.FiniteCorrespondenceGenerator
