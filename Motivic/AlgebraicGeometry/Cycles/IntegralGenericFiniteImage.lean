/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FundamentalSupport
public import Motivic.AlgebraicGeometry.Cycles.ResidueDegree
public import Motivic.AlgebraicGeometry.Intersection.CoefficientStalkTransport

/-!
# The actual finite morphism between integral point closures

Restrict an arbitrary finite morphism to the reduced integral closure of one
source point. Its actual scheme-theoretic image has the exact kernel ideal
sheaf of the reduced integral target point closure. The resulting image
isomorphism constructs a finite surjective morphism of these two integral
supports, with the original immersion and pointed stalk squares.

Only these two point closures are integral. The original schemes and their
whole scheme-theoretic image may be nonreduced or have multiple components.
No preservation of the whole target's generic points is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.IntegralClosedSubscheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)

/-- Equality of the actual image kernel ideal sheaf, not only of its support.
The faithful integral-support dictionary uses reducedness of the actual image. -/
theorem pointClosure_image_kernel :
    ((pointClosure x).val.subschemeι ≫ f).ker = (pointClosure (f x)).val := by
  change ((pointClosure x).finiteImage f).val = (pointClosure (f x)).val
  apply congrArg Subtype.val
  apply point_injective
  simp only [point_finiteImage, point_pointClosure]

/-- On every affine open, the image ideal is literally the kernel of the
original map of sections from the whole ambient target. -/
theorem pointClosure_image_ideal (U : Y.affineOpens) :
    (pointClosure (f x)).val.ideal U =
      RingHom.ker (((pointClosure x).val.subschemeι ≫ f).app U.1).hom := by
  rw [← pointClosure_image_kernel f x]
  exact Scheme.Hom.ker_apply _ U

/-- The actual scheme-theoretic image is the reduced integral point closure.
Both directions are the canonical ideal-sheaf inclusions of the proved equality. -/
def pointClosureImageIso :
    ((pointClosure x).val.subschemeι ≫ f).image ≅ (pointClosure (f x)).val.subscheme where
  hom := Scheme.IdealSheafData.inclusion (pointClosure_image_kernel f x).ge
  inv := Scheme.IdealSheafData.inclusion (pointClosure_image_kernel f x).le
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The image isomorphism respects the literal target closed immersion. -/
@[reassoc (attr := simp)] theorem pointClosureImageIso_ambient :
    (pointClosureImageIso f x).hom ≫ (pointClosure (f x)).val.subschemeι =
      ((pointClosure x).val.subschemeι ≫ f).imageι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The genuine finite image factor, transported by its actual ideal equality. -/
def pointClosureMap :
    (pointClosure x).val.subscheme ⟶ (pointClosure (f x)).val.subscheme :=
  ((pointClosure x).val.subschemeι ≫ f).toImage ≫ (pointClosureImageIso f x).hom

/-- The integral-support factorization preserves the original ambient morphism. -/
@[reassoc (attr := simp)] theorem pointClosureMap_ambient :
    pointClosureMap f x ≫ (pointClosure (f x)).val.subschemeι =
      (pointClosure x).val.subschemeι ≫ f := by
  simp only [pointClosureMap, Category.assoc, pointClosureImageIso_ambient,
    Scheme.Hom.toImage_imageι]

/-- Finiteness belongs to this actual support morphism, not an unrelated projection. -/
instance pointClosureMap_isFinite : IsFinite (pointClosureMap f x) := by
  let := isFinite_toImage ((pointClosure x).val.subschemeι ≫ f)
  unfold pointClosureMap
  infer_instance

/-- Every point of the integral target support occurs in this actual finite image. -/
theorem pointClosureMap_surjective : Function.Surjective (pointClosureMap f x) := by
  change Function.Surjective
    ((pointClosureImageIso f x).hom ∘ ((pointClosure x).val.subschemeι ≫ f).toImage)
  exact (Scheme.homeoOfIso (pointClosureImageIso f x)).surjective.comp
    (surjective_toImage ((pointClosure x).val.subschemeι ≫ f))

instance pointClosureMap_isDominant : IsDominant (pointClosureMap f x) :=
  ⟨(pointClosureMap_surjective f x).denseRange⟩

/-- Generic preservation is proved only between these two integral supports. -/
@[simp] theorem pointClosureMap_genericPoint :
    pointClosureMap f x (genericPoint (pointClosure x).val.subscheme) =
      genericPoint (pointClosure (f x)).val.subscheme := by
  apply (pointClosure (f x)).val.subschemeι.isEmbedding.injective
  change (pointClosureMap f x ≫ (pointClosure (f x)).val.subschemeι)
    (genericPoint (pointClosure x).val.subscheme) = _
  rw [pointClosureMap_ambient, Scheme.Hom.comp_apply]
  change f (pointClosure x).point = (pointClosure (f x)).point
  simp only [point_pointClosure]

/-- The generic support map retains the actual original ambient scalar map,
including all equal-point transports. -/
theorem pointClosureMap_genericStalkSquare :
    StalkTransport.pointedMap (pointClosure (f x)).val.subschemeι
        (genericPoint (pointClosure (f x)).val.subscheme) (f x)
        (point_pointClosure (f x)).symm ≫
      StalkTransport.pointedMap (pointClosureMap f x)
        (genericPoint (pointClosure x).val.subscheme)
        (genericPoint (pointClosure (f x)).val.subscheme)
        (pointClosureMap_genericPoint f x).symm =
    StalkTransport.pointedMap f x (f x) rfl ≫
      StalkTransport.pointedMap (pointClosure x).val.subschemeι
        (genericPoint (pointClosure x).val.subscheme) x (point_pointClosure x).symm := by
  rw [StalkTransport.pointedMap_comp, StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _ (pointClosureMap_ambient f x) _ _ _ _

/-- Actual residue degrees agree because the literal immersion square commutes
and both closed immersions induce isomorphisms on the corresponding residue fields. -/
theorem pointClosureMap_residueDegree :
    (pointClosureMap f x).residueDegree (genericPoint (pointClosure x).val.subscheme) =
      f.residueDegree x := by
  have he := congrArg
    (fun m => m.residueDegree (genericPoint (pointClosure x).val.subscheme))
    (pointClosureMap_ambient f x)
  simp only [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul, mul_one] at he
  change (pointClosureMap f x).residueDegree (genericPoint (pointClosure x).val.subscheme) =
    f.residueDegree (pointClosure x).point at he
  simpa only [point_pointClosure] using he

/-- Reducedness of the target support upgrades its proved dominance to the
actual zero-kernel ideal-sheaf condition. -/
theorem pointClosureMap_kernel_eq_bot : (pointClosureMap f x).ker = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff, ← SetLike.coe_injective.eq_iff,
    TopologicalSpace.Closeds.coe_top, ← Set.univ_subset_iff,
    ← (pointClosureMap f x).denseRange.closure_eq,
    (pointClosureMap f x).ker.support.isClosed.closure_subset_iff]
  exact (pointClosureMap f x).range_subset_ker_support

/-- The actual affine map of sections is injective; no carrier equivalence is used. -/
theorem pointClosureMap_app_injective
    {U : (pointClosure (f x)).val.subscheme.Opens} (hU : IsAffineOpen U) :
    Function.Injective ((pointClosureMap f x).app U) := by
  rw [RingHom.injective_iff_ker_eq_bot, ← (pointClosureMap f x).ker_apply ⟨U, hU⟩,
    pointClosureMap_kernel_eq_bot]
  simp

/-- A neighborhood of the target generic point gives domain coordinate rings
on that open and on its entire inverse image. -/
theorem pointClosureMap_coordinate_domains
    (U : (pointClosure (f x)).val.subscheme.Opens)
    (hU : genericPoint (pointClosure (f x)).val.subscheme ∈ U) :
    IsDomain Γ((pointClosure (f x)).val.subscheme, U) ∧
      IsDomain Γ((pointClosure x).val.subscheme, pointClosureMap f x ⁻¹ᵁ U) := by
  let : Nonempty U := ⟨⟨_, hU⟩⟩
  let : Nonempty (pointClosureMap f x ⁻¹ᵁ U) := ⟨⟨
    genericPoint (pointClosure x).val.subscheme, by
      change pointClosureMap f x (genericPoint (pointClosure x).val.subscheme) ∈ U
      rw [pointClosureMap_genericPoint]
      exact hU⟩⟩
  exact ⟨inferInstance, inferInstance⟩

/-- An affine generic neighborhood gives the literal finite coordinate map
used by the whole finite-domain generic-fiber construction. -/
theorem pointClosureMap_coordinate_finite
    {U : (pointClosure (f x)).val.subscheme.Opens} (hU : IsAffineOpen U) :
    ((pointClosureMap f x).app U).hom.Finite :=
  (pointClosureMap f x).finite_app U hU

end Motivic.IntegralClosedSubscheme
