/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteNormal
public import Motivic.AlgebraicGeometry.SmoothSiteBaseChange

/-!
# Consumers of actual smooth normal stalks and integral components

The field and smooth-site objects are arbitrary. In particular the signatures
impose no global integrality, nonemptiness, connectedness, or perfectness.
The component consumers use the actual open subschemes and their section
rings, and the final consumer permits arbitrary changes of ground field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.SmoothSiteNormal

variable (k L : Type u) [Field k] [Field L]

/-- Arbitrary smooth schemes have genuine normal-domain stalks. -/
theorem smooth_stalk_normal {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  normalDomain_stalk_of_smooth_field k f x

/-- Normality of the actual stalks is available on arbitrary smooth objects. -/
theorem object_stalk_normal (X : SmoothSite (Spec (.of k))) (x : X.left) :
    IsDomain (X.left.presheaf.stalk x) ∧ IsIntegrallyClosed (X.left.presheaf.stalk x) :=
  ⟨inferInstance, inferInstance⟩

/-- The genuine irreducible components of an arbitrary smooth object are disjoint. -/
theorem components_disjoint (X : SmoothSite (Spec (.of k))) :
    (irreducibleComponents X.left).PairwiseDisjoint id :=
  SmoothSite.pairwiseDisjoint_irreducibleComponents k X

/-- A component is closed and open without global connectedness. -/
theorem component_clopen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) : IsClopen Z :=
  SmoothSite.isClopen_irreducibleComponent k X hZ

/-- The component's actual open subscheme is integral. -/
theorem component_integral (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    IsIntegral (SmoothSite.componentOpen k X Z hZ).toScheme := inferInstance

/-- Its actual nonempty affine-open section rings are normal domains. -/
theorem component_affine_normal (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left)
    {U : (SmoothSite.componentOpen k X Z hZ).toScheme.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    IsDomain Γ((SmoothSite.componentOpen k X Z hZ).toScheme, U) ∧
      IsIntegrallyClosed Γ((SmoothSite.componentOpen k X Z hZ).toScheme, U) :=
  SmoothSite.normalDomain_sections_componentOpen k X Z hZ hU

/-- The actual open component cover is finite. -/
theorem component_cover_finite (X : SmoothSite (Spec (.of k))) :
    Finite (SmoothSite.componentOpenCover k X).I₀ := inferInstance

/-- Every cover member is integral and has normal nonempty affine sections. -/
theorem component_cover_normal (X : SmoothSite (Spec (.of k)))
    (Z : (SmoothSite.componentOpenCover k X).I₀)
    {U : ((SmoothSite.componentOpenCover k X).X Z).Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegral ((SmoothSite.componentOpenCover k X).X Z) ∧
      IsDomain Γ((SmoothSite.componentOpenCover k X).X Z, U) ∧
        IsIntegrallyClosed Γ((SmoothSite.componentOpenCover k X).X Z, U) :=
  ⟨inferInstance, SmoothSite.normalDomain_sections_componentOpenCover k X Z hU⟩

/-- Arbitrary changes of ground field retain actual normal-domain local rings. -/
theorem field_baseChange_stalk_normal (f : k →+* L) (X : SmoothSite (Spec (.of k)))
    (x : ((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom f))).obj X).left) :
    IsDomain
      (((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom f))).obj X).left.presheaf.stalk x) ∧
      IsIntegrallyClosed
        (((SmoothSite.baseChange (Spec.map (CommRingCat.ofHom f))).obj X).left.presheaf.stalk x) :=
  ⟨inferInstance, inferInstance⟩

end MotivicTest.SmoothSiteNormal
