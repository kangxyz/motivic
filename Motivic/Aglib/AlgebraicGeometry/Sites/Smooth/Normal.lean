/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.Aglib.AlgebraicGeometry.Scheme.SmoothNormal
public import Motivic.Aglib.AlgebraicGeometry.Scheme.DomainStalkComponents

/-!
# Normal local rings and integral open components of smooth-site objects

For an arbitrary field, the actual local rings of every smooth-site object
are normal domains. Its irreducible components are pairwise disjoint and
clopen. Each component has its genuine integral open-subscheme structure,
whose nonempty affine section rings are normal domains. These are conclusions
from the smooth structure morphism, not extra conditions on smooth objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- Every actual smooth-site stalk is a domain. -/
instance isDomain_stalk (X : SmoothSite (Spec (.of k))) (x : X.left) :
    IsDomain (X.left.presheaf.stalk x) :=
  (normalDomain_stalk_of_smooth_field k X.hom x).1

/-- Every actual smooth-site stalk is integrally closed. -/
instance isIntegrallyClosed_stalk (X : SmoothSite (Spec (.of k))) (x : X.left) :
    IsIntegrallyClosed (X.left.presheaf.stalk x) :=
  (normalDomain_stalk_of_smooth_field k X.hom x).2

/-- The irreducible components of a smooth-site object are pairwise disjoint. -/
theorem pairwiseDisjoint_irreducibleComponents (X : SmoothSite (Spec (.of k))) :
    (irreducibleComponents X.left).PairwiseDisjoint id :=
  pairwiseDisjoint_irreducibleComponents_of_domain_stalks (fun _ ↦ inferInstance)

/-- Every irreducible component of a smooth-site object is clopen. -/
theorem isClopen_irreducibleComponent (X : SmoothSite (Spec (.of k)))
    {Z : Set X.left} (hZ : Z ∈ irreducibleComponents X.left) : IsClopen Z :=
  isClopen_irreducibleComponent_of_domain_stalks (fun _ ↦ inferInstance) hZ

/-- The actual open subscheme associated to an irreducible component. -/
def componentOpen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) : X.left.Opens :=
  domainStalkComponentOpen (fun _ ↦ inferInstance) Z hZ

/-- The open has precisely the given irreducible component as its underlying set. -/
@[simp] theorem coe_componentOpen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    (componentOpen k X Z hZ : Set X.left) = Z := rfl

/-- Every open irreducible component is an integral scheme. -/
instance isIntegral_componentOpen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    IsIntegral (componentOpen k X Z hZ).toScheme :=
  isIntegral_domainStalkComponentOpen (fun _ ↦ inferInstance) Z hZ

/-- Every nonempty affine open in an actual component has a normal-domain
section ring. No global integrality or perfect-field hypothesis is used. -/
theorem normalDomain_sections_componentOpen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left)
    {U : (componentOpen k X Z hZ).toScheme.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    IsDomain Γ((componentOpen k X Z hZ).toScheme, U) ∧
      IsIntegrallyClosed Γ((componentOpen k X Z hZ).toScheme, U) :=
  normalDomain_sections_open_of_smooth_field k X.hom (componentOpen k X Z hZ) hU

/-- The genuine irreducible components form an open cover of the smooth object. -/
def componentOpenCover (X : SmoothSite (Spec (.of k))) : X.left.OpenCover :=
  domainStalkComponentOpenCover X.left (fun _ ↦ inferInstance)

/-- This cover has finitely many members, including none for an empty object. -/
instance finite_componentOpenCover_index (X : SmoothSite (Spec (.of k))) :
    Finite (componentOpenCover k X).I₀ :=
  inferInstanceAs <| Finite (domainStalkComponentOpenCover X.left
    (fun _ ↦ inferInstance)).I₀

/-- Every member of the actual finite component cover is integral. -/
instance isIntegral_componentOpenCover_obj (X : SmoothSite (Spec (.of k)))
    (Z : (componentOpenCover k X).I₀) : IsIntegral ((componentOpenCover k X).X Z) :=
  isIntegral_domainStalkComponentOpenCover_obj X.left (fun _ ↦ inferInstance) Z

/-- All nonempty affine section rings in the component cover are normal domains. -/
theorem normalDomain_sections_componentOpenCover (X : SmoothSite (Spec (.of k)))
    (Z : (componentOpenCover k X).I₀)
    {U : ((componentOpenCover k X).X Z).Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsDomain Γ((componentOpenCover k X).X Z, U) ∧
      IsIntegrallyClosed Γ((componentOpenCover k X).X Z, U) :=
  @normalDomain_sections_componentOpen k _ X Z.1 Z.2 U hU ‹Nonempty U›

end AlgebraicGeometry.Scheme.SmoothSite
