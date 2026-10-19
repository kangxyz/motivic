/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyComponentRegularity

/-!
# Original numerator and denominator affine-line maps

The canonical global-sections–Spec adjunction realizes each literal section on
the unchanged ambient scheme. Its coordinate is proved to be that section.
The resulting numerator and denominator satisfy the actual face conditions;
neither a replacement divisor nor a supplied coordinate identity is used.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyDivisorMaps`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyZeroCoefficient`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical affine-line morphism defined by an original global section. -/
def sectionToAffineLine {R : Type u} [CommRing R] {P : Scheme.{u}}
    (p : P ⟶ Spec (.of R)) (s : Γ(P, ⊤)) : P ⟶ Spec (.of R[X]) :=
  ΓSpec.adjunction.homEquiv P (op (.of R[X]))
    (CommRingCat.ofHom (Polynomial.eval₂RingHom
      (p.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom) s)).op

/-- The original coordinate, not merely an isomorphic zero scheme, is retained. -/
theorem sectionToAffineLine_coordinate {R : Type u} [CommRing R] {P : Scheme.{u}}
    (p : P ⟶ Spec (.of R)) (s : Γ(P, ⊤)) :
    (sectionToAffineLine p s).appTop ((ΓSpecIso (.of R[X])).inv Polynomial.X) = s := by
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
    (CommRingCat.ofHom (Polynomial.eval₂RingHom
      (p.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom) s))
  have he := congrArg (fun f => f Polynomial.X) h
  change (sectionToAffineLine p s).appTop
      ((ΓSpecIso (.of R[X])).inv Polynomial.X) =
    (Polynomial.eval₂RingHom
      (p.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom) s) Polynomial.X at he
  simpa using he

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.PrincipalFamilyEndpointCuts

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))

/-- The numerator map lives on the unchanged polynomial parameter space. -/
def numeratorMap (a b : Γ(W, ⊤)) : parameterSpace p ⟶ Spec (.of k[X]) :=
  Scheme.sectionToAffineLine (projection p ≫ p) (numerator p a b)

/-- The polar denominator map lives on the same unchanged parameter space. -/
def denominatorMap (b : Γ(W, ⊤)) : parameterSpace p ⟶ Spec (.of k[X]) :=
  Scheme.sectionToAffineLine (projection p ≫ p) (denominator p b)

private instance parameterSpace_noetherian [IsNoetherian W] :
    IsNoetherian (parameterSpace p) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection p)

/-- Both original nonreduced principal divisors satisfy the concrete endpoint
conditions, with their maps and coordinates constructed rather than supplied. -/
theorem original_divisor_maps_principalFaceConditions [IsIntegral W] [IsNoetherian W]
    (a b : Γ(W, ⊤)) (x : W) (hx : Order.coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)
    (c : k) (hc : c = 0 ∨ c = 1)
    (q : FiniteFlatCurve.fiber (parameterProjection p) c)
    (hq : FiniteFlatCurve.fiberInclusion (parameterProjection p) c q = endpoint p c x) :
    FiniteFlatCurve.PrincipalFaceConditions (numeratorMap p a b) (parameterProjection p) c q ∧
      FiniteFlatCurve.PrincipalFaceConditions (denominatorMap p b) (parameterProjection p) c q := by
  constructor
  · exact numerator_denominator_principalFaceConditions p a b x hx ha hb c hc
      (numeratorMap p a b) (Or.inl (Scheme.sectionToAffineLine_coordinate _ _)) q hq
  · exact numerator_denominator_principalFaceConditions p a b x hx ha hb c hc
      (denominatorMap p b) (Or.inr (Scheme.sectionToAffineLine_coordinate _ _)) q hq

end AlgebraicGeometry.PrincipalFamilyEndpointCuts
