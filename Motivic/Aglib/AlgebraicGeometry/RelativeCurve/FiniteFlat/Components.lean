/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Integral components of finite flat curves

Each reduced component of a finite flat scheme over the affine line still
maps flatly to that line. Flat generalization lifting makes the component
surjective. Its integral coordinate algebra is therefore torsion-free over
the polynomial ring, and finite torsion-free modules over that PID are free.
The whole finite flat scheme is never assumed reduced or irreducible.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite surjective integral scheme over the affine line is flat, by
torsion-freeness of its actual polynomial coordinate algebra. -/
theorem finiteCurve_flat_of_integral_surjective
    {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (g : C ⟶ Spec (.of k[X])) [IsFinite g] [Surjective g] : Flat g := by
  let : IsAffine C := isAffine_of_isAffineHom g
  let e : Γ(Spec (.of k[X]), ⊤) ≃+* k[X] :=
    (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv
  let φ : k[X] →+* Γ(C, ⊤) := g.appTop.hom.comp e.symm.toRingHom
  let : Algebra k[X] Γ(C, ⊤) := φ.toAlgebra
  have : Module.Finite k[X] Γ(C, ⊤) := by
    change φ.Finite
    exact g.finite_appTop.comp (RingHom.Finite.of_surjective _ e.symm.surjective)
  let : IsSchemeTheoreticallyDominant g :=
    IsSchemeTheoreticallyDominant.of_isDominant g
  have hg : Function.Injective g.appTop := by
    rw [RingHom.injective_iff_ker_eq_bot,
      ← g.ker_apply ⟨⊤, isAffineOpen_top _⟩, g.ker_eq_bot]
    simp
  have hφ : Function.Injective φ := hg.comp e.symm.injective
  have : Module.IsTorsionFree k[X] Γ(C, ⊤) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r b h
    change φ r * b = 0 at h
    rcases mul_eq_zero.mp h with hr | hb
    · exact Or.inl (hφ (hr.trans (map_zero _).symm))
    · exact Or.inr hb
  have : Module.Free k[X] Γ(C, ⊤) := Module.free_of_finite_type_torsion_free'
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  have hflat : φ.Flat := by
    change Module.Flat k[X] Γ(C, ⊤)
    infer_instance
  have he : g.appTop.hom = φ.comp e.toRingHom := by
    ext r
    simp [φ]
  rw [he]
  exact (RingHom.Flat.of_bijective e.bijective).comp hflat

/-- Every actual reduced component of a finite flat curve over the affine line
is flat over that line, even when the original curve has nilpotents or several
components. No extra Noetherian or separability hypothesis is needed. -/
theorem finiteFlatCurve_component_flat
    {k : Type u} [Field k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k[X])) [IsFinite f] [Flat f] (z : genericPoints P) :
    Flat ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ f) := by
  let : Surjective ((IntegralClosedSubscheme.pointClosure z.val).val.subschemeι ≫ f) :=
    ⟨surjective_pointClosure_of_finite_generalizing f (Flat.generalizingMap f) z.val z.property⟩
  exact finiteCurve_flat_of_integral_surjective _

end AlgebraicGeometry.Scheme.Hom
