/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.DualNumber
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual finite-scheme norm base change

The statements retain the literal scheme pullback, both actual global-sections
scalar maps, and the original unit map. A nonzero square-zero global section
remains nonzero on every field extension, testing the unreduced scheme rather
than a reduced surrogate. All dependencies are audited by rejection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open AlgebraicGeometry.FiniteSchemeNormBaseChange

universe u

namespace Motivic.MotivicTest.FiniteSchemeNormBaseChange

variable {k L : Type u} [Field k] [Field L] {T : Scheme.{u}}
  (p : T ⟶ Spec (.of k)) (φ : k →+* L)

/-- The theorem applies with the literal structural ring homomorphisms,
without any choice of scalar structure or coordinate-ring replacement. -/
theorem actual_norm [IsFinite p] (b : Γ(T, ⊤)) :
    let : Algebra k Γ(T, ⊤) :=
      (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      ((pullback.snd p (Spec.map (CommRingCat.ofHom φ))).appTop.hom.comp
        (Scheme.ΓSpecIso (.of L)).inv.hom).toAlgebra
    Algebra.norm L ((pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b) =
      φ (Algebra.norm k b) := norm_fst p φ b

/-- The actual original unit pulls back along fst; both norm values belong
to the prescribed base unit groups. -/
theorem actual_unit_norm [IsFinite p] (b : Γ(T, ⊤)ˣ) :
    let : Algebra k Γ(T, ⊤) :=
      (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      ((pullback.snd p (Spec.map (CommRingCat.ofHom φ))).appTop.hom.comp
        (Scheme.ΓSpecIso (.of L)).inv.hom).toAlgebra
    Units.map (Algebra.norm L)
        (Units.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop.hom.toMonoidHom b) =
      Units.map φ.toMonoidHom (Units.map (Algebra.norm k) b) := normUnits_fst p φ b

/-- On arbitrary pure tensors the actual identification is the product of
new structural scalars and the actual original pullback map. -/
theorem actual_tensor_formula [IsAffine T] (a : L) (b : Γ(T, ⊤)) :
    let : Algebra k L := φ.toAlgebra
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    sectionsTensorEquiv p φ (a ⊗ₜ[k] b) =
      scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) a *
        (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  change (sectionsTensorIso p φ).hom (a ⊗ₜ[k] b) = _
  rw [← sectionsTensorIso_tmul_one p φ a, ← sectionsTensorIso_one_tmul p φ b,
    ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Field base change does not erase nilpotent structure from actual global
sections. This argument makes no finiteness or separability assumption on φ. -/
theorem actual_nonzero_squareZero [IsAffine T] (b : Γ(T, ⊤))
    (hb : b ≠ 0) (hb2 : b ^ 2 = 0) :
    (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b ≠ 0 ∧
      ((pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b) ^ 2 = 0 := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  constructor
  · intro hzero
    apply hb
    have ht : ((1 : L) ⊗ₜ[k] b) = (0 : L ⊗[k] Γ(T, ⊤)) :=
      (sectionsTensorEquiv p φ).injective (by
        rw [sectionsTensorEquiv_one_tmul, map_zero, hzero])
    exact (Algebra.TensorProduct.includeRight_injective
      (R := k) (A := L) (B := Γ(T, ⊤)) φ.injective) (by
        change ((1 : L) ⊗ₜ[k] b) = (1 : L) ⊗ₜ[k] (0 : Γ(T, ⊤))
        simpa only [TensorProduct.tmul_zero] using ht)
  · rw [← map_pow, hb2, map_zero]

/-- A genuinely nonreduced affine input, finite over its original field. -/
def dualProjection : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

instance dualProjection_finite : IsFinite (dualProjection (k := k)) := by
  let : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The actual dual-number global section epsilon is nonzero and square-zero. -/
theorem actual_dual_epsilon :
    (Scheme.ΓSpecIso (.of (DualNumber k))).inv (DualNumber.eps : DualNumber k) ≠ 0 ∧
      ((Scheme.ΓSpecIso (.of (DualNumber k))).inv (DualNumber.eps : DualNumber k)) ^ 2 = 0 := by
  constructor
  · intro h
    have he : (DualNumber.eps : DualNumber k) = 0 := by
      apply (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of (DualNumber k))).inv).1
      simpa only [map_zero] using h
    have hs := congrArg TrivSqZeroExt.snd he
    exact one_ne_zero hs
  · rw [← map_pow, DualNumber.eps_pow_two, map_zero]

/-- Epsilon survives in the literal geometric fiber after every field map. -/
theorem actual_dual_baseChange_nonreduced :
    (pullback.fst (dualProjection (k := k)) (Spec.map (CommRingCat.ofHom φ))).appTop
        ((Scheme.ΓSpecIso (.of (DualNumber k))).inv (DualNumber.eps : DualNumber k)) ≠ 0 ∧
      ((pullback.fst (dualProjection (k := k)) (Spec.map (CommRingCat.ofHom φ))).appTop
        ((Scheme.ΓSpecIso (.of (DualNumber k))).inv (DualNumber.eps : DualNumber k))) ^ 2 = 0 :=
  actual_nonzero_squareZero (dualProjection (k := k)) φ _
    actual_dual_epsilon.1 actual_dual_epsilon.2

/-- The actual determinant norm identity applies to this unreduced finite
scheme, not only to field or reduced coordinate algebras. -/
theorem actual_dual_norm (b : Γ(Spec (.of (DualNumber k)), ⊤)ˣ) :
    let p := dualProjection (k := k)
    let : Algebra k Γ(Spec (.of (DualNumber k)), ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    Units.map (Algebra.norm L)
        (Units.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop.hom.toMonoidHom b) =
      Units.map φ.toMonoidHom (Units.map (Algebra.norm k) b) :=
  normUnits_fst (dualProjection (k := k)) φ b

/-- The nonreduced consumer includes characteristic two. -/
example :
    (pullback.fst (dualProjection (k := ZMod 2))
      (Spec.map (CommRingCat.ofHom (RingHom.id (ZMod 2))))).appTop
      ((Scheme.ΓSpecIso (.of (DualNumber (ZMod 2)))).inv
        (DualNumber.eps : DualNumber (ZMod 2))) ≠ 0 :=
  (actual_dual_baseChange_nonreduced (RingHom.id (ZMod 2))).1

open Lean in
run_cmd do
  for name in #[``scalarMap, ``sections_isPushout, ``sectionsTensorIso,
      ``sectionsTensorIso_tmul_one, ``sectionsTensorIso_one_tmul, ``sectionsTensorEquiv,
      ``sectionsTensorEquiv_one_tmul, ``sections_finite, ``norm_fst, ``normUnits_fst,
      ``actual_norm, ``actual_unit_norm, ``actual_tensor_formula,
      ``actual_nonzero_squareZero, ``dualProjection_finite, ``actual_dual_epsilon,
      ``actual_dual_baseChange_nonreduced, ``actual_dual_norm] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite-scheme norm base change uses only standard Lean foundations."

end Motivic.MotivicTest.FiniteSchemeNormBaseChange
