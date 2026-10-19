/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Norm.Basic

/-!
# Determinant norms on the actual finite-scheme base change

The affine pullback/global-sections pushout identifies the actual coordinate
ring with its scalar extension. Both scalar actions come from the displayed
structure morphisms, and the original projection is the right tensor inclusion.
Consequently finite-free determinant norms commute with arbitrary commutative
scalar extension, including nonreduced bases. The original finite-scheme field
statements remain specializations; global freeness is not inferred from flatness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

section CommRings

variable {k L : Type u} [CommRing k] [CommRing L] {T : Scheme.{u}}

/-- Scalars on actual global sections, induced by the displayed structure map. -/
def scalarMap (p : T ⟶ Spec (.of k)) : k →+* Γ(T, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

variable (p : T ⟶ Spec (.of k)) (φ : k →+* L)

/-- The actual affine base-change coordinate ring is the pushout of the
original scalar map and the specified scalar map. -/
theorem sections_isPushout [IsAffine T] :
    IsPushout (CommRingCat.ofHom (scalarMap p)) (CommRingCat.ofHom φ)
      (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop
      (CommRingCat.ofHom (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ))))) := by
  have h := isPushout_appTop_of_isPullback
    (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom φ)))
  refine h.of_iso (Scheme.ΓSpecIso (.of k)) (Iso.refl _)
    (Scheme.ΓSpecIso (.of L)) (Iso.refl _) ?_ ?_ ?_ ?_
  · change p.appTop ≫ 𝟙 _ = (Scheme.ΓSpecIso (.of k)).hom ≫
      (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
    simp
  · rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
    simp only [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  · simp
  · change (pullback.snd p (Spec.map (CommRingCat.ofHom φ))).appTop ≫ 𝟙 _ =
      (Scheme.ΓSpecIso (.of L)).hom ≫ (Scheme.ΓSpecIso (.of L)).inv ≫
        (pullback.snd p (Spec.map (CommRingCat.ofHom φ))).appTop
    simp

/-- The canonical ring isomorphism is the uniqueness isomorphism between the
literal tensor pushout and the global sections of the actual scheme pullback. -/
def sectionsTensorIso [IsAffine T] :
    let : Algebra k L := φ.toAlgebra
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    CommRingCat.of (L ⊗[k] Γ(T, ⊤)) ≅
      Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  exact (CommRingCat.isPushout_tensorProduct k L Γ(T, ⊤)).isoIsPushout _ _
    (sections_isPushout p φ).flip

/-- The left tensor inclusion is precisely the actual new scalar map. -/
theorem sectionsTensorIso_tmul_one [IsAffine T] (a : L) :
    let : Algebra k L := φ.toAlgebra
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    (sectionsTensorIso p φ).hom (a ⊗ₜ[k] (1 : Γ(T, ⊤))) =
      scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) a := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  exact congrArg (fun q : CommRingCat.of L ⟶
      Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) => q.hom a)
    (IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct k L Γ(T, ⊤))
      (sections_isPushout p φ).flip)

/-- The right tensor inclusion is precisely pullback through the original
projection, rather than an unspecified isomorphic coordinate map. -/
theorem sectionsTensorIso_one_tmul [IsAffine T] (b : Γ(T, ⊤)) :
    let : Algebra k L := φ.toAlgebra
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    (sectionsTensorIso p φ).hom ((1 : L) ⊗ₜ[k] b) =
      (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  exact congrArg (fun q : Γ(T, ⊤) ⟶
      Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) => q.hom b)
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct k L Γ(T, ⊤))
      (sections_isPushout p φ).flip)

/-- The actual global-sections identification respects the new scalars. -/
def sectionsTensorEquiv [IsAffine T] :
    let : Algebra k L := φ.toAlgebra
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    L ⊗[k] Γ(T, ⊤) ≃ₐ[L] Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  exact { (sectionsTensorIso p φ).commRingCatIsoToRingEquiv with
    commutes' := sectionsTensorIso_tmul_one p φ }

/-- The canonical algebra equivalence sends `1 ⊗ b` to the original
geometric pullback of `b`. -/
theorem sectionsTensorEquiv_one_tmul [IsAffine T] (b : Γ(T, ⊤)) :
    let : Algebra k L := φ.toAlgebra
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    sectionsTensorEquiv p φ ((1 : L) ⊗ₜ[k] b) =
      (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b :=
  sectionsTensorIso_one_tmul p φ b

/-- The actual coordinate algebra of a finite scheme is finite for exactly
its structural scalar action. -/
theorem sections_finite [IsFinite p] :
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    Module.Finite k Γ(T, ⊤) := by
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  change (scalarMap p).Finite
  exact p.finite_appTop.comp (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- Freeness of the original coordinate module is preserved by actual scheme
base change, with both scalar actions induced by the structural maps. -/
theorem sections_free_pullback [IsAffine T] :
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    ∀ [Module.Free k Γ(T, ⊤)],
      Module.Free L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  intro _
  exact Module.Free.of_equiv (sectionsTensorEquiv p φ).toLinearEquiv

/-- An isomorphism over the original affine base transports coordinate-module
freeness for the literal structural scalar actions. -/
theorem sections_free_of_iso {T' : Scheme.{u}} (q : T' ⟶ Spec (.of k))
    (e : T ≅ T') (he : e.hom ≫ q = p) :
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra k Γ(T', ⊤) := (scalarMap q).toAlgebra
    ∀ [Module.Free k Γ(T, ⊤)], Module.Free k Γ(T', ⊤) := by
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra k Γ(T', ⊤) := (scalarMap q).toAlgebra
  dsimp only
  intro hfree
  let : Module.Free k Γ(T, ⊤) := hfree
  let ei : Γ(T, ⊤) ≅ Γ(T', ⊤) :=
    { hom := e.inv.appTop
      inv := e.hom.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop]; simp
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop]; simp }
  have hc : CommRingCat.ofHom (scalarMap p) ≫ ei.hom =
      CommRingCat.ofHom (scalarMap q) := by
    change (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ e.inv.appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop
    rw [← Scheme.Hom.comp_appTop, ← he, Iso.inv_hom_id_assoc]
  let ea : Γ(T, ⊤) ≃ₐ[k] Γ(T', ⊤) :=
    { ei.commRingCatIsoToRingEquiv with
      commutes' a := congrArg (fun h : CommRingCat.of k ⟶ Γ(T', ⊤) => h.hom a) hc }
  exact Module.Free.of_equiv ea.toLinearEquiv

/-- On an actual finite-free affine chart, determinant norm commutes with any
commutative scalar extension and the literal geometric projection. The explicit
finite/free hypotheses concern the displayed original scalar action. -/
theorem norm_fst_of_finite_free [IsAffine T] (b : Γ(T, ⊤)) :
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    ∀ [Module.Finite k Γ(T, ⊤)] [Module.Free k Γ(T, ⊤)],
      Algebra.norm L ((pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b) =
        φ (Algebra.norm k b) := by
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  intro _ _
  rw [← sectionsTensorEquiv_one_tmul p φ b]
  exact (Algebra.norm_eq_of_algEquiv (sectionsTensorEquiv p φ) ((1 : L) ⊗ₜ[k] b)).trans
    (Algebra.norm_one_tmul (R := k) (A := L) b)

end CommRings

variable {k L : Type u} [Field k] [Field L] {T : Scheme.{u}}
  (p : T ⟶ Spec (.of k)) (φ : k →+* L)

/-- Determinant norm of an actual pulled-back global section under an arbitrary
field map. In particular the entire possibly nonreduced finite scheme is retained. -/
theorem norm_fst [IsFinite p] (b : Γ(T, ⊤)) :
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    Algebra.norm L ((pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop b) =
      φ (Algebra.norm k b) := by
  let : IsAffine T := isAffine_of_isAffineHom p
  let : Algebra k L := φ.toAlgebra
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  let : Module.Finite k Γ(T, ⊤) := sections_finite p
  exact norm_fst_of_finite_free p φ b

/-- The same determinant identity in the actual unit groups. -/
theorem normUnits_fst [IsFinite p] (b : Γ(T, ⊤)ˣ) :
    let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
    let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
    Units.map (Algebra.norm L)
        (Units.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).appTop.hom.toMonoidHom b) =
      Units.map φ.toMonoidHom (Units.map (Algebra.norm k) b) := by
  let : Algebra k Γ(T, ⊤) := (scalarMap p).toAlgebra
  let : Algebra L Γ(pullback p (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  apply Units.ext
  exact norm_fst p φ b.val

end AlgebraicGeometry.FiniteSchemeNormBaseChange
