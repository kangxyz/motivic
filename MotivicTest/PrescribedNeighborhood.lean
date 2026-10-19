/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General

/-! # Prescribed trivializations on whole scheme-theoretic boundaries -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace Motivic.MotivicTest.PrescribedNeighborhood

/-- The constructed principal spectrum really is an open neighborhood map. -/
example (R : CommRingCat.{u}) (r : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
  inferInstance

/-- The full original isomorphism equality is exposed to a direct consumer. -/
theorem canonicalBoundaryIso (R S : CommRingCat.{u}) [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) (L : LineBundle (Spec R))
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj L.val ≅
      SheafOfModules.unit (Spec S).ringCatSheaf) :
    ∃ (r : R), algebraMap R S r = 1 ∧
      ∃ (q : Spec S ⟶ Spec (.of (Localization.Away r)))
        (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) =
          Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (d : (Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj L.val ≅
          SheafOfModules.unit (Spec (.of (Localization.Away r))).ringCatSheaf),
        ((Scheme.Modules.pullbackCongr hq).app L.val).symm ≪≫
          ((Scheme.Modules.pullbackComp q
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).app L.val).symm ≪≫
          (Scheme.Modules.pullback q).mapIso d ≪≫ pullbackUnitIso q = e :=
  exists_prescribed_principal_unitIso R S h L e

/-- The original sheaf isomorphism is retained on the full ideal-defined
boundary, with no reducedness, connectedness, or nonemptiness assumption. -/
theorem wholeIdealBoundary (R : CommRingCat.{u}) (I : Ideal R)
    (L : LineBundle (Spec R))
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I))))).obj L.val ≅
      SheafOfModules.unit (Spec (.of (R ⧸ I))).ringCatSheaf) :
    ∃ F : L.val ⟶ SheafOfModules.unit (Spec R).ringCatSheaf,
      pullbackUnitMap (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I)))) F = e.hom ∧
      ∃ r : R, r - 1 ∈ I ∧
        IsIso (pullbackUnitMap
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) F) := by
  obtain ⟨F, hF, r, hr, hi⟩ := exists_globalFunctional_prescribed_boundary R (.of (R ⧸ I))
    (Ideal.Quotient.mk_surjective (I := I)) L e
  exact ⟨F, hF, r, (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I) r).mp hr, hi⟩

/-- This concrete boundary has coordinate ring
`(ℤ × ℤ) / ((4,4))`, so both disconnected components and nilpotents remain
in the prescribed restriction. The line bundle and its coordinate are arbitrary. -/
theorem twoThickenedComponents
    (L : LineBundle (Spec (.of (ℤ × ℤ))))
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap (ℤ × ℤ) ((ℤ × ℤ) ⧸ Ideal.span {((4, 4) : ℤ × ℤ)}))))).obj L.val ≅
      SheafOfModules.unit (Spec (.of ((ℤ × ℤ) ⧸ Ideal.span {((4, 4) : ℤ × ℤ)}))).ringCatSheaf) :
    ∃ F : L.val ⟶ SheafOfModules.unit (Spec (.of (ℤ × ℤ))).ringCatSheaf,
      pullbackUnitMap (Spec.map (CommRingCat.ofHom
        (algebraMap (ℤ × ℤ) ((ℤ × ℤ) ⧸ Ideal.span {((4, 4) : ℤ × ℤ)})))) F = e.hom ∧
      ∃ r : ℤ × ℤ, r - 1 ∈ Ideal.span {((4, 4) : ℤ × ℤ)} ∧
        IsIso (pullbackUnitMap
          (Spec.map (CommRingCat.ofHom (algebraMap (ℤ × ℤ) (Localization.Away r)))) F) :=
  wholeIdealBoundary (.of (ℤ × ℤ)) (Ideal.span {((4, 4) : ℤ × ℤ)}) L e

set_option linter.hashCommand false in
#print axioms exists_globalFunctional_prescribed_boundary
set_option linter.hashCommand false in
#print axioms exists_prescribed_principal_unitIso
set_option linter.hashCommand false in
#print axioms twoThickenedComponents

end Motivic.MotivicTest.PrescribedNeighborhood
