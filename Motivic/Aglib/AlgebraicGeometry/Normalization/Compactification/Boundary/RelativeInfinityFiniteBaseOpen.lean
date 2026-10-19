/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Coheight
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # The full relative infinity boundary is finite after shrinking only the base -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme
attribute [local instance] specializationOrder

/-- A finite map into the actual relative projective line avoiding its generic point
has finite fiber over the generic point of the coefficient base. -/
theorem finite_generic_base_fiber_of_finite_projectiveLine
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {D : Scheme.{u}} (q : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite q]
    (hq : ∀ a : D, q a ≠ genericPoint (ProjectiveSpace R (ULift.{u} (Fin 2)))) :
    ((q ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⁻¹'
      {genericPoint (Spec (.of R))}).Finite := by
  let S := Spec (.of R)
  let E : CommRingCat.{u} := S.functionField
  let c : CommRingCat.of R ⟶ E := StructureSheaf.toStalk R (genericPoint S)
  let b := Spec.map c
  have hb : b = S.fromSpecStalk (genericPoint S) := (Spec.fromSpecStalk_eq' _ _).symm
  let : Flat b := hb ▸ fromSpecStalk_flat S (genericPoint S)
  let d := ProjectiveSpace.map c.hom (ULift.{u} (Fin 2))
  have H := ProjectiveSpace.isPullback_map c.hom (ULift.{u} (Fin 2))
  let : Flat (Spec.map (CommRingCat.ofHom c.hom)) := inferInstanceAs (Flat b)
  let : Flat d := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsNoetherian (ProjectiveSpace E (ULift.{u} (Fin 2))) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (ProjectiveSpace.toSpec E (ULift.{u} (Fin 2)))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (ProjectiveSpace.toSpec E (ULift.{u} (Fin 2))) }
  let : Subsingleton (Spec E) := inferInstanceAs (Subsingleton (PrimeSpectrum E))
  let K := pullback q d
  let j : K ⟶ D := pullback.fst q d
  let t : K ⟶ ProjectiveSpace E (ULift.{u} (Fin 2)) := pullback.snd q d
  let : IsFinite t := inferInstanceAs (IsFinite (pullback.snd q d))
  have hgen : d (genericPoint (ProjectiveSpace E (ULift.{u} (Fin 2)))) =
      genericPoint (ProjectiveSpace R (ULift.{u} (Fin 2))) := by
    have ht := Hom.mem_genericPoints_of_generalizing d (Flat.generalizingMap d)
      (genericPoint (ProjectiveSpace E (ULift.{u} (Fin 2))))
      (by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _)
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using ht
  let P : Set (ProjectiveSpace E (ULift.{u} (Fin 2))) := Set.range t
  have hP : IsClosed P := by
    simpa [P, ← Set.image_univ] using t.isClosedMap _ isClosed_univ
  have hη : genericPoint (ProjectiveSpace E (ULift.{u} (Fin 2))) ∉ P := by
    rintro ⟨a, ha⟩
    apply hq (j a)
    have he := congrArg (fun f => f a) (pullback.condition (f := q) (g := d))
    exact he.trans ((congrArg d ha).trans hgen)
  have : QuasiSober P := hP.isClosedEmbedding_subtypeVal.quasiSober
  have hn : closure P ≠ Set.univ := by
    rw [hP.closure_eq]
    intro he
    exact hη (he.symm ▸ Set.mem_univ _)
  have hpfin : P.Finite :=
    (NoetherianSpace.finite_coheight_one_of_closure_ne_univ hn).subset
      (fun a ha => ⟨ha, ProjectiveLine.coheight_eq_one_of_ne_genericPoint E a
        (fun he => hη (he ▸ ha))⟩)
  have hK : (Set.univ : Set K).Finite := by
    simpa [P] using t.finite_preimage hpfin
  have hbr : Set.range b = {genericPoint S} := by
    rw [hb]
    ext s
    constructor
    · rintro ⟨a, rfl⟩
      rw [Subsingleton.elim a (IsLocalRing.closedPoint E)]
      exact fromSpecStalk_closedPoint
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint E, fromSpecStalk_closedPoint⟩
  have hdr : Set.range d = (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⁻¹' Set.range b := by
    ext a
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨ProjectiveSpace.toSpec E (ULift.{u} (Fin 2)) a,
        (congrArg (fun f => f a) H.w).symm⟩
    · rintro ⟨e, he⟩
      obtain ⟨a', ha', _⟩ := exists_preimage_of_isPullback H a e he.symm
      exact ⟨a', ha'⟩
  have hj : Set.range j = (q ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) ⁻¹'
      {genericPoint S} := by
    rw [show Set.range j = q ⁻¹' Set.range d from Pullback.range_fst q d, hdr, hbr]
    rfl
  rw [← hj]
  simpa only [Set.image_univ] using hK.image j

namespace RelativeAffineLineEtaleCompactification
variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]

/-- The full boundary of the original étale source becomes finite on a genuine
open neighborhood of the base generic point. The parameter line is never shrunk. -/
theorem exists_base_open_finite_infinity :
    ∃ O : (Spec (.of R)).Opens, genericPoint (Spec (.of R)) ∈ O ∧
      IsFinite ((infinityInclusion R p ≫ projection R p) ∣_ O) := by
  apply exists_isFinite_morphismRestrict_of_finite_preimage_singleton
  exact finite_generic_base_fiber_of_finite_projectiveLine R
    (infinityInclusion R p ≫ toProjectiveLine R p)
    (EtaleCompactification.infinity_avoids_generic _ (projectiveMap R p))

end RelativeAffineLineEtaleCompactification
end AlgebraicGeometry.Scheme
