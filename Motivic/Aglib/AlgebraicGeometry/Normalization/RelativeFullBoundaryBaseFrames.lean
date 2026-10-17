/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.RelativeInfinityFiniteBaseOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ProperFiniteFiberFrame
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteBoundaryTwists

/-! # One base-only neighborhood frames the entire infinity and finite closed support -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- Finite fibers on both actual coproduct summands give a finite fiber on their coproduct. -/
theorem finite_coprod_fiber {D Z S : Scheme.{u}} (f : D ⟶ S) (g : Z ⟶ S)
    (x : S) (hf : (f ⁻¹' {x}).Finite) (hg : (g ⁻¹' {x}).Finite) :
    ((coprod.desc f g) ⁻¹' {x}).Finite := by
  apply ((hf.image (coprod.inl : D ⟶ D ⨿ Z)).union
    (hg.image (coprod.inr : Z ⟶ D ⨿ Z))).subset
  intro a ha
  rcases (isCompl_range_inl_inr D Z).sup_eq_top.ge (Set.mem_univ a) with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · left
    refine ⟨a, ?_, rfl⟩
    change (coprod.inl ≫ coprod.desc f g) a = x at ha
    change f a = x
    simpa only [coprod.inl_desc] using ha
  · right
    refine ⟨a, ?_, rfl⟩
    change (coprod.inr ≫ coprod.desc f g) a = x at ha
    change g a = x
    simpa only [coprod.inr_desc] using ha

namespace RelativeAffineLineEtaleCompactification
variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]

/-- A frame of every positive twist on the full original boundary plus prescribed
finite support, constructed by shrinking the coefficient base alone. -/
theorem exists_base_open_full_boundary_twist_frames
    {Z : Scheme.{u}} (a : Z ⟶ compactification R p)
    [IsFinite (a ≫ projection R p)] :
    ∃ O : (Spec (.of R)).Opens, genericPoint (Spec (.of R)) ∈ O ∧
      Nonempty ((n : ℕ) →
        (Modules.pullback (((coprod.desc (infinityInclusion R p) a ≫ projection R p) ⁻¹ᵁ O).ι ≫
          coprod.desc (infinityInclusion R p) a ≫ toProjectiveLine R p)).obj
            (twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
          SheafOfModules.unit
            ((coprod.desc (infinityInclusion R p) a ≫ projection R p) ⁻¹ᵁ O).toScheme.ringCatSheaf)
    := by
  let d := coprod.desc (infinityInclusion R p) a
  let b := d ≫ projection R p
  have hb : b = coprod.desc (infinityInclusion R p ≫ projection R p)
      (a ≫ projection R p) := by simp [b, d, coprod.desc_comp]
  let : IsFinite a := IsFinite.of_comp a (projection R p)
  let : IsFinite d := inferInstanceAs (IsFinite (coprod.desc (infinityInclusion R p) a))
  have : IsProper b := inferInstanceAs (IsProper (d ≫ projection R p))
  have hfin : (b ⁻¹' {genericPoint (Spec (.of R))}).Finite := by
    rw [hb]
    apply finite_coprod_fiber
    · exact finite_generic_base_fiber_of_finite_projectiveLine R
        (infinityInclusion R p ≫ toProjectiveLine R p)
        (EtaleCompactification.infinity_avoids_generic _ (projectiveMap R p))
    · exact (a ≫ projection R p).finite_preimage (Set.finite_singleton _)
  let g := d ≫ toProjectiveLine R p
  let L := pullbackLineBundle g (twistingLineBundle R (ULift.{u} (Fin 2)) 1)
  obtain ⟨O, hx, ⟨e⟩⟩ := exists_base_open_unitIso_of_isProper_finite_fiber b
    (genericPoint (Spec (.of R))) hfin L
  let W := b ⁻¹ᵁ O
  let e₁ : (Modules.pullback (W.ι ≫ g)).obj (twistingSheaf R (ULift.{u} (Fin 2)) 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι g).symm.app (twistingSheaf R (ULift.{u} (Fin 2)) 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback g).obj (twistingSheaf R (ULift.{u} (Fin 2)) 1)) ≪≫ e
  exact ⟨O, hx, ⟨CoherentGraph.positiveTwistUnitIso R (ULift.{u} (Fin 2)) (W.ι ≫ g) e₁⟩⟩

end RelativeAffineLineEtaleCompactification
end AlgebraicGeometry.Scheme
