/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteBaseNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange

/-!
# A produced common frame on an actual finite-free principal base change

Around an arbitrary target point, the original finite morphism supplies a
whole-inverse-image line-bundle frame. A principal base neighborhood refines it;
the frame is transported to the literal localization pullback, and the actual
coordinate module remains free for its structural scalar action. No source
domain, reducedness, nontriviality or chosen neighborhood is assumed.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFreePrincipal`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFreeAffineNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteSchemeNormBaseChange

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The actual finite-free affine chart produces one whole-source frame after
an original principal base shrink containing the specified target point.
Both the frame and coordinate-module freeness use the literal pullback maps. -/
theorem exists_principal_frame_of_finite_free
    (A : CommRingCat.{u}) {C : Scheme.{u}} (p : C ⟶ Spec A) [IsFinite p]
    (L : LineBundle C) (x : Spec A) :
    letI : Algebra A Γ(C, ⊤) := (scalarMap p).toAlgebra
    ∀ [Module.Free A Γ(C, ⊤)], ∃ r : A, r ∉ x.asIdeal ∧
      Nonempty ((Modules.pullback
        (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))))).obj
          L.val ≅ SheafOfModules.unit
            (Limits.pullback p (Spec.map (CommRingCat.ofHom
              (algebraMap A (Localization.Away r))))).ringCatSheaf) ∧
      (letI : Algebra (Localization.Away r)
          Γ(Limits.pullback p (Spec.map (CommRingCat.ofHom
            (algebraMap A (Localization.Away r)))), ⊤) :=
        (scalarMap (pullback.snd p (Spec.map (CommRingCat.ofHom
          (algebraMap A (Localization.Away r)))))).toAlgebra
       Module.Free (Localization.Away r)
         Γ(Limits.pullback p (Spec.map (CommRingCat.ofHom
           (algebraMap A (Localization.Away r)))), ⊤)) := by
  let : Algebra A Γ(C, ⊤) := (scalarMap p).toAlgebra
  intro hfree
  let : IsAffine C := isAffine_of_isAffineHom p
  obtain ⟨U, hxU, ⟨e⟩⟩ := exists_base_open_unitIso_of_isFinite p x L
  obtain ⟨_, ⟨_, ⟨r : A, rfl⟩, rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))
  let q := pullback.fst p j
  let V := p ⁻¹ᵁ U
  have hq : Set.range q ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change p (q z) ∈ U
    have hj : j (pullback.snd p j z) ∈ PrimeSpectrum.basicOpen r := by
      rw [← Scheme.Hom.opensRange_localizationAway (R := A) r]
      exact ⟨_, rfl⟩
    have hc := congrArg (fun f => f z) (pullback.condition (f := p) (g := j))
    exact hc.symm ▸ hrU hj
  let l := IsOpenImmersion.lift V.ι q hq
  have hl : l ≫ V.ι = q := IsOpenImmersion.lift_fac V.ι q hq
  let eV : (Modules.pullback V.ι).obj L.val ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf :=
    ((Modules.restrictFunctorIsoPullback V.ι).app L.val).symm ≪≫ e
  let e' : (Modules.pullback q).obj L.val ≅
      SheafOfModules.unit (Limits.pullback p j).ringCatSheaf :=
    ((Modules.pullbackCongr hl).app L.val).symm ≪≫
      ((Modules.pullbackComp l V.ι).app L.val).symm ≪≫
      (Modules.pullback l).mapIso eV ≪≫ pullbackUnitIso l
  refine ⟨r, hxr, ⟨e'⟩, ?_⟩
  exact sections_free_pullback p (algebraMap A (Localization.Away r))

end AlgebraicGeometry.Scheme.Modules.Invertible
