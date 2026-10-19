/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFreePrincipal

/-!
# Canonical affine neighborhoods with a whole-source frame

An original finite-free affine chart refines around every target point to a
canonical affine open chart with one frame on its entire inverse image. Freeness
uses the literal structural scalar action and is transported by actual pullbacks.


Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFreeAffineNeighborhood`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.FiniteSchemeNormBaseChange

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A finite-free canonical affine chart produces a smaller canonical affine
chart containing the given point, together with a frame on the whole source. -/
theorem exists_affine_frame_of_finite_free
    {C T : Scheme.{u}} (f : C ⟶ T) [IsFinite f]
    (U : T.Opens) (hU : IsAffineOpen U) (L : LineBundle C)
    (x : T) (hx : x ∈ U) :
    letI : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
      (scalarMap (pullback.snd f hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤)],
      ∃ (V : T.Opens) (hV : IsAffineOpen V), x ∈ V ∧ V ≤ U ∧
        Nonempty ((Modules.pullback (pullback.fst f hV.fromSpec)).obj L.val ≅
          SheafOfModules.unit (Limits.pullback f hV.fromSpec).ringCatSheaf) ∧
        (letI : Algebra Γ(T, V) Γ(Limits.pullback f hV.fromSpec, ⊤) :=
          (scalarMap (pullback.snd f hV.fromSpec)).toAlgebra
         Module.Free Γ(T, V) Γ(Limits.pullback f hV.fromSpec, ⊤)) := by
  let p := pullback.snd f hU.fromSpec
  let j := pullback.fst f hU.fromSpec
  let : Algebra Γ(T, U) Γ(Limits.pullback f hU.fromSpec, ⊤) :=
    (scalarMap p).toAlgebra
  intro hfree
  let : IsAffine (Limits.pullback f hU.fromSpec) := isAffine_of_isAffineHom p
  obtain ⟨y, hy⟩ : ∃ y, hU.fromSpec y = x := by
    have : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx
    exact this
  obtain ⟨W, hyW, ⟨e⟩⟩ :=
    exists_base_open_unitIso_of_isFinite p y (pullbackLineBundle j L)
  obtain ⟨_, ⟨_, ⟨r : Γ(T, U), rfl⟩, rfl⟩, hyr, hrW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hyW W.isOpen
  let V := T.basicOpen r
  have hV : IsAffineOpen V := hU.basicOpen r
  have hVU : V ≤ U := T.basicOpen_le r
  let rho := T.presheaf.map (homOfLE hVU).op
  have hc : Spec.map rho ≫ hU.fromSpec = hV.fromSpec :=
    hU.map_fromSpec hV (homOfLE hVU).op
  let E : Limits.pullback p (Spec.map rho) ≅ Limits.pullback f hV.fromSpec :=
    pullbackLeftPullbackSndIso f hU.fromSpec (Spec.map rho) ≪≫
      pullback.congrHom rfl hc
  have hEs : E.hom ≫ pullback.snd f hV.fromSpec =
      pullback.snd p (Spec.map rho) := by
    simp [E, p, pullback.congrHom_hom, pullback.map]
  let q := E.inv ≫ pullback.fst p (Spec.map rho)
  have hqj : q ≫ j = pullback.fst f hV.fromSpec := by
    simp [q, j, p, E, pullback.congrHom_inv, pullback.map, Category.assoc]
  have hqp : q ≫ p = pullback.snd f hV.fromSpec ≫ Spec.map rho := by
    dsimp only [q]
    rw [Category.assoc, pullback.condition]
    have he : E.inv ≫ pullback.snd p (Spec.map rho) =
        pullback.snd f hV.fromSpec := by rw [← hEs, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, he]
  let O := p ⁻¹ᵁ W
  have hqO : Set.range q ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change p (q z) ∈ W
    have hz : Spec.map rho (pullback.snd f hV.fromSpec z) ∈
        PrimeSpectrum.basicOpen r := by
      rw [← hU.fromSpec_preimage_basicOpen]
      change hU.fromSpec (Spec.map rho _) ∈ V
      rw [← Scheme.Hom.comp_apply, hc]
      change hV.fromSpec _ ∈ (V : Set T)
      rw [← hV.range_fromSpec]
      exact Set.mem_range_self _
    have he := congrArg (fun a => a z) hqp
    exact he.symm ▸ hrW hz
  let l := IsOpenImmersion.lift O.ι q hqO
  have hl : l ≫ O.ι = q := IsOpenImmersion.lift_fac O.ι q hqO
  let eO : (Modules.pullback O.ι).obj ((Modules.pullback j).obj L.val) ≅
      SheafOfModules.unit O.toScheme.ringCatSheaf :=
    ((Modules.restrictFunctorIsoPullback O.ι).app _).symm ≪≫ e
  let eq : (Modules.pullback q).obj ((Modules.pullback j).obj L.val) ≅
      SheafOfModules.unit (Limits.pullback f hV.fromSpec).ringCatSheaf :=
    ((Modules.pullbackCongr hl).app _).symm ≪≫
      ((Modules.pullbackComp l O.ι).app _).symm ≪≫
      (Modules.pullback l).mapIso eO ≪≫ pullbackUnitIso l
  let ef : (Modules.pullback (pullback.fst f hV.fromSpec)).obj L.val ≅
      SheafOfModules.unit (Limits.pullback f hV.fromSpec).ringCatSheaf :=
    ((Modules.pullbackCongr hqj).app L.val).symm ≪≫
      ((Modules.pullbackComp q j).app L.val).symm ≪≫ eq
  refine ⟨V, hV, ?_, hVU, ⟨ef⟩, ?_⟩
  · rw [← hy]
    change y ∈ hU.fromSpec ⁻¹ᵁ T.basicOpen r
    rw [hU.fromSpec_preimage_basicOpen]
    exact hyr
  · let : Algebra Γ(T, V) Γ(Limits.pullback p (Spec.map rho), ⊤) :=
      (scalarMap (pullback.snd p (Spec.map rho))).toAlgebra
    let : Module.Free Γ(T, V) Γ(Limits.pullback p (Spec.map rho), ⊤) :=
      sections_free_pullback p rho.hom
    exact sections_free_of_iso (pullback.snd p (Spec.map rho))
      (pullback.snd f hV.fromSpec) E hEs

end AlgebraicGeometry.Scheme.Modules.Invertible
