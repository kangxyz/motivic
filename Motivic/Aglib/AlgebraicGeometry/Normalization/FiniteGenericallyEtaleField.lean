/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.FunctionField.GenericFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Actual function-field finiteness and étaleness from one nonempty étale open -/
@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- A nonempty actual étale source neighborhood forces dominance over an integral target. -/
theorem isDominant_of_nonempty_etale_open {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (U : X.Opens) (hU : (U : Set X).Nonempty) [Etale (U.ι ≫ f)] :
    IsDominant f := by
  have : Nonempty U.toScheme := hU.to_subtype
  have : IsDominant (U.ι ≫ f) :=
    ⟨(U.ι ≫ f).isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  exact IsDominant.of_comp U.ι f

/-- Finiteness of the original map induces finiteness of its actual generic stalk map. -/
theorem finite_functionFieldMap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] :
    IsFinite (Spec.map (CommRingCat.ofHom (functionFieldMap f))) := by
  have := genericFibreMap_isIso f
  have h : genericFibreMap f ≫ pullback.snd f (Y.fromSpecStalk (genericPoint Y)) =
      Spec.map (CommRingCat.ofHom (functionFieldMap f)) := by
    exact pullback.lift_snd _ _ _
  rw [← h]
  infer_instance

/-- The original generic stalk map is étale when a source open containing the
actual generic point is étale. The finite map supplies the native generic fiber. -/
theorem etale_functionFieldMap_of_etale_open
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (U : X.Opens) (hU : genericPoint X ∈ U) [Etale (U.ι ≫ f)] :
    Etale (Spec.map (CommRingCat.ofHom (functionFieldMap f))) := by
  have := genericFibreMap_isIso f
  let gx := X.fromSpecStalk (genericPoint X)
  let gy := Y.fromSpecStalk (genericPoint Y)
  let a := Spec.map (CommRingCat.ofHom (functionFieldMap f))
  have H : IsPullback gx a f gy := by
    apply IsPullback.of_iso_pullback ⟨fromSpecStalk_genericPoint_naturality f⟩
      (asIso (genericFibreMap f))
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  have hr : Set.range gx ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    simpa [gx, fromSpecStalk_genericPoint_apply] using hU
  let l := IsOpenImmersion.lift U.ι gx hr
  have hl : l ≫ U.ι = gx := IsOpenImmersion.lift_fac _ _ _
  have H' : IsPullback l a (U.ι ≫ f) gy := by
    apply IsPullback.of_isLimit' ⟨by rw [← Category.assoc, hl]; exact H.w⟩
    refine PullbackCone.IsLimit.mk _
      (fun s => H.lift (s.fst ≫ U.ι) s.snd (by simpa using s.condition)) ?_ ?_ ?_
    · intro s
      apply (cancel_mono U.ι).mp
      rw [Category.assoc, hl, H.lift_fst]
    · intro s
      exact H.lift_snd _ _ _
    · intro s m hm₁ hm₂
      apply H.hom_ext
      · rw [H.lift_fst]
        calc
          m ≫ gx = m ≫ l ≫ U.ι := congrArg (m ≫ ·) hl.symm
          _ = s.fst ≫ U.ι := by rw [← Category.assoc, hm₁]
      · rw [hm₂, H.lift_snd]
  exact MorphismProperty.of_isPullback H' inferInstance

end AlgebraicGeometry.Scheme
