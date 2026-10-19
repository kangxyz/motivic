/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Isomorphism neighborhoods of finite étale morphisms

An actual residue-field isomorphism gives a section of the scheme-theoretic
fiber map. If the étale fiber has only that point, this section is a surjective
open immersion and hence an isomorphism. For a finite étale morphism, local
constancy of its rank then extends the isomorphism to a Zariski neighborhood.
No reducedness or connectedness assumption on the base is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The section of the actual fiber map induced by the inverse of the actual
residue-field map at a rational point. -/
def fiberSectionOfResidueFieldIso (f : X ⟶ Y) (x : X) [IsIso (f.residueFieldMap x)] :
    Spec (Y.residueField (f x)) ⟶ f.fiber (f x) :=
  Spec.map (inv (f.residueFieldMap x)) ≫ f.asFiberHom x

@[reassoc (attr := simp)]
lemma fiberSectionOfResidueFieldIso_fiberToSpecResidueField
    (f : X ⟶ Y) (x : X) [IsIso (f.residueFieldMap x)] :
    f.fiberSectionOfResidueFieldIso x ≫ f.fiberToSpecResidueField (f x) = 𝟙 _ := by
  rw [fiberSectionOfResidueFieldIso, Category.assoc,
    asFiberHom_fiberToSpecResidueField, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

/-- A section of an étale morphism is an open immersion. -/
lemma isOpenImmersion_of_section_of_etale (f : X ⟶ Y) [Etale f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : IsOpenImmersion s := by
  have : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      (fun _ _ g _ ↦ inferInstanceAs (IsOpenImmersion (pullback.diagonal g)))
  apply MorphismProperty.of_postcomp (W := @IsOpenImmersion) s f (inferInstance : Etale f)
  rw [hs]
  infer_instance

/-- An étale fiber with only one point and with isomorphic actual residue-field
map is isomorphic to the spectrum of the base residue field. -/
theorem isIso_fiberToSpecResidueField_of_singleton
    (f : X ⟶ Y) [Etale f] (x : X) [IsIso (f.residueFieldMap x)]
    (h : ∀ x' : X, f x' = f x → x' = x) :
    IsIso (f.fiberToSpecResidueField (f x)) := by
  let s := f.fiberSectionOfResidueFieldIso x
  have hs : s ≫ f.fiberToSpecResidueField (f x) = 𝟙 _ :=
    f.fiberSectionOfResidueFieldIso_fiberToSpecResidueField x
  have : Etale (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (Etale (pullback.snd f (Y.fromSpecResidueField (f x))))
  have : IsOpenImmersion s :=
    isOpenImmersion_of_section_of_etale _ s hs
  have : Surjective s := ⟨fun z ↦ by
    refine ⟨IsLocalRing.closedPoint _, ?_⟩
    apply (f.fiberι (f x)).isEmbedding.injective
    have hz : f (f.fiberι (f x) z) = f x := (f.fiberHomeo (f x) z).property
    change f.fiberι (f x) ((f.asFiberHom x) _) = f.fiberι (f x) z
    rw [asFiberHom_apply, fiberι_asFiber]
    exact (h _ hz).symm⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso (s ≫ f.fiberToSpecResidueField (f x)) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left (f := s) _

/-- Under the singleton hypothesis, the rational-point section is also a left
inverse of the actual scheme-theoretic fiber map. -/
lemma fiberToSpecResidueField_fiberSectionOfResidueFieldIso
    (f : X ⟶ Y) [Etale f] (x : X) [IsIso (f.residueFieldMap x)]
    (h : ∀ x' : X, f x' = f x → x' = x) :
    f.fiberToSpecResidueField (f x) ≫ f.fiberSectionOfResidueFieldIso x = 𝟙 _ := by
  have := f.isIso_fiberToSpecResidueField_of_singleton x h
  apply (cancel_mono (f.fiberToSpecResidueField (f x))).mp
  simp

/-- A finite flat morphism of finite presentation and rank one at a point is
an isomorphism on a Zariski neighborhood of that point. -/
theorem exists_isIso_morphismRestrict_of_finrank_eq_one
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (y : Y) (hy : f.finrank y = 1) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  obtain ⟨U, hU, hyU, hconst⟩ :=
    f.isLocallyConstant_finrank.exists_open y
  let W : Y.Opens := ⟨U, hU⟩
  refine ⟨W, hyU, (f ∣_ W).isIso_iff_finrank_eq.mpr ?_⟩
  funext z
  change (f ∣_ W).finrank z = 1
  rw [finrank_of_isPullback (f ⁻¹ᵁ W).ι (f ∣_ W) f W.ι
    (isPullback_morphismRestrict f W).flip z]
  exact (hconst z.val z.property).trans hy

/-- An isomorphism on the actual fiber of a finite flat morphism of finite
presentation extends to an isomorphism on a Zariski neighborhood. -/
theorem exists_isIso_morphismRestrict_of_isIso_fiber
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (y : Y) [IsIso (f.fiberToSpecResidueField y)] :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  apply f.exists_isIso_morphismRestrict_of_finrank_eq_one y
  let z : Spec (Y.residueField y) := IsLocalRing.closedPoint _
  have h := finrank_pullback_snd f (Y.fromSpecResidueField y) z
  change (f.fiberToSpecResidueField y).finrank _ = _ at h
  rw [Y.fromSpecResidueField_apply] at h
  rw [← h, finrank_eq_one_of_isIso]
  rfl

/-- A finite étale morphism with exactly one point over `y`, whose actual
residue-field map is an isomorphism, is an isomorphism near `y`.
The base may be nonreduced or disconnected. -/
theorem exists_isIso_morphismRestrict_of_singleton
    (f : X ⟶ Y) [IsFinite f] [Etale f] (y : Y) (x : X) (hx : f x = y)
    (h : ∀ x' : X, f x' = y → x' = x) (hres : IsIso (f.residueFieldMap x)) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  subst y
  let := hres
  have := f.isIso_fiberToSpecResidueField_of_singleton x h
  exact f.exists_isIso_morphismRestrict_of_isIso_fiber (f x)

end AlgebraicGeometry.Scheme.Hom
