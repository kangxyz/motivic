/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Ideal
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The original ideal of a section in a curve smooth near that section

Local rank one extends from an open containing a closed subscheme: on its
complement the original ideal inclusion is an isomorphism. Thus a compactified
curve need only be smooth near the section, not at infinity. The actual ideal,
its dual, and the canonical section are retained rather than Picard classes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The original ideal of a morphism with empty source is canonically the unit. -/
theorem idealInclusion_isIso_of_isEmpty {D X : Scheme.{u}} [IsEmpty D] (i : D ⟶ X) :
    IsIso (idealInclusion i) := by
  have h : structureModuleMap i = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    ext r
    change (i.app U) r = 0
    exact Subsingleton.elim _ _
  exact kernel.ι_of_zero h

/-- Local rank one near the entire closed support implies local rank one of the
original ideal globally; off that support its actual inclusion is invertible. -/
theorem idealModule_isLocallyRankOne_of_neighborhood {D X : Scheme.{u}}
    (i : D ⟶ X) [IsClosedImmersion i] (U : X.Opens)
    (hU : Set.range i ⊆ U)
    (h : IsLocallyRankOne U.toScheme (idealModule (i ∣_ U))) :
    IsLocallyRankOne X (idealModule i) := by
  classical
  let V : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let W : ULift.{u} Bool → X.Opens := fun b => if b.down then U else V
  have hcov : IsOpenCover W := .mk (by
    apply top_le_iff.mp
    intro x _
    by_cases hx : x ∈ Set.range i
    · exact Opens.mem_iSup.mpr ⟨⟨true⟩, hU hx⟩
    · exact Opens.mem_iSup.mpr ⟨⟨false⟩, hx⟩)
  apply isLocallyRankOne_of_cover_restrict (idealModule i) W hcov
  intro ⟨b⟩
  cases b with
  | true =>
    exact isLocallyRankOne_of_iso U.toScheme (idealRestrictionIso i U).symm h
  | false =>
    have : IsEmpty (i ⁻¹ᵁ V).toScheme := ⟨fun x => x.property ⟨x.val, rfl⟩⟩
    have := idealInclusion_isIso_of_isEmpty (i ∣_ V)
    have hu : IsLocallyRankOne V.toScheme (SheafOfModules.unit V.toScheme.ringCatSheaf) :=
      isLocallyRankOne_of_iso V.toScheme
        (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
          SheafOfModules.unit V.toScheme.ringCatSheaf))
        (trivialLineBundle V.toScheme).property
    exact isLocallyRankOne_of_iso V.toScheme
      ((asIso (idealInclusion (i ∣_ V))).symm ≪≫ (idealRestrictionIso i V).symm) hu

/-- Only the indicated neighborhood of the finite flat divisor must be smooth.
No smoothness condition is imposed on the complement. -/
theorem idealModule_isLocallyRankOne_of_smooth_near_range {S X D : Scheme.{u}}
    (p : X ⟶ S) (i : D ⟶ X) [IsClosedImmersion i]
    [IsFinite (i ≫ p)] [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)]
    (U : X.Opens) (hU : Set.range i ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    IsLocallyRankOne X (idealModule i) := by
  apply idealModule_isLocallyRankOne_of_neighborhood i U hU
  have htop : i ⁻¹ᵁ U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact hU ⟨x, rfl⟩
  have : IsIso (i ⁻¹ᵁ U).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simpa using htop)
  have hc : (i ∣_ U) ≫ (U.ι ≫ p) = (i ⁻¹ᵁ U).ι ≫ (i ≫ p) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have : IsFinite ((i ∣_ U) ≫ (U.ι ≫ p)) := by rw [hc]; infer_instance
  have : Flat ((i ∣_ U) ≫ (U.ι ≫ p)) := by rw [hc]; infer_instance
  have : LocallyOfFinitePresentation ((i ∣_ U) ≫ (U.ι ≫ p)) := by
    rw [hc]; infer_instance
  exact idealModule_isLocallyRankOne_of_smooth_of_finite_flat S U.toScheme
    (i ⁻¹ᵁ U).toScheme (U.ι ≫ p) (i ∣_ U) inferInstance inferInstance
    inferInstance inferInstance inferInstance

/-- A closed section has invertible original ideal if the curve is smooth near
its image. The possibly singular complement is untouched. -/
theorem section_idealModule_isLocallyRankOne {S X : Scheme.{u}} (p : X ⟶ S)
    (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 S)
    (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    IsLocallyRankOne X (idealModule s) := by
  have : IsFinite (s ≫ p) := by rw [hs]; infer_instance
  have : Flat (s ≫ p) := by rw [hs]; infer_instance
  have : LocallyOfFinitePresentation (s ≫ p) := by rw [hs]; infer_instance
  exact idealModule_isLocallyRankOne_of_smooth_near_range p s U hU

/-- The ideal line bundle is the original kernel, not merely its isomorphism class. -/
def sectionIdealLineBundle {S X : Scheme.{u}} (p : X ⟶ S)
    (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 S)
    (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] : LineBundle X :=
  ⟨idealModule s, section_idealModule_isLocallyRankOne p s hs U hU⟩

/-- The actual divisor bundle of the section is the dual of its original ideal. -/
def sectionDivisorLineBundle {S X : Scheme.{u}} (p : X ⟶ S)
    (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 S)
    (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] : LineBundle X :=
  dualLineBundle X (sectionIdealLineBundle p s hs U hU)

/-- The canonical global section is precisely the original ideal inclusion,
viewed as a section of the dual by the internal-Hom equivalence. -/
def sectionDivisorCanonicalSection {S X : Scheme.{u}} (p : X ⟶ S)
    (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 S)
    (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    Γ((sectionDivisorLineBundle p s hs U hU).val, ⊤) :=
  (InternalHom.sectionHomEquiv X (idealModule s)
    (SheafOfModules.unit X.ringCatSheaf) ⊤).symm
      ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).map (idealInclusion s))

/-- The canonical section represents the specified inclusion, with no choice of
another section or trivialization. -/
theorem sectionDivisorCanonicalSection_eq_inclusion {S X : Scheme.{u}} (p : X ⟶ S)
    (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 S)
    (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    InternalHom.sectionHomEquiv X (idealModule s)
        (SheafOfModules.unit X.ringCatSheaf) ⊤
        (sectionDivisorCanonicalSection p s hs U hU) =
      (SheafOfModules.overFunctor X.ringCatSheaf ⊤).map (idealInclusion s) :=
  Equiv.apply_symm_apply _ _

/-- The diagonal ideal of a separated curve, using the specified smooth
neighborhood of the diagonal in the product. -/
theorem diagonal_idealModule_isLocallyRankOne {S C : Scheme.{u}} (p : C ⟶ S)
    [IsSeparated p] (U : (pullback p p).Opens)
    (hU : Set.range (pullback.diagonal p) ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst p p)] :
    IsLocallyRankOne (pullback p p) (idealModule (pullback.diagonal p)) :=
  section_idealModule_isLocallyRankOne (pullback.fst p p) (pullback.diagonal p)
    (pullback.diagonal_fst p) U hU

/-- For a smooth open in a possibly singular compactification, the diagonal is
its graph in the mixed product. Only a neighborhood of this graph is required
to be smooth; the compactification is not assumed smooth. -/
theorem graph_idealModule_isLocallyRankOne {S C X : Scheme.{u}}
    (j : C ⟶ X) (p : X ⟶ S) [IsSeparated p]
    (U : (pullback (j ≫ p) p).Opens)
    (hU : Set.range (pullback.lift (𝟙 C) j (Category.id_comp (j ≫ p))) ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst (j ≫ p) p)] :
    IsLocallyRankOne (pullback (j ≫ p) p)
      (idealModule (pullback.lift (𝟙 C) j (Category.id_comp (j ≫ p)))) :=
  section_idealModule_isLocallyRankOne (pullback.fst (j ≫ p) p)
    (pullback.lift (𝟙 C) j (Category.id_comp (j ≫ p))) (pullback.lift_fst _ _ _) U hU

end AlgebraicGeometry.Scheme.Hom
