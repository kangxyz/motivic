/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedSourceInclusion
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.PencilSites
public import Motivic.Aglib.AlgebraicGeometry.Scheme.DomainStalkComponents
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.AffineParameterNormal
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Stalks
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
/-! # Integral parameter components of the same original source

The source after both original coefficient restrictions is open in the one
canonical normalization. Its normal domain stalks give a finite clopen integral
component cover, including the empty cover for an empty source. Only the first
parameter will be restricted to these components in the norm construction.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.NativeSectionPairParameterComponents`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.NativeSectionPairNormalizedUnit`, `Pencils.NativeOriginalComponentActions`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}} [IsAffine Y]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

/-- Both unchanged coefficient restrictions preserve affineness of the source. -/
instance nativeFinalSource_affine : IsAffine (finalOriginalSource R p O V) := by
  have hO : IsAffineOpen O := by
    simpa only [Scheme.Opens.opensRange_ι] using isAffineOpen_opensRange O.ι
  let : IsAffine (boundaryBaseSourceOpen (boundaryLineProjection R) ⊤ O).toScheme :=
    boundaryBaseSourceOpen_affine (boundaryLineProjection R) ⊤ O (isAffineOpen_top _) hO
  let : IsAffine (boundaryBaseCoverOpen (boundaryLineProjection R) p ⊤ O).toScheme :=
    inferInstance
  have hV : IsAffineOpen V := by
    simpa only [Scheme.Opens.opensRange_ι] using isAffineOpen_opensRange V.ι
  let : IsAffine (boundaryBaseSourceOpen
      (boundaryLineProjection Γ(O.toScheme, ⊤)) ⊤ V).toScheme :=
    boundaryBaseSourceOpen_affine (boundaryLineProjection Γ(O.toScheme, ⊤)) ⊤ V
      (isAffineOpen_top _) hV
  change IsAffine (boundaryBaseCoverOpen (boundaryLineProjection Γ(O.toScheme, ⊤))
    (sourceNativeCoverMap R O p) ⊤ V).toScheme
  infer_instance

/-- Noetherianity is inherited through the actual open map into the finite
normalization; compactness comes from the proved affine source. -/
instance nativeFinalSource_noetherian : IsNoetherian (finalOriginalSource R p O V) := by
  let : IsLocallyNoetherian (compactification R p) :=
    LocallyOfFiniteType.isLocallyNoetherian (toProjectiveLine R p)
  let : IsLocallyNoetherian (finalOriginalSource R p O V) :=
    LocallyOfFiniteType.isLocallyNoetherian (finalOriginalSourceInclusion R p O V)
  exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

omit [IsAffine Y] [IsAffine V.toScheme] in
/-- The same original-source stalk is normal and a domain. This does not imply
that its whole, possibly disconnected, source scheme is integral. -/
theorem nativeFinalSource_stalk_normal_domain (y : finalOriginalSource R p O V) :
    IsIntegrallyClosed ((finalOriginalSource R p O V).presheaf.stalk y) ∧
      IsDomain ((finalOriginalSource R p O V).presheaf.stalk y) := by
  let P := ProjectiveSpace R (ULift.{u} (Fin 2))
  have h := FiniteEtale.GenericNormalization.stalk_normal_domain P
    (EtaleCompactification.genericCover P (projectiveMap R p))
    (finalOriginalSourceInclusion R p O V y)
  let := h.1
  let := h.2
  let e := (finalOriginalSourceStalkIso R p O V y).commRingCatIsoToRingEquiv
  exact ⟨IsIntegrallyClosed.of_equiv e, e.symm.toMulEquiv.isDomain _⟩

instance nativeFinalSource_stalk_domain (y : finalOriginalSource R p O V) :
    IsDomain ((finalOriginalSource R p O V).presheaf.stalk y) :=
  (nativeFinalSource_stalk_normal_domain R p O V y).2

instance nativeFinalSource_stalk_normal (y : finalOriginalSource R p O V) :
    IsIntegrallyClosed ((finalOriginalSource R p O V).presheaf.stalk y) :=
  (nativeFinalSource_stalk_normal_domain R p O V y).1

/-- The actual finite component cover, with empty index when the source is empty. -/
def nativeSectionPairParameterComponentCover : (finalOriginalSource R p O V).OpenCover :=
  AlgebraicGeometry.Scheme.domainStalkComponentOpenCover (finalOriginalSource R p O V)
    (fun _ => inferInstance)

instance nativeSectionPairParameterComponentCover_finite :
    Finite (nativeSectionPairParameterComponentCover R p O V).I₀ := by
  unfold nativeSectionPairParameterComponentCover
  infer_instance

variable (i : (nativeSectionPairParameterComponentCover R p O V).I₀)

instance nativeSectionPairParameterComponent_integral :
    IsIntegral ((nativeSectionPairParameterComponentCover R p O V).X i) := by
  unfold nativeSectionPairParameterComponentCover
  infer_instance

/-- A clopen component of the actual affine source is affine, using its
closed immersion rather than assuming arbitrary opens of an affine are affine. -/
instance nativeSectionPairParameterComponent_affine :
    IsAffine ((nativeSectionPairParameterComponentCover R p O V).X i) := by
  let α := (nativeSectionPairParameterComponentCover R p O V).f i
  have hclosed : IsClosed (Set.range α) := by
    change IsClosed (Set.range (AlgebraicGeometry.Scheme.domainStalkComponentOpen
      (fun y : finalOriginalSource R p O V => inferInstance) i.val i.property).ι)
    rw [AlgebraicGeometry.Scheme.range_domainStalkComponentOpen_ι]
    exact isClosed_of_mem_irreducibleComponents i.val i.property
  let : IsClosedImmersion α := IsClosedImmersion.of_isPreimmersion α hclosed
  exact isAffine_of_isAffineHom α

/-- Each actual parameter product is integral, Noetherian and normal. The
coefficient map is the original one restricted only to this first parameter. -/
theorem nativeSectionPairParameterComponent_product_normal
    (R' : Type u) [CommRing R']
    (b : (nativeSectionPairParameterComponentCover R p O V).X i ⟶ Spec (.of R')) :
    IsIntegral (pullback b (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2)))) ∧
      IsNoetherian (pullback b (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2)))) ∧
      ∀ x : (pullback b (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2))) : Scheme.{u}),
        IsIntegrallyClosed
          ((pullback b (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2)))).presheaf.stalk x) := by
  let A := (nativeSectionPairParameterComponentCover R p O V).X i
  let α := (nativeSectionPairParameterComponentCover R p O V).f i
  let (x : A) : IsIntegrallyClosed (A.presheaf.stalk x) := by
    exact IsIntegrallyClosed.of_equiv (asIso (α.stalkMap x)).commRingCatIsoToRingEquiv
  let : Nonempty (⊤ : A.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  let : IsIntegrallyClosed Γ(A, ⊤) :=
    A.isIntegrallyClosed_sections_of_isAffineOpen ⊤ (isAffineOpen_top A)
  let : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian α
  let : IsNoetherianRing Γ(A, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top A⟩
  exact affineParameterPullback_normal R' b

/-- The actual target map changes only the first parameter to its component. -/
def nativeSectionPairParameterComponentProductMap
    (R' : Type u) [CommRing R'] (q : finalOriginalSource R p O V ⟶ Spec (.of R')) :
    pullback ((nativeSectionPairParameterComponentCover R p O V).f i ≫ q)
        (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2))) ⟶
      pullback q (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2))) :=
  constantSourceMapOfEq ((nativeSectionPairParameterComponentCover R p O V).f i) q
    (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2)))
    ((nativeSectionPairParameterComponentCover R p O V).f i ≫ q) rfl

instance nativeSectionPairParameterComponentProductMap_open
    (R' : Type u) [CommRing R'] (q : finalOriginalSource R p O V ⟶ Spec (.of R')) :
    IsOpenImmersion (nativeSectionPairParameterComponentProductMap R p O V i R' q) := by
  exact MorphismProperty.of_isPullback
    (constantSourceMapOfEq_isPullback ((nativeSectionPairParameterComponentCover R p O V).f i) q
      (ProjectiveSpace.toSpec R' (ULift.{u} (Fin 2)))
      ((nativeSectionPairParameterComponentCover R p O V).f i ≫ q) rfl).flip inferInstance

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
