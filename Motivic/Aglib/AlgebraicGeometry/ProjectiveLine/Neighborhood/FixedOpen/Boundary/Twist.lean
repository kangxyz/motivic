module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Boundary.Map
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.RelativeNeighborhood
/-! # The same original boundary frame on the unchanged punctured source -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (r : R)

@[reassoc (attr := simp)] lemma fixedPsiAmbientIso_snd :
    (fixedPsiAmbientIso R r).hom ≫ pullback.snd _ _ =
      pullback.snd (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _) := by
  simp [fixedPsiAmbientIso, pullback.congrHom_hom, pullback.map]

def fixedPsiOriginalTwistIso (d : ℤ) :
    (Scheme.Modules.pullback (fixedPsiProjectiveIso R r).hom).obj
      (ProjectiveSpace.twistingSheaf Γ((fixedPsiSource R r).toScheme, ⊤)
        (ULift.{u} (Fin 2)) d) ≅
    (Scheme.Modules.pullback (pullback.snd (fixedPsiProjection R r)
      (ProjectiveSpace.toSpec R _))).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) d) :=
  (pullbackComp (fixedPsiAmbientIso R r).hom
    (neighborhoodProjectiveIso R (fixedPsiSource R r)).hom).symm.app _ ≪≫
  (Scheme.Modules.pullback (fixedPsiAmbientIso R r).hom).mapIso
    (neighborhoodOriginalTwistIso R (fixedPsiSource R r) d) ≪≫
  (pullbackComp (fixedPsiAmbientIso R r).hom (pullback.snd _ _)).app _ ≪≫
  (pullbackCongr (fixedPsiAmbientIso_snd R r)).app _

variable (V : (Spec (.of (Polynomial R))).Opens)

lemma fixedPsiBoundaryToOriginal_mem (x : fixedPsiBoundary R V r) :
    fixedPsiBoundaryToOriginal R r V x ∈ fullBoundaryPrincipalOpen R V r := by
  have h := congrArg (fun f => f x)
    (fixedPsiBoundaryToOriginal_fac R r V)
  have hp := congrArg (fun f => f (fixedPsiBoundaryMap R r V x))
    (pullback.condition (f := fixedPsiProjection R r) (g := ProjectiveSpace.toSpec R _))
  change (fullBoundaryStructure R V) (fixedPsiBoundaryToOriginal R r V x) ∈
    PrimeSpectrum.basicOpen r
  simp only [Scheme.Hom.comp_apply] at h hp
  change (ProjectiveSpace.toSpec R _)
    ((fullNeighborhoodBoundaryMap R V) (fixedPsiBoundaryToOriginal R r V x)) ∈ _
  rw [← h, ← hp]
  have hm := (pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)
    (fixedPsiBoundaryMap R r V x)).property
  have hle : fixedPsiSource R r ≤
      Scheme.Hom.boundaryLineProjection R ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
    rw [fixedPsiSource_eq]
    exact inf_le_right
  exact hle hm

def fixedPsiBoundaryPrincipalMap : fixedPsiBoundary R V r ⟶
    (fullBoundaryPrincipalOpen R V r).toScheme :=
  IsOpenImmersion.lift (fullBoundaryPrincipalOpen R V r).ι
    (fixedPsiBoundaryToOriginal R r V) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact fixedPsiBoundaryToOriginal_mem R r V x)

@[reassoc (attr := simp)] lemma fixedPsiBoundaryPrincipalMap_ι :
    fixedPsiBoundaryPrincipalMap R r V ≫ (fullBoundaryPrincipalOpen R V r).ι =
      fixedPsiBoundaryToOriginal R r V := IsOpenImmersion.lift_fac _ _ _

abbrev fixedPsiSerreTwist (n : ℕ) :=
  (Scheme.Modules.pullback (fixedPsiProjectiveIso R r).hom).obj
    (ProjectiveSpace.twistingSheaf Γ((fixedPsiSource R r).toScheme, ⊤)
      (ULift.{u} (Fin 2)) (n : ℤ))

def fixedPsiBoundaryTwistIso (n : ℕ)
    (e : (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    (Scheme.Modules.pullback (fixedPsiBoundaryMap R r V)).obj
      (fixedPsiSerreTwist R r n) ≅
        SheafOfModules.unit (fixedPsiBoundary R V r).ringCatSheaf :=
  (Scheme.Modules.pullback (fixedPsiBoundaryMap R r V)).mapIso
    (fixedPsiOriginalTwistIso R r (n : ℤ)) ≪≫
  (pullbackComp (fixedPsiBoundaryMap R r V) (pullback.snd _ _)).app _ ≪≫
  (pullbackCongr (by rw [fixedPsiBoundaryToOriginal_fac,
    ← fixedPsiBoundaryPrincipalMap_ι R r V, Category.assoc])).app _ ≪≫
  (pullbackComp (fixedPsiBoundaryPrincipalMap R r V)
    ((fullBoundaryPrincipalOpen R V r).ι ≫ fullNeighborhoodBoundaryMap R V)).symm.app _ ≪≫
  (Scheme.Modules.pullback (fixedPsiBoundaryPrincipalMap R r V)).mapIso e ≪≫
  pullbackUnitIso _
end AlgebraicGeometry.RelativeProjectiveLine
