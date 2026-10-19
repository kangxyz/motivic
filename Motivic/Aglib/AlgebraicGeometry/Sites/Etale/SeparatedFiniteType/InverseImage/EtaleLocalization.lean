module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Actual étale localization of the finite-type Nisnevich site

For an étale separated finite-type map, the genuine inverse image is restriction
along postcomposition. This is proved from the actual site adjunction, not assumed
for arbitrary closed morphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (p : T ⟶ S)
  [Etale p] [IsSeparated p] [QuasiCompact p]

/-- Postcomposition retains each actual étale neighborhood scheme. -/
def etalePostcompose : EtaleSeparatedFiniteType T ⥤ EtaleSeparatedFiniteType S :=
  MorphismProperty.Over.map ⊤ (P := etaleSeparatedFiniteType)
    (f := p) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

instance etalePostcompose_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (etalePostcompose p) := by
  have : PreservesLimitsOfShape WalkingCospan
      (etalePostcompose p ⋙ forgetScheme S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (forgetScheme T))
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (etalePostcompose p) (forgetScheme S)

instance etalePostcompose_isContinuous :
    (etalePostcompose p).IsContinuous (nisnevichTopology T) (nisnevichTopology S) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  simp only [nisnevichPrecoverage, ← Precoverage.comap_comp]
  exact le_rfl

/-- The scheme-level postcomposition/base-change adjunction. -/
def etalePostcomposeAdjunction : etalePostcompose p ⊣ baseChange p :=
  MorphismProperty.Over.mapPullbackAdj etaleSeparatedFiniteType ⊤ p
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ trivial

/-- Literal restriction of sheaves along the étale neighborhood inclusion. -/
def etaleRestriction :
    Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1} :=
  (etalePostcompose p).sheafPushforwardContinuous _ _ _

/-- Restriction is left adjoint to actual direct image for an étale map. -/
def etaleRestrictionAdjunction : etaleRestriction p ⊣ directImage p :=
  ((etalePostcomposeAdjunction p).op.whiskerLeft (C := AddCommGrpCat.{u + 1})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

/-- Comparison with the previously defined, genuine left-adjoint inverse image. -/
def inverseImageEtaleIso : inverseImage p ≅ etaleRestriction p :=
  (imageAdjunction p).leftAdjointUniq (etaleRestrictionAdjunction p)

instance etaleRestriction_isLeftAdjoint : (etaleRestriction p).IsLeftAdjoint :=
  (etaleRestrictionAdjunction p).isLeftAdjoint

instance etaleRestriction_preservesColimits : PreservesColimits (etaleRestriction p) :=
  inferInstance

section Composition

variable {R : Scheme.{u}} (f : R ⟶ T) (g : T ⟶ S)

/-- Direct image composition uses the actual iterated scheme pullback comparison. -/
def directImageCompIso : directImage f ⋙ directImage g ≅ directImage (f ≫ g) := by
  let e : baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
    MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤) f g
  exact Functor.sheafPushforwardContinuousComp' e.symm
    AddCommGrpCat.{u + 1} (nisnevichTopology S) (nisnevichTopology T)
    (nisnevichTopology R)

/-- Composition for the genuine closed or arbitrary inverse image. -/
def inverseImageCompIso : inverseImage g ⋙ inverseImage f ≅ inverseImage (f ≫ g) :=
  (((imageAdjunction g).comp (imageAdjunction f)).ofNatIsoRight
    (directImageCompIso f g)).leftAdjointUniq (imageAdjunction (f ≫ g))

end Composition

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
