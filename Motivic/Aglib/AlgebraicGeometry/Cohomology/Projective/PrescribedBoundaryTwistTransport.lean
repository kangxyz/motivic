module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PrincipalBoundaryTwists
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteBoundaryGraphSections
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.TwistBaseChangeIsomorphism
/-! # Native relative-twist transport of the same original boundary frame -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- Original prescribed boundary units trivialize the actual relative twist on the whole
base-changed boundary, with its given coefficient-map square and without shrinking the source. -/
def prescribedBoundaryRelativeTwistIso (k R : Type u) [CommRing k] [CommRing R]
    (f : k →+* R) (ι : Type u) {Z W : Scheme.{u}}
    (g : Z ⟶ ProjectiveSpace k ι)
    (b : W ⟶ Z) (a : W ⟶ ProjectiveSpace R ι)
    (ha : a ≫ ProjectiveSpace.map f ι = b ≫ g) (n : ℕ)
    (e : (Modules.pullback g).obj (twistingSheaf k ι (n : ℤ)) ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback a).obj (twistingSheaf R ι (n : ℤ)) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  (Modules.pullback a).mapIso (twistingBaseChangeIso f ι (n : ℤ)).symm ≪≫
    (Modules.pullbackComp a (ProjectiveSpace.map f ι)).app (twistingSheaf k ι (n : ℤ)) ≪≫
    (Modules.pullbackCongr ha).app (twistingSheaf k ι (n : ℤ)) ≪≫
    (Modules.pullbackComp b g).symm.app (twistingSheaf k ι (n : ℤ)) ≪≫
      (Modules.pullback b).mapIso e ≪≫ pullbackUnitIso b

/-- Transport the original chosen frame to the literal tensor coefficient on the whole boundary. -/
def prescribedBoundaryRelativeCoefficientIso (k R : Type u) [CommRing k] [CommRing R]
    (f : k →+* R) (ι : Type u) {Z W C : Scheme.{u}}
    (g : Z ⟶ ProjectiveSpace k ι)
    (b : W ⟶ Z) (a : C ⟶ ProjectiveSpace R ι) (z : W ⟶ C)
    (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ g) (n : ℕ)
    (e : (Modules.pullback g).obj (twistingSheaf k ι (n : ℤ)) ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    (moduleTensorLeftFunctor W
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (n : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  boundaryTwistCoefficientIso a z (twistingSheaf R ι (n : ℤ)) ≪≫
    prescribedBoundaryRelativeTwistIso k R f ι g b (z ≫ a) ha n e


end AlgebraicGeometry.Scheme.CoherentGraph
