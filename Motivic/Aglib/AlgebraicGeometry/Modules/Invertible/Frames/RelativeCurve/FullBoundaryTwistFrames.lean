module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.Serre
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.PrescribedTransport
/-! # Both original Serre coefficients come from one frame on the full target boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A Z C D : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)

abbrev fullTargetBoundaryMap : D ⨿ Z ⟶ C := coprod.desc d (s ≫ j)

def lambdaBoundaryToFullTarget :
    (pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)) ⟶ D ⨿ Z :=
  coprod.desc (pullback.snd _ _ ≫ coprod.inl) (pullback.snd _ _ ≫ coprod.inr)

@[reassoc]
theorem lambdaBoundaryToFullTarget_map :
    lambdaBoundaryToFullTarget π j s d ≫ fullTargetBoundaryMap j s d =
      Hom.fullBoundaryProductMap π j d s ≫ pullback.snd (j ≫ π) π := by
  apply coprod.hom_ext
  · simp only [lambdaBoundaryToFullTarget, fullTargetBoundaryMap, Hom.fullBoundaryProductMap,
      coprod.inl_desc_assoc, Category.assoc, coprod.inl_desc, Hom.infinityProductMap]
    exact pullback.condition.symm
  · simp [lambdaBoundaryToFullTarget, fullTargetBoundaryMap, Hom.fullBoundaryProductMap,
      Hom.graphBoundaryRestriction]

def psiBoundaryToFullTarget :
    (pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)) ⟶ D ⨿ Z :=
  coprod.desc (pullback.snd _ _ ≫ coprod.inl) (pullback.snd _ _ ≫ coprod.inr)

@[reassoc]
theorem psiBoundaryToFullTarget_map :
    psiBoundaryToFullTarget q π a z d ≫ fullTargetBoundaryMap j s d =
      psiBoundaryInclusion q π j p hq a z s hs d ≫ pullback.snd (a ≫ q) π := by
  apply coprod.hom_ext
  · simp only [psiBoundaryToFullTarget, fullTargetBoundaryMap, psiBoundaryInclusion,
      coprod.inl_desc_assoc, Category.assoc, coprod.inl_desc]
    exact pullback.condition.symm
  · simp [psiBoundaryToFullTarget, fullTargetBoundaryMap, psiBoundaryInclusion,
      psiZeroInclusion]

/-- The native coefficient of every affine-source Serre twist is pulled from the same
original whole-target boundary frame; neither source is shrunk to choose a frame. -/
def affineBoundaryTwistFrames_of_target
    (R : Type u) [CommRing R] (ι : Type u)
    {T C W D : Scheme.{u}} [IsAffine T]
    (b : T ⟶ Spec (.of R)) (f : C ⟶ ProjectiveSpace R ι)
    (z : W ⟶ pullback b (f ≫ toSpec R ι)) (d : D ⟶ C)
    (v : W ⟶ D) (hv : z ≫ pullback.snd b (f ≫ toSpec R ι) = v ≫ d)
    (e : ∀ n : ℕ, (Modules.pullback (d ≫ f)).obj (twistingSheaf R ι (n : ℤ)) ≅
      SheafOfModules.unit D.ringCatSheaf) :
    affineBoundaryTwistFrames R ι b f z := fun n =>
  CoherentGraph.prescribedBoundaryRelativeCoefficientIso R Γ(T, ⊤)
    (ConstantCurve.affineSourceCoefficientMap R b) ι (d ≫ f) v
    (ConstantCurve.affineSourceToProjectiveSpace R ι b f) z (by
      rw [Category.assoc, ConstantCurve.affineSourceToProjectiveSpace_map,
        ← Category.assoc, hv, Category.assoc]) n (e n)
/-- Lambda uses the same original full-target frame. -/
def lambdaTwistFrames_of_fullTargetFrame
    (R : Type u) [CommRing R] (ι : Type u)
    {Y C D Z : Scheme.{u}} [IsAffine Y]
    (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C) (s : Z ⟶ Y) (d : D ⟶ C)
    (e : ∀ n : ℕ, (Modules.pullback (fullTargetBoundaryMap j s d ≫ f)).obj
      (twistingSheaf R ι (n : ℤ)) ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf) :
    affineBoundaryTwistFrames R ι (j ≫ (f ≫ toSpec R ι)) f
      (Hom.fullBoundaryProductMap (f ≫ toSpec R ι) j d s) :=
  affineBoundaryTwistFrames_of_target R ι (j ≫ (f ≫ toSpec R ι)) f
    (Hom.fullBoundaryProductMap (f ≫ toSpec R ι) j d s) (fullTargetBoundaryMap j s d)
    (lambdaBoundaryToFullTarget (f ≫ toSpec R ι) j s d)
    (lambdaBoundaryToFullTarget_map (f ≫ toSpec R ι) j s d).symm e

/-- Psi uses that identical original frame on its unchanged affine source. -/
def psiTwistFrames_of_fullTargetFrame
    (R : Type u) [CommRing R] (ι : Type u)
    {X Y A C D Z : Scheme.{u}} [IsAffine A]
    (q : X ⟶ Spec (.of R)) (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C)
    (p : Y ⟶ X) (hq : j ≫ (f ≫ toSpec R ι) = p ≫ q) (a : A ⟶ X)
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C)
    (e : ∀ n : ℕ, (Modules.pullback (fullTargetBoundaryMap j s d ≫ f)).obj
      (twistingSheaf R ι (n : ℤ)) ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf) :
    affineBoundaryTwistFrames R ι (a ≫ q) f
      (psiBoundaryInclusion q (f ≫ toSpec R ι) j p hq a z s hs d) :=
  affineBoundaryTwistFrames_of_target R ι (a ≫ q) f
    (psiBoundaryInclusion q (f ≫ toSpec R ι) j p hq a z s hs d) (fullTargetBoundaryMap j s d)
    (psiBoundaryToFullTarget q (f ≫ toSpec R ι) a z d)
    (psiBoundaryToFullTarget_map q (f ≫ toSpec R ι) j p hq a z s hs d).symm e
end AlgebraicGeometry.Scheme.RelativeCurvePencil
