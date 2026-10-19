module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CanonicalFrame
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.Finite
/-! # One actual base neighborhood supplies the graph frame and all boundary twists -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Both frame families are constructed on the same actual base neighborhood. The
finite projective boundary may be nonreduced or nonflat, and the degree is chosen later. -/
theorem exists_simultaneous_boundary_frames
    (R : Type u) [CommRing R] (ι : Type u)
    {X Z D : Scheme.{u}} [IsAffine X]
    (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (z : Z ⟶ X) [IsFinite (z ≫ q)]
    (g : D ⟶ ProjectiveSpace R ι) [IsFinite (g ≫ toSpec R ι)] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ V : (Spec (.of R)).Opens, IsAffineOpen V ∧ q x ∈ V ∧
    ∃ h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U,
      IsAffineOpen (boundaryBaseSourceOpen q U V) ∧
      Nonempty (SheafOfModules.unit
        (pullback (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V)).ringCatSheaf ≅
        idealModule (boundaryGraphTarget (boundaryBaseSourceProjection q U V)
          (boundaryBaseLift q z U V h))) ∧
      Nonempty ((n : ℕ) →
        (Modules.pullback (((g ≫ toSpec R ι) ⁻¹ᵁ V).ι ≫ g)).obj
          (twistingSheaf R ι (n : ℤ)) ≅
            SheafOfModules.unit ((g ≫ toSpec R ι) ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  obtain ⟨U, hU, hx, V₁, hx₁, hz, ⟨e⟩⟩ :=
    exists_affine_relativeBoundaryFrame_over_base_neighborhood q z x
  let f := g ≫ toSpec R ι
  let L := pullbackLineBundle g (twistingLineBundle R ι 1)
  obtain ⟨V₂, hx₂, ⟨e₂⟩⟩ := exists_base_open_unitIso_of_isFinite f (q x) L
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset
    (show q x ∈ V₁ ⊓ V₂ from ⟨hx₁, hx₂⟩)
  let h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U := fun t ht => hz t (hVV ht).1
  let W := f ⁻¹ᵁ V
  let eW := restrictUnitIsoOfLE L.val
    (show W ≤ f ⁻¹ᵁ V₂ from fun _ ht => (hVV ht).2) e₂
  let e₁ : (Modules.pullback (W.ι ≫ g)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι g).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback g).obj (twistingSheaf R ι 1)) ≪≫ eW
  exact ⟨U, hU, hx, V, hV, hxV, h, boundaryBaseSourceOpen_affine q U V hU hV,
    ⟨boundaryBaseCanonicalFrame q z U V h e⟩,
    ⟨CoherentGraph.positiveTwistUnitIso R ι (W.ι ≫ g) e₁⟩⟩
end AlgebraicGeometry.Scheme.Hom
