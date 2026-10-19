module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ParameterProduct
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Motivic.Cohomology.A1.Contraction.Relative
public import Motivic.Transfers.Presheaf.ContractionSheaf

/-! # The literal cylinder neighborhoods used by the contraction boundary map -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- The literal étale affine-line cylinder over a base neighborhood. -/
abbrev cylinderNeighborhood := parameterProduct X (SmoothSite.affineLine (.of k))

/-- The actual pullback of this cylinder to the punctured ambient cylinder. -/
abbrev puncturedNeighborhood :=
  cylinderNeighborhood X ⋙ baseChange (SmoothSite.contractionOpen (.of k) X).left

/-- The actual pullback of the cylinder to the ambient zero section. -/
abbrev zeroNeighborhood :=
  cylinderNeighborhood X ⋙ baseChange (SmoothSite.a1Section (.of k) X 0).left

/-- The punctured neighborhood maps to the original literal Laurent product. -/
def puncturedProjection (V : EtaleSeparatedFiniteType X.left) :
    (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj ((puncturedNeighborhood X).obj V) ⟶
      SmoothSite.torusCylinder (.of k) ((toSmoothSite X).obj V) :=
  SmoothSite.productLift
    ((restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app
        ((cylinderNeighborhood X).obj V) ≫
      (parameterProductUnderlyingIso X (SmoothSite.affineLine (.of k))).hom.app V ≫
      SmoothSite.productFst _ _)
    (toBase (SmoothSite.torusCylinder (.of k) X) ((puncturedNeighborhood X).obj V) ≫
      SmoothSite.productSnd X (SmoothSite.torus (.of k)))

/-- The original affine-line restriction agrees with the actual open pullback projection. -/
theorem puncturedProjection_open (V : EtaleSeparatedFiniteType X.left) :
    puncturedProjection X V ≫
      SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V) =
      (restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app
        ((cylinderNeighborhood X).obj V) ≫
      (parameterProductUnderlyingIso X (SmoothSite.affineLine (.of k))).hom.app V := by
  apply SmoothSite.product_hom_ext
  · simp [puncturedProjection, SmoothSite.contractionOpen]
  · simp only [puncturedProjection, SmoothSite.contractionOpen, Category.assoc,
      SmoothSite.productMap_snd, SmoothSite.productLift_snd_assoc]
    apply MorphismProperty.Over.Hom.ext
    change (pullback.snd ((cylinderNeighborhood X).obj V).hom
        (SmoothSite.contractionOpen (.of k) X).left ≫
        (SmoothSite.productSnd X (SmoothSite.torus (.of k))).left) ≫
        (SmoothSite.torusInAffineLine (.of k)).left =
      pullback.fst ((cylinderNeighborhood X).obj V).hom
        (SmoothSite.contractionOpen (.of k) X).left ≫ 𝟙 _ ≫
        (SmoothSite.productSnd ((toSmoothSite X).obj V) (SmoothSite.affineLine (.of k))).left
    rw [Category.id_comp]
    have h := pullback.condition
      (f := ((cylinderNeighborhood X).obj V).hom)
      (g := (SmoothSite.contractionOpen (.of k) X).left)
    have h' := congrArg (fun a ↦ a ≫ (SmoothSite.productSnd X
      (SmoothSite.affineLine (.of k))).left) h
    have ho := congrArg (fun a ↦ a.left)
      (SmoothSite.productMap_snd (𝟙 X) (SmoothSite.torusInAffineLine (.of k)))
    have hc := congrArg (fun a ↦ a.left)
      (SmoothSite.productMap_snd (toBase X V) (𝟙 (SmoothSite.affineLine (.of k))))
    change (SmoothSite.contractionOpen (.of k) X).left ≫
      (SmoothSite.productSnd X (SmoothSite.affineLine (.of k))).left = _ at ho
    change ((cylinderNeighborhood X).obj V).hom ≫
      (SmoothSite.productSnd X (SmoothSite.affineLine (.of k))).left =
      (SmoothSite.productSnd ((toSmoothSite X).obj V)
        (SmoothSite.affineLine (.of k))).left ≫ 𝟙 _ at hc
    simp only [Category.assoc, ho, hc, Category.comp_id] at h'
    exact h'.symm

/-- The actual affine comparison is natural in the étale base neighborhood. -/
def affineProjection :
    puncturedNeighborhood X ⋙ toSmoothSite (SmoothSite.torusCylinder (.of k) X) ⟶
      toSmoothSite X ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine (.of k)) :=
  Functor.whiskerLeft (cylinderNeighborhood X)
    (restrictionProjection (SmoothSite.contractionOpen (.of k) X)) ≫
    (parameterProductUnderlyingIso X (SmoothSite.affineLine (.of k))).hom

/-- Naturality of the original Laurent restriction on the neighborhood products. -/
theorem puncturedProjection_naturality {V W : EtaleSeparatedFiniteType X.left} (f : V ⟶ W) :
    (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).map
        ((puncturedNeighborhood X).map f) ≫ puncturedProjection X W =
      puncturedProjection X V ≫
        SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 (SmoothSite.torus (.of k))) := by
  apply (cancel_mono (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj W))).mp
  have hn : SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V) ≫
      SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 (SmoothSite.affineLine (.of k))) =
      SmoothSite.productMap ((toSmoothSite X).map f) (𝟙 (SmoothSite.torus (.of k))) ≫
        SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj W) := by
    simp only [SmoothSite.contractionOpen, ← SmoothSite.productMap_comp,
      Category.comp_id, Category.id_comp]
  rw [Category.assoc, puncturedProjection_open, Category.assoc, ← hn,
    ← Category.assoc (puncturedProjection X V), puncturedProjection_open]
  exact (affineProjection X).naturality f

/-- The original zero section lifts a base neighborhood into the true closed pullback. -/
def zeroNeighborhoodLift (V : EtaleSeparatedFiniteType X.left) :
    V ⟶ (zeroNeighborhood X).obj V :=
  MorphismProperty.Over.homMk
    (pullback.lift (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left
      V.hom (by
        exact congrArg (fun a ↦ a.left)
          (SmoothSite.a1Section_naturality (.of k) (toBase X V) 0)))
    (pullback.lift_snd _ _ _)

/-- The lifted zero sections form a natural map of actual small-site functors. -/
def zeroNeighborhoodLiftNat : 𝟭 (EtaleSeparatedFiniteType X.left) ⟶ zeroNeighborhood X where
  app := zeroNeighborhoodLift X
  naturality V W f := by
    have hf (V : EtaleSeparatedFiniteType X.left) :
        (zeroNeighborhoodLift X V).left ≫
          pullback.fst ((cylinderNeighborhood X).obj V).hom
            (SmoothSite.a1Section (.of k) X 0).left =
          (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left :=
      pullback.lift_fst _ _ _
    have hs (V : EtaleSeparatedFiniteType X.left) :
        (zeroNeighborhoodLift X V).left ≫
          pullback.snd ((cylinderNeighborhood X).obj V).hom
            (SmoothSite.a1Section (.of k) X 0).left = V.hom :=
      pullback.lift_snd _ _ _
    have hmf : ((zeroNeighborhood X).map f).left ≫
        pullback.fst ((cylinderNeighborhood X).obj W).hom
          (SmoothSite.a1Section (.of k) X 0).left =
        pullback.fst ((cylinderNeighborhood X).obj V).hom
          (SmoothSite.a1Section (.of k) X 0).left ≫
          (SmoothSite.productMap ((toSmoothSite X).map f)
            (𝟙 (SmoothSite.affineLine (.of k)))).left :=
      pullback.lift_fst _ _ _
    have hms : ((zeroNeighborhood X).map f).left ≫
        pullback.snd ((cylinderNeighborhood X).obj W).hom
          (SmoothSite.a1Section (.of k) X 0).left =
        pullback.snd ((cylinderNeighborhood X).obj V).hom
          (SmoothSite.a1Section (.of k) X 0).left :=
      pullback.lift_snd _ _ _
    apply MorphismProperty.Over.Hom.ext
    change f.left ≫ (zeroNeighborhoodLift X W).left =
      (zeroNeighborhoodLift X V).left ≫ ((zeroNeighborhood X).map f).left
    apply pullback.hom_ext
    · rw [Category.assoc, hf, Category.assoc, hmf, ← Category.assoc, hf]
      exact (congrArg (fun a ↦ a.left)
        (SmoothSite.a1Section_naturality (.of k) ((toSmoothSite X).map f) 0)).symm
    · rw [Category.assoc, hs, Category.assoc, hms, hs, MorphismProperty.Over.w]

end Motivic.FiniteEtaleSite
