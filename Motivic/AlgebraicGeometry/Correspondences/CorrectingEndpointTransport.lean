module
public import Motivic.AlgebraicGeometry.Correspondences.DiagonalSignedPencilProducer
/-! # Transport of actual correcting correspondences to the original cover objects -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic

/-- Native cylinder naturality transports both literal endpoints through the actual
source/target comparison maps. No surjectivity on newly restricted sections is used. -/
theorem correctingEndpoints_transport {k : Type u} [Field k]
    {X T V Y X' T' V' Y' : SmoothSite (Spec (.of k))}
    (f : X ⟶ T) (g : X ⟶ V) (j : X ⟶ Y)
    (f' : X' ⟶ T') (g' : X' ⟶ V') (j' : X' ⟶ Y')
    (eX : X' ⟶ X) (eT : T' ⟶ T) (eV : V' ⟶ V) (eY : Y ⟶ Y')
    (hf : f' ≫ eT = eX ≫ f) (hg : g' ≫ eV = eX ≫ g)
    (hj : eX ≫ j ≫ eY = j')
    (lam : Cor.mk T ⟶ Cor.mk Y) (psi : Cor.mk V ⟶ Cor.mk Y)
    (alpha : Cor.mk (SmoothSite.a1Cylinder (.of k) X) ⟶ Cor.mk Y)
    (h0 : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 0) ≫ alpha =
      (Cor.graphFunctor k).map j)
    (h1 : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 1) ≫ alpha =
      (Cor.graphFunctor k).map f ≫ lam - (Cor.graphFunctor k).map g ≫ psi) :
    let lam' := (Cor.graphFunctor k).map eT ≫ lam ≫ (Cor.graphFunctor k).map eY
    let psi' := (Cor.graphFunctor k).map eV ≫ psi ≫ (Cor.graphFunctor k).map eY
    let alpha' := (Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) eX) ≫
      alpha ≫ (Cor.graphFunctor k).map eY
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X' 0) ≫ alpha' =
      (Cor.graphFunctor k).map j' ∧
    (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X' 1) ≫ alpha' =
      (Cor.graphFunctor k).map f' ≫ lam' - (Cor.graphFunctor k).map g' ≫ psi' := by
  have hnat (c : k) :
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X' c) ≫
        (Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) eX) =
      (Cor.graphFunctor k).map eX ≫
        (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X c) := by
    rw [← Functor.map_comp, SmoothSite.a1Section_naturality, Functor.map_comp]
  have hmove (c : k) :
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X' c) ≫
          ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) eX) ≫
            alpha ≫ (Cor.graphFunctor k).map eY) =
        (Cor.graphFunctor k).map eX ≫
          ((Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X c) ≫ alpha) ≫
            (Cor.graphFunctor k).map eY := by
    rw [← Category.assoc _ _ (alpha ≫ (Cor.graphFunctor k).map eY), hnat]
    simp only [Category.assoc]
  dsimp only
  constructor
  · rw [hmove, h0, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
  · rw [hmove, h1, Preadditive.sub_comp, Preadditive.comp_sub]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← hf, Functor.map_comp,
      ← Functor.map_comp_assoc, ← hg, Functor.map_comp]
    simp only [Category.assoc]
end Motivic
