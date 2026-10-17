module
public import Motivic.AlgebraicGeometry.Correspondences.CorrectingEndpointTransport
/-! Direct consumer of the literal correcting endpoint construction. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace Motivic
example {k : Type u} [Field k]
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
      (Cor.graphFunctor k).map f ≫ lam - (Cor.graphFunctor k).map g ≫ psi) :=
  correctingEndpoints_transport f g j f' g' j' eX eT eV eY hf hg hj lam psi alpha h0 h1
#print axioms correctingEndpoints_transport
end Motivic
