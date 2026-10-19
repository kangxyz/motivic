module
import Motivic.AlgebraicGeometry.Correspondences.Pencils.NormalizedCurve.CorrectingEndpoints
/-! Direct consumer of the compact actual endpoint statement. -/
set_option linter.hashCommand false
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
universe u
example {k : Type u} [Field k] {X T V Y : SmoothSite (Spec (.of k))}
    (f : X ⟶ T) (g : X ⟶ V) (j : X ⟶ Y) (h : HasCorrectingEndpoints f g j) :
    ∃ (lam : Cor.mk T ⟶ Cor.mk Y) (psi : Cor.mk V ⟶ Cor.mk Y)
      (alpha : Cor.mk (SmoothSite.a1Cylinder (.of k) X) ⟶ Cor.mk Y),
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 0) ≫ alpha =
        (Cor.graphFunctor k).map j ∧
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) X 1) ≫ alpha =
        (Cor.graphFunctor k).map f ≫ lam - (Cor.graphFunctor k).map g ≫ psi := h
#print axioms AlgebraicGeometry.Scheme.AffineLineEtaleCompactification.has_actualCorrectingEndpoints
