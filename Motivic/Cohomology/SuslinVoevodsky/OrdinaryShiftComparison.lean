/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.Hypercohomology
public import Motivic.Aglib.Algebra.Homology.Embedding.MapExtension

/-! # The original motivic sheaf complex as signed ordinary singular chains -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Forgetting transfers, zero extension, and the actual signed motivic shift
commute by full complex isomorphisms. No commutation of singular chains with
sheafification of their coefficient is used. -/
def motivicSheafComplexOrdinaryShiftIso (q : ℕ) :
    motivicSheafComplex k q ≅
      ((SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (cosimplicialSmoothSite k)
        ((toPresheaf k).obj (reducedTorus k q))).extend
          (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧ := by
  let F := SheafWithTransfers.toSheaf k
  let G := nisnevichSheafify k
  let e := ComplexShape.embeddingUpIntLE 0
  let K := singularComplex (reducedTorus k q)
  exact (F.mapCochainComplexShiftIso (-(q : ℤ))).app
      ((G.mapHomologicalComplex (.up ℤ)).obj (K.extend e)) ≪≫
    (shiftFunctor _ (-(q : ℤ))).mapIso
      (_root_.HomologicalComplex.MapExtension.iso (G ⋙ F) e K ≪≫
        (e.extendFunctor _).mapIso (singularSheafOrdinaryIso k (reducedTorus k q)))

end Motivic
