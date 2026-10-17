module

public import Motivic.Aglib.RingTheory.BoundaryOneRationalCylinder
public import Motivic.AlgebraicGeometry.AffineSimplexUnitComplex

/-! # All-degree boundary-one acyclicity on actual relative simplex schemes

The comparison retains the original Cartesian products and every face map.
It does not assert that this coefficient is already the correspondence kernel.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicTopology

universe u

namespace Motivic.AlgebraicSimplex

open Polynomial.BoundaryOneRationalFunctions

variable (R : Type u) [CommRing R]

/-- Global rational functions on actual simplex schemes agree naturally with
rational functions in their actual coordinate rings. -/
def schemeBoundaryOneSimplicialIso :
    SingularComplex.simplicial (cosimplicialScheme R) (Scheme.Γ ⋙ functor) ≅
      SingularComplex.simplicial (algebraicSimplex R) ringPresheaf :=
  NatIso.ofComponents (fun n =>
    functor.mapIso (Scheme.ΓSpecIso (.of (CoordinateRing R n.unop.len)))) (by
      intro n m f
      change functor.map _ ≫ functor.map _ = functor.map _ ≫ functor.map _
      rw [← functor.map_comp, ← functor.map_comp]
      exact congrArg functor.map (Scheme.ΓSpecIso_naturality ((simplicialRing R).map f)))

/-- The actual scheme coefficient complex has zero homology in every degree. -/
theorem isZero_homology_schemeBoundaryOne (n : ℕ) :
    IsZero ((SingularComplex.obj (cosimplicialScheme R) (Scheme.Γ ⋙ functor)).homology n) := by
  let e := (alternatingFaceMapComplex AddCommGrpCat).mapIso (schemeBoundaryOneSimplicialIso R)
  exact (isZero_homology_algebraicSimplex R n).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e)

variable {k : Type u} [CommRing k]

/-- The acyclic coefficient complex is on the literal relative products
Δ over k times Spec R, not merely on an un-compared affine replacement. -/
theorem isZero_homology_affineRelativeBoundaryOne (c : k →+* R) (n : ℕ) :
    IsZero ((SingularComplex.obj (affineRelativeSimplex c)
      (Scheme.Γ ⋙ functor)).homology n) := by
  let e := (alternatingFaceMapComplex AddCommGrpCat).mapIso
    (isoWhiskerRight (NatIso.op (affineRelativeSimplexIso c).symm) (Scheme.Γ ⋙ functor))
  exact (isZero_homology_schemeBoundaryOne R n).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e)

end Motivic.AlgebraicSimplex
