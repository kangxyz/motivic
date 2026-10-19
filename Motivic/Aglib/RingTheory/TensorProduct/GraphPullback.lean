/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.TensorProduct.EtaleGraph
public import Motivic.Aglib.RingTheory.TensorProduct.EtaleDiagonal

/-!
# Literal diagonal equations pulled back to an arbitrary graph

The actual map `B ⊗[R] B → A ⊗[R] B` induced by `B → A` carries each
diagonal coordinate difference to the corresponding graph equation. The same
identity holds on local rings at corresponding diagonal and graph points.
Consequently the image of the very same diagonal list is regular, even when
the graph map is nonflat. This is stronger than merely finding some unrelated
regular generating list for the graph kernel.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open RingTheory.Sequence

namespace Algebra.TensorProduct.PolynomialGraph

variable (R σ A B : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra (MvPolynomial σ R) B] [IsScalarTower R (MvPolynomial σ R) B]
  (f : B →ₐ[MvPolynomial σ R] A)

/-- The actual ambient ring map pulling the diagonal back to the graph. -/
def diagonalPullback : B ⊗[R] B →ₐ[R] A ⊗[R] B :=
  Algebra.TensorProduct.map (f.restrictScalars R) (AlgHom.id R B)

@[simp]
theorem diagonalPullback_tmul (b₁ b₂ : B) :
    diagonalPullback R σ A B f (b₁ ⊗ₜ[R] b₂) = f b₁ ⊗ₜ[R] b₂ := by
  simp [diagonalPullback]

@[simp]
theorem diagonalPullback_difference (i : σ) :
    diagonalPullback R σ A B f (RelativePolynomial.difference R σ B i) =
      difference R σ A B i := by
  simp [RelativePolynomial.difference, difference]

/-- The actual graph evaluation intertwines the diagonal multiplication map. -/
theorem evaluation_diagonalPullback (x : B ⊗[R] B) :
    evaluation R σ A B f (diagonalPullback R σ A B f x) =
      f (RelativePolynomial.multiplication R B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [RelativePolynomial.multiplication]
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- The inverse image of the actual graph prime is the corresponding diagonal prime. -/
theorem comap_graphPrime (p : Ideal A) :
    (graphPrime R σ A B f p).comap (diagonalPullback R σ A B f).toRingHom =
      RelativePolynomial.diagonalPrime R B (p.comap (f : B →+* A)) := by
  ext x
  change evaluation R σ A B f (diagonalPullback R σ A B f x) ∈ p ↔
    f (RelativePolynomial.multiplication R B x) ∈ p
  rw [evaluation_diagonalPullback]

/-- The actual localized ambient map from a diagonal point to its graph pullback. -/
def localDiagonalPullback (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime
      (RelativePolynomial.diagonalPrime R B (p.comap (f : B →+* A))) →+*
        Localization.AtPrime (graphPrime R σ A B f p) :=
  Localization.localRingHom _ _ (diagonalPullback R σ A B f).toRingHom
    (comap_graphPrime R σ A B f p).symm

@[simp]
theorem localDiagonalPullback_algebraMap (p : Ideal A) [p.IsPrime] (x : B ⊗[R] B) :
    localDiagonalPullback R σ A B f p (algebraMap _ _ x) =
      algebraMap (A ⊗[R] B) (Localization.AtPrime (graphPrime R σ A B f p))
        (diagonalPullback R σ A B f x) :=
  Localization.localRingHom_to_map _ _ _ _ x

@[simp]
theorem localDiagonalPullback_localDifference (p : Ideal A) [p.IsPrime] (i : σ) :
    localDiagonalPullback R σ A B f p
      (RelativePolynomial.localDifference R σ B (p.comap (f : B →+* A)) i) =
        localDifference R σ A B f p i := by
  exact (localDiagonalPullback_algebraMap R σ A B f p
    (RelativePolynomial.difference R σ B i)).trans
      (congrArg (algebraMap (A ⊗[R] B) _) (diagonalPullback_difference R σ A B f i))

/-- The same literal diagonal equation list becomes the graph equation list. -/
theorem map_localDiagonalDifferences (p : Ideal A) [p.IsPrime] (l : List σ) :
    (l.map (RelativePolynomial.localDifference R σ B (p.comap (f : B →+* A)))).map
      (localDiagonalPullback R σ A B f p) = l.map (localDifference R σ A B f p) := by
  simp only [List.map_map, Function.comp_def, localDiagonalPullback_localDifference]

/-- The image of the actual diagonal list is regular despite a possibly nonflat pullback. -/
theorem isRegular_map_localDiagonalDifferences [Module.Flat (MvPolynomial σ R) B]
    (p : Ideal A) [p.IsPrime] (l : List σ) (hl : l.Nodup) :
    IsRegular (Localization.AtPrime (graphPrime R σ A B f p))
      ((l.map (RelativePolynomial.localDifference R σ B (p.comap (f : B →+* A)))).map
        (localDiagonalPullback R σ A B f p)) := by
  rw [map_localDiagonalDifferences]
  exact isRegular_localDifferences R σ A B f p l hl

set_option backward.isDefEq.respectTransparency false in
/-- The original diagonal list acts weakly regularly on the actual graph ambient ring. -/
theorem isWeaklyRegular_diagonalList_on_graph [Module.Flat (MvPolynomial σ R) B]
    (p : Ideal A) [p.IsPrime] (l : List σ) (hl : l.Nodup) :
    letI := (localDiagonalPullback R σ A B f p).toAlgebra
    IsWeaklyRegular (Localization.AtPrime (graphPrime R σ A B f p))
      (l.map (RelativePolynomial.localDifference R σ B (p.comap (f : B →+* A)))) := by
  let := (localDiagonalPullback R σ A B f p).toAlgebra
  exact (isWeaklyRegular_map_algebraMap_iff
    (Localization.AtPrime (graphPrime R σ A B f p))
    (Localization.AtPrime (graphPrime R σ A B f p)) _).mp
      (isRegular_map_localDiagonalDifferences R σ A B f p l hl).toIsWeaklyRegular

/-- The very same mapped diagonal list generates the actual local graph kernel. -/
theorem ker_localEvaluation_eq_mapped_diagonalList [Algebra.Etale (MvPolynomial σ R) B]
    (p : Ideal A) [p.IsPrime] (l : List σ) (hcover : ∀ i, i ∈ l) :
    RingHom.ker (localEvaluation R σ A B f p) =
      Ideal.ofList
        ((l.map (RelativePolynomial.localDifference R σ B (p.comap (f : B →+* A)))).map
          (localDiagonalPullback R σ A B f p)) := by
  rw [map_localDiagonalDifferences]
  exact ker_localEvaluation_eq_ofList R σ A B f p l hcover

end Algebra.TensorProduct.PolynomialGraph
