module
public import Motivic.Aglib.RingTheory.NoetherNormalization.FiniteElimination.IteratedDifferential

/-! # An actual polynomial presentation retaining specified original functions

Append the chosen differential coordinates to finite algebra generators. The
resulting presentation is surjective, and its last coordinates are exactly the
original functions, not an independently selected presentation.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace ParameterizedNoetherNormalization

/-- The original algebra generators precede the retained differential coordinates. -/
def headCoordinate (d e : ℕ) (j : Fin e) : Fin (d + e) := ⟨j.val, by omega⟩

/-- A finite-type algebra has an actual surjective polynomial presentation whose
last coordinates are any prescribed finite family of original elements. -/
theorem exists_surjective_presentation_with_tail_coordinates
    (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (d : ℕ) (g : Fin d → R) :
    ∃ e, ∃ θ : MvPolynomial (Fin (d + e)) k →ₐ[k] R,
      Function.Surjective θ ∧ ∀ j, θ (X (tailCoordinate d e j)) = g j := by
  classical
  obtain ⟨e, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k R)
  let x : Fin (d + e) → R := fun j =>
    if h : j.val < e then q (X ⟨j.val, h⟩) else g ⟨j.val - e, by omega⟩
  let θ : MvPolynomial (Fin (d + e)) k →ₐ[k] R := MvPolynomial.aeval x
  have hhead : θ.comp (MvPolynomial.rename (headCoordinate d e)) = q := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [θ, x, headCoordinate]
  refine ⟨e, θ, ?_, ?_⟩
  · intro y
    obtain ⟨p, hp⟩ := hq y
    exact ⟨MvPolynomial.rename (headCoordinate d e) p,
      (AlgHom.congr_fun hhead p).trans hp⟩
  · intro j
    simp [θ, x, tailCoordinate]

end ParameterizedNoetherNormalization
