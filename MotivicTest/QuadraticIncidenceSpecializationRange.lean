module
import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceSpecializationRange
import Lean.Util.CollectAxioms

/-! # The original incidence image is contained in its actual specialization

The original coefficient algebra already maps through the intermediate field.
Together with preservation of the literal parameter coordinates, this implies
that every original incidence element lies in the specialized image.
-/
noncomputable section
open _root_.MvPolynomial Module TensorProduct KaehlerDifferential
universe u v
namespace QuadraticIncidence
variable (k R A K E : Type u) [CommRing k] [CommRing R] [CommRing A]
  [CommRing K] [CommRing E] [Algebra k R] [Algebra R A]
  [Algebra R K] [Algebra A K] [Algebra R E] [Algebra A E] [Algebra K E]
  [IsScalarTower R A E] [IsScalarTower R K E]
  [IsScalarTower A K E] [Algebra.Smooth k R]
  {σ : Type v} [Fintype σ]

example
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (h : CoordinateRing k R A g a d w →ₐ[A] E)
    (c : CoordinateRing k R A g a d w) :
    h c ∈ (specialize k R A K E g a d w h).range :=
  image_mem_specialize_range k R A K E g a d w h c

open Lean in
run_cmd do
  for dependency in ← collectAxioms ``image_mem_specialize_range do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "Unsupported assumption {dependency}"
  logInfo "Actual incidence specialization image: standard foundations only."

end QuadraticIncidence
