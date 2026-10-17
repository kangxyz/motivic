module
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion
public import Motivic.Aglib.RingTheory.Kaehler.SimultaneousResidueCoordinates

/-! # Actual simultaneous polynomial coordinates over an infinite field

The same original functions define maps étale near all selected primes.
No rational-point, chosen chart, or compatibility assumption is supplied.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u v w
namespace Algebra

/-- A smooth affine algebra admits one set of original polynomial coordinates
étale locally at finitely many primes of equal cotangent dimension.
This is the initial smooth-coordinate supplier, not a finite compactification. -/
theorem exists_simultaneous_etale_polynomial_coordinates
    (k : Type u) (R : Type v) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Smooth k R] {ι : Type w} [Finite ι]
    (p : ι → Ideal R) [∀ i, (p i).IsPrime] (d : ℕ)
    (hd : ∀ i, Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime (p i)))
      (IsLocalRing.ResidueField (Localization.AtPrime (p i)) ⊗[R] Ω[R⁄k]) = d) :
    ∃ g : Fin d → R, ∀ i, ∃ r ∉ p i,
      ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) g).toRingHom).Etale := by
  let K (i : ι) := IsLocalRing.ResidueField (Localization.AtPrime (p i))
  obtain ⟨g, hg⟩ := exists_simultaneous_residue_differential_coordinates k R K d hd
  refine ⟨g, fun i => ?_⟩
  let bK := basisOfLinearIndependentOfCardEqFinrank'
    (fun j => (1 ⊗ₜ[R] D k R (g j) : K i ⊗[R] Ω[R⁄k])) (hg i)
      (by simpa using (hd i).symm)
  apply exists_etale_polynomial_map_of_residue_differential_basis k R (p i) g bK
  intro j
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j

end Algebra
