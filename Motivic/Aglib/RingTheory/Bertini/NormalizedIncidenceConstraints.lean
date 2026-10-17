module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Independent equations on normalized left-kernel incidence charts

A normalized left-kernel vector gives exactly one full cotangent vector of
constraints in addition to the independent value constraints. This is the
linear elimination step in the whole-fiber Bertini incidence argument.
-/
@[expose] public noncomputable section
namespace LinearMap
universe u v w z
variable {K : Type u} [Field K] {Q : Type v} [AddCommGroup Q] [Module K Q]
  {V : Type w} [AddCommGroup V] [Module K V] {ι : Type z} [Fintype ι]

/-- Value constraints for each coordinate and the weighted sum of their derivatives. -/
def normalizedJetConstraints (J : Q →ₗ[K] K × V) (w : ι → K) :
    (ι → Q) →ₗ[K] (ι → K) × V where
  toFun f := (fun i => (J (f i)).1, ∑ i, w i • (J (f i)).2)
  map_add' f g := by
    ext <;> simp [smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Prod.ext
    · ext i
      simp
    · change (∑ i, w i • (J (c • f i)).2) = c • ∑ i, w i • (J (f i)).2
      simp only [map_smul, Prod.smul_snd, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm (w i) c (J (f i)).2

/-- A unit pivot in the left-kernel vector makes all displayed equations independent. -/
theorem normalizedJetConstraints_surjective (J : Q →ₗ[K] K × V)
    (hJ : Function.Surjective J) (w : ι → K) (i₀ : ι) (hw : w i₀ = 1) :
    Function.Surjective (normalizedJetConstraints J w) := by
  classical
  rintro ⟨c, v⟩
  choose f hf using fun i => hJ (c i, if i = i₀ then v else 0)
  refine ⟨f, Prod.ext ?_ ?_⟩
  · exact funext fun i => congrArg Prod.fst (hf i)
  · change ∑ i, w i • (J (f i)).2 = v
    simp only [hf]
    simp [hw]

/-- The actual kernel has codimension `card ι + finrank V`, before counting
 the extra normalized left-kernel parameters or the moving point. -/
theorem finrank_ker_normalizedJetConstraints [Module.Finite K Q] [Module.Finite K V]
    (J : Q →ₗ[K] K × V) (hJ : Function.Surjective J)
    (w : ι → K) (i₀ : ι) (hw : w i₀ = 1) :
    Fintype.card ι + Module.finrank K V +
      Module.finrank K (normalizedJetConstraints J w).ker =
        Module.finrank K (ι → Q) := by
  have h := (normalizedJetConstraints J w).finrank_range_add_finrank_ker
  rw [range_eq_top.mpr (normalizedJetConstraints_surjective J hJ w i₀ hw)] at h
  simpa [Module.finrank_prod] using h

end LinearMap
