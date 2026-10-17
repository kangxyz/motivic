module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleNisnevich
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Cover lifting from the smooth site to the finite-type small site -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteEtaleSite

variable {B : Scheme.{u}} (X : SmoothSite B)

/-- A smooth Nisnevich cover of an étale neighborhood is already a family of
separated finite-type étale neighborhoods over the original scheme. -/
theorem exists_toSmoothSite_cover_lift {U : FiniteEtaleSite X.left}
    {R : Sieve ((toSmoothSite X).obj U)}
    (hR : R ∈ SmoothSite.nisnevichTopology B _) :
    ∃ Q ∈ nisnevichPrecoverage X.left U,
      Q ≤ (R.functorPullback (toSmoothSite X)).arrows := by
  obtain ⟨R₀, hR₀, h₀⟩ := SmoothSite.mem_nisnevichTopology_iff.mp hR
  obtain ⟨ι, V, f, rfl⟩ := R₀.exists_eq_ofArrows
  have hf := (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff f).mp hR₀
  let (i : ι) : Etale (f i).left := hf.1 i
  have hw (i : ι) : ((f i).left ≫ U.hom) ≫ X.hom = (V i).hom := by
    rw [Category.assoc]
    exact (f i).w
  let (i : ι) : IsSeparated ((f i).left ≫ U.hom) := by
    apply IsSeparated.of_comp _ X.hom
  let (i : ι) : QuasiCompact ((f i).left ≫ U.hom) := by
    apply QuasiCompact.of_comp _ X.hom
  let W (i : ι) : FiniteEtaleSite X.left :=
    MorphismProperty.Over.mk ⊤ ((f i).left ≫ U.hom)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let g (i : ι) : W i ⟶ U := MorphismProperty.Over.homMk (f i).left rfl
  refine ⟨Presieve.ofArrows W g, ?_, ?_⟩
  · exact (ofArrows_mem_nisnevichPrecoverage_iff g).mpr hf
  · rw [Presieve.ofArrows_le_iff]
    intro i
    let e : (toSmoothSite X).obj (W i) ⟶ V i :=
      SmoothSite.homMk (𝟙 _) (by
        change 𝟙 _ ≫ (V i).hom = ((f i).left ≫ U.hom) ≫ X.hom
        simpa only [Category.id_comp] using (hw i).symm)
    have he : e ≫ f i = (toSmoothSite X).map (g i) := by
      ext
      simp [e, g, toSmoothSite]
    change R ((toSmoothSite X).map (g i))
    rw [← he]
    exact R.downward_closed (h₀ _ _ ⟨i⟩) e

/-- Restriction to the actual small site has the cover-lifting property. -/
instance toSmoothSite_isCocontinuous :
    (toSmoothSite X).IsCocontinuous
      (nisnevichTopology X.left) (SmoothSite.nisnevichTopology B) where
  cover_lift hR := by
    obtain ⟨Q, hQ, hQR⟩ := exists_toSmoothSite_cover_lift X hR
    exact (nisnevichTopology X.left).superset_covering
      ((Sieve.generate_le_iff _ _).mpr hQR)
      (Precoverage.generate_mem_toGrothendieck hQ)

end Motivic.FiniteEtaleSite
