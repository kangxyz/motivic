module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.BoundaryBaseWholeTarget
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.CoproductRestriction
/-! # The full boundary coproduct after base restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C D Z : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C) (z : Z ⟶ C) (V : S.Opens)

/-- Each component retains its full original scheme structure. -/
def boundaryBaseCoproductMap :
    ((d ≫ π) ⁻¹ᵁ V).toScheme ⨿ ((z ≫ π) ⁻¹ᵁ V).toScheme ⟶
      ((coprod.desc d z ≫ π) ⁻¹ᵁ V).toScheme :=
  coprod.desc
    (IsOpenImmersion.lift ((coprod.desc d z ≫ π) ⁻¹ᵁ V).ι
      (((d ≫ π) ⁻¹ᵁ V).ι ≫ coprod.inl) (by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        change (coprod.inl ≫ coprod.desc d z ≫ π) x.val ∈ V
        simpa only [coprod.inl_desc_assoc, Scheme.Hom.mem_preimage] using x.property))
    (IsOpenImmersion.lift ((coprod.desc d z ≫ π) ⁻¹ᵁ V).ι
      (((z ≫ π) ⁻¹ᵁ V).ι ≫ coprod.inr) (by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Opens.range_ι]
        change (coprod.inr ≫ coprod.desc d z ≫ π) x.val ∈ V
        simpa only [coprod.inr_desc_assoc, Scheme.Hom.mem_preimage] using x.property))

@[reassoc]
theorem boundaryBaseCoproductMap_ι :
    boundaryBaseCoproductMap π d z V ≫ ((coprod.desc d z ≫ π) ⁻¹ᵁ V).ι =
      coprod.desc (((d ≫ π) ⁻¹ᵁ V).ι ≫ coprod.inl)
        (((z ≫ π) ⁻¹ᵁ V).ι ≫ coprod.inr) := by
  apply coprod.hom_ext <;> simp [boundaryBaseCoproductMap]

/-- The componentwise original boundary map equals the same full-boundary base change. -/
@[reassoc]
theorem boundaryBaseCoproductMap_boundary :
    boundaryBaseCoproductMap π d z V ≫ boundaryBaseWholeMap π (coprod.desc d z) V =
      coprod.desc (boundaryBaseWholeMap π d V) (boundaryBaseWholeMap π z V) := by
  apply (cancel_mono (pullback.snd V.ι π)).mp
  simp only [Category.assoc, boundaryBaseWholeMap_snd]
  rw [boundaryBaseCoproductMap_ι_assoc]
  apply coprod.hom_ext <;> simp
/-- The two component boundaries use the very same full-boundary frame, pulled along
its literal comparison. No independent component trivializations are chosen. -/
def boundaryBaseCoproductFrame (M : (boundaryBaseCompactification π V).Modules)
    (e : (Modules.pullback (boundaryBaseWholeMap π (coprod.desc d z) V)).obj M ≅
      SheafOfModules.unit ((coprod.desc d z ≫ π) ⁻¹ᵁ V).toScheme.ringCatSheaf) :
    (Modules.pullback (coprod.desc (boundaryBaseWholeMap π d V)
      (boundaryBaseWholeMap π z V))).obj M ≅
      SheafOfModules.unit
        (((d ≫ π) ⁻¹ᵁ V).toScheme ⨿ ((z ≫ π) ⁻¹ᵁ V).toScheme).ringCatSheaf :=
  (Modules.pullbackCongr (boundaryBaseCoproductMap_boundary π d z V).symm).app M ≪≫
    (Modules.pullbackComp (boundaryBaseCoproductMap π d z V)
      (boundaryBaseWholeMap π (coprod.desc d z) V)).symm.app M ≪≫
    (Modules.pullback (boundaryBaseCoproductMap π d z V)).mapIso e ≪≫
      Modules.pullbackUnitIso (boundaryBaseCoproductMap π d z V)
end AlgebraicGeometry.Scheme.Hom
