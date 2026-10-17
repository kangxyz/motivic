module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldDirectImageExact

/-! # Exactness of the actual small-site direct image from a field -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic Motivic.FiniteEtaleSite

universe u

namespace MotivicTest.FiniteEtaleFieldDirectImageExact

variable {K : Type u} [Field K] {X : Scheme.{u}} (b : Spec (.of K) ⟶ X)

/-- Sectionwise surjectivity refers to the literal direct-image map. -/
theorem actual_sections_surjective
    {F G : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) [Epi a] (V : FiniteEtaleSite X) :
    Function.Surjective (((directImage b).map a).hom.app (op V)) :=
  fieldDirectImage_map_app_surjective b a V

/-- The underlying presheaf map is epi, without any assumption on sheaf products. -/
theorem actual_presheaf_epi
    {F G : Sheaf (nisnevichTopology (Spec (.of K))) AddCommGrpCat.{u + 1}}
    (a : F ⟶ G) [Epi a] : Epi ((directImage b).map a).hom :=
  fieldDirectImage_map_presheaf_epi b a

example : (directImage b).PreservesHomology := inferInstance

open Lean in
run_cmd do
  for name in #[``actual_sections_surjective, ``actual_presheaf_epi,
      ``fieldDirectImage_preservesEpimorphisms, ``fieldDirectImage_preservesHomology,
      ``fieldDirectImage_shortExact] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Field direct image exactness: standard foundations only."

end MotivicTest.FiniteEtaleFieldDirectImageExact
