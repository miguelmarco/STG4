import Game.Levels.FamUnion.L06unionsub

variable {U : Type}

World "FamUnion"
Level 7
Title "Unión de una familia de intersecciones"

Introduction
"
En este nivel, introduciremos otra forma de definir conjuntos. Si `P x` es una afirmación sobre
un objeto arbitrario `x`, `{x | P x}` denota el conjunto de todos los valores de `x` para los que se
cumple `P x`. Está notación se suele llamar *notación de generación de conjuntos*. Por ejemplo,
`{x | x ∈ A ∧ x ∈ B}` es otra forma de escribir `A ∩ B`.

Como de costumbre, tenemos un teorema que establece el significado de esta notación. Lean reconocerá
`set_builder_def` como una prueba de cualquier afirmación de la forma `a ∈ {x | P x} ↔ P a`.
Esto quiere decir que `rewrite [set_builder_def]` reescribirá `a ∈ {x | P x}` como `P a`.
"

lemma set_builder_def {P : U → Prop} {a : U} : a ∈ {x | P x} ↔ P a := by rfl

LemmaDoc set_builder_def as "set_builder_def" in "{}"
"
Lean reconocerá `set_builder_def` como una prueba de cualquier afirmación de la forma
`a ∈ {x | P x} ↔ P a`.
"

NewLemma set_builder_def

/--Supón que $A$ es un conjunto y $F$ una familia de conjuntos. Entonces $A \cap (\bigcup F) =
\bigcup\{B \mid \exists S \in F, B = A \cap S\}$.-/
Statement (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {B | ∃ S ∈ F, B = A ∩ S} := by
  ext x
  apply Iff.intro
  intro h1
  Hint (strict := true) "Puede ser útil sacar toda la información posible de `{h1}` antes de
  atacar el objetivo."
  rewrite [inter_def] at h1
  Hint (strict := true) "Puede ser útil separar la mitad derecha de `{h1}`.
  Puedes hacer eso con `have {h1}r := {h1}.right`."
  have h2 : x ∈ ⋃₀ F := h1.right
  rewrite [fam_union_def] at h2
  obtain ⟨S, hS⟩ := h2
  rewrite [fam_union_def]
  Hint "Tu objetivo es una afirmación de existencia. ¿Ves qué valor puedes usar como testigo?"
  Hint (hidden := true) "Intenta `apply Exists.intro (A ∩ {S})` o `use A ∩ {S}`."
  use A ∩ S
  apply And.intro
  Hint "Puedes usar `rewrite [set_builder_def]` para reescribir el significado del objetivo."
  rewrite [set_builder_def]
  use S
  apply And.intro hS.left
  rfl
  exact And.intro h1.left hS.right
  intro h1
  Hint (strict := true) "De nuevo, extrae las consecuencias de `{h1}` antes de seguir."
  obtain ⟨B, hB⟩ := h1
  Hint (strict := true) "Puedes separar la primera mitad de `{hB}` con `have {hB}l := {hB}.left`."
  have hBl := hB.left
  rewrite [set_builder_def] at hBl
  obtain ⟨S, hS⟩ := hBl
  Hint (hidden := true) "Sabes que `{x} ∈ {B}` y `{B} = A ∩ {S}`.  Así que puedes usar `rewrite`
  para obtener `{x} ∈ A ∩ {S}`."
  rewrite [inter_def]
  rewrite [hS.right, inter_def] at hB
  apply And.intro hB.right.left
  rewrite [fam_union_def]
  use S
  exact And.intro hS.left hB.right.right
