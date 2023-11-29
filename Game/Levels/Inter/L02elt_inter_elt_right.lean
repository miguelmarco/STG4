import Game.Levels.Inter.L01and

variable {U : Type}

World "Intersecciones"
Level 2
Title "Elementos de la intersección"

Introduction
"
En este nivel, necesitaremos usar la definición de \"intersección\". El teorema que
expresa esa definición se llama `inter_def`. Si tienes `x : U`, `A : Set U` y
`B : Set U`, entonces `inter_def x A B` es una prueba de la afirmación
`x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`. Como vimos en el Mundo de complementarios, esto significa
que la táctica `rewrite [inter_def x A B]` puede usarse para reemplazar `x ∈ A ∩ B`
en la meta con `x ∈ A ∧ x ∈ B`. Por lo general, Lean puede deducir `x`, `A` y `B`
por sí mismo, así que simplemente puedes escribir `rewrite [inter_def]`,
y puedes usar `rewrite [inter_def] at h` para reescribir en una hipótesis
`h` en lugar del objetivo.

Al igual que `comp_def`, `inter_def` puede demostrarse usando la táctica `rfl`.
Pero no te pediremos que lo demuestres; está predefinido en este juego. Para ingresar
el símbolo `∩`, puedes escribir `\\inter` o `\\cap`.
"

DefinitionDoc inter as "∩"
"Si `A` y `B` son conjuntos, entonces `A ∩ B` es la intersección de `A` y `B`.
Para introducir el símbolo `∩`, puedes escribir `\\inter` o `\\cap`.
"

NewDefinition inter

LemmaTab "Teoría de conjuntos"

LemmaDoc inter_def as "inter_def" in "Teoría de conjuntos"
"Si tienes `x : U`, `A : Set U` y `B : Set U`, entonces `inter_def x A B` es una prueba
de la afirmación `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`.
"

lemma inter_def (x : U) (A B : Set U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by rfl

NewLemma inter_def

/-- Supongamos que $x \in A ∩ B$.  Entonces $x \in B$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  Hint "Para empezar esta prueba, intenta escribir el significado de intersección en `h`."
  rewrite [inter_def] at h
  Hint "Ahora estás en una situación parecida al nivel anterior."
  exact h.right

Conclusion
"
"
