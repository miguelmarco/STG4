import Game.Levels.Inter.L03inter_sub_left

variable {U : Type}

World "Intersecciones"
Level 4
Title "Demostrando una conjunción"

Introduction
"
En este nivel, probaremos una afirmación de la forma `P ∧ Q`. Para hacer esto, necesitaremos
otro teorema: `And.intro`. Si tienes `h1 : P` y `h2 : Q`, entonces `And.intro h1 h2` es una
prueba de `P ∧ Q`.
"

LemmaTab "Lógica"

LemmaDoc And.intro as "And.intro" in "Lógica"
"Si tenemos `h1 : P` y `h2 : Q`, entonces `And.intro h1 h2` es una prueba de `P ∧ Q`."

NewLemma And.intro

/-- Supón que $x \in A$ y $x \in B$.  Entonces $x \in A \cap B$. -/
Statement (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  Hint "Reescribir el significado de la intersección en el objetivo puede ayudarte a ver
  qué es lo necesario para completar este nivel."
  rewrite [inter_def]
  Hint "Ahora puedes usar `And.intro` para probar el objetivo."
  Hint (hidden := true) "`exact And.intro h1 h2` cerrará el objetivo."
  exact And.intro h1 h2

Conclusion
"
De nuevo, `rewrite` no era realmente necesario. Podrías haber demostrado este teorema
en un sólo paso: `exact And.intro h1 h2`.
"
