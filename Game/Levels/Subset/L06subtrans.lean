import Game.Levels.Subset.L05subref

variable {U : Type}

World "Subconjunto"
Level 6
Title "La relación de contenido es transitiva"

Introduction
"
Para empezar una demostración, empieza mirando el objetivo.
¿Qué necesitas hacer para demostrar el objetivo?
En este nivel, el objetivo es `A ⊆ C`.  ¿Qué te dice eso sobre los pasos a dar?"

LemmaTab "Teoría de conjuntos"

LemmaTab "⊆"

LemmaDoc sub_trans as "sub_trans" in "⊆"
"
Si tienes `h1 : A ⊆ B` y `h2 : B ⊆ C`, `sub_trans h1 h2` es una prueba de `A ⊆ C`.
"

/--Sea $A \subseteq B$ y $B \subseteq C$.  Entonces $A \subseteq C$. -/
Statement sub_trans {A B C : Set U}
    (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  Hint (hidden := true) "Para empezar, hay que introducir un objeto `x` y la
  hiótesis de que `x ∈ A`."
  intro x h3
  Hint "¿Te recuerda esta situación al nivel anterior?"
  Hint (hidden := true) "Usa `have` para afirmar que `{x} ∈ B`, y
  después demuestra `{x} ∈ C`."
  have h4 : x ∈ B := h1 h3
  exact h2 h4

NewLemma sub_trans

Conclusion
"
El teorema que has demostrado en este nivel dice que la relación de contenido tiene
una propiedad llamada *transitividad*. Hemos llamado a este teorema `sub_trans`.
"
