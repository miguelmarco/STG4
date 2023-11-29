import Game.Levels.Inter.L06inter_sub_swap

variable {U : Type}

World "Intersecciones"
Level 7
Title "La intersección es conmutativa"

Introduction
"
Como vimos en el mundo de los complementarios, cuando tu objetivo es una igualdad entre conjuntos,
una buena forma de empezar es usar `apply sub_antisymm`. Para el teorema en este nivel,
esto te dejará dos objetivos: `A ∩ B ⊆ B ∩ A` and `B ∩ A ⊆ A ∩ B`. Por suerte, puedes probar
*ambos* teoremas usando el teorema `inter_sub_swap` del nivel anterior.
"

LemmaTab "Teoría de conjuntos"

LemmaDoc inter_comm as "inter_comm" in "Teoría de conjuntos"
"Dados dos conjuntos `A` y `B`, `inter_comm A B` es una prueba de la afirmación
`A ∩ B = B ∩ A`."

/-- Dados dos conjuntos $A$ y $B$, $A \cap B = B \cap A$. -/
Statement inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  apply sub_antisymm
  exact inter_sub_swap A B
  exact inter_sub_swap B A

NewLemma inter_comm

Conclusion
"
Probaremos una última propiedad de las intersecciones en el sighu
"
