import Game.Levels.Inter.L05subint

variable {U : Type}

World "Intersecciones"
Level 6
Title "La intersección es un subconjunto de la intersección conmutada"

Introduction
"
En el siguiente nivel vamos a probar que la intersección es conmutativa, es decir,
`A ∩ B = B ∩ A`. Como calentamiento, en este nivel probaremos que `A ∩ B ⊆ B ∩ A`.
"

LemmaTab "∩∪

LemmaDoc inter_sub_swap as "inter_sub_swap" in "∩∪"
"Dados dos conjuntos `A` y `B`, `inter_sub_swap A B` es una prueba de
`A ∩ B ⊆ B ∩ A`."

/-- Para dos conjuntos $A$ y $B$, $A \cap B \subseteq B \cap A$. -/
Statement inter_sub_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x h
  Hint (hidden := true) "Te puede resultar útil reescribir la definición de la intersección
  tanto en la hipótesis {h} como en el objetivo. No es necesario usar la táctica `rewrite`;
  puedes hacer la reescritura mentalmente en lugar de pedirle a Lean que lo haga. Pero si
  te ayuda a entender la prueba, adelante, usa la táctica `rewrite`."
  rewrite [inter_def]
  rewrite [inter_def] at h
  Hint (hidden := true) "Ahora`And.intro {h}.right {h}.left` prueba el objetivo."
  exact And.intro h.right h.left

NewLemma inter_sub_swap

Conclusion
"
Hemos llamado a este teorema `inter_sub_swap`.  A partir de ahora, para dos conjuntos cualesquiera
`A` y `B`, `inter_sub_swap A B` es una prueba de `A ∩ B ⊆ B ∩ A`.
"
