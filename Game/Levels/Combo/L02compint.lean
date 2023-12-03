import Game.Levels.Combo.L01compunion

variable {U : Type}

World "Combination"
Level 2
Title "Complementario de una intersección"

Introduction
"
Como de costrumbre, una forma de empezar la prueba en este nivel es `apply sub_antisymm`.
Pero hay una solución más corta: puedes usar el teorema del nivel anterior (`comp_union`) para
probar el teorema de este nivel. Si quieres una pista de cómo hacerlo, pulsa en \"Show more help!\".
"

LemmaTab "ᶜ"

LemmaDoc comp_inter as "comp_inter" in "ᶜ"
"Dados conjuntos `A` y `B`, `comp_inter A B` es una prueba de `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`."

/-- Dados conjuntos $A$ y $B$, $(A \cap B)^c = A^c \cup B^c$. -/
Statement comp_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  Hint (hidden := true) "Empieza reescribiendo `Aᶜ ∪ Bᶜ` como `(Aᶜ ∪ Bᶜ)ᶜᶜ`."
  rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]
  rewrite [comp_union]
  rewrite [comp_comp, comp_comp]
  rfl

NewLemma comp_inter

Conclusion
"
"
