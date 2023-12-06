import Game.Levels.Combo.L01compunion

variable {U : Type}

World "Combination"
Level 2
Title "Complementario de una intersección"

Introduction
"
Como de costrumbre, podrías empezar esta prueba con `ext x` o `apply sub_antisymm`.
Pero hay una solución más corta: puedes usar el teorema del nivel anterior (`comp_union`) para
probar el teorema de este nivel.

El truco para empezar es reescribir `Aᶜ ∪ Bᶜ` como `(Aᶜ ∪ Bᶜ)ᶜᶜ`. Como sabes, `comp_comp (Aᶜ ∪ Bᶜ)`
es una prueba de `(Aᶜ ∪ Bᶜ)ᶜᶜ = Aᶜ ∪ Bᶜ`, así que se podría usar`rewrite [comp_comp (Aᶜ ∪ Bᶜ)]`
para reescribir `(Aᶜ ∪ Bᶜ)ᶜᶜ` como `Aᶜ ∪ Bᶜ`; pero queremos ir en la otra dirección, reescribiendo
`Aᶜ ∪ Bᶜ` como `(Aᶜ ∪ Bᶜ)ᶜᶜ`. Para ello, usa `rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]`.
(Para introducir la flecha hacia la izquierda, teclea `\\l`.)
"

LemmaTab "ᶜ"

LemmaDoc comp_inter as "comp_inter" in "ᶜ"
"Dados conjuntos `A` y `B`, `comp_inter A B` es una prueba de `(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ`."

/-- Dados conjuntos $A$ y $B$, $(A \cap B)^c = A^c \cup B^c$. -/
Statement comp_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rewrite [← comp_comp (Aᶜ ∪ Bᶜ)]
  Hint "¿Ves cómo podrías usar el teroema del nivel anterior?"
  rewrite [comp_union]
  rewrite [comp_comp, comp_comp]
  rfl

NewLemma comp_inter

Conclusion
"
"
