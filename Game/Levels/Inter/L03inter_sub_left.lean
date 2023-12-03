import Game.Levels.Inter.L02elt_inter_elt_right

variable {U : Type}

World "Intersecciones"
Level 3
Title "La intersección es un subconjunto"

Introduction
"
Deberías poder combinar ideas de los niveles anteriores para resolver este.
"

LemmaTab "∩∪"

/-- Dados dos conjuntos $A$ y $B$, $A \cap B \subseteq A$. -/
Statement (A B : Set U) : A ∩ B ⊆ A := by
  Hint (hidden := true) "Como el objetivo es una afirmación de contenido, deberías empezar
  introduciendo un objeto `x` y la hipótesis de que `x ∈ A ∩ B`."
  intro x h
  rewrite [inter_def] at h
  exact h.left

Conclusion
"
Probablemente hayas usado un paso como `rewrite [inter_def] at h` en esta prueba. Este paso
es de hecho opcional. Escribir la definición de la intersección probablemente te ayuda a *ti*
a entender cómo proceder con la prueba, pero *Lean* no necesita que le digan que escriba
la definición. Lo hará por sí mismo. En otras palabras, si tienes `h : x ∈ A ∩ B`, Lean
aceptará `h.left` como una prueba de `x ∈ A`.
"
