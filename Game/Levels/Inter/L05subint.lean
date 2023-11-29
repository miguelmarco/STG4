import Game.Levels.Inter.L04proveand

variable {U : Type}

World "Intersecciones"
Level 5
Title "Subconjunto de una intersección"

Introduction
"
Por supuesto, ahora ya sabes empezar una demostración de que un conjunto es subconjunto de otro.
"

LemmaTab "Lógica"

/-- Supongamos que $A \subseteq B$ y $A \subseteq C$.  Entonces $A \subseteq B \cap C$. -/
Statement (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x h3
  Hint "Reescribir la definición de intersección en el objetivo puede ayudar."
  rewrite [inter_def]
  Hint "Si tuvieras `hB : x ∈ B` y `hC : x ∈ C`, entonces `And.intro hB hC`
  probaría el objetivo. Así que hay dos formas de seguir. Una opción es usar
  `have` para introducir las hipótesis `x ∈ B` y `x ∈ C`--si es que puedes
  justificarlas.--  Entonces puedes usar `And.intro` para probar el objetivo.

  La segunda opción es usar la táctica `apply`. Recuerda que si escribes
  `apply And.intro`, Lean deducirá que el teorema `And.intro` podría aplicarse para probar
  el objetivo si tuvieras pruebas de `x ∈ B` y `x ∈ C`. Así que establecerá esas
  afirmaciones como nuevos objetivos, para probarlas de una en una."
  apply And.intro
  Hint "Tu objetivo inmediato es ahora probar `x ∈ B`. Una vez lo cierres, tendrás que
  probar el segundo objetivo `x ∈ C`."
  exact h1 h3
  exact h2 h3

Conclusion
"
En general, si piensas que algún teorema `t` podría usarse para demostrar la meta, la táctica
`apply t` trabajará hacia atrás desde el objetivo, estableciendo como nuevos objetivos
las hipótesis necesarias para poder aplicar el teorema `t`.
"
