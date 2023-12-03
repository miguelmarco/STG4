import Game.Levels.Comp.L04compcomp

variable {U : Type}

World "Complementario"
Level 5
Title "Equivalencia de complementarios de subconjuntos"

Introduction
"
En este último nivel del mundo de los complementarios, demostrarás una aformación del tipo `P ↔ Q`.
El teorema más útil para este fin es `Iff.intro`. Si tienes `h1 : P → Q` y `h2 : Q → P`, entonces
`Iff.intro h1 h2` es una prueba de `P ↔ Q`. Como vimos en el anterior nivel, esto significa que
puedes empezar la prueba con `apply Iff.intro`. Lean establecerá `P → Q` y `Q → P` como objetivos
que deben demostrarse para completar la prueba.
"

LemmaTab "ᶜ"

LemmaDoc Iff.intro as "Iff.intro" in "ᶜ"
"Si tienes `h1 : P → Q` y `h2 : Q → P`, entonces `Iff.intro h1 h2` es una prueba de `P ↔ Q`."

NewLemma Iff.intro

/-- Suppose $A$ and $B$ are sets.  Then $A \subseteq B$ if and only if $B^c \subseteq A^c$. -/
Statement (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  Hint "Para la prueba en este nivel, `apply Iff.intro` creará los objetivos `A ⊆ B → Bᶜ ⊆ Aᶜ`
  y `Bᶜ ⊆ Aᶜ → A ⊆ B`."
  apply Iff.intro
  Hint (hidden := true) "Por descontado, deberías empezar introduciendo la hipótesis
  `h1 : A ⊆ B`."
  intro h1
  Hint "Afortunadamente, ahora se puede usar el teorema `comp_sub_of_sub` para probar el objetivo.
  (Pulsa en `comp_sub_of_sub` en la lista de teoremas a la derecha si no recuerdas lo que dice
  el teorema.)"
  Hint (hidden := true) "`comp_sub_of_sub {h1}` demostrará el objetivo."
  exact comp_sub_of_sub h1
  Hint "El segundo objetivo es parecido, pero un poco más difícil."
  intro h1
  Hint (strict := true) "El teorema `comp_sub_of_sub {h1}` no prueba el objetivo, pero se acerca.
  ¿Ves qué afirmación faltaría?"
  Hint (strict := true) (hidden := true) "Puedes usar `comp_sub_of_sub {h1}` como prueba de la afirmación
  `Aᶜᶜ ⊆ Bᶜᶜ`."
  have h2 : Aᶜᶜ ⊆ Bᶜᶜ := comp_sub_of_sub h1
  Hint (strict := true) "Por suerte, podemos usar el teorema `comp_comp` para probar `Aᶜᶜ = A` y
  `Bᶜᶜ = B`, y esas afirmaciones deberían servirnos para pasar de `{h2}` al objetivo.
  Hemos visto en niveles anteriores que la táctica `rewrite` se pueda aplicar con una prueba de una
  afirmación del tipo `P ↔ Q` para sustituir `P` con `Q`.  La táctica se puede usar también con
  ecuaciones : si `t` es una prueba de una ecuación `p = q`, entonces `rewrite [t]` sustituirá
  `p` por `q`."
  Hint (strict := true) (hidden := true) "`rewrite [comp_comp A] at {h2}` cambiará `Aᶜᶜ` a `A`, y
  `rewrite [comp_comp B] at {h2}` cambiará `Bᶜᶜ` a `B`.  De hecho, puedes usar ambas a la vez:
  `rewrite [comp_comp A, comp_comp B] at {h2}`."
  rewrite [comp_comp A, comp_comp B] at h2
  exact h2

NewHiddenTactic constructor

Conclusion
"
La prueba en este nivel ilustra cómo teoremas previamente demostrados pueden usarse en nuevas pruebas.

Hay otra táctica que puedes usar si tu objetivo es de la forma `P ↔ Q`. En esta situación, la
táctica `constructor` tendrá el mismo efecto que `apply Iff.intro`; es decir, establecerá dos
nuevos obejtivos `P → Q` y `Q → P`.
"
