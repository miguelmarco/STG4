import Game.Levels.Comp.L02compdef

variable {U : Type}

World "Complementario"
Level 3
Title "Conjuntos complementaros de subconjuntos"

Introduction
"
En el último nivel, demostraste el teorema `comp_def`. Si tienes `x : U` y `A : Set U`,
entonces `comp_def x A` es una prueba de la afirmación `x ∈ Aᶜ ↔ x ∉ A`.

Podrías pensar en la afirmación `x ∈ Aᶜ ↔ x ∉ A` como decir que si `x ∈ Aᶜ` ocurre en cualquier
parte de una prueba, puedes reemplazarlo con `x ∉ A`. Hay una táctica llamada `rewrite` que se puede
usar para realizar tales reemplazos. Tendrás la oportunidad de probar la táctica `rewrite` en este nivel.
"

TacticDoc rewrite
"Si la expresión `t` es una prueba de una afirmación de la forma `P ↔ Q`, entonces la táctica
`rewrite [t]` reemplazará `P` en cualquier lugar donde aparezca en la meta con `Q`. Si deseas
reemplazar `Q` con `P`, usa `rewrite [← t]`. (Escribe `\\l` para ingresar el símbolo `←`.) Para
realizar el reemplazo en una suposición `h`, usa `rewrite [t] at h`.

La táctica `rewrite` también se puede usar con ecuaciones. Si `t` es una prueba de una ecuación
`p = q`, entonces `rewrite [t]` reemplazará `p` con `q` dondequiera que aparezca, y `rewrite [← t]`
reemplazará `q` con `p`.

Para realizar múltiples reemplazos, uno después de otro, coloca una lista de pruebas dentro de los corchetes, así:
`rewrite [t1, t2]`.
"

NewTactic rewrite

LemmaTab "Teoría de conjuntos"

LemmaDoc comp_sub_of_sub as "comp_sub_of_sub" in "Teoría de conjuntos"
"Si tenemos `h : A ⊆ B`, entonces `comp_sub_of_sub h` es una prueba de `Bᶜ ⊆ Aᶜ`."

/-- Supongamos $A \subseteq B$.  Entonces $B^c \subseteq A^c$. -/
Statement comp_sub_of_sub {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  Hint "Como de costumbre, para demostrar un contenido, necesitas introducir un nuevo objeto `x` y
  una nueva suposición `h2`.  Puedes hacerlo de golpe con `intro x h2`."
  intro x h2
  Hint "Ahora `comp_def {x} A` es una prueba de `{x} ∈ Aᶜ ↔ {x} ∉ A`, que nos dice que podemos
  reescribir el objetivo `{x} ∈ Aᶜ` como `{x} ∉ A`.  Para hacer esta reescritura,
  usa la táctica `rewrite [comp_def x A]`."
  rewrite [comp_def x A]
  Hint "La táctica `rewrite` es suficientemente inteligente para deducir algunas cosas por sí misma.
  Si hubieras escrito sólamente `rewrite [comp_def]`, Lean habría deducido como aplicar el teorema
  `comp_def` para obtener una equivalencia que pueda usarse para hacer una reescritura en el objetivo.
  En otras palabras, habría deducido que el teorema `comp_def` tenía que aplicarse a `{x}` y `A`.

  Análogamente, puedes escribir `rewrite [comp_def] at {h2}` para reescribir el significado de `{h2}`.
  Lean deducirá que, en ese caso, `comp_def` se tiene que aplicar a `{x}` y `B`."
  rewrite [comp_def] at h2
  Hint (hidden := true) "Ahora tu objetivo es una negación, así que intenta demostrarlo por contradicción."
  by_contra h3
  Hint (hidden := true) "Esto debería recordarte el primer nivel de este mundo. Para obtener una
  contradicción, intenta contradecir `{h2} : {x} ∉ B`."
  have h4 : x ∈ B := h1 h3
  exact h2 h4

NewLemma comp_sub_of_sub

NewHiddenTactic rw

Conclusion
"
La táctica `rewrite` es útil a menudo para reescribir definiciones. Para obtener más información
sobre cómo funciona, pulsa en `rewrite` en la lista de tácticas a la derecha. También puedes usar
`rw` en lugar de `rewrite`. (De hecho, hay una pequeña diferencia entre las tácticas `rw` y `rewrite`,
pero esa diferencia no nos preocupará en este juego).

Encontrarás el teorema que demostraste en este nivel listado como `comp_sub_of_sub` en la lista de
teoremas a la derecha. Este teorema será útil en el último nivel de este mundo.
"
