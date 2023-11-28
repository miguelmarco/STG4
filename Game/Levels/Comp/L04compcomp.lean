import Game.Levels.Comp.L03compsub

variable {U : Type}

World "Complementario"
Level 4
Title "Complementario de un complementario"

Introduction
"
¿Cómo demostramos que dos conjuntos, `A` y `B`, son iguales? Usualmente lo hacemos utilizando el teorema
`sub_antisymm`. Este teorema está predefinido en este juego; no necesitas demostrarlo.
Si tienes `h1 : A ⊆ B` y `h2 : B ⊆ A`, entonces
`sub_antisymm h1 h2` es una prueba de `A = B`. El teorema `sub_antisymm` establece que la
relación de subconjunto tiene una propiedad llamada *antisimetría*.

Pero, ¿qué pasa si aún no sabes que `A ⊆ B` y `B ⊆ A`? En ese caso, puedes usar una nueva
táctica, `apply`. Si tu objetivo es `A = B` y escribes `apply sub_antisymm`, entonces Lean
determinará que el teorema `sub_antisymm` podría aplicarse para demostrar el objetivo si
tuvieras pruebas de `A ⊆ B` y `B ⊆ A`. Entonces establecerá esos *dos* enunciados como objetivos.

Si tu objetivo afirma que dos conjuntos son iguales, generalmente es buena idea comenzar con
`apply sub_antisymm`.
"

TacticDoc apply
"
Puedes utilizar la táctica `apply` para trabajar hacia atrás desde el objetivo. Supongamos que crees
que podrás utilizar algún teorema `t` para demostrar el objetivo. En otras palabras, crees que hay
una prueba del objetivo de la forma `t ?`, donde el signo de interrogación debe ser reemplazado con
una prueba de alguna afirmación `P` a la cual se debe aplicar el teorema `t`. La táctica `apply t`
establecerá entonces `P` como tu objetivo. Si es necesario aplicar el teorema `t` a más de una
prueba para establecer el objetivo, entonces `apply t` establecerá todas las pruebas necesarias como
objetivos.
"

NewTactic apply

LemmaTab "Teoría de conjuntos"

lemma sub_antisymm {A B : Set U} (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B := Set.Subset.antisymm h1 h2

LemmaDoc sub_antisymm as "sub_antisymm" in "Teoría de conjuntos"
"Si tienes `h1 : A ⊆ B` y `h2 : B ⊆ A`, entonces `sub_antisymm h1 h2` es una prueba de `A = B`."

LemmaDoc comp_comp as "comp_comp" in "Teoría de conjuntos"
"Si `A` es un conjunto, entonces `comp_comp A` es una prueba de `Aᶜᶜ = A`."

/-- Si $A$ es un conjunto, entonces $(A^c)^c = A$. -/
Statement comp_comp (A : Set U) : Aᶜᶜ = A := by
  Hint "En este nivel, tu objetivo es `Aᶜᶜ = A`--decir, el complementario de `Aᶜ` es `A`.
  Así que usar `apply sub_antisymm` es una buena forma de empezar."
  apply sub_antisymm
  Hint "Tu objetivo inmediato ahora es probar que `Aᶜᶜ ⊆ A`.  Una vez cierres este objetivo, tendrás
  que demostrar un segundo objetivo, `A ⊆ Aᶜᶜ`."
  intro x h1
  Hint (hidden := true) "Intenta escribir la definición de complementario en {h1}."
  rewrite [comp_def] at h1
  Hint "Aunque tu objetivo no es una negación, la hipótesis `{h1}` es ahora la negación
  `{x} ∉ Aᶜ`.  Esto sugiere que la demostración por contradicción podría funcionar:
  si asumes lo contrario del objetivo, tal vez puedas llegar a contradicción probando `{x} ∈ Aᶜ`."
  by_contra h2
  Hint "¿Puedes probar `{x} ∈ Aᶜ` a partir de tu nueva hipótesis `{h2} : {x} ∉ A`?  La táctica
  `rewrite [comp_def] at {h2}` reescribirá `{x} ∈ Aᶜ` como `{x} ∉ A`, pero queremos ir en la otra
  dirección, reescribiendo `{x} ∉ A` como `{x} ∈ Aᶜ`.  Para ello, usa
  `rewrite [← comp_def] at {h2}`.  (Para introducir la flecha hacia la izquierda, teclea `\\l`.)"
  rewrite [← comp_def] at h2
  exact h1 h2
  Hint "La prueba del segundo objetivo es parecida."
  intro x h1
  rewrite [comp_def]
  by_contra h2
  rewrite [comp_def] at h2
  exact h2 h1

NewLemma sub_antisymm comp_comp

Conclusion
"
Veremos muchos más usos de la táctica `apply`. Para obtener más detalles sobre el uso de la táctica,
haz clic en `apply` en la lista de tácticas a la derecha.

Hemos dado a este teorema el nombre `comp_comp`. Tanto este teorema como el de nivel anterior
serán útiles en el próximo nivel.
"
