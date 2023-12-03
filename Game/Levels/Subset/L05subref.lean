import Game.Levels.Subset.L04imp

variable {U : Type}

World "Subconjunto"
Level 5
Title "La relación de contenido es reflexiva"

Introduction
"
¿Cómo demuestras que un conjunto es un subconjunto de otro? Para demostrar que `A ⊆ B`,
tienes que mostrar que si algún objeto `x` es un elemento de `A`, entonces también lo es
un elemento de `B`. Para hacer eso, tendrás que introducir un objeto `x` en
la prueba. Este elemento `x` podría ser cualquiera, así que decimos que es *arbitrario*.

En este nivel, comenzamos con un ejemplo simple de este tipo de prueba. Vamos a mostrar
que si `A` es un conjunto, entonces `A ⊆ A`.
"

LemmaTab "⊆"

LemmaDoc sub_ref as "sub_ref" in "⊆"
"
Si tenemos `A : Set U`, entonces `sub_ref A` es una prueba de que `A ⊆ A`.
"

/-- Sea $A$ un conjunto cualquiera.  Entonces $A \subseteq A$. -/
Statement sub_ref (A : Set U) : A ⊆ A := by
  Hint "Nuestro primer paso es introducir un objeto `x` en la prueba. Para hacer esto,
  escribe `intro x`. Ya hemos visto que la táctica `intro` se puede utilizar para introducir
  una nueva *suposición* en una prueba. Este paso ilustra un segundo uso de `intro`:
  introducir un nuevo *objeto* en una prueba."
  intro x
  Hint "Observa que `{x} : U` se ha agregado a la lista de objetos, y
  el objetivo ha cambiado a `{x} ∈ A → {x} ∈ A`. Afortunadamente, ya sabes cómo demostrar
  un objetivo de esta forma."
  Hint (hidden := true) "Usa `intro` otra vez para introducir la suposición `{x} ∈ A`."
  intro h
  Hint "La situación ahora debería recordarte a tu primera demostración, en el nivel 1 de este mundo."
  Hint (hidden := true) "Observa que {h} es ahora una prueba del objetivo."
  exact h

NewLemma sub_ref

Conclusion
"
El teorema que has demostrado en este nivel muestra que la relación de ser subconjunto tiene
una propiedad llamada *reflexividad*. Hemos dado al teorema el nombre `sub_ref`.
Lo verás en la lista de teoremas a la derecha.
"
