import Game.Levels.Subset.L02subhyp

variable {U : Type}

World "Subconjunto"
Level 3
Title "La táctica have"

Introduction
"
En este nivel, tenemos las hipótesis `h1 : A ⊆ B`, `h2 : B ⊆ C`, y `h3 : x ∈ A`.
Como vimos en el nivel anterior, `h1 h3` es una prueba de que `x ∈ B`. Lamentablemente,
ese no es el objetivo, así que no podemos usar `exact h1 h3` para cerrar el objetivo.
Sin embargo, podemos usar la prueba `h1 h3` para justificar agregar `h4 : x ∈ B` a nuestra
lista de suposiciones. Para hacer eso, usaremos una nueva táctica: `have`.
"

TacticDoc «have»
"
Usa `have` para afirmar una declaración que puedes probar a partir de tus suposiciones actuales.
Debes darle a la nueva afirmación un identificador; asegúrate de
usar un identificador que sea diferente de los que ya se están utilizando.

Si alguna expresión `t` es una prueba de una afirmación `P`, y `h` es un
identificador que no está en uso, entonces `have h : P := t` agregará `h : P`
a la lista de suposiciones.

A veces quieres afirmar una declaración `P`, pero la prueba de `P` es demasiado
difícil para ser dada en una sola línea. En esa situación, simplemente puedes escribir
`have h : P`. Por supuesto, aún debes justificar la afirmación de `P`, así que
la prueba de `P` se convierte en tu objetivo inmediato.
Una vez que se haya cerrado el objetivo de demostrar `P`, podrás volver a
tu objetivo original, con `h : P` añadido a la lista de suposiciones.
"

NewTactic «have»

/-- Supón que $A \subseteq B$, $B \subseteq C$, y $x \in A$.  Entonces $x \in C$. -/
Statement (x : U) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  Hint "Para iniciar esta prueba, teclea `have h4 : x ∈ B := h1 h3`
  en la caja de texto y pulsa \"Execute\" o la tecla \"Return\" o \"Enter\".
  Recuerda que puedes introducir el símbolo `∈` tecleando `\\mem` or `\\in`."
  have h4 : x ∈ B := h1 h3
  Hint "Observa que  `{h4} : x ∈ B` se ha añadido a la lista de suposiciones.
  ¿Puedes completar la demostración ahora?"
  Hint (hidden := true) "Como vimos en el anterior nivel, `h2 {h4}` es ahora una prueba
  del objetivo, así que `exact h2 {h4}` cerrará el objetivo."
  exact h2 h4

Conclusion
"
Puedes usar la táctica `have` para añadir una afirmación a tu lista de suposiciones,
siempre que puedas justificarla con una demostración. Para más información, pulsa en `have`
en la lista de tácticas a la derecha.
"
