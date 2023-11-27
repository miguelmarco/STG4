import GameServer.Commands
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

variable {U : Type}

World "Subconjunto"
Level 1
Title "La táctica exact"

Introduction
"
# Empieza leyendo esto

Cada nivel en este juego implica demostrar una afirmación matemática (el \"Objetivo\").
Cuando presentas una prueba de esta afirmación que
es aceptada por Lean, decimos que has *cerrado* el objetivo.

En este primer nivel, vas a demostrar que si `x` pertenece al universo `U`,
`A` es un conjunto de objetos de `U`, y `x ∈ A`, entonces `x ∈ A`. Deberías ver
`U : Type`, `x : U`, y `A : Set U` bajo *Objects* en el panel a la derecha, y
`h : x ∈ A` bajo *Assumptions*. La letra `h` aquí se llama un *identificador*
para la suposición `x ∈ A`.

Vas a demostrar objetivos en Lean utilizando *tácticas*. La primera táctica que vas
a aprender se llama `exact`, y se utiliza para cerrar el objetivo.
Puedes cerrar el objetivo escribiendo `exact` seguido de una prueba del objetivo.
"

TacticDoc exact
"
Utiliza `exact` para cerrar un objetivo. Si alguna expresión `t` es una prueba del
objetivo, entonces `exact t` cerrará el objetivo.

Puedes pensar que \"exact\" significa
\"esto es exactamente lo que se necesita para demostrar el objetivo.\"
"

NewTactic exact

DefinitionDoc elt as "∈"
"`x ∈ A` significa que `x` es un elemento de `A`.  Para introducir el símbolo `∈`, teclea
`\\mem` or `\\in` seguido de un espacio."

NewDefinition elt

/-- Sea $x$ un objeto en el universo $U$, y sea $A$ un conjuntos cuyos elementos proceden de
$U$.  Supón que $x ∈ A$.  Entonces $x \in A$. -/
Statement (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  Hint "Para completar esta prueba, teclea `exact h` en la caja de texto bajo el objetivo
  y haz click en  \"Execute\" o pulsa le tecla \"Return\" o \"Enter\"."
  exact h

Conclusion
"
¡Enhorabuena! Has completado tu primera demostración.

Aunque este teorema era trivial, ilustra un hecho importante:
aunque llamamos a `h` un *identificador* para la suposición `x ∈ A`,
también es reconocido por Lean como una *prueba* de la afirmación `x ∈ A`.
Cada vez que veas `h : P` enumerado como una suposición, donde `P` es alguna afirmación,
eso significa que Lean reconocerá `h` como una prueba de la afirmación `P`.

Recuerda que `exact` es una *táctica*. Si alguna vez quieres obtener información sobre la táctica `exact`,
puedes pulsar en `exact` en la lista de tácticas a la derecha.

Ahora pulsa en \"Next\" para ver un uso más interesante de la táctica `exact`.
"
