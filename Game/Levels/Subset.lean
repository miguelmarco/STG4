import Game.Levels.Subset.L06subtrans  --It imports all previous levels.
/-!

# Mundo de los subconjuntos

This file defines Subset World. Like all worlds, this world
has a name, a title, an introduction, and most importantly
a finite set of levels (imported above). Each level has a
level number defined within it, and that's what determines
the order of the levels.
-/
World "Subconjunto"
Title "Mundo de subconjuntos."

Introduction
"
# ¡Bienvenido al mundo de los subconjuntos!

En este mundo, aprenderás sobre conjuntos y subconjuntos, y también aprenderás los conceptos
básicos de cómo demostrar teoremas en Lean.

Los elementos de los conjuntos en este mundo provendrán de un universo llamado `U`.
(Lean llama a `U` un *Tipo*.) Para especificar que un objeto `x` pertenece al universo `U`,
escribimos `x : U`. Para especificar que `A` es un conjunto de objetos de `U`, escribimos
`A : Set U`. Para decir que `x` es un elemento de `A`, escribimos `x ∈ A`.
(Puedes ingresar el símbolo `∈` escribiendo `\\mem` o `\\in`, seguido de un espacio).

Probarás teoremas en este juego utilizando herramientas llamadas *tácticas*.
El objetivo es demostrar el teorema aplicando tácticas en el orden correcto.

Aprendamos algunas tácticas básicas. Haz click en \"Start\" a continuación
para empezar.
"
