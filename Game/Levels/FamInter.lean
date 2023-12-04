import Game.Levels.FamInter.L06eltwiseunion  --It imports all previous levels.
/-!

# FamInter world

-/
World "FamInter"
Title "Mundo de intersección de familias"

Introduction
"Hasta ahora, los elementos de todos nuestros conjuntos han sido objetos en el universo `U`. Pero
los conjuntos pueden contener otros tipos de objetos. En los dos mundos siguientes,
trabajaremos con conjuntos cuyos elementos son conjuntos de objetos de `U`. Llamaremos a estos
conjuntos *familias de conjuntos* de `U`. Para indicar que `F` es una familia de conjuntos de
`U`, escribimos `F: Set (Set U)`.

Por ejemplo, supongamos que `U` contiene a las personas en cierto club, y queremos formar un
comité compuesto por cinco miembros del club. El conjunto de todos los comités posibles es una
familia de conjuntos de `U`. Cada elemento de esta familia es un conjunto que contiene a cinco
miembros del club.

En este mundo extendemos la idea de intersecciones a familias de conjuntos. Si `F` es una
familia de conjuntos de `U`, entonces la *intersección* de la familia `F` es el conjunto formado
por de `U` que pertenecen a todos los elementos de `F`.
"
