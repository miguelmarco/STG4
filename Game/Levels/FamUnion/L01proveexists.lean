import Game.Levels.FamInter

variable {U : Type}

World "FamUnion"
Level 1
Title "Demostrar afirmaciones de existencia"

Introduction
"
Para trabajar con uniones de familias, necesitamos saber como trabajar con afirmaciones de existencia.
Si `P x` es una afirmación sobre un objeto `x` no especificado, `∃ x, P x` significa \"hay al menos
un objeto `x` para el cual se cumple `P x`\". El símbolo `∃` se llama *cuantificador existencial*,
y lo puedes introducir tecleando `\\exists`.

La forma más fácil de probar la afirmación `∃ x, P x` es especificar un valor para `x`, y
proporcionar una prueba de `P x` para ese valor `x`. El teorema que te permite hacer eso se llama
`Exists.intro`.  Si tienes `h : P a`, para algún objeto `a`, entonces `Exists.intro a h` es una
prueba de `∃ x, P x`. En este nivel usaremos este teorema.
"

DefinitionDoc ex as "∃"
"Si `P x` representa una afirmación sobre `x`, `∃ x, P x` significa \"hay al menos un objeto
`x` para el que se cumple `P x`\".  Para introducir el símbolo `∃`, teclea `\\exists`."

NewDefinition ex

LemmaDoc Exists.intro as "Exists.intro" in "Lógica"
"Si `P x` representa una afirmación sobre `x` y tienes `h : P a`, para algún objeto `a`, entonces
`Exists.intro a h` es una prueba de `∃ x, P x`."

NewLemma Exists.intro

/--Supón que $A$ es un conjunto. Entonces hay algún conjunto $S$ tal que $S \subseteq A$.-/
Statement (A : Set U) : ∃ S, S ⊆ A := by
  Hint (strict := true) "Tu objetivo afirma que existe un subcojunto de `A`. ¿Se te ocurre cual puede ser?"
  Hint (strict := true) (hidden := true) "Recuerda que `sub_ref A` es una pruebaa de `A ⊆ A`. Así
  que puedes empezar tu prueba con `have h : A ⊆ A := sub_ref A`."
  have h : A ⊆ A := sub_ref A
  Hint "Ahora puedes usar `Exists.intro` para completar la prueba."
  Hint (hidden := true) "Exists.intro A {h}` demuestra el objetivo."
  exact Exists.intro A h

Conclusion
"
Ahora que sabes probar afirmaciones de existencia, puedes empezar a trabajar con uniones de familias.
"
