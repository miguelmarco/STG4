import Game.Levels.Inter

variable {U : Type}

World "Uniones"
Level 1
Title "O"

Introduction
"
Para trabajar con uniones, la palabra lógica importante es \"o\".

Si `P` y `Q` son afirmaciones, entonces `P ∨ Q` significa \"P o Q o ambas\". Para introducie
el símbolo `∨`, escribe `\\or`. Para que la afirmación `P ∨ Q` sea verdadera, `P` o `Q`
o ambos deben ser verdaderos. Esto nos proporciona dos formas de demostrar una afirmación
de esta forma. Si tienes `h : P`, entonces `Or.inl h` puede usarse para demostrar `P ∨ Q`.
Si tienes `h : Q`, entonces `Or.inr h` demuestra `P ∨ Q`.
"

DefinitionDoc or as "∨"
"`P ∨ Q` significa \"P o Q o ambas\".  Para introducir el símbolo `∨`, teclea `\\or`."

NewDefinition or

LemmaTab "Lógica"

LemmaDoc Or.inl as "Or.inl" in "Lógica"
"si tenemos `h : P`, entonces `Or.inl h` puede usarse como prueba de `P ∨ Q`, para cualquier
afirmación `Q`."

LemmaDoc Or.inr as "Or.inr" in "Lógica"
"si tenemos `h : Q`, entonces `Or.inr h` puede usarse como prueba de `P ∨ Q`, para cualquier
afirmación `P`."

NewLemma Or.inl Or.inr

/-- Supón que $x \in A$, y $B$ es un conjunto. Entonces $x \in A ∨ x ∈ B$. -/
Statement (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  Hint (hidden := true) "`Or.inl h` is a proof of the goal."
  exact Or.inl h

Conclusion
"
Ahora podemos empezar a probar teoremas sobre uniones.
"
