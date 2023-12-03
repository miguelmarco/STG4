--Unused--contradiction introduced in Complement World.
--import Game.Levels.Subset.L06contra

variable {U : Type}

World "Subconjunto"
Level 7
Title "Demostración por reducción al absurdo"

Introduction
"
Si tenemos un objetivo que empieza por `¬`, una prueba por reducción al absurdo
parece una buena idea.
"

LemmaTab "Teoría de conjuntos"

/-- supón que $A \subseteq B$ y $\neg A \subseteq C$.  Entonces $\neg B \subseteq C$. -/
Statement {A B C : Set U} (h1 : A ⊆ B) (h2 : ¬A ⊆ C) : ¬B ⊆ C := by
  by_contra h3
  Hint "Ya hemos demostrado el teorema `sub_trans`, que dice que si `A ⊆ B` y
  `B ⊆ C`, entonces `A ⊆ C`.  (Pulsa en `sub_trans` en la lista de teoremas de la derecha
  para ver qué dice el teorema). Como sabemos que `h1 : A ⊆ B` y `{h3} : B ⊆ C`, Lean
  reconoce `sub_trans h1 {h3}` como una prueba de que `A ⊆ C`.  Recuerda que puedes
  introducir el símbolo `⊆` tecleando `\\sub`."
  Hint (hidden := true) "Intenta `have h4 : A ⊆ C := sub_trans h1 {h3}`."
  have h4 : A ⊆ C := sub_trans h1 h3
  Hint "Ahora tienes suposiciones contradictorias."
  Hint (hidden := true) "`h2` y `{h4}` dan la contradicción necesaria."
  exact h2 h4

Conclusion
"
¡Enhorabuena por completar el mundo de los subconjuntos!
"
