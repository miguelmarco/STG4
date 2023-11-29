import Game.Levels.Combo.L04union_distrib_inter

variable {U : Type}

World "Combination"
Level 5
Title "Una demostración de contenido complidada"

Introduction
"
Esta prueba es un poco complicada. Pero deberías saber al menos cómo empezar.
"

LemmaTab "Teoría de conjuntos"

/-- Supongamos que $A \cup C \subseteq B \cup C$ y $A \cap C \subseteq B \cap C$. Entonces $A \subseteq B$. -/
Statement (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x h3
  Hint (strict := true) "Ahora usa `have` para establecer que `{x} ∈ A ∪ C`. Recuerda que, tal
  como vimos en la descripción de la táctica `have`, esto se puede hacer aunque no veas cómo
  demostrarla en un solo paso."
  have h4 : x ∈ A ∪ C
  rewrite [union_def]
  exact Or.inl h3
  Hint (strict := true) (hidden := true) "Usa `h1`."
  have h5 : x ∈ B ∪ C := h1 h4
  Hint (strict := true) (hidden := true) "Ahora sabes que `x ∈ B ∪ C`, puedes usar eso como base
  para partir la demostración en casos."
  rewrite [union_def] at h5
  cases' h5 with h5B h5C
  exact h5B
  Hint (strict := true) (hidden := true) "Fíjate en que aún no has usado `h2`."
  have h6 : x ∈ A ∩ C
  rewrite [inter_def]
  exact And.intro h3 h5C
  have h7 : x ∈ B ∩ C := h2 h6
  rewrite [inter_def] at h7
  exact h7.left

Conclusion
"
¡Has terminado el mundo combinado!
"
