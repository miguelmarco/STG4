import Game.Levels.Combo.L02compint

variable {U : Type}

World "Combination"
Level 3
Title "Distributividad de la intersección respecto de la unión"

Introduction
"
Esta prueba es más larga que las anteriores, pero no requiere nuevas tácticas o teoremas.
Símplemente tienes que ir trabajándola, usando tácticas y teoremas ya vistos.
"

LemmaTab "Teoría de conjuntos"

LemmaDoc inter_distrib_over_union as "inter_distrib_over_union" in "Set Theory"
"Dados conjuntos `A`, `B`, y `C`, `inter_distrib_over_union A B C` es una prueba de
`A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`."

/-- Dados conjuntos $A$, $B$, y $C$, $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$. -/
Statement inter_distrib_over_union (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply sub_antisymm
  intro x h
  rewrite [inter_def] at h
  rewrite [union_def]
  Hint (strict := true) (hidden := true) "Puede ser útil separar la segunda parte de `{h}` como una
  hiótesis separada. Lo puedes hacer con `have {h}BC : {x} ∈ B ∪ C := {h}.right`."
  have hBC : x ∈ B ∪ C := h.right
  rewrite [union_def] at hBC
  cases' hBC with hB hC
  apply Or.inl
  exact And.intro h.left hB
  apply Or.inr
  exact And.intro h.left hC
  intro x h
  rewrite [union_def] at h
  rewrite [inter_def]
  cases' h with hB hC
  rewrite [inter_def] at hB
  apply And.intro
  exact hB.left
  rewrite [union_def]
  exact Or.inl hB.right
  rewrite [inter_def] at hC
  apply And.intro
  exact hC.left
  rewrite [union_def]
  exact Or.inr hC.right

NewLemma inter_distrib_over_union

Conclusion
"
¡Lo conseguiste!
"
