import Game.Levels.FamUnion.L04unionpair

variable {U : Type}

World "FamUnion"
Level 5
Title "Unión de una unión"

Introduction
"
En este nivel, `F` y `G` son familias de conjuntos, y verás qué relación hay entre `⋃₀ (F ∪ G)`,
`⋃₀ F` y `⋃₀ G`.
"

/-- Supón que $F$ y $G$ son familias de conjuntos. Entonces $\bigcup (F \cup G) =
(\bigcup F) \cup (\bigcup G)$ . -/
Statement (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [fam_union_def] at h1
  obtain ⟨S, h1⟩ := h1
  rewrite [union_def]
  rewrite [union_def] at h1
  cases' h1.left with hF hG
  left
  rewrite [fam_union_def]
  use S
  exact And.intro hF h1.right
  right
  use S
  exact And.intro hG h1.right
  intro h1
  rewrite [union_def] at h1
  rewrite [fam_union_def]
  cases' h1 with hF hG
  obtain ⟨S, h1⟩ := hF
  use S
  apply And.intro
  exact Or.inl h1.left
  exact h1.right
  obtain ⟨S, h1⟩ := hG
  use S
  apply And.intro
  exact Or.inr h1.left
  exact h1.right
