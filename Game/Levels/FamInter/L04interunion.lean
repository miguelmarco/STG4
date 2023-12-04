import Game.Levels.FamInter.L03interpair

variable {U : Type}

World "FamInter"
Level 4
Title "Intersección de una unión de familias"

Introduction
"
Si `F` y `G` son familias de conjuntos, ¿qué es `⋂₀ (F ∪ G)`? En este nivel lo veremos.
"

/-- Supón que $F$ y $G$ son familias de conjuntos. Entonces
$\bigcap (F \cup G) = (\bigcap F) \cap (\bigcap G)$. -/
Statement (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [fam_inter_def] at h1
  rewrite [inter_def]
  apply And.intro
  rewrite [fam_inter_def]
  intro S h2
  have h3 : S ∈ F ∪ G := Or.inl h2
  exact h1 S h3
  rewrite [fam_inter_def]
  intro S h2
  have h3 : S ∈ F ∪ G := Or.inr h2
  exact h1 S h3
  intro h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [inter_def] at h1
  have hxF := h1.left
  have hxG := h1.right
  rewrite [fam_inter_def] at hxF
  rewrite [fam_inter_def] at hxG
  rewrite [union_def] at h2
  cases' h2 with hSF hSG
  exact hxF S hSF
  exact hxG S hSG

Conclusion
"

"
