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
  Hint "Este es un enfoque que podrías probar:  si tuvieras `hFG : {S} ∈ F ∪ G`,
  podrías probar el objetivo con `{h1} {S} hFG`.  Así que si usas la táctica `apply {h1} {S}`, Lean
  verá que `{h1} {S}` se puede aplicar a una prueba de `{S} ∈ F ∪ G` para cerrar el objetivo,
  así que establecerá `{S} ∈ F ∪ G` coimo tu nuevo objetivo."
  apply h1 S
  rewrite [union_def]
  exact Or.inl h2
  rewrite [fam_inter_def]
  intro S h2
  apply h1 S
  exact Or.inr h2
  intro h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [inter_def] at h1
  rewrite [fam_inter_def, fam_inter_def] at h1
  rewrite [union_def] at h2
  cases' h2 with hSF hSG
  exact h1.left S hSF
  exact h1.right S hSG
