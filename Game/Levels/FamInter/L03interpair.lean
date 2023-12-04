import Game.Levels.FamInter.L02intersubinter

variable {U : Type}

World "FamInter"
Level 3
Title "Intersección de un par"

Introduction
"
Este nivel muestra que las intersecciones de familias generalizan las intersecciones
de dos conjuntos que vimos en el mundo de las intersecciones. Veremos que si `A` y `B`
son conjuntos, `A ∩ B` es lo mismo que la intersección de la familia formada exactamente
por `A` y `B`.

Necesitamos una notación para esta familia formada exactamaente por `A` y `B`; la
denotaremos por `{A, B}`. Como de costumbre, necesitamos in teorema correspondiente
a esta notación. Para conjuntos `S`, `A`, y `B`, `pair_def S A B` es una prueba de
`S ∈ {A, B} ↔ S = A ∨ S = B`.
"

lemma pair_def (S A B : Set U) : S ∈ {A, B} ↔ S = A ∨ S = B := by rfl

LemmaDoc pair_def as "pair_def" in "{}"
"Para conjuntos `S`, `A`, y `B`, `pair_def S A B` es una prueba de
`S ∈ {A, B} ↔ S = A ∨ S = B`."

NewLemma pair_def

LemmaTab "{}"

/-- Suppose $A$ and $B$ are sets.  Then $A \cap B = \bigcap \{A, B\}$. -/
Statement (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  apply Iff.intro
  intro h1
  rewrite [inter_def] at h1
  rewrite [fam_inter_def]
  intro S h2
  rewrite [pair_def] at h2
  cases' h2 with hA hB
  rewrite [hA]
  exact h1.left
  rewrite [hB]
  exact h1.right
  intro h1
  rewrite [inter_def]
  rewrite [fam_inter_def] at h1
  apply And.intro
  have h2 : A ∈ {A, B}
  rewrite [pair_def]
  apply Or.inl
  rfl
  exact h1 A h2
  have h2 : B ∈ {A, B}
  rewrite [pair_def]
  apply Or.inr
  rfl
  exact h1 B h2

Conclusion
"

"
