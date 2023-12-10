import Game.Levels.FamCombo.L06unionintcompint

variable {U : Type}

World "FamCombo"
Level 7
Title "Un conjunto con un único elemento"

Introduction
"
Con `{a}` denotamos un conjunto cuyo único elemento es `a`. El teorema `single_def` expresa la
definición de estos conjuntos: `single_def x a` es una prueba de `x ∈ {a} ↔ x = a`.
"

lemma single_def (x a : U) : x ∈ {a} ↔ x = a := by rfl

LemmaDoc single_def as "single_def" in "{}"
"Dados `x` y `a`, `single_def x a` es una prueba de `x ∈ {a} ↔ x = a`."

NewLemma single_def

LemmaTab "{}"

/-- Supón que $A$ es un conjunto, y para cada familia $F$ tal que $\bigcup F = A$, se cumple que
$A \in F$. Entonces $A$ debe tener un único elemento.-/
Statement (A : Set U) (h1 : ∀ F, (⋃₀ F = A → A ∈ F)) : ∃ x, A = {x} := by
  Hint (strict := true) "Empieza con `have h2 := h1 \{S | ...}`. La parte difícil es darte cuenta de
  qué debes poner en  `...`."
  Hint (strict := true) (hidden := true) "Tienes que aplicar h1 a una familia de conjuntos que
  cumpla dos condiciones: la unión de la familia debe ser `A`, y saber que `A` pertenece a la
  familia debe ayudarte a probar que `A` está formado por un único elemento."
  have h2 := h1 {S | ∃ x ∈ A, S = {x}}
  have h3 : ⋃₀ {S | ∃ x ∈ A, S = {x}} = A
  ext x
  apply Iff.intro
  intro h3
  obtain ⟨S, hS⟩ := h3
  rewrite [set_builder_def] at hS
  obtain ⟨y, hy⟩ := hS.left
  rewrite [hy.right] at hS
  rewrite [single_def] at hS
  rewrite [hS.right]
  exact hy.left
  intro h3
  use {x}
  apply And.intro
  rewrite [set_builder_def]
  use x
  rewrite [single_def]
  rfl
  have h4 := h2 h3
  rewrite [set_builder_def] at h4
  obtain ⟨y, hy⟩ := h4
  use y
  exact hy.right
