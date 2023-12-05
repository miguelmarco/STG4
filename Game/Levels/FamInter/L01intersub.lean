import Game.Levels.Combo

variable {U : Type}

World "FamInter"
Level 1
Title "La intersección de una familia es un subconjunto"

Introduction
"
En lenguaje matemático, la intersección de la familia $F$ suele denotarse como $\\bigcap F$.
En Lean, la intersección de una familia `F` se denota como `⋂₀ F`. (Puedes ingresar el símbolo
`⋂₀` escribiendo `\\I0`).

Supongamos que tenemos `F: Set (Set U)` y `x: U`. Entonces, `x ∈ ⋂₀ F` significa que para cada
conjunto `S`, si `S` está en `F`, entonces `x ∈ S`. Para escribir esta afirmación en Lean,
escribimos `∀ S, S ∈ F → x ∈ S`. Lean abrevia esta afirmación como `∀ S ∈ F, x ∈ S`.
El símbolo `∀` se llama el *cuantificador universal*, y puedes ingresarlo en Lean escribiendo
`\\forall`.

Al igual que con otras operaciones de teoría de conjuntos, tenemos un teorema que expresa esta
definición. Si `F: Set (Set U)` y `x: U`, entonces `fam_inter_def x F` es una prueba de la
afirmación `x ∈ ⋂₀ F ↔ ∀ S ∈ F, x ∈ S`.

En este nivel, manejarás estas ideas.
"

DefinitionDoc famint as "⋂₀"
"`⋂₀ F` es la intersección de la familia de conjuntos `F`. Para introducir el símbolo `⋂₀`,
teclea `\\I0`."

DefinitionDoc all as "∀"
"Si `P x` representa una afirmación sobre un objeto `x`, entonces `∀ x, P x` significa \"para todo
`x`, se cumple `P x`\".  Para introducir el símbolo `∀`, teclea `\\forall`."

NewDefinition famint all

lemma fam_inter_def (x : U) (F : Set (Set U)) : x ∈ ⋂₀ F ↔ ∀ S ∈ F, x ∈ S := by rfl

LemmaDoc fam_inter_def as "fam_inter_def" in "⋂₀⋃₀"
"Si `F : Set (Set U)` y `x : U`, entonces `fam_inter_def x F` es una prueba de la afirmación
`x ∈ ⋂₀ F ↔ ∀ S ∈ F, x ∈ S`."

NewLemma fam_inter_def

LemmaTab "⋂₀⋃₀"

/-- Supón que $F$ es una familia de conjuntos, y $A \in F$.  Entonces $\bigcap F \subseteq A$. -/
Statement (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x h2
  Hint "Como de costumbre, puede ser útil usar la táctica `rewrite` para reescribir la definición de
  `{x} ∈ ⋂₀ F`, usando el teorema `fam_inter_def`."
  rewrite [fam_inter_def] at h2
  Hint "Recuerda que `{h2} : ∀ S ∈ F, {x} ∈ S` es una forma abreviada de
  `{h2} : ∀ S, S ∈ F → {x} ∈ S`.  Como `∀` significa \"para todo\", se puede aplicar `{h2}`
  a cualquier conjunto--es decir, podemos proporcionar cualquier conjunto como `S` en `{h2}`.
  En particular, aplicándolo al conjunto `A`, concluimos que `A ∈ F → {x} ∈ A`.
  Para aplicar `{h2}` a `A`, símplemente escribimos `{h2}` seguido de `A`, con un espacio en medio.
  Así, tu siguiente paso puede ser `have h3 : A ∈ F → {x} ∈ A := {h2} A`."
  have h3 : A ∈ F → x ∈ A := h2 A
  Hint "Como también tenemos `h1 : A ∈ F`, puedes aplicar `{h3}` a `h1` para probar que `{x} ∈ A`.
  Esto significa que `{h3} h1` es una prueba del objetivo."
  exact h3 h1


Conclusion
"
Los últimos dos pasos podrían haberse combinado en un único paso. En general, si tienes
`h1 : A ∈ F` y `h2 : ∀ S ∈ F, P S`, donde `P S` es alguna afirmación sobre `S`, entonces `h2 A` es
una prueba de `A ∈ F →  P A`, y aplicando esa prueba a `h1` tenemos que `h2 A h1` es una prueba de
`P A`. Por ejemplo, si  `h1 : A ∈ F` y `h2 : ∀ S ∈ F, x ∈ S`, `h2 A h1` es una prueba de `x ∈ A`.
"
