-- Here's the import to make Lean know about things called `Game`s
--import GameServer.Commands  --unnecessary because imported by first level

-- Here are the imports defining many worlds for the game `Game`.
-- Each world consists of a finite number of levels, and levels
-- are numbered 1,2,3,4... inside the level files.
--import Game.Levels.Subset   --only need to import last level
--import Game.Levels.Comp
--import Game.Levels.Inter
--import Game.Levels.Union
import Game.Levels.FamCombo

-- Here's what we'll put on the title screen
Title "Juego de Teoría de Conjuntos"
Introduction
"
# Bienvenido al Juego de Teoría de Conjuntos
#### Una introducción a la demostración matemática.

En este juego, resolverás una secuencia de niveles demostrando teoremas.
El juego se basa en un demostrador interactivo de teoremas llamado *Lean*.

Los teoremas en este juego tratarán sobre conjuntos.
Un *conjunto* es una colección de objetos; los objetos en la colección se llaman *elementos*
del conjunto. Por ejemplo, el conjunto de planetas en nuestro sistema solar tiene ocho elementos:
Mercurio, Venus, Tierra, Marte, Júpiter, Saturno, Urano y Neptuno.

# Lee esto.

Aprender a usar un demostrador interactivo de teoremas lleva tiempo. Obtendrás más provecho de este
juego si lees los textos de ayuda como este.

Para comenzar, haz clic en\"Mundo de subconjuntos\".

## Más

Abre \"Game Info\" en el menú  \"≡\" en la esquina superior derecha para obtener recursos, enlaces
y formas de interactuar con la comunidad Lean.

**Información**
*Versión del juego: 4.1*

## Guardado de progreso

El juego guarda tu progreso en el almacenamiento local del navegador. ¡Si lo borras, perderás tu progreso!

**Advertencia:** En la mayoría de los navegadores, borrar cookies también eliminará el
almacenamiento local (o \"datos del sitio local\"). ¡Asegúrate de descargar primero tu progreso en el juego!

## Créditos

- **Creador:** Daniel J. Velleman; basado en el Juego de Números Naturales, de Kevin Buzzard
- **Motor del juego:** Alexander Bentkamp, Jon Eugster, Patrick Massot
- **Traducción al español:** Miguel Marco

## Recursos

- [Foro de chat Lean Zulip](https://leanprover.zulipchat.com/)

## ¿Problemas?

Por favor, haz cualquier pregunta sobre este juego en el
[foro de chat Lean Zulip](https://leanprover.zulipchat.com/), por ejemplo, en el canal
\"New Members\". La comunidad estará encantada de ayudar. Ten en cuenta que el chat Lean Zulip es
un foro de investigación profesional. Utiliza tu nombre real completo allí, mantente en el tema
y sé amable. Si buscas un lugar menos formal (por ejemplo, si quieres publicar memes del juego de
teoría de conjuntos), dirígete al [Discord de Lean](https://discord.gg/WZ9bs9UCvx).

Alternativamente, si experimentas problemas/errores, también puedes abrir problemas en GitHub:

- Para problemas con el motor del juego, abre un
[issue en el repositorio lean4game](https://github.com/leanprover-community/lean4game/issues).
- Para problemas sobre el contenido del juego, abre un
[issue en el repositorio STG](https://github.com/djvelleman/STG4/issues).
"

-- Here we could add additional connections between the worlds
-- The game automatically computes connections between worlds based on introduced
-- tactics and theorems, but for example it cannot detect introduced definitions

-- Dependency Implication → Power -- `Power` uses `≠` which is introduced in `Implication`

-- Future plan for the game:
-- Dependency AdvAddition → AdvMultiplication → Inequality → Prime → Hard
-- Dependency Multiplication → AdvMultiplication
-- Dependency AdvAddition → EvenOdd → Inequality → StrongInduction

Dependency Intersecciones → Uniones
Dependency FamInter → FamUnion

MakeGame
