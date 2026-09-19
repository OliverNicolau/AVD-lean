import Mathlib
import Schoenflies

/-!
# Imports

This project depends on the Lean 4 formalization of the **Jordan–Schönflies theorem** by
Álvaro Begué (<https://github.com/alonamaloh/schoenflies-lean>), which proves, with no
`sorry` and only the standard axioms, the Jordan curve theorem, the crosscut theorem, the
non-planarity of `K₃,₃` and the Jordan–Schönflies extension theorem for the plane
`EuclideanSpace ℝ (Fin 2)` — the same plane this development works with.

This file collects that dependency together with `Mathlib`, and every file of the project
imports it (directly or indirectly).
-/
