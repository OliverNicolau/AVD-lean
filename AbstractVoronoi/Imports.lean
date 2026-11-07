import Mathlib

/-!
# Imports

Every file of the project imports this file (directly or indirectly); it collects `Mathlib`.

The planar topology the development takes from outside (the Jordan curve theorem, the
Jordan–Schönflies theorem, simple arcs in open connected sets) is imported in one place
only, `AbstractVoronoi/Jordan/Backend.lean`, which states those results and proves them from
the Lean 4 formalization of the Jordan–Schönflies theorem by Álvaro Begué
(<https://github.com/alonamaloh/schoenflies-lean>).
-/
