import Mathlib

/-!
# Imports

Every file of the project imports this file (directly or indirectly); it collects `Mathlib`.

The planar topology the development takes from outside (the Jordan curve theorem, the
Jordan–Schönflies theorem, the connectedness of the complement of a simple arc) is imported
in one place only, `AbstractVoronoi/Jordan/Backend.lean`, which states those results and
proves them from Tau Ceti (<https://github.com/TauCetiProject/TauCeti>).
-/
