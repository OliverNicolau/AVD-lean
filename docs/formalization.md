# How the paper is formalized

This document is the bridge between the printed paper

> R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
> Computational Geometry 42 (2009) 885-902, doi:10.1016/j.comgeo.2009.03.002
> (publisher's page: <https://www.sciencedirect.com/science/article/pii/S0925772109000364>,
> not open access),

and the Lean library.  It says which declaration formalizes which numbered statement, where
the formal statement deliberately differs from the printed one, and what is proved and what
is assumed.  The file-by-file layout of the library is in [`library.md`](library.md); a
statement-by-statement comparison in more detail is in `notes/statement-check.md`.

## The numbered statements

| statement of the paper | Lean declaration | file |
| --- | --- | --- |
| Definition 1 | `AVD.CurveSystem`, `AVD.CurveSystem.Admissible` | `Paper/Definitions.lean` |
| Definition 2 | `AVD.CurveSystem.voronoiRegion`, `AVD.CurveSystem.voronoiDiagram` | `Paper/Definitions.lean` |
| Lemma 3 | `AVD.CurveSystem.lemma3` | `Paper/Lemma3.lean` |
| Theorem 4 | `AVD.JordanCurveAccessibility`, `AVD.theorem4` | `Paper/Theorem4.lean` |
| Lemma 5 | `AVD.CurveSystem.lemma5` | `Paper/Lemma5.lean` |
| Lemma 6 | `AVD.CurveSystem.lemma6` | `Paper/Lemma6.lean` |
| Lemma 7 (i), (ii) | `AVD.CurveSystem.lemma7_touching`, `AVD.CurveSystem.lemma7_crossing` | `Paper/Lemma7.lean` |
| Lemma 8 | `AVD.CurveSystem.lemma8` | `Paper/Lemma8.lean` |
| Lemma 9 | `AVD.CurveSystem.lemma9` | `Paper/Lemma9.lean` |
| Theorem 10 | `AVD.CurveSystem.theorem10` | `Paper/Theorem10.lean` |

The equations (1) and (2) of the paper (the Voronoi region and the Voronoi diagram of a
curve system) are `AVD.CurveSystem.VR` and `AVD.CurveSystem.V`, also in
`Paper/Definitions.lean`.

## Notes on the formalization

* Axiom `A₁` is stated exactly as in the paper: a bisecting curve is mapped to a closed
  Jordan curve through the north pole by stereographic projection to the sphere
  (`AVD.IsUnboundedJordanCurve`).  That such a curve is a properly embedded line, i.e. that
  it admits a proper continuous injective parametrization `ℝ → ℝ²` — the form in which the
  curves are used in Lemmas 6 to 8 — is *proved*
  (`AVD.IsUnboundedJordanCurve.exists_properParam`).
* The paper's requirement `J(p,q) = J(q,p)` is not part of the data of a curve system: it is
  derived from the fact that `J(p,q)` splits the plane into `D(p,q)` and `D(q,p)`
  (`AVD.CurveSystem.J_symm`).
* The formal notion of a curve system (`AVD.CurveSystem`) is slightly *more general* than the
  printed one.  The paper requires each curve `J(p,q)` to split the plane into two *unbounded
  domains*; the structure only requires the two labelled pieces `D(p,q)`, `D(q,p)` to be
  open, disjoint, preconnected and complementary to the curve.  Nothing is lost: for an
  admissible system the remaining properties are proved from axiom `A₁` — the two pieces are
  non-empty (`AVD.CurveSystem.D_nonempty`), hence domains
  (`AVD.CurveSystem.D_isConnected`), and unbounded (`AVD.CurveSystem.D_not_isBounded`).  The
  lemmas that identify them with the two complementary domains of the Jordan curve theorem
  therefore carry the admissibility hypothesis.
* The `O(n)` count of Theorem 10 is obtained in the paper from Euler's formula for plane
  graphs.  One topological input is *stated* but not proved here, and the proof of
  `theorem10` invokes it through the single `sorry` of the development: the **Euler
  inequality** `e + 1 ⩽ v + f` (`AVD.EulerSphereInequality`).  The other input, the **degree
  condition** at a Voronoi vertex — at least three edges end at it — is proved
  (`AVD.CurveSystem.three_le_edges_at_vertex`): near a vertex the diagram consists of the
  vertex and of the edges ending there, each of which is a single branch of its bisecting
  curve; if there were at most two such branches they would form an arc through the vertex,
  which lies on a closed Jordan curve, so at most two faces could meet there, whereas three
  faces meet at a Voronoi vertex.
  The counting that turns the two inputs into the bounds `v ⩽ 2f`, `e ⩽ 3f` used by the paper
  is proved (`AVD.IsFinitePlaneGraph.ncard_le_of_degree`).  Everything else `theorem10` asserts — the finite
  plane graph structure — is proved, as are the sharper Euler-free bounds `2·C(n,3)` on the
  vertices and `C(n,2)·(2·C(n,3) + 1)` on the edges, kept as separate lemmas so that the
  statement of `theorem10` stays close to the printed one.  See
  `notes/euler-formula-and-counting.md`.

In four places the formal statement is slightly *stronger* than the printed one; each time
the docstring of the declaration says so.

* **Theorem 4**: "there exists a neighbourhood `U`" is strengthened to "arbitrarily small
  such neighbourhoods `U` exist", which is how the paper uses the theorem ("we can make `U`
  small enough").
* **Lemma 7**: the branches are only assumed to lie in the *closures* of the half-planes,
  as in part (i) of the paper's statement; and only two of the four non-degeneracy
  conditions of footnote 8 (those for the two branches of `J(p,q)`) are needed.
* **Lemma 7 (ii)**: the paper fixes which of the two crossing patterns occurs by its
  orientation convention ("`D(p,r)` lies on the right hand side of `J(p,r)` as `t` tends to
  `+∞`"); that convention is not formalized, so the conclusion is stated in the
  orientation-free form "the two branches of `J(p,r)` lie in the closures of *different*
  half-planes of `J(p,q)`", which is the assertion of the lemma together with its "`+` and
  `−` reversed" variant.
* **Lemma 9**: the hypothesis `n ⩾ 3` is not needed (for `n < 3` both sides of the bound are
  `0`) and is therefore omitted.

## What is proved and what is assumed

**One statement is left open, and it is used in exactly one place.**  The project contains a
single `sorry`, in the proof of **Theorem 10**: Euler's inequality `e + 1 ⩽ v + f`, stated as
`AVD.EulerSphereInequality` in `AbstractVoronoi/Jordan/PlaneGraph.lean`, from which the paper
reads off the count `O(n)`.  The other input of that count, the degree condition at a Voronoi
vertex — at least three edges end at it — is proved
(`AVD.CurveSystem.three_le_edges_at_vertex`).  Both are discussed in
`notes/euler-formula-and-counting.md`; the counting step that derives the bounds the paper
uses from them is proved.  Everything else is proved: Definition 1 to Lemma 9
and every supporting statement depend only on the standard axioms of Lean (`propext`,
`Classical.choice`, `Quot.sound`) on top of the Jordan–Schönflies dependency described
above, and `AVD.CurveSystem.theorem10` is the only declaration of the project depending on
`sorryAx`.  In particular:

* **Lemma 3** and **Lemma 5** are proved *unconditionally*: the only input they take from
  Theorem 4 is that a bisecting curve is the common boundary of its two domains
  (`AVD.CurveSystem.frontier_D_eq_J`), which is proved;
* **Theorem 4** is proved *unconditionally* (`AVD.theorem4` uses only the axioms `propext`,
  `Classical.choice` and `Quot.sound`).  Its *global* part — the separation of the plane
  into two domains with common boundary `C` — is
  `AVD.IsClosedJordanCurve.exists_separation_frontier_eq` (by the classical "theta curve"
  argument on top of the Jordan curve theorem and the non-separation theorem for arcs) and,
  for the unbounded curves of axiom `A₁`,
  `AVD.IsUnboundedJordanCurve.exists_separation_frontier_eq` (by the transfer through the
  sphere that the paper performs).  Its *local* part is proved from the local connectedness
  of the two complementary domains at the points of the curve
  (`AVD.jordanCurveLocalConnectedness`), in `Jordan/LocalAccessibility.lean` and
  `Jordan/UnboundedLocal.lean`; that local connectedness is itself proved from the
  Jordan–Schönflies theorem of the dependency, in `Jordan/SchoenfliesClosed.lean` (closed
  curves) and `Jordan/SchoenfliesUnbounded.lean` (unbounded curves);
* **Lemma 6**, **Lemma 7** (i) and (ii) are proved from Theorem 4;
* **Lemma 8** is proved in full.  The cases in which the boundary point lies on only one
  bisecting curve and the configurations AD, DD, DA of Fig. 7 (`lemma8_of_branches`) follow
  Lemma 7; the non-degenerate configuration AA is impossible
  (`aa_configuration_impossible`); configuration BC is settled by the construction of
  Fig. 8(3) (`bc_configuration_access`), whose two first steps are the separation of the two
  curves near the boundary point (`exists_branch_disjoint`, which replaces the ordering
  discussion of Fig. 8(1)–(2) by a direct use of the Jordan domain of Lemma 6) and the
  crosscut itself (`exists_crosscut_arc`).  The identification of the domain cut off by the
  crosscut is carried out with no orientation convention (`access_of_crosscut_aux`), and the
  degenerate configurations in which the two curves share a segment — which the paper
  disposes of by its orientation conventions, and which footnote 8 of the paper excludes
  from the discussion of Fig. 7 — are settled in `AVD/SharedSegment.lean`;
* **Lemma 9** is proved in full, including Thomassen's argument for three sites;
* **Theorem 10**: the plane graph structure is proved — the Voronoi diagram is the disjoint
  union of its finite set of Voronoi vertices and of its finitely many edges, each of which
  is connected and contained in a single bisecting curve.  So are the two facts about the
  diagram that the Euler count needs: the faces of `V(S)` are the Voronoi regions, of which
  there are at most
  `n` (`AVD.CurveSystem.faceSet_V_eq`, `…faceSet_V_ncard_le`), and every Voronoi vertex lies
  on the closures of at least three faces (`AVD.CurveSystem.three_le_faces_at_vertex`);
  moreover the diagram is a finite plane graph in the sense of `AVD.IsFinitePlaneGraph`
  (`AVD.CurveSystem.isFinitePlaneGraph`), each edge being an open subarc of a bisecting
  curve whose ends are Voronoi vertices (`AVD.CurveSystem.edge_isSubarc_and_ends`).  The
  final count `|B'| ⩽ 2n` and `|E| ⩽ 3n` — the `O(n)` of the paper, and the only numerical
  assertion in the statement of `theorem10` — is deduced from the proved degree condition at
  a Voronoi vertex (`AVD.CurveSystem.three_le_edges_at_vertex`) and the unproved
  `AVD.EulerSphereInequality` by a proved counting argument
  (`AVD.IsFinitePlaneGraph.ncard_le_of_degree`, which uses the proved handshake inequality
  `AVD.IsFinitePlaneGraph.three_mul_vtx_le_two_mul_edge` and the fact that an edge has at most
  two ends, `AVD.IsFinitePlaneGraph.edge_ends_ncard_le_two`).  Sharper bounds that do not use Euler's formula are proved separately:
  at most `2·C(n,3)` vertices (`AVD.CurveSystem.vertexSet_ncard_le`, Lemma 9) and at most
  `C(n,2)·(2·C(n,3) + 1)` edges (`AVD.CurveSystem.edgeSet_ncard_le`).

Proved with no assumption at all, along the way:

* `AVD.noPlaneEmbeddingK33` — the complete bipartite graph `K₃,₃` has no plane embedding;
* `AVD.exists_arc_of_accessible` and `AVD.exists_star_of_accessible` — two, respectively
  three, points accessible from an open path-connected set can be joined by an arc,
  respectively a plane tree, whose relative interior lies in that set (the three "Facts" of
  the proof of Lemma 6 and the trees `T_j` of footnote 10);
* `AVD.IsClosedJordanCurve.exists_separation` and `…exists_separation_frontier` — the Jordan
  curve theorem for the notion of closed Jordan curve used here, and the parts of Theorem 4
  that follow from it;
* `AVD.exists_arc_avoiding_arc` — the non-separation theorem for arcs;
* `AVD.IsClosedJordanCurve.locallyConnectedAt` and
  `AVD.IsUnboundedJordanCurve.locallyConnectedAt` — the local connectedness of the
  complementary domains of a Jordan curve at the points of the curve, from the
  Jordan–Schönflies theorem;
* `AVD.IsClosedJordanCurve.accessibleWithin`, `…exists_access_arc_in_subarc`,
  `…exists_access_arc_near`, `…dense_accessible` — every point of a closed Jordan curve is
  accessible from each complementary domain;
* `AVD.IsClosedJordanCurve.exists_arc_decomposition` and `AVD.exists_crosscut_domains` — the
  decomposition of a closed Jordan curve into two arcs, and the crosscut theorem for a
  Jordan domain;
* `AVD.exists_circular_crosscut`, `AVD.IsClosedJordanCurve.exists_small_crosscut(_in)` and
  `…exists_small_crosscut_domain` — crosscuts of arbitrarily small diameter near a point of
  the curve, and the small Jordan subdomains they bound;
* `AVD.circular_crosscut_exhausts` — the θ-curve theorem for a crosscut lying on a circle;
* `AVD.exists_arc_in_open` — an open connected plane set is arcwise connected;
* `AVD.isClosedJordanCurve_of_arcs`, `AVD.IsUnboundedJordanCurve.exists_properParam` and
  `AVD.finite_components_of_finite_frontier`.

## The blueprint

`blueprint/generate.py` extracts, from the files of `AbstractVoronoi/Paper/`, the docstring
of each numbered statement (which quotes the paper) and the Lean statement itself, and
writes

* `blueprint/blueprint.tex` — a LaTeX document, and `blueprint/blueprint.pdf`, compiled from
  it with `tectonic blueprint/blueprint.tex` (XeLaTeX also works; the Lean snippets are
  typeset in DejaVu Sans Mono);
* `blueprint/blueprint.md` — the same document in Markdown, for reading on the web.

Re-run `python3 blueprint/generate.py` after changing a statement in `AbstractVoronoi/Paper/`.
