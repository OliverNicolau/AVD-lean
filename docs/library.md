# The layout of the library

This document describes the Lean library file by file, and the development it builds on.
For the correspondence with the numbered statements of the paper, see
[`formalization.md`](formalization.md).

## Layout

The library is organized in three folders, so that the statements one wants to compare with
the paper are separated from the supporting theory.

| folder | contents |
| --- | --- |
| `AbstractVoronoi/Paper/` | **the numbered statements of the paper**, and nothing else |
| `AbstractVoronoi/Jordan/` | the planar topology: the Jordan curve theorem and everything built on top of it |
| `AbstractVoronoi/AVD/` | the API about systems of bisecting curves and their Voronoi diagrams |

Outside the library, `scripts/axioms.lean` is the axiom audit,
`scripts/set-repository-url.sh` fills in the address of the repository, `blueprint/` holds
the generated blueprint, `docbuild/` the auxiliary Lake package that generates the HTML API
documentation with `doc-gen4`, `docs/` this documentation (including
[`publishing.md`](publishing.md), the checklist for making the repository public), `notes/`
the accompanying working notes described below, `.github/workflows/` the continuous
integration (`lean.yml`) and documentation (`docs.yml`) workflows, `CHANGELOG.md` the list
of released versions, and `AGENTS.md` the conventions and checks for contributors.

The directory `notes/` contains

* `statement-check.md` — a statement-by-statement comparison of the formal declarations with
  the printed statements of the paper, listing every place where the two differ;
* `Lemma8-figures-and-plan.md` — a description of Figs. 5–8 of the paper, which carry
  conventions that the text of the proof of Lemma 8 leaves implicit, and a record of how
  each configuration of that proof is handled in the formalization;
* `euler-formula-and-counting.md` — what the `O(n)` count of Theorem 10 needs from Euler's
  formula for plane graphs, why an existing Lean formalization of Euler's formula does not
  supply it, and what is proved here instead;
* `status-and-open-problems.md` — what is proved, the one statement left open (Euler's
  inequality) and the shape of the work it needs, and the smaller improvements and
  continuations the development invites;
* `aristotle-session-log.md` — the log of the sessions that produced the library, kept for
  provenance only.

### `AbstractVoronoi/Paper/` — the statements of the paper

One file per numbered statement; the table matching them with the paper is in
[`formalization.md`](formalization.md#the-numbered-statements).  The equations (1) and (2) of
the paper (the Voronoi region and the Voronoi diagram of a curve system) are
`AVD.CurveSystem.VR` and `AVD.CurveSystem.V`, in `Paper/Definitions.lean`.

### `AbstractVoronoi/Jordan/` — planar topology

| file | contents |
| --- | --- |
| `Sphere.lean` | the plane, closed Jordan curves (in any space), the sphere `S²` and its stereographic projection, **axiom `A₁`** stated as in the paper, and the proof that such a curve admits a proper parametrization `ℝ → ℝ²` |
| `SupNorm.lean` | the sup norm of the plane, axis-parallel squares, and the model curve, the boundary of the square `[-1,1]²` |
| `Backend.lean` | **the trust boundary**: the only file importing the external planar-topology library; it states, and proves from Tau Ceti and Mathlib, the Jordan curve theorem, the connectedness of the complement of a simple arc and the Jordan–Schönflies theorem (see below) |
| `Arcs.lean` | arcs and accessibility |
| `Adapter.lean` | the adapter to `Backend.lean`: the two notions of arc and of closed Jordan curve are identified, and the Jordan curve theorem is restated |
| `ArcSurgery.lean` | surgery on arcs: reversal, subarcs, concatenation, first intersection point with a closed set, and the cutting step |
| `SimpleArcs.lean` | two points of an open connected plane set are joined by an arc inside it (`AVD.exists_isArc_of_isPreconnected`, `AVD.exists_arc_in_open`), and two points off a simple arc by an arc avoiding it (`AVD.exists_isArc_compl_arc`) |
| `CyclicParam.lean` | `1`-periodic parametrizations of closed Jordan curves, and the arcs cut out of a curve by a short parameter interval |
| `Schoenflies.lean` | the non-separation theorem for arcs, and the proof that each complementary domain of a closed Jordan curve has the **whole** curve as boundary (global part of **Theorem 4**) |
| `SphereTransfer.lean` | the transfer of that statement through the sphere to the unbounded curves of axiom `A₁` |
| `ArcLimit.lean` | the construction of an arc ending at the limit point of a nested family of domains (the access arcs of **Theorem 4**) |
| `LocalConnectivity.lean` | local connectedness of a plane set at a boundary point, and the access arcs it produces |
| `LocalStructure.lean` | the three `Prop`-valued forms of the local part of **Theorem 4**, the implications between them, and the proof of `AVD.jordanCurveLocalConnectedness` |
| `LocallyConnectedTransfer.lean` | local connectedness at a point is a topological and a local notion: it transports along a homeomorphism of the plane, or along one defined near the point only |
| `SchoenfliesClosed.lean` | **the local part of Theorem 4 for a closed Jordan curve, from the Jordan–Schönflies theorem**: the curve is carried onto the boundary of a square by a homeomorphism of the plane, and the two complementary domains of that square are locally connected at each of its boundary points |
| `SchoenfliesUnbounded.lean` | the same for the unbounded curves of axiom `A₁`, by charting the sphere away from a point off the completed curve |
| `ArcFacts.lean` | the two classical facts about arcs used implicitly in the paper (joining accessible points by an arc, and the plane trees of footnote 10), both proved |
| `Accessibility.lean` | every point of a closed Jordan curve is accessible from each complementary domain, and the approximate forms of that statement |
| `Crosscut.lean` | the cutting of a closed Jordan curve at two of its points into two arcs, and the **crosscut theorem** for a Jordan domain |
| `CrosscutSplit.lean` | a crosscut cuts a Jordan domain into exactly two Jordan domains (`AVD.exists_crosscut_split`), and a bounded domain whose frontier is a closed Jordan curve is the bounded complementary domain of that curve |
| `CircleParam.lean` | the standard parametrization of a circle of the plane |
| `CircularCrosscut.lean` | the connected components of the part of a circle lying in an open set are open circular arcs with endpoints on the frontier of the set |
| `SmallCrosscut.lean` | crosscuts of arbitrarily small diameter near a prescribed point of a closed Jordan curve |
| `SmallDomain.lean` | an open set whose frontier lies in a closed ball is itself in that ball, and the resulting **small Jordan subdomains** near a boundary point |
| `PlaneTools.lean` | further plane topology used by the local constructions |
| `ThetaCurve.lean` | the θ-curve theorem for a crosscut, from the local connectedness of the domain |
| `CircularTheta.lean` | the θ-curve theorem for a crosscut lying on a circle, with no extra hypothesis (auxiliary; not used by the main line) |
| `CrosscutNear.lean` | crosscuts near a point, in the form used by the local construction |
| `LocalAccessibility.lean` | the local part of **Theorem 4** for a closed Jordan curve, from local connectedness |
| `UnboundedLocal.lean` | the same for the unbounded curves of axiom `A₁` |
| `K33.lean` | the fact that `K₃,₃` has no plane embedding (Thomassen's argument used in Lemma 9), proved from the Jordan–Schönflies theorem and the θ-curve theorem |
| `LineComponents.lean` | an open subset of the line with finite frontier has finitely many components, at most one more than it has frontier points; the ends of a component are frontier points; and an open interval has at most two ends (`frontier I ⊆ {sInf I, sSup I}`) |
| `PlaneGraph.lean` | finite plane graphs, their faces and **Euler's formula**: an edge has at most two ends and the handshake inequality `3v ⩽ 2e` are proved here, and with them the counting bounds `AVD.EulerPlaneBounds`; the two classical topological inputs `AVD.PlaneGraphVertexDegree` (the degree condition, proved for the Voronoi diagram in `AVD/VertexDegree.lean`) and `AVD.EulerSphereInequality` (Euler's inequality, the only statement of the project that is not proved) are stated here |
| `ProperLocal.lean` | properly embedded lines near one of their points: affine reparametrization (`AVD.IsProperLineParam.affine`) and the fact that small balls around `γ a` pull back to small parameter intervals (`AVD.IsProperLineParam.exists_ball_preimage_subset`), whence the branch structure of a subarc at a frontier parameter (`AVD.IsProperLineParam.exists_branch`) |
| `ArcCompletion.lean` | **an arc that can be continued at both of its ends lies on a closed Jordan curve** (`AVD.exists_closedJordanCurve_extend`), and its form for two branches issued from a common point of two properly embedded curves (`AVD.exists_closedJordanCurve_two_branches`) |
| `LocalFaces.lean` | how many faces can meet at a point: if a closed plane set agrees, near a point `z`, with a subset of a single Jordan curve through `z`, then at most two faces have `z` in their closure (`AVD.faces_at_ncard_le_two_of_local_subset_jordan`) |

### `AbstractVoronoi/AVD/` — abstract Voronoi diagrams

| file | contents |
| --- | --- |
| `Basic.lean` | elementary consequences of Definition 1: symmetry of the bisecting curves (derived, not assumed), openness and disjointness of the Voronoi regions, the two domains of a bisecting curve, and the consequences of Theorem 4 used later |
| `ThreeSites.lean` | parametrizations of a bisecting curve through a point, its two local branches, `exists_lemma6_jordan_domain` (the closed Jordan curve construction behind Lemma 6, stated for reuse) and `lemma6_core` |
| `Branches.lean` | the dichotomy for the local branches of two bisecting curves at a common point |
| `CrossingCases.lean` | the case analysis of Fig. 7 in the proof of Lemma 8: the configurations AD, DD, DA (`lemma8_of_branches`), the impossibility of the non-degenerate AA (`exists_trapping_radius`, `aa_configuration_impossible`), and the two first steps of BC (`no_preconnected_crossing`, `exists_branch_disjoint`, `exists_crosscut_arc`) |
| `BCConfiguration.lean` | the construction of Fig. 8(3): a crosscut of a Theorem 4 neighbourhood of the boundary point cuts off a piece of the Voronoi region (`access_of_crosscut_aux`, `access_of_crosscut_join`, `access_of_crosscut`, `access_of_crosscut_common_point`), whence configuration BC (`bc_configuration_access`) and the configurations in which both branches of one curve lie on the `p`-side of the other (`access_of_both_branches_f`, `access_of_both_branches_g`) |
| `SharedSegment.lean` | the degenerate configurations in which the two curves share a segment at the boundary point (`shared_both_branches_access`, `shared_crosscut_access`, `shared_branch_access`) |
| `AAConfiguration.lean` | configuration AA: the branches lie in the *open* half-planes unless a segment is shared (`branchAfter_D_of_nondegenerate`), so AA is impossible (`lemma8_three_quadrants`), and the full case analysis at a point lying on two curves (`lemma8_common_point`) |
| `Graph.lean` | the Voronoi vertices, the Voronoi edges, and the three-site case of Lemma 9 |
| `Edges.lean` | the sets `B_{p,q}`, the finiteness of the set of Voronoi edges, and the structure of an edge: an open subarc of a bisecting curve whose ends are Voronoi vertices (`edge_isSubarc_and_ends`) |
| `Faces.lean` | the faces of the diagram are its non-empty Voronoi regions (`faceSet_V_eq`), there are at most `n` of them, every Voronoi vertex lies on at least three of them, and `V(S)` is a finite plane graph (`isFinitePlaneGraph`) |
| `VertexDegree.lean` | how many edges end at a Voronoi vertex: near a point the diagram consists of that point and of the edges ending there (`exists_nbhd_V_inter_subset`); if those all lie on a single bisecting curve, at most two faces meet there (`faces_at_le_two_of_edges_subset_J`); near one of its ends an edge is a single branch of the curve carrying it (`edge_isBranch_at_end`); and **at least three edges end at every Voronoi vertex** (`three_le_edges_at_vertex`), the degree condition of the Euler count |

Two further top-level files: `AbstractVoronoi/Imports.lean` collects `Mathlib` (every file
of the project imports it, directly or indirectly), and `AbstractVoronoi/All.lean` imports every module of the project.

## Dependency: Tau Ceti

The planar topology the paper relies on is taken from

> Tau Ceti, <https://github.com/TauCetiProject/TauCeti> (Apache License 2.0),

which is a Lake dependency of this project (pinned commit
`4908b0344e1be5f7e9e5af7f7e640464843a2c84`).  The project uses the toolchain
`leanprover/lean4:v4.36.0-rc2` and pins Mathlib at exactly the commit of Tau Ceti's own
manifest, `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`.  Tau Ceti has no prebuilt binaries
usable here, so a first build compiles about 360 of its files before the project.

Only `AbstractVoronoi/Jordan/Backend.lean` imports Tau Ceti.  It defines set-level simple
arcs and Jordan curves (`Backend.IsArc`, `Backend.IsArcBetween`, `Backend.IsJordanCurve`)
and proves from Tau Ceti and Mathlib

* the **Jordan curve theorem** (`Backend.jordan_curve_theorem`);
* the connectedness of the **complement of a simple arc** (`Backend.isConnected_compl_arc`);
* the **Jordan–Schönflies theorem** (`Backend.jordan_schoenflies_of_homeomorph`): every
  homeomorphism between two Jordan curves of the plane extends to a homeomorphism of the
  plane;
* that the boundary of the square `[-1,1]²` is a Jordan curve homeomorphic to every Jordan
  curve (`Backend.isJordanCurve_modelCurve`,
  `Backend.IsJordanCurve.nonempty_homeomorph_modelCurve`).

The plane is `EuclideanSpace ℝ (Fin 2)`; inside `Backend.lean` it is identified with the
plane `ℂ` of Tau Ceti by the linear isometry `Complex.orthonormalBasisOneI.repr`.
`AbstractVoronoi/Jordan/Adapter.lean` identifies the set-level notions of arc and Jordan
curve with the parametrized notions used in the rest of the library.  Arcs in open connected
sets, the non-separation theorem for arcs and the non-planarity of `K₃,₃` are proved in this
project (`Jordan/SimpleArcs.lean`, `Jordan/Schoenflies.lean`, `Jordan/K33.lean`).

It is the Jordan–Schönflies theorem that makes the *local* part of **Theorem 4** of the paper
provable: see `AbstractVoronoi/Jordan/SchoenfliesClosed.lean`.

Version 0.1.0 took this planar topology from Álvaro Begué's `schoenflies-lean`; that version
is tagged `v1-schoenflies`.

## Acknowledgements and dependencies

This formalization stands on work by others; none of the mathematics below is due to this
project.

* **The paper.**  R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams
  revisited*, Computational Geometry 42 (2009) 885–902,
  [doi:10.1016/j.comgeo.2009.03.002](https://doi.org/10.1016/j.comgeo.2009.03.002),
  [publisher's page](https://www.sciencedirect.com/science/article/pii/S0925772109000364)
  (not open access).  All
  numbered statements, all proofs and the figures referred to in the comments are theirs.
  The paper itself is not redistributed here; the `notes/` files describe what is used from
  it.
* **Lean 4** (<https://github.com/leanprover/lean4>), the proof assistant, by the Lean FRO;
  released under the Apache 2.0 licence.
* **Mathlib** (<https://github.com/leanprover-community/mathlib4>), the Lean mathematical
  library, by the Mathlib community; released under the Apache 2.0 licence.  It supplies
  all the general topology, analysis and combinatorics used here.
* **Tau Ceti** (<https://github.com/TauCetiProject/TauCeti>), pinned at commit
  `4908b0344e1be5f7e9e5af7f7e640464843a2c84`; released under the Apache 2.0 licence.  It
  supplies the Jordan curve theorem, the Jordan–Schönflies theorem and the fact that a
  simple arc does not separate the plane, from which `AbstractVoronoi/Jordan/Backend.lean`
  proves the inputs of the planar topology of `AbstractVoronoi/Jordan/`.
* **`schoenflies-lean`** (<https://github.com/alonamaloh/schoenflies-lean>), the Lean 4
  formalization of the Jordan–Schönflies theorem by Álvaro Begué.  Version 0.1.0 of this
  project was built on it (pinned at commit `05a43d29cde026618777db3d4e4316204ccca237`), and
  the sup-norm helpers of `AbstractVoronoi/Jordan/SupNorm.lean` are adapted from its
  `Schoenflies/Square.lean`.  See its repository for its own licence terms.
* The transitive Lake dependencies pinned in `lake-manifest.json` (Batteries, Aesop, Qq,
  ProofWidgets, LeanSearchClient, `import-graph`, Plausible, `lean4-cli`), each under its
  own licence.

The Lean sources of this repository are released under the Apache License 2.0
(see `LICENSE`) and were written by [Aristotle](https://aristotle.harmonic.fun); see the
"Citing" section of the top-level `README.md`.
