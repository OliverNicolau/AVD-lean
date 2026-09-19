# Configurations AA and BC in the proof of Lemma 8

> **Status.**  Every configuration described in this note is now formalized and proved, with
> no `sorry`: the only unproved statement of the project is the classical plane topology
> behind Euler's formula, used in Theorem 10 and unrelated to Lemma 8 (see
> `notes/euler-formula-and-counting.md`).
> Sections 1–4 below describe the figures of the paper and the
> arguments used, section 5 is the plan as it stood while the proof was being built (kept
> for the record, and partly superseded), and section 6 describes how the remaining cases
> were finally closed.

This note accompanies `AbstractVoronoi/AVD/CrossingCases.lean`,
`AbstractVoronoi/AVD/BCConfiguration.lean`, `AbstractVoronoi/AVD/SharedSegment.lean` and
`AbstractVoronoi/AVD/AAConfiguration.lean`.  It records

1. a careful description of Figs. 5–8 of Klein–Langetepe–Nilforoushan, *Abstract Voronoi
   diagrams revisited*, Computational Geometry 42 (2009) 885–902 (those figures carry the
   conventions that the text of the proof of Lemma 8 leaves implicit),
2. the exact state of the formalization of the proof of Lemma 8,
3. a rigorous reformulation of the paper's argument for configuration AA which avoids all
   orientation conventions, and which is now formalized and proved,
4. the argument for the separation step of configuration BC,
5. the plan that was followed for the rest of configuration BC,
6. the final treatment of configuration BC and of the degenerate configurations.

Throughout, `p, q, r` are three sites, `J(p,q)` and `J(p,r)` are the two bisecting curves
through the common point `w`, `D(p,q)` and `D(q,p)` are the two open domains of `J(p,q)`,
and `f`, `g` are proper parametrizations of `J(p,q)`, `J(p,r)` with `f 0 = g 0 = w`.  The
four local branches at `w` are

* `F⁻ = f((-δ,0))`, `F⁺ = f((0,δ))` on `J(p,q)`,
* `G⁻ = g((-δ,0))`, `G⁺ = g((0,δ))` on `J(p,r)`.

## 1. What the figures show

### Fig. 5 (p. 891) — the four branches

A horizontal line drawn with an arrow to the right is `J(p,q)`; the labels `q` above and
`p` below the line mean that `D(p,q)` is the **lower** half plane and `D(q,p)` the upper
one.  The point `w` sits on the line; the part of the line to the left of `w` is `F⁻`, the
part to the right is `F⁺`.  A second curve, `J(p,r)`, comes down from the upper left
(labelled `G⁻`), oscillates against the line infinitely often *without crossing it* — the
oscillations are drawn as bumps from above that touch the line and accumulate at `w` from
the left — passes through `w`, then oscillates below the line and leaves to the lower right
(labelled `G⁺`, with labels `r` above and `p` below its arrow, i.e. `D(p,r)` is below `G⁺`
near its end).  The caption states the situation depicted: `G⁻ ⊆ closure D(q,p)`,
`G⁺ ⊆ closure D(p,q)`, `F⁻ ⊆ closure D(p,r)`, `F⁺ ⊆ closure D(r,p)`.

The point of the picture is that the branches need **not** be contained in the *open*
domains: they may touch the other curve infinitely often, and those touching points may
accumulate at `w`.  This is exactly why the formal statements use closures
(`BranchBefore f (closure (C.D p r))` etc.), and why footnote 8 of the paper has to exclude
separately the case of a branch *contained* in the other curve.

### Fig. 6 (p. 891) — the proof of Lemma 7

The same horizontal `J(p,q)`, with `D(p,q)` below.  A large blob around `w` is the
Theorem 4 neighbourhood `U`, whose boundary is a closed Jordan curve.  The thick horizontal
segment through `z`, `w`, `z'` is `H`, the connected piece of `J(p,q) ∩ U` containing `w`;
it divides `U` into `U₁` (above `H`) and `U₂` (below `H`).  `J(p,r)` enters `U` from above
and crosses the thick arc `α₁ ⊆ U₁` joining `z` to `z'` at the marked point `y`.  The small
dotted semicircles near the right end of `α₁` depict the replacement of the "excursions" of
`α₁` into `D(p,q)` by finitely many circular arcs (footnote 9), so that `α₁` may be assumed
to run in the open half plane `D(q,p)`.  This proof is formalized as
`AVD.CurveSystem.not_crossing_aux`.

### Fig. 7 (p. 892) — the four configurations at `w`

All four pictures have `J(p,q)` drawn as the horizontal line with the arrow to the right,
labels `q` above and `p` below (so `D(p,q)` is the lower half plane), `F⁻` on the left and
`F⁺` on the right of `w`.  `J(p,r)` is the second curve through `w`, its arrow indicating
the direction of increasing parameter, and its own labels `p`/`r` telling on which side of
it `D(p,r)` lies.  The `=` and `≠` signs between two curve pieces say whether the two
pieces are allowed to coincide (the degenerate situations discussed just before Lemma 8) or
are supposed to be distinct.

* **AD** (upper left).  `J(p,r)` comes from the upper left (`G⁻`), descends to `w`, and
  leaves to the upper right (`G⁺`, arrow to the right, labels `r` above and `p` below, so
  `D(p,r)` is below `G⁺`).  Both branches of `J(p,r)` lie in the closed upper half plane
  `closure D(q,p)` — **case D for `G`** — while `F⁻, F⁺ ⊆ closure D(p,r)` — case A for `F`.
  Two `=` signs, one on each side of `w`, say that `F⁻` may coincide with `G⁻` and `F⁺`
  with `G⁺`.
* **DD** (upper right).  `J(p,r)` comes from the upper right (`G⁻`), descends to `w` and
  leaves to the upper **left** (`G⁺`, arrow to the left, labels `p` above `r`).  Again both
  branches of `J(p,r)` are in `closure D(q,p)`, and now the labels put `D(r,p)` below both
  of them, i.e. `F⁻, F⁺ ⊆ closure D(r,p)`: case D for `F` as well.  Two `=` signs again.
* **AA** (lower left).  `J(p,r)` **touches** the line at `w` from below: it comes from the
  lower right (`G⁻`, arrow to the lower right, labels `p` above and `r` below), rises to
  `w`, and goes back down to the lower left (`G⁺`, arrow to the left, labels `p` above and
  `r` below).  So both branches of `J(p,r)` lie in `closure D(p,q)` (case A for `G`) and
  the horizontal line lies on the `p` side of `J(p,r)`, i.e. `F⁻, F⁺ ⊆ closure D(p,r)`
  (case A for `F`).  Two points are marked: `a` on `G⁺` (left of `w`, below the line) and
  `b` on `G⁻` (right of `w`, below the line); these are the two points used in the
  argument.  Two `≠` signs (between `F⁻` and `G⁺` on the left, between `F⁺` and `G⁻` on the
  right) say that in configuration AA the two curves are supposed **not** to share a
  segment at `w`.  Locally at `w` the region of `p`, `D(p,q) ∩ D(p,r)`, consists of the two
  "wedges" between the line and the two branches of `J(p,r)`, while the pocket between `G⁻`
  and `G⁺` below `w` belongs to `D(r,p)`; this is the "region of `p` would be disconnected"
  of the proof.
* **BC** (lower right).  `J(p,r)` comes from the upper left (`G⁻`), **crosses** the line at
  `w` and leaves to the lower right (`G⁺`, labels `r` above and `p` below).  So
  `G⁻ ⊆ closure D(q,p)` and `G⁺ ⊆ closure D(p,q)` (case C for `G`) and, by Lemma 7 (ii),
  `F⁻ ⊆ closure D(p,r)` and `F⁺ ⊆ closure D(r,p)` (case B for `F`).  A `≠` sign sits
  between `G⁻` and `F⁻` (upper left) and between `G⁺` and `F⁻` (lower left), while `=`
  signs sit between `G⁻` and `F⁺` (upper right) and between `G⁺` and `F⁺` (lower right): in
  the degenerate cases `G⁻` may coincide with `F⁺`, and `G⁺` with `F⁺`.

### Fig. 8 (p. 893) — the discussion of case BC

Three pictures, all with the horizontal `J(p,q)` (`q` above, `p` below, arrow to the right,
`F⁻` left of `w`, `F⁺` right of `w`).

* **(1)** The good ordering.  `G⁻` descends from the upper right to `w`.  From `w` the
  branch `G⁺` goes downwards, sweeps to the left below the line (through the marked point
  `a` at the bottom) and rises to touch the line at the marked point `b`; from `b` it dips
  again (through the marked point `c`) and touches the line at the marked point `d`, which
  lies between `b` and `w`; an arrow just after `d` shows the direction of travel.  Walking
  along `G⁺` *backwards*, i.e. from far away towards `w`, one meets first `d` and then `b`,
  and `b` lies to the left of `d` on `F⁻`, hence farther from `w`: the order of the
  touching points is the same on the oriented `F⁻` and on the oriented `G⁺`.
* **(2)** The bad ordering, which the paper shows to be impossible.  Now the touching
  points on the line are, from the left, `d`, then `b`, then `w`, while `G⁺` leaving `w`
  reaches `b` first (after the dip through `a`) and `d` afterwards (after the dip through
  `c`), and then leaves to the left.  So the two points appear in the order `(d,b)` on `F⁻`
  and in the order `(b,d)` on `G⁺`.  The labels `p` above `r` below on the descending
  pieces show which side of `J(p,r)` is `D(p,r)`.  The paper says this is impossible "by
  the same formal proof as for AA".
* **(3)** The construction of the access arc.  A blob `U` (the Theorem 4 neighbourhood of
  `w`) around the part of the line near `w`.  Inside it: the thick segment `H` of `F⁻`
  adjacent to `w`, with its left endpoint marked; the curve `G⁻` entering `U` from the
  upper right and `G⁺` leaving through the bottom right, oscillating (the comb-like
  wiggles) against the line to the right of `w` but **not** meeting `H`; the grey shaded
  region `D` below `H`, bounded by `H`, by a piece of `G⁺` and by a piece of `∂U`; and a
  dashed arc `α` inside `D` ending at `w`.  This is the access arc: `α ∖ {w} ⊆ D ⊆
  U ∩ D(p,r)`, and the part of `α` near `w` also lies in `D(p,q)`, hence in `VR(p,S)`.

## 2. State of the formalization

`AVD.CurveSystem.lemma8_common_point` (the case where `w` lies on both curves) splits, via
the branch dichotomy of Lemma 6 (`AVD.CurveSystem.branch_dichotomy`), into

* the configurations in which **both** branches of one curve lie in the closure of the half
  plane of the other curve that is *not* labelled `p` (AD, DD, DA):
  `AVD.CurveSystem.lemma8_of_branches`, proved;
* everything else, i.e. one branch of `J(p,q)` in `closure D(p,r)` *and* one branch of
  `J(p,r)` in `closure D(p,q)`: `AVD.CurveSystem.lemma8_common_point_crossing`.  That
  hypothesis covers AA, BC and all the degenerate situations of the discussion preceding
  Lemma 8 (branches shared by the two curves).  It is proved by the case analysis described
  in §6.

The AA argument is rigorous and formalized (§3).  By itself it does not close
`lemma8_common_point_crossing`, which is phrased with closures and therefore also covers the
degenerate configurations, and BC; see §6 for those.

The following supporting results, all proved and `sorry`-free, are what that case analysis
is built from (the plan they were produced under is kept, for the record, in §5):

* `AVD.CurveSystem.no_preconnected_crossing` — the Jordan domain of Lemma 6 cannot be
  crossed by a connected piece of `J(p,q)` lying in the closure of `D(p,r)`;
* `AVD.CurveSystem.exists_branch_disjoint` — "a subsegment of `G⁺` with endpoint `w` must be
  wholly disjoint from `F⁻`", the step that the paper derives from the ordering discussion
  of Fig. 8(1)–(2);
* `AVD.IsProperLineParam.exists_first_exit` and `…exists_first_exit_neg` — the first exit of
  a curve from a bounded open set, which cuts out the pieces `H ⊆ F⁻` and `G⁺ ∩ U` of
  Fig. 8(3);
* `AVD.CurveSystem.exists_crosscut_arc` — those two pieces, joined at `w`, form a crosscut
  of `U`: an arc with both endpoints on `∂U` and relative interior inside `U`;
* `AVD.eq_domain_of_frontier_eq` — a non-empty connected open set is one of the two
  complementary domains of its frontier; this is the bridge which lets the crosscut theorem
  `AVD.exists_crosscut_domains` be applied to a Theorem 4 neighbourhood `U`, whose frontier
  is a closed Jordan curve.

## 3. Configuration AA, without orientations

The paper's AA argument ("the Voronoi region of `p` would be disconnected … this is in
conflict with the supposed orientation of `J(p,r)` at `w`") can be replaced by the
following argument, which uses no orientation at all.

**Claim.** Let `w ∈ J(p,q) ∩ J(p,r)` and let `f`, `g` be proper parametrizations with
`f 0 = g 0 = w`.  If both branches of `J(p,r)` at `w` lie in the *open* half plane
`D(p,q)`, and if one branch of `J(p,q)` at `w` lies in the *open* half plane `D(p,r)`, then
a contradiction follows.

*Proof.*  Pick `u < 0 < v` with `g([u,0)) ∪ g((0,v]) ⊆ D(p,q)`.  The two points `g u` and
`g v` lie on `J(p,r)` and are interior points of `D(p,q)`, so, exactly as in the three
Facts of the proof of Lemma 6, they are accessible from `VR(p,{p,q,r})` (Theorem 4 for
`J(p,r)`, plus shortening) and from `VR(r,{p,q,r})` (Theorem 4 and Lemma 5), and axiom `A₂`
joins the access arcs: there are arcs `π` and `ρ` from `g u` to `g v` with
`π° ⊆ VR(p,{p,q,r})` and `ρ° ⊆ VR(r,{p,q,r})`.  Their union is a closed Jordan curve `Γ`;
let `Dm` be its bounded and `Em` its unbounded complementary domain.  The argument already
formalized inside `lemma6_core` gives

  `g((u,v)) ⊆ Dm`,  `g((-∞,u)) ∪ g((v,∞)) ⊆ Em`,

so in particular `w = g 0 ∈ Dm`, and `J(p,r) ∩ Dm ⊆ g([u,v])`.

Let `x = f t₀` be a point of the branch of `J(p,q)` that lies in `D(p,r)`, with `t₀` so
small that `x ∈ Dm` (possible because `Dm` is open and `f` is continuous at `0`), and let
`V` be the connected component of the open set `Dm ∖ g([u,v])` that contains `x`.  Then:

* `V ⊆ D(p,r)`: `V` is connected, disjoint from `J(p,r)` (because `J(p,r) ∩ Dm ⊆ g([u,v])`)
  and contains `x ∈ D(p,r)`;
* `V` is bounded, being contained in `Dm`;
* the half curve `N = f((0,∞))` (or `f((-∞,0))`, whichever contains `x`) is connected and
  unbounded and meets `V`, hence it meets `frontier V`.

But a point `y ∈ N ∩ frontier V` cannot exist:

* `y ∉ Dm ∖ g([u,v])`, since otherwise `y` would lie in the same component `V`, which is
  open;
* if `y ∈ g([u,v])`: `g([u,v]) ∖ {w} ⊆ D(p,q)` is disjoint from `J(p,q) ⊇ N`, and `y ≠ w`
  because `f` is injective and `y = f t` with `t ≠ 0`;
* otherwise `y ∈ closure Dm ∖ Dm = frontier Dm = Γ = π ∪ ρ`; but `π ⊆ D(p,q)` (its relative
  interior lies in `VR(p) ⊆ D(p,q)` and its endpoints `g u`, `g v` are in `D(p,q)`), which
  is disjoint from `J(p,q) ⊇ N`, and `ρ° ⊆ VR(r) ⊆ D(r,p)` is disjoint from
  `closure V ⊆ closure D(p,r) = D(p,r) ∪ J(p,r)`, while the endpoints of `ρ` are again
  `g u, g v ∈ D(p,q)`.

Contradiction. ∎

Formally this is `AVD.CurveSystem.aa_configuration_impossible` in
`AbstractVoronoi/AVD/CrossingCases.lean`.  Its substance is isolated as the reusable
`AVD.CurveSystem.exists_trapping_radius`: under the hypothesis that both branches of
`J(p,r)` at `w` lie in the open half-plane `D(p,q)`, there is a radius `ε > 0` such that
every point `f t₀` of `J(p,q)` with `|t₀| < ε` lying in `D(p,r)` is trapped, i.e. every
connected piece of `J(p,q)` containing it and avoiding `w` is bounded.  Configuration AA is
then impossible because the half curve of `J(p,q)` through such a point is unbounded.  Both
rest on the new `AVD.CurveSystem.exists_lemma6_jordan_domain`, the first half of the proof
of Lemma 6, extracted from `lemma6_core` as a reusable statement.  The trapping form is the
one that the monotonicity step of case BC needs, since there the connected piece of
`J(p,q)` is an arc between two touching points rather than a half curve.

Note that the argument needs the branches in the *open* half planes.  This is precisely the
non-degeneracy assumption of footnote 8 of the paper: if a branch of `J(p,r)` at `w` is
contained in `J(p,q)`, the two curves share a segment at `w`, and the configuration is one
of the degenerate ones that the paper reduces to AD, DD and BC.

## 4. The separation step of BC, without the ordering argument

The paper proves "a subsegment of `G⁺` with endpoint `w` is disjoint from `F⁻`" by showing
that the points of `F⁻` met on the backward walk along `G⁺` occur in the same order on both
segments (Fig. 8(1) versus Fig. 8(2)), the bad order being excluded "by the same formal
proof as for AA".  The formalization uses a shorter route, which avoids orders altogether.

**Claim.**  Let `b = f(t) = g(s)` be a common point of `F⁻` and `G⁺` (so `t < 0 < s`), and
assume that `G⁺` contains points `g u, g v` of the *open* half plane `D(p,q)` with
`0 < u < s < v`.  This is impossible.

*Proof.*  Apply `exists_lemma6_jordan_domain` to `g u, g v`: the closed Jordan curve
`Γ = π ∪ ρ` of the proof of Lemma 6 bounds a domain `Dm` with `g((u,v)) ⊆ Dm` and
`g((-∞,u)) ∪ g((v,∞)) ⊆ Em`.  Hence `b = g s ∈ Dm` while `w = g 0 ∈ Em`.  The piece
`K = f([t,0])` of `J(p,q)` joins `b` to `w`, so the connected set `K` meets `Γ`.  But
`K ⊆ J(p,q)` is disjoint from `π ⊆ D(p,q)` (interior in `VR(p)`, endpoints `g u, g v`), and
`K ⊆ closure D(p,r)` by the BC hypothesis `F⁻ ⊆ closure D(p,r)`, which is disjoint from
`ρ° ⊆ VR(r) ⊆ D(r,p)` — and again from the endpoints `g u, g v ∈ D(p,q)`.  Contradiction. ∎

This is `AVD.CurveSystem.no_preconnected_crossing`.  Since, in the non-degenerate case, the
points of `G⁺` lying in the open `D(p,q)` accumulate at `w`, the hypothesis on `u, v` is
automatic for every common point close enough to `w`, which gives
`AVD.CurveSystem.exists_branch_disjoint`.  Note that the same argument does *not* apply to
touchings of `G⁺` with `F⁺` (whose branch lies in `closure D(r,p)`), in accordance with
Figs. 5 and 8(3), where such touchings accumulate at `w`.

## 5. The plan that was followed (kept for the record)

1. **The reduction.**  From the hypotheses of `lemma8_common_point_crossing` (branches in
   *closures*) one has to reach either the hypotheses of `aa_configuration_impossible`, or
   the BC configuration, or one of the degenerate configurations.  The paper does this in
   the paragraph preceding Lemma 8 and in footnote 8.  Formally, the following trichotomy is
   needed for a branch `B` of `J(p,r)` at `w` with `B ⊆ closure D(p,q)`: either
   `B ⊆ D(p,q)` after shrinking, or `B ⊆ J(p,q)` after shrinking, or `B` meets both `D(p,q)`
   and `J(p,q)` in every neighbourhood of `w` (the situation of Fig. 5).  The third case is
   the delicate one; the argument of §3 does survive it in part, since it uses only two
   *points* `g u`, `g v` of the branches inside `D(p,q)` — but then `g([u,v]) ∖ {w}` is no
   longer disjoint from `J(p,q)`, and the last step of §3 has to be strengthened: one has
   to show that the first point at which the half curve `N` leaves `V` cannot be one of the
   touching points on `g([u,v])`, e.g. by choosing `u`, `v` so that `g([u,v]) ∩ J(p,q)` is
   contained in the *branch* of `J(p,q)` through which `N` does not run, or by a
   compactness argument on the closed set `g([u,v]) ∩ J(p,q)`.
2. **Configuration BC.**  Here the conclusion is not a contradiction: an access arc has to
   be produced.  The plan, following Fig. 8, is
   1. *(done)* separation: a subsegment of `G⁺` at `w` is disjoint from `F⁻`, §4 above,
      `AVD.CurveSystem.exists_branch_disjoint`;
   2. *(done)* the crosscut: the piece of `F⁻` from the first exit point of `J(p,q)` back to
      `w`, followed by the piece of `G⁺` from `w` to the first exit point of `J(p,r)`, is an
      arc with both endpoints on `∂U` and relative interior inside `U`
      (`AVD.CurveSystem.exists_crosscut_arc`, from
      `AVD.IsProperLineParam.exists_first_exit`);
   3. *(to do)* the assembly of the neighbourhood: choose `U` by Theorem 4 — so that
      `frontier U` is a closed Jordan curve, `U ∩ D(p,r)` is connected and `w` is accessible
      from it — small enough that `J(p,q) ∩ U` and `J(p,r) ∩ U` consist of the four branches
      only (`AVD.IsProperLineParam.exists_nbhd`) and that the exit parameters fall inside
      the range where step 1 applies.  Two pieces of data have to be threaded through the
      existing Theorem 4 interface, which currently drops them:
      `AVD.CurveSystem.exists_theorem4_data` forgets the assertion
      `IsClosedJordanCurve (frontier U)`, and nothing records that `U` is the *bounded
      complementary domain* of that Jordan curve — which is what the crosscut theorem
      `AVD.exists_crosscut_domains` needs as its hypothesis `D ∪ E = Cᶜ`.  Both are available
      in the construction of the neighbourhood: `AVD.exists_local_nbhd_of_data` builds
      `U = Ω₁ ∪ Ω₂ ∪ g₁''(0,1)` from two crosscuts `k₁, k₂` of the two complementary domains
      of the bisecting curve, and `frontier U = k₁ ∪ k₂`.  Given the Jordan curve theorem for
      `frontier U` and the *connectedness* of `U` (also visible in that construction, and
      likewise not exported), `AVD.eq_domain_of_frontier_eq` identifies `U` with one of the
      two complementary domains of `frontier U`, which is exactly the input of
      `AVD.exists_crosscut_domains`;
   4. *(to do)* the two domains cut off by the crosscut: `AVD.exists_crosscut_domains`
      applied to the crosscut of step 2 and to the two arcs into which its endpoints divide
      `∂U`.  One gets two domains `P₁, P₂ ⊆ U` with `frontier Pᵢ = κ ∪ γᵢ`;
   5. *(to do)* the identification of the grey domain `D` of Fig. 8(3): one of the `Pᵢ`
      contains points of `VR(p,{p,q,r})` arbitrarily close to `w`, and the component of
      `Pᵢ ∖ (J(p,q) ∪ J(p,r))` containing such a point lies in `VR(p,{p,q,r})` (it is
      connected and avoids both curves).  This is the delicate step: the paper argues
      "`H` cannot enter `D(r,p)`; hence `D` belongs to `U ∩ D(p,r)`" and then that "`α` can
      leave `D(p,q)` only through points on `J(p,q)` to the left of `H`", i.e. that, inside
      `D` and near `w`, neither curve is met — for `J(p,q)` because near `w` it consists of
      `H` (on the boundary of `D`) and of `F⁺ ⊆ closure D(r,p)`, which is disjoint from
      `D(p,r) ⊇ D`, and for `J(p,r)` because near `w` it consists of the crosscut piece of
      `G⁺` and of `G⁻ ⊆ closure D(q,p)`.  Formally one also needs that `P₁ ∪ P₂ = U ∖ κ`
      (the θ-curve theorem, `AVD.crosscut_exhausts` in `AbstractVoronoi/Jordan/ThetaCurve.lean`),
      in order to place the point of `VR(p,{p,q,r})` in one of the two domains;
   6. *(to do)* accessibility: apply Theorem 4 to the closed Jordan curve `frontier Pᵢ` at
      the point `w ∈ κ`, obtaining an arc `α` with `α ∖ {w} ⊆ Pᵢ`, and shorten it so that
      its tail avoids the two curves, as in step 5; the tail then lies in
      `VR(p,{p,q,r})` and is the required access arc.

## 6. How the remaining configurations were closed

The plan of §5 was carried out, with one change of strategy in step 5: the identification of
the grey domain `D` of Fig. 8(3) is done without any orientation convention, and the
reduction of the degenerate configurations to AD, DD and BC (§5.1) is replaced by a direct
treatment of the shared-segment cases.

### 6.1 The crosscut engine (`AbstractVoronoi/AVD/BCConfiguration.lean`)

`AVD.exists_crosscut_split` (in `AbstractVoronoi/Jordan/CrosscutSplit.lean`) packages
steps 3–4 of §5: a crosscut `κ` of a bounded domain `U` whose frontier is a closed Jordan
curve cuts `U` into exactly two Jordan domains `Ω₁, Ω₂` with `Ω₁ ∪ Ω₂ = U ∖ κ`.

`AVD.CurveSystem.access_of_crosscut_aux` is the engine.  Its data are a Theorem 4
neighbourhood `U` of `w` for the curve `J(p,q)` — bounded, with a closed Jordan curve as
frontier, and with `U ∩ D(q,p)` connected — a Theorem 4 neighbourhood `Ur ⊆ U` for `J(p,r)`
with `Ur ∩ D(r,p)` connected, and a crosscut `κ` of `U` through `w` which meets neither
`D(q,p)` nor `D(r,p)`.  Let `Ω` be the domain cut off by `κ` which does *not* contain the
connected set `U ∩ D(q,p)`.  Then:

* `Ω` misses `D(q,p)`; being open it misses `J(p,q) = frontier D(q,p)` as well, so
  `Ω ⊆ D(p,q)`;
* provided `Ω` does not swallow the whole of `Ur ∩ D(r,p)`, that connected set lies in the
  *other* domain, so `Ω ∩ Ur` misses `D(r,p)` and, again by openness, `J(p,r)`; hence
  `Ω ∩ Ur ⊆ D(p,q) ∩ D(p,r) = VR(p,{p,q,r})`;
* `w` lies on the crosscut, hence on the closed Jordan curve `frontier Ω`, and Theorem 4
  applied to that curve produces the access arc (`AVD.accessibleFrom_of_jordan_domain`).

No orientation of the curves is used: the domain of Fig. 8(3) is *defined* as the one on the
far side of `D(q,p)`.

The proviso is guaranteed in two ways:

* **a joining set** (`access_of_crosscut_join`): a preconnected subset of `Ur` off the
  crosscut meeting both `D(q,p)` and `D(r,p)`.  Such a set cannot be split by the crosscut.
  A single point of the fourth quadrant `D(q,p) ∩ D(r,p)` near `w` is one
  (`access_of_crosscut`), and so is a small disc around a common point of the two curves
  lying off the crosscut (`access_of_crosscut_common_point`);
* **the Voronoi region itself**, in the degenerate case where the two curves coincide
  near `w` (§6.3).

Configuration BC is then `AVD.CurveSystem.bc_configuration_access`: the crosscut is the one
of §5 step 2, it misses `D(q,p)` because it consists of a piece of `J(p,q)` and a piece of
`closure D(p,q)`, and it misses `D(r,p)` symmetrically; the fourth quadrant is non-empty
near `w` by the hypothesis that distinguishes BC from AA.  When both branches of one of the
two curves lie on the `p`-side of the other, the crosscut can be taken to be the whole local
piece of that curve (`access_of_both_branches_f`, `access_of_both_branches_g`).

### 6.2 Configuration AA (`AbstractVoronoi/AVD/AAConfiguration.lean`)

If the fourth quadrant `D(q,p) ∩ D(r,p)` *is* empty near `w`, then each branch of each curve
lies in the closure of the half-plane of the other curve labelled by `p`
(`fourth_quadrant_of_branch`): a branch on the other side which is not contained in the
other curve produces points of the fourth quadrant arbitrarily close to `w`.  This is
configuration AA.

The touchings of Fig. 5 are then excluded by the separation lemma of §4 applied to all four
pairs of branches: `branchAfter_D_of_nondegenerate` upgrades "branch in the closed
half-plane" to "branch in the open half-plane" as soon as the branch is not contained in the
other curve.  The argument of §3 (`aa_configuration_impossible`) applies and AA is
impossible.  What is left is the case where a branch *is* contained in the other curve.

### 6.3 The shared-segment configurations (`AbstractVoronoi/AVD/SharedSegment.lean`)

After reversing parametrizations and exchanging `q` and `r`, one may assume that the branch
`G⁺` of `J(p,r)` is contained in `J(p,q)`.

*Both branches shared.*  Then the piece of `J(p,r)` inside `U` lies on both curves, so it
misses all four half-planes and is a legitimate crosscut.  With `U` chosen so that both
`U ∩ D(q,p)` and `U ∩ D(p,q)` are connected and `Ur` so that both `Ur ∩ D(r,p)` and
`Ur ∩ D(p,r)` are connected (`exists_theorem4_jordan_nbhd_both`), the proviso of the engine
holds: suppose `Ur ∩ D(r,p) ⊆ Ω`.  Since `Ω ⊆ D(p,q)` is non-empty and `U ∩ D(p,q)` is
connected and avoids the crosscut, `U ∩ D(p,q) ⊆ Ω`.  The connected set `Ur ∩ D(p,r)` also
avoids the crosscut, so it lies in `Ω` or in `Ω'`; in the first case `Ur ∖ J(p,r) ⊆ Ω`, so
the non-empty open set `Ω' ∩ Ur` would be contained in the curve `J(p,r)`, which is the
frontier of an open set and contains no open set; in the second case a point of
`VR(p,{p,q,r})` near `w` — one exists because `w ∈ frontier VR(p,{p,q,r})` — would lie in
`Ω ∩ Ω' = ∅`.  Both are impossible (`shared_both_branches_access`).

*One branch shared.*  Then `G⁻` is not contained in `J(p,q)`, so the separation lemma of §4
applies to `G⁻` and to each branch of `J(p,q)`, and the crosscut of Fig. 8(3) can be built
from `G⁻` and from one of the two branches of `J(p,q)`.  Which one is chosen is decided by
the shared branch itself: the points of `G⁺` near `w` lie on `J(p,q)`, hence — being distinct
from `w` — on one of its two branches, and the crosscut uses the *other* one.  A point `z` of
`G⁺` then lies on both curves, inside `Ur`, and off the crosscut, so a small disc around it
is a joining set (`shared_crosscut_access`, `shared_branch_access`).

Notably, the hypothesis that the fourth quadrant is empty near `w` is not needed in either
case, and the shared-segment configurations are settled without the orientation conventions
of Fig. 7 that the paper uses for them.
