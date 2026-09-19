import AbstractVoronoi.Jordan.ArcLimit

/-!
# Local connectedness at a boundary point, and accessibility

This file turns the *local connectedness* of a plane domain at a boundary point into the
*accessibility* of that point, in the sense of Theorem 4 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

The notion used is `AVD.LocallyConnectedAt D z`: for every `ε > 0` there is a `δ > 0` such
that any two points of `D` at distance less than `δ` from `z` can be joined by a path inside
`D` which stays at distance less than `ε` from `z`.  This is the classical uniform local
connectedness of `D` at the boundary point `z`.

The two results are:

* `AVD.exists_locally_connected_nbhd`: if the open set `D` is locally connected at a point
  `z` of its frontier, then arbitrarily small open connected sets `V ⊆ D` exist which
  contain `D ∩ ball z δ` for some `δ > 0` and from every point of which `z` is accessible by
  an arc;
* `AVD.locallyConnectedAt_of_accessibility`: conversely, the local structure asserted by
  Theorem 4 implies local connectedness, so that the latter is a *weaker* hypothesis.

The construction of the access arcs is `AVD.exists_arc_to_limit`.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- `LocallyConnectedAt D z`: the set `D` is *locally connected at the point `z`*, in the
uniform sense: for every `ε > 0` there is a `δ > 0` such that any two points of `D` within
distance `δ` of `z` can be joined by a path inside `D` staying within distance `ε` of `z`.

For a complementary domain `D` of a Jordan curve `C` and a point `z ∈ C` this is the local
structure of `C` at `z` that the (Jordan–Schönflies) Theorem 4 of
Klein–Langetepe–Nilforoushan (2009) provides; it is the hypothesis from which the
accessibility statements of that theorem are derived in this development. -/
def LocallyConnectedAt (D : Set Plane) (z : Plane) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D ∩ ball z δ, ∀ y ∈ D ∩ ball z δ, JoinedIn (D ∩ ball z ε) x y

/-- A path inside a set `S` joining `x` to `y` puts `y` in the connected component of `x`
in `S`. -/
theorem mem_connectedComponentIn_of_joinedIn {S : Set Plane} {x y : Plane}
    (h : JoinedIn S x y) :
    y ∈ connectedComponentIn S x := by
  obtain ⟨γ, hγ⟩ := h
  have hrange : range γ ⊆ S := by
    rintro w ⟨t, rfl⟩
    exact hγ t
  have hpre : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  have hx : x ∈ range γ := ⟨0, γ.source⟩
  exact hpre.subset_connectedComponentIn hx hrange ⟨1, γ.target⟩

/-- **The nested family of domains at a boundary point.**  If the open set `D` is locally
connected at a point `z` of its closure which does not belong to it, then there is a
decreasing sequence of non-empty open connected subsets of `D` shrinking to `z`, the first
of which lies in a prescribed ball around `z` and contains all the points of `D` in a
smaller ball.

This is the family to which `AVD.exists_arc_to_limit` is applied. -/
theorem exists_nested_components {D : Set Plane} {z : Plane} (hDopen : IsOpen D)
    (hzc : z ∈ closure D) (hlc : LocallyConnectedAt D z) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ (W : ℕ → Set Plane) (δ : ℝ), 0 < δ ∧ δ ≤ ε₀ ∧ D ∩ ball z δ ⊆ W 0 ∧
      (∀ n, IsOpen (W n)) ∧ (∀ n, IsPreconnected (W n)) ∧ (∀ n, (W n).Nonempty) ∧
      Antitone W ∧ (∀ ε > 0, ∃ n, W n ⊆ ball z ε) ∧ W 0 ⊆ D ∧ W 0 ⊆ ball z ε₀ := by
  classical
  -- the radius provided by local connectedness, as a function of `ε`
  have hchoice : ∀ e : ℝ, ∃ d : ℝ, 0 < e → (0 < d ∧ d ≤ e ∧
      ∀ x ∈ D ∩ ball z d, ∀ y ∈ D ∩ ball z d, JoinedIn (D ∩ ball z e) x y) := by
    intro e
    rcases le_or_gt e 0 with he | he
    · exact ⟨0, fun h => absurd h (not_lt.2 he)⟩
    · obtain ⟨d, hd, hjoin⟩ := hlc e he
      refine ⟨min d e, fun _ => ⟨lt_min hd he, min_le_right _ _, ?_⟩⟩
      intro x hx y hy
      exact hjoin x ⟨hx.1, ball_subset_ball (min_le_left d e) hx.2⟩ y
        ⟨hy.1, ball_subset_ball (min_le_left d e) hy.2⟩
  choose dfun hdfun using hchoice
  -- the sequence of radii
  set r : ℕ → ℝ := fun n => Nat.rec ε₀ (fun _ e => dfun e / 2) n with hrdef
  have hr0 : r 0 = ε₀ := rfl
  have hrsucc : ∀ n, r (n + 1) = dfun (r n) / 2 := fun _ => rfl
  have hrpos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero => rw [hr0]; exact hε₀
    | succ n ih => rw [hrsucc]; exact half_pos (hdfun (r n) ih).1
  have hrhalf : ∀ n, r (n + 1) ≤ r n / 2 := by
    intro n
    rw [hrsucc]
    have h := (hdfun (r n) (hrpos n)).2.1
    linarith
  have hranti : ∀ n, r (n + 1) ≤ r n := by
    intro n
    have := hrhalf n
    have := hrpos n
    linarith
  have hrmono : Antitone r := antitone_nat_of_succ_le hranti
  have hrbound : ∀ n, r n ≤ ε₀ / 2 ^ n := by
    intro n
    induction n with
    | zero => rw [hr0]; simp
    | succ n ih =>
        have h1 := hrhalf n
        have h2 : r n / 2 ≤ ε₀ / 2 ^ n / 2 := by linarith
        calc r (n + 1) ≤ r n / 2 := h1
          _ ≤ ε₀ / 2 ^ n / 2 := h2
          _ = ε₀ / 2 ^ (n + 1) := by ring
  have hrsmall : ∀ e > 0, ∃ n, r n < e := by
    intro e he
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (ε₀ / e) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, lt_of_le_of_lt (hrbound n) ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ he] at hn
    linarith
  -- the joining property between two successive radii
  have hjoin : ∀ n, ∀ x ∈ D ∩ ball z (r (n + 1)), ∀ y ∈ D ∩ ball z (r (n + 1)),
      JoinedIn (D ∩ ball z (r n)) x y := by
    intro n x hx y hy
    have hle : r (n + 1) ≤ dfun (r n) := by
      rw [hrsucc]
      have := (hdfun (r n) (hrpos n)).1
      linarith
    exact (hdfun (r n) (hrpos n)).2.2 x ⟨hx.1, ball_subset_ball hle hx.2⟩ y
      ⟨hy.1, ball_subset_ball hle hy.2⟩
  -- base points
  have hne : ∀ n : ℕ, (D ∩ ball z (r n)).Nonempty := by
    intro n
    obtain ⟨y, hyD, hdist⟩ := Metric.mem_closure_iff.1 hzc (r n) (hrpos n)
    exact ⟨y, hyD, by rwa [mem_ball, dist_comm]⟩
  choose xpt hxpt using fun n : ℕ => hne (n + 1)
  set W : ℕ → Set Plane := fun n => connectedComponentIn (D ∩ ball z (r n)) (xpt n) with hWdef
  have hxmem : ∀ n, xpt n ∈ D ∩ ball z (r n) :=
    fun n => ⟨(hxpt n).1, ball_subset_ball (hranti n) (hxpt n).2⟩
  have hWsub : ∀ n, W n ⊆ D ∩ ball z (r n) := fun n => connectedComponentIn_subset _ _
  have hWopen : ∀ n, IsOpen (W n) := fun n =>
    (hDopen.inter isOpen_ball).connectedComponentIn
  have hWconn : ∀ n, IsPreconnected (W n) := fun n => isPreconnected_connectedComponentIn
  have hWne : ∀ n, (W n).Nonempty := fun n =>
    connectedComponentIn_nonempty_iff.2 (hxmem n)
  -- the key inclusion: everything close enough to `z` lies in `W n`
  have hkey : ∀ n, D ∩ ball z (r (n + 1)) ⊆ W n := by
    intro n y hy
    exact mem_connectedComponentIn_of_joinedIn (hjoin n (xpt n) (hxpt n) y hy)
  have hWanti : Antitone W :=
    antitone_nat_of_succ_le fun n => (hWsub (n + 1)).trans (hkey n)
  refine ⟨W, r 1, hrpos 1, ?_, hkey 0, hWopen, hWconn, hWne, hWanti, ?_, ?_, ?_⟩
  · have := hrhalf 0
    rw [hr0] at this
    linarith
  · intro e he
    obtain ⟨n, hn⟩ := hrsmall e he
    exact ⟨n, fun x hx => ball_subset_ball hn.le (hWsub n hx).2⟩
  · exact fun x hx => (hWsub 0 hx).1
  · intro x hx
    have := (hWsub 0 hx).2
    rwa [hr0] at this

/-- **Accessibility from a locally connected domain.**

If the open set `D` is locally connected at a point `z` of its frontier, then for every
`ε > 0` there is an open connected set `V` with

* `V ⊆ D` and `V ⊆ ball z ε`,
* `D ∩ ball z δ ⊆ V` for some `δ > 0`,
* `z` is accessible inside `V` from *every* point of `V`.

This is the accessibility assertion of Theorem 4 of Klein–Langetepe–Nilforoushan (2009) for
one complementary domain, derived from the local connectedness of that domain at `z`. -/
theorem exists_locally_connected_nbhd {D : Set Plane} {z : Plane} (hDopen : IsOpen D)
    (hz : z ∉ D) (hzc : z ∈ closure D) (hlc : LocallyConnectedAt D z) {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : Set Plane) (δ : ℝ), IsOpen V ∧ IsPreconnected V ∧ V.Nonempty ∧ V ⊆ D ∧
      V ⊆ ball z ε ∧ 0 < δ ∧ δ ≤ ε ∧ D ∩ ball z δ ⊆ V ∧
      ∀ x ∈ V, AccessibleWithin V x z := by
  obtain ⟨W, δ, hδ, hδε, hδsub, hWopen, hWconn, hWne, hWanti, hWsmall, hW0D, hW0ball⟩ :=
    exists_nested_components hDopen hzc hlc hε
  refine ⟨W 0, δ, hWopen 0, hWconn 0, hWne 0, hW0D, hW0ball, hδ, hδε, hδsub, ?_⟩
  intro x hx
  have hzW : z ∉ W 0 := fun h => hz (hW0D h)
  obtain ⟨γ, harc, h0, h1, hsub⟩ :=
    exists_arc_to_limit hWopen hWconn hWne hWanti hWsmall hzW hx
  exact ⟨γ, harc, h0, h1, hsub⟩

/-- Conversely, the local structure asserted by Theorem 4 of
Klein–Langetepe–Nilforoushan (2009) implies the local connectedness used here: if `z` has
arbitrarily small neighbourhoods `U` such that `U ∩ D` is connected, then `D` is locally
connected at `z`.  Hence `AVD.LocallyConnectedAt` is a *weaker* hypothesis than the local
part of Theorem 4. -/
theorem locallyConnectedAt_of_small_connected {D : Set Plane} {z : Plane} (hDopen : IsOpen D)
    (h : ∀ V ∈ 𝓝 z, ∃ U : Set Plane, U ∈ 𝓝 z ∧ U ⊆ V ∧ IsOpen U ∧ IsConnected (U ∩ D)) :
    LocallyConnectedAt D z := by
  intro ε hε
  obtain ⟨U, hUnhds, hUV, hUopen, hUconn⟩ := h (ball z ε) (ball_mem_nhds z hε)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hUnhds
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  have hxU : x ∈ U ∩ D := ⟨hδU hx.2, hx.1⟩
  have hyU : y ∈ U ∩ D := ⟨hδU hy.2, hy.1⟩
  have hpath : IsPathConnected (U ∩ D) :=
    (hUopen.inter hDopen).isConnected_iff_isPathConnected.1 hUconn
  have := hpath.joinedIn x hxU y hyU
  refine this.mono ?_
  rintro w ⟨hwU, hwD⟩
  exact ⟨hwD, hUV hwU⟩

end AVD
