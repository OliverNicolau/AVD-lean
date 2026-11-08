# Publishing the repository

Everything in the repository is ready to be made public; what is left needs an account or a
decision that only the owner of the repository has.  This page is the short list, in the
order in which the steps are easiest to do.

## 1. Fill in the address of the repository

Until the repository exists, the files that must name it carry the placeholders `OliverNicolau`
and `AVD-lean`: the Lake `require` snippet of `README.md`, the CI badge of `README.md`
(hidden in a comment) and the `repository-code:` field of `CITATION.cff` (commented out).
After creating the repository, run once, from the root:

```
scripts/set-repository-url.sh OliverNicolau AVD-lean
```

The script replaces the placeholders everywhere, reveals the badge and the
`repository-code:` field, and lists the files it changed; check the result with `git diff`
before committing.

## 2. Repository settings on GitHub

* **Description** (suggested): *A Lean 4 formalization of the foundations of abstract
  Voronoi diagrams: Definition 1 – Theorem 10 of Klein, Langetepe and Nilforoushan (2009),
  with a self-contained development of the plane topology they use.*
* **Topics**: `lean4`, `mathlib`, `formalization`, `formal-methods`,
  `computational-geometry`, `voronoi-diagrams`, `plane-topology`, `theorem-proving`.
* **Website**: the GitHub Pages address of the API documentation, once step 4 is done.
* **Default branch**: `main` or `master` — the build workflow triggers on both.
* **Actions**: the `Build` workflow (`.github/workflows/lean.yml`) needs nothing beyond
  Actions being enabled; it builds `AbstractVoronoi.All`, runs the Mathlib linter and fails
  if a `sorry` appears.  Each run also compiles about 360 files of Tau Ceti, which has no
  prebuilt binaries usable here (about ten minutes on a 16-core laptop, longer on CI
  runners).
* The blueprint is tracked in the repository as
  [`blueprint/blueprint.pdf`](../blueprint/blueprint.pdf), so it can be linked from the
  description or the release notes directly.

## 3. Tag a release

The version in `lakefile.toml` is `0.2.0`; `CHANGELOG.md` describes what it contains.  Tag
the published commit so that downstream projects can pin a revision:

```
git tag -a v0.2.0 -m "AbstractVoronoi 0.2.0: Definition 1 – Theorem 10 of Klein–Langetepe–Nilforoushan"
git push origin v0.2.0
```

The `require` snippet of `README.md` already refers to `rev = "v0.2.0"`.  A GitHub release
made from that tag can use the corresponding section of `CHANGELOG.md` as its notes, with
the blueprint PDF attached.

## 4. API documentation on GitHub Pages

The `Documentation` workflow (`.github/workflows/docs.yml`) builds browsable HTML from the
docstrings with [`doc-gen4`](https://github.com/leanprover/doc-gen4), out of the auxiliary
Lake package in [`docbuild/`](../docbuild), and publishes it with GitHub Pages.  To switch
it on, set **Settings → Pages → Source** to **GitHub Actions**.  The workflow runs when a
`v*` tag is pushed and can be started by hand from the Actions tab; it is not run on every
push, because generating the documentation walks the whole import closure, Mathlib included,
and therefore takes a long time.  The generator is kept in a separate Lake package so that
an ordinary `lake build` does not have to download it.

The same documentation can be produced locally:

```
lake -d docbuild update doc-gen4
lake -d docbuild build AbstractVoronoi.All:docs
```

and read at `docbuild/.lake/build/doc/index.html`.  Generating it compiles `doc-gen4` and
then produces a page for every module of the import closure, Mathlib included — some twenty
thousand build jobs — so expect the first run to take on the order of an hour.

`doc-gen4` builds the "source" link of each page from the `origin` remote of the clone and
stops with `Could not interpret Git remote uri ... as a Github source repo` if that remote is
not on GitHub; in such a clone, run the second command as
`DOCGEN_SRC=file lake -d docbuild build AbstractVoronoi.All:docs`.  On GitHub, where the
workflow runs, the default is what you want.

## 5. What is quoted from the paper

The article is published by Elsevier and is not open access (© 2009 Elsevier B.V.).  This
repository does not redistribute it: the PDF is git-ignored, and the article is cited by DOI
with a link to the [publisher's
page](https://www.sciencedirect.com/science/article/pii/S0925772109000364), which may ask
for a subscription.  What the docstrings contain are the printed statements of the
definitions, lemmas and theorems, quoted so that each Lean declaration can be compared with
the statement it formalizes, together with their attribution.  If you would like a second
opinion on that before publishing, ask someone qualified: this page is not legal advice.

## 6. After publication

The mathematics that could follow is described in `notes/status-and-open-problems.md`:
Euler's inequality `AVD.EulerSphereInequality`, which would remove the hypothesis `hEuler`
of Theorem 10 and sharpen it to the classical `2n − 4` and `3n − 6`; the paper's orientation
convention, which would let Lemma 7 (ii) be stated literally; and the sections of the paper
after Theorem 10 (Lemma 11 onwards, the randomized incremental construction).  None of it is
needed for the repository to be published as it stands.
