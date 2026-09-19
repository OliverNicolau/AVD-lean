#!/usr/bin/env python3
"""Generate the blueprint of the formalization.

The blueprint is a human-readable document that puts side by side the numbered statements of

    R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
    Computational Geometry 42 (2009) 885-902,

as they are quoted in the docstrings of the formalization, and the Lean statements that
formalize them.  Everything it contains is extracted from the Lean sources in
`AbstractVoronoi/Paper/`, so it cannot drift away from them.

Usage (from the root of the project):

    python3 blueprint/generate.py        # writes blueprint/blueprint.tex and blueprint.md
    tectonic blueprint/blueprint.tex     # (or xelatex) to get blueprint.pdf
"""

import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "blueprint")

# ---------------------------------------------------------------------------
# what goes into the blueprint, in the order of the paper
# ---------------------------------------------------------------------------

ITEMS = [
    ("Bisecting curve systems", "Paper/Definitions.lean", ["CurveSystem"], "full"),
    ("The Voronoi region (1) and the Voronoi diagram (2)", "Paper/Definitions.lean",
     ["VR", "V"], "full"),
    ("Definition 1", "Paper/Definitions.lean", ["Admissible"], "full"),
    ("Definition 2", "Paper/Definitions.lean", ["voronoiRegion", "voronoiDiagram"], "full"),
    ("Lemma 3", "Paper/Lemma3.lean", ["lemma3"], "statement"),
    ("Theorem 4", "Paper/Theorem4.lean", ["JordanCurveAccessibility", "theorem4"], "mixed"),
    ("Lemma 5", "Paper/Lemma5.lean", ["lemma5"], "statement"),
    ("Lemma 6", "Paper/Lemma6.lean", ["lemma6"], "statement"),
    ("Lemma 7", "Paper/Lemma7.lean", ["lemma7_touching", "lemma7_crossing"], "statement"),
    ("Lemma 8", "Paper/Lemma8.lean", ["lemma8"], "statement"),
    ("Lemma 9", "Paper/Lemma9.lean", ["lemma9"], "statement"),
    ("Theorem 10", "Paper/Theorem10.lean", ["theorem10"], "statement"),
]

# The statement the development does not prove: Euler's inequality for plane graphs, from
# which the proof of Theorem 10 reads off the count O(n).  It is printed together with the
# plane-graph vocabulary it is stated in, and with the degree condition at a Voronoi vertex,
# which is proved.
ASSUMPTIONS = [("Jordan/PlaneGraph.lean",
                ["faceSet", "IsFinitePlaneGraph", "EulerFormula", "EulerPlaneBounds",
                 "PlaneGraphVertexDegree", "EulerSphereInequality"]),
               ("AVD/VertexDegree.lean",
                ["faces_at_le_two_of_edges_subset_J", "two_le_edges_at_vertex",
                 "three_le_edges_at_vertex"])]

# ---------------------------------------------------------------------------
# reading the Lean sources
# ---------------------------------------------------------------------------

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def|noncomputable def|structure|abbrev)"
    r"\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def declarations(path):
    """Return a dict `name -> (docstring, code)` for the declarations of a file."""
    lines = open(os.path.join(ROOT, "AbstractVoronoi", path)).read().split("\n")
    out = {}
    i = 0
    while i < len(lines):
        if lines[i].startswith("/--"):
            j = i
            while "-/" not in lines[j]:
                j += 1
            doc = "\n".join(lines[i:j + 1])
            doc = doc[3:doc.rindex("-/")].strip("\n")
            k = j + 1
            while k < len(lines) and not DECL.match(lines[k]):
                k += 1
            if k == len(lines):
                i = j + 1
                continue
            name = DECL.match(lines[k]).group(1)
            e = k + 1
            while e < len(lines) and (lines[e][:1] in (" ", "\t") or lines[e] == ""):
                e += 1
            out[name] = (doc, "\n".join(lines[k:e]).rstrip())
            i = e
        else:
            i += 1
    return out


def statement_only(code):
    """Cut a theorem at the start of its proof."""
    m = re.search(r"\s*:=\s*by\b", code)
    if m:
        return code[:m.start()].rstrip()
    m = re.search(r"\n\s*:=\s", code)
    if m:
        return code[:m.start()].rstrip()
    return code.rstrip()


# ---------------------------------------------------------------------------
# turning the docstrings into LaTeX
# ---------------------------------------------------------------------------

TEX_ESCAPE = {"\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "$": r"\$",
              "&": r"\&", "#": r"\#", "%": r"\%", "_": r"\_", "^": r"\^{}",
              "~": r"\textasciitilde{}"}

UNICODE = {
    "¬": r"$\lnot$", "²": r"$^2$", "·": r"$\cdot$", "ö": r'\"o', "α": r"$\alpha$",
    "ε": r"$\varepsilon$", "ι": r"$\iota$", "ᵢ": r"$_i$", "ᶜ": r"$^{\mathrm{c}}$",
    "–": "--", "—": "---", "⁺": r"$^+$", "⁻": r"$^-$", "₀": r"$_0$", "₁": r"$_1$",
    "₂": r"$_2$", "₃": r"$_3$", "₄": r"$_4$", "ℝ": r"$\mathbb{R}$",
    "←": r"$\leftarrow$", "→": r"$\to$", "∀": r"$\forall$", "∃": r"$\exists$",
    "∈": r"$\in$", "∉": r"$\notin$", "∑": r"$\sum$", "−": "$-$", "∓": r"$\mp$",
    "∞": r"$\infty$", "∧": r"$\land$", "∨": r"$\lor$", "∩": r"$\cap$", "∪": r"$\cup$",
    "≠": r"$\neq$", "≤": r"$\leq$", "⊆": r"$\subseteq$", "⋂": r"$\bigcap$",
    "⋃": r"$\bigcup$", "▸": r"$\blacktriangleright$", "⟨": r"$\langle$",
    "⟩": r"$\rangle$", "⩾": r"$\geq$", "𝓝": r"$\mathcal{N}$", "∖": r"$\setminus$",
    "π": r"$\pi$", "γ": r"$\gamma$", "κ": r"$\kappa$", "δ": r"$\delta$",
    "Ω": r"$\Omega$", "θ": r"$\theta$", "ρ": r"$\rho$", "β": r"$\beta$",
    "φ": r"$\varphi$", "×": r"$\times$", "≥": r"$\geq$", "⊇": r"$\supseteq$",
    "∅": r"$\emptyset$", "↦": r"$\mapsto$", "ₙ": r"$_n$", "′": r"$'$",
    "“": "``", "”": "''", "’": "'", "‘": "`",
}


def tex_text(s):
    out = []
    for ch in s:
        if ch in TEX_ESCAPE:
            out.append(TEX_ESCAPE[ch])
        elif ord(ch) > 127:
            out.append(UNICODE.get(ch, ch))
        else:
            out.append(ch)
    return "".join(out)


CODE_UNICODE = {"⋃": r"\(\bigcup\)", "⋂": r"\(\bigcap\)", "𝓝": r"\(\mathcal{N}\)",
                "∖": r"\(\setminus\)", "⩾": r"\(\geq\)", "∓": r"\(\mp\)",
                "▸": r"\(\blacktriangleright\)"}


def tex_code(code):
    """A Lean snippet, verbatim, in an `alltt` environment."""
    out = []
    for ch in code:
        if ch == "\\":
            out.append(r"\textbackslash{}")
        elif ch == "{":
            out.append(r"\{")
        elif ch == "}":
            out.append(r"\}")
        else:
            out.append(CODE_UNICODE.get(ch, ch))
    return "\\begin{leancode}\n" + "".join(out) + "\n\\end{leancode}\n"


def tex_inline(s):
    """Prose with `code spans`, **bold** and *emphasis*."""
    out = []
    for p in re.split(r"(`[^`]*`)", s):
        if len(p) > 1 and p.startswith("`") and p.endswith("`"):
            # long identifiers such as `AVD.CurveSystem.lemma8` must be breakable
            body = tex_text(p[1:-1]).replace(".", ".\\allowbreak{}")
            body = body.replace(r"\_", r"\_\allowbreak{}")
            out.append(r"\texttt{" + body + "}")
        else:
            t = tex_text(p)
            t = re.sub(r"\*\*([^*]+)\*\*", r"\\textbf{\1}", t)
            t = re.sub(r"(?<![A-Za-z*])\*([^*\n]+)\*(?![A-Za-z*])", r"\\emph{\1}", t)
            out.append(t)
    return "".join(out)


def tex_doc(doc):
    """A Lean docstring as LaTeX: `>` blocks become quotations, `*` become items."""
    paragraphs = []
    buf, mode = [], None

    def flush():
        nonlocal buf, mode
        if buf:
            if mode == "quote":
                paragraphs.append("\\begin{quotation}\\noindent\n"
                                  + tex_inline(" ".join(buf)) + "\n\\end{quotation}")
            elif mode == "item":
                paragraphs.append("\\begin{itemize}\n"
                                  + "\n".join("\\item " + tex_inline(x) for x in buf)
                                  + "\n\\end{itemize}")
            else:
                paragraphs.append(tex_inline(" ".join(buf)))
        buf, mode = [], None

    for line in doc.split("\n"):
        stripped = line.strip()
        if stripped == "":
            flush()
        elif stripped.startswith("> "):
            if mode != "quote":
                flush()
                mode = "quote"
            buf.append(stripped[2:])
        elif stripped.startswith("* "):
            if mode != "item":
                flush()
                mode = "item"
            buf.append(stripped[2:])
        elif mode == "item":
            buf[-1] += " " + stripped
        else:
            mode = mode or "text"
            buf.append(stripped)
    flush()
    return "\n\n".join(paragraphs)


# ---------------------------------------------------------------------------
# the document
# ---------------------------------------------------------------------------

PREAMBLE = r"""% !TEX program = xelatex
% Generated by blueprint/generate.py -- do not edit by hand.
\documentclass[11pt,a4paper]{article}
\usepackage{geometry}
\geometry{margin=2cm}
\usepackage{fontspec}
\usepackage{amsmath,amssymb}
\usepackage{alltt}
\usepackage{xcolor}
\usepackage[colorlinks=true,linkcolor=blue!50!black,urlcolor=blue!50!black]{hyperref}
\setmonofont{DejaVuSansMono.ttf}[Scale=0.72]

% Lean code blocks: a vertical rule on the left, the code verbatim in the mono font
\newenvironment{leancode}%
  {\par\medskip\noindent\begin{minipage}{\linewidth}%
   \color{gray}\vrule\hspace{0.6em}%
   \begin{minipage}{\dimexpr\linewidth-1.2em\relax}\color{black}%
   \footnotesize\begin{alltt}}%
  {\end{alltt}\end{minipage}\end{minipage}\par\medskip}

\title{\bfseries Abstract Voronoi diagrams revisited\\[2mm]
\large A blueprint of the Lean~4 formalization}
\author{}
\date{}

\sloppy

\begin{document}
\maketitle
\tableofcontents
"""

INTRO = r"""
\section*{About this document}
\addcontentsline{toc}{section}{About this document}

This blueprint accompanies the Lean~4 formalization of the first part of

\begin{quotation}\noindent
R. Klein, E. Langetepe, Z. Nilforoushan, \emph{Abstract Voronoi diagrams revisited},
Computational Geometry \textbf{42} (2009) 885--902,
\end{quotation}

\noindent
namely Definition~1, Definition~2, Lemma~3, Theorem~4, Lemma~5, Lemma~6, Lemma~7, Lemma~8,
Lemma~9 and Theorem~10.  For each of them it shows the statement of the paper, as quoted in
the docstring of the corresponding Lean declaration, the remarks on the formalization, and
the Lean statement itself.  Proofs are not reproduced here: they are in the Lean sources.

Everything below is extracted automatically from the files of
\texttt{AbstractVoronoi/Paper/} by \texttt{blueprint/generate.py}, so it always agrees with
the sources.  The supporting material lives in two other folders:
\texttt{AbstractVoronoi/Jordan/} (planar topology: the Jordan curve theorem and everything
built on top of it) and \texttt{AbstractVoronoi/AVD/} (the API about systems of bisecting
curves).

Every statement of the development is proved except one, invoked by the proof of Theorem~10
and stated at the end of this document: Euler's inequality for plane graphs
(\texttt{AVD.EulerSphereInequality}).  The other input of the count \(O(n)\), the degree
condition at a Voronoi vertex --- at least three edges end at every Voronoi vertex,
\texttt{AVD.CurveSystem.three\_le\_edges\_at\_vertex} --- is proved.  Everything else,
Definition~1 to Lemma~9 included, depends only on the standard axioms of Lean, on top of the
Lean~4 formalization of the Jordan--Sch\"onflies theorem the project uses as a dependency.
"""


def main():
    tex = [PREAMBLE, INTRO]
    md = ["# Abstract Voronoi diagrams revisited — blueprint of the Lean 4 formalization\n",
          "Generated from the Lean sources in `AbstractVoronoi/Paper/` by "
          "`blueprint/generate.py`.  For each numbered statement of Klein, Langetepe and "
          "Nilforoushan (2009) it shows the statement of the paper, the remarks on the "
          "formalization, and the Lean statement.\n"]
    cache = {}

    def emit(title, path, names, kind):
        if path not in cache:
            cache[path] = declarations(path)
        decls = cache[path]
        if title:
            tex.append("\\section{%s}\n" % tex_text(title))
            md.append("## %s\n" % title)
        tex.append("\\noindent\\emph{Source: \\texttt{AbstractVoronoi/%s}}\n" % tex_text(path))
        md.append("*Source: `AbstractVoronoi/%s`*\n" % path)
        for name in names:
            doc, code = decls[name]
            if kind == "statement" or (kind == "mixed" and code.startswith("theorem")):
                code = statement_only(code)
            tex.append(tex_doc(doc))
            tex.append(tex_code(code))
            md.append(doc + "\n")
            md.append("```lean\n" + code + "\n```\n")

    for item in ITEMS:
        emit(*item)
    if ASSUMPTIONS:
        tex.append("\\section{The remaining unproved statements}\n")
        md.append("## The remaining unproved statements\n")
        for path, names in ASSUMPTIONS:
            emit(None, path, names, "full")
    tex.append("\\end{document}\n")
    open(os.path.join(OUT, "blueprint.tex"), "w").write("\n".join(tex))
    open(os.path.join(OUT, "blueprint.md"), "w").write("\n".join(md))
    print("written blueprint/blueprint.tex and blueprint/blueprint.md")


main()
