# Reproduction

Install the exact Lean toolchain named in lean-toolchain. The declarative
lakefile.toml and committed lake-manifest.json pin Mathlib and its dependencies.
Do not update the dependency graph.

From the repository root:

```sh
lake exe cache get
lake build Solution
lake build Challenge
lake comparator --config comparator.json --paranoid
```

The Challenge deliberately contains one statement hole per selected theorem;
its compilation alone is not proof acceptance. Solution builds treat warnings
as errors. Comparator must compare all selected declarations and accept only
the standard three axioms. The configured Palomar checker additionally uses
Lean paranoid, lean4lean, NanoDa, con-leche, con-ron and Lean default. A standalone
local check does not replace Palomar's complete pinned cloud workflow.

The paper builds with installed pdflatex and bibtex on PATH:

```sh
python paper/build.py
```

No figure regeneration or numerical integration is needed to build the paper.
The optional figure producer reads the saved trajectory arrays and uses NumPy
and Matplotlib. The parameter-corner script uses exact rational arithmetic
where applicable; its stochastic arithmetic is ancillary to the deterministic
formalization. These scripts resolve data and output paths relative to their
package, so they do not require the original research workspace.

Historical native records authenticate their original source hashes and pins.
Fresh target records bind the migrated files, declaration interfaces and
independent comparison separately in verification/local-check.json. Source correspondence and licenses are
documented in the provenance files and NOTICE.
