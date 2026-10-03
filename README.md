# Paper–Lean Audit

Generate a self-contained HTML review of a LaTeX manuscript against exact Lean source commits. The browser shows rendered mathematics, theorem signatures, ambient assumptions, linked statement definitions, correspondence notes and revision-sensitive review checklists. It does not prove mathematical correspondence or replace the Lean kernel.

Requires Node.js 24 and Git. Reading the generated HTML needs only a browser; no Lean installation is required. PDF export additionally needs Chromium.

```sh
npm ci
node build.mjs --map /path/to/paper-lean-map.json --check \
  --source paper=/path/to/paper --source formal=/path/to/formal \
  --source mathlib=/path/to/mathlib --out build
```

Use `--source NAME=PATH` for any additional repository referred to by the map. The `paper` and `formal` roles are required. Legacy `--paper`, `--formal`, `--library`, `--global` and `--mathlib` flags remain supported. Every excerpt is read by `git show` at its configured commit; an unavailable pin is an error.

Start from `examples/minimal-map.json`; replace the repository names, full commit pins, excerpt range and fully qualified theorem name. The map is the project-specific, human-reviewed contract. `sources` gives GitHub repository names, full commit pins and the paper file. `items` gives excerpt ranges, fully qualified declaration names, hypotheses/statement correspondence and selected proof routes. `challenge_definitions` explicitly maps important definitions and typeclasses; identifiers link only when resolution is unambiguous. `challenge_endpoints` names the proved solutions, not template holes. Set `review_scope` to `publication`, `alternative` or `reference`; `publication_proof` can link a readable mathematical account. `live_url` enables current-version checks; omit it for a fully offline review. `output_stem` sets output filenames.

The [Stafford supplementary project](https://github.com/itpplasma/stafford38-supplementary) is the first real application. Its map, papers and proof content live separately. Tests build independent miniature Git repositories and exercise rendering, name resolution, definition links and browser review behavior.

```sh
npm test
```

Use the starting link to review claims in paper order, then follow the previous/next links. The resume link returns to the last visited or edited claim. Export JSON to retain or share findings, checks and that position; import it to continue. Review notes stay in the browser until exported. Input or generator changes invalidate sign-offs while preserving notes. Browser-side notes are not shared collaboration state. Named definitions and source links improve inspection; neither an HTML badge nor a checklist is evidence of a theorem proof.

Apache-2.0 covers the generator. Input manuscript excerpts and third-party packages retain their own licenses. See LICENSE and NOTICE.
