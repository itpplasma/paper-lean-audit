# Paper–Lean Audit

Generate a self-contained HTML review of a LaTeX manuscript against exact Lean source commits. The browser shows rendered mathematics, complete Lean declarations and proof bodies, clickable sources, definitions and optional review notes. It does not prove mathematical correspondence or replace the Lean kernel.

Requires Node.js 24 and Git. Reading the generated HTML needs only a browser; no Lean installation is required. PDF export additionally needs Chromium.

```sh
npm ci
node build.mjs --map /path/to/paper-lean-map.json --check \
  --source paper=/path/to/paper --source formal=/path/to/formal \
  --source mathlib=/path/to/mathlib --out build
```

Use `--source NAME=PATH` for any additional repository referred to by the map. The `paper` and `formal` roles are required. Legacy `--paper`, `--formal`, `--library`, `--global` and `--mathlib` flags remain supported. Every excerpt is read by `git show` at its configured commit; an unavailable pin is an error.

Start from `examples/minimal-map.json`; replace the repository names, full commit pins, excerpt range and fully qualified theorem name. The map is the project-specific, human-reviewed contract. `sources` gives GitHub repository names, full commit pins and the paper file. `items` gives excerpt ranges, fully qualified declaration names, hypotheses/statement correspondence and selected proof routes. `challenge_definitions` explicitly maps important definitions and typeclasses; identifiers link only when resolution is unambiguous. `challenge_endpoints` names the proved solutions, not template holes. Set `review_scope` to `publication`, `alternative` or `reference`; `publication_proof` can link a readable mathematical account. `live_url` records the published reader location. `output_stem` sets output filenames.

The [Stafford supplementary project](https://github.com/itpplasma/stafford38-supplementary) is the first real application. Its map, papers and proof content live separately. Tests build independent miniature Git repositories and exercise rendering, name resolution, definition links and browser review behavior.

```sh
npm test
```

Use the starting link to review claims in paper order, then follow the previous/next links. The resume link returns to the last visited or edited claim. Export JSON to retain or share findings, checks and that position; import it to continue. Review notes stay in the browser until exported. Input or generator changes invalidate sign-offs while preserving notes. Browser-side notes are not shared collaboration state. Named definitions and source links improve inspection; neither an HTML badge nor a checklist is evidence of a theorem proof.

## Side-by-side reader (map v2)

`v2/` builds a second reader that puts each paper environment beside the Lean statement and its definitions, and each sentence of a printed proof beside the Lean proof state it corresponds to. The data come from Lean itself: `lean/Extract.lean` runs inside the target project's Lake environment and writes, for the declarations the map names, the pretty-printed statement, the project definitions it depends on down to a configured library boundary, fingerprints, binders the proof never uses, the mapped and library results the proof uses (also through unmapped helper lemmas) and, for traced proofs, every tactic step with its goals before and after and the results it used.

```sh
lake build                                  # in the Lean project, at the pinned commit
node v2/extract.mjs --map map.json --project /path/to/lean --out extraction.json
node v2/build.mjs --map map.json --out build --check
```

The map (`"schema": "paper-lean-audit/map-2"`) anchors the paper by exact quotes with an optional occurrence index and the Lean side by fully qualified names; a proof sentence names its tactic steps by a quoted Lean span or a `[line, column]` position, optionally with `decl` naming a lemma the proof calls, so that a sentence can follow the argument into that lemma (its proof is traced too, its unclaimed steps are shown as Lean adds, and uses are still computed through it); `decl` alone anchors that lemma's whole proof, or its statement if it is proved by a term. A proof printed as running text rather than a proof environment is given by `proof.paper` and `proof.end` quotes. Each entry has a kind: `formalizes`, `cites` (a known result whose printed text gives no argument), `lean-only` or `prose` (with a note). `lean_only` lists Lean definitions without a paper counterpart, by name or name prefix, each with a note. `scope.sections` restricts the coverage checks to some top-level sections; `"front"` names the text before the first section, such as the abstract. `settings.lean_ref_commands` lists further paper commands of the form `\cmd{file}{line}{name}` that are shown like `\leandecl`. See `test/fixtures/v2/` for a complete small example.

`--check` fails on: a theorem-like environment without an entry; a quote, declaration or step anchor that does not resolve; a statement-context definition with neither a paper counterpart nor a `lean_only` entry; a printed proof or proof sentence without an entry; a proof whose cited results differ from the mapped results the Lean proof uses, unless `citations` records the difference; an extraction for another Lean commit; and two builds that differ. `--previous REPORT` lists moved, new and broken anchors. The graph section (Graphviz `dot`) draws the cards with paper and Lean edges and one graph per printed proof. Review marks are stored in the browser with each card's fingerprint and become invalid when it changes; export and import them as JSON.

The extractor re-elaborates each module with traced proofs in its own process (a second import in one Lean process does not yield a usable environment) and, by default, replaces the proofs of the other declarations of that module by `sorry` (`lean.skip_earlier_proofs`); the kernel check remains the project's own build. Unused binders are found on the proof term, so a hypothesis that a tactic such as `subst` or `omega` carries along counts as used.

Apache-2.0 covers the generator. Input manuscript excerpts and third-party packages retain their own licenses. See LICENSE and NOTICE.
