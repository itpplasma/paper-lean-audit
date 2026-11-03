// Graphs of the view, laid out by Graphviz `dot` with nodes and edges emitted
// in paper order, so equal inputs give the same picture. Nodes are cards and
// link to them; card colours follow the kind and the review marks (reader.js).
import { execFileSync, spawnSync } from 'node:child_process';
import { escapeHtml, slug } from './util.mjs';

const q = (s) => '"' + String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"';

function wrap(text, width = 28) {
  const words = String(text).split(/\s+/).filter(Boolean);
  const lines = [];
  let line = '';
  for (const w of words) {
    if (line && (line + ' ' + w).length > width) { lines.push(line); line = w; } else line = line ? line + ' ' + w : w;
  }
  if (line) lines.push(line);
  return lines.join('\n');
}

export function dotSvg(dot) {
  const svg = execFileSync('dot', ['-Tsvg'], { input: dot, encoding: 'utf8', maxBuffer: 64 << 20 });
  return svg.replace(/^[\s\S]*?(<svg\b)/, '$1').replace(/<!--[\s\S]*?-->\n?/g, '').replace(/&#45;/g, '-');
}

export function dotVersion() {
  const r = spawnSync('dot', ['-V'], { encoding: 'utf8' });
  return ((r.stderr ?? '') + (r.stdout ?? '')).trim() || null;
}

const nodeAttrs = (c, cardTitle, prefix = 'g-') => {
  const cls = ['card-node', `kind-${c.entry.kind}`, ...(c.flags ?? []).map((f) => 'flag-' + slug(f))].join(' ');
  const shownFlags = (c.flags ?? []).filter((f) => f !== 'Lean-only definitions');
  const flags = shownFlags.length ? '\n[' + shownFlags.join(', ') + ']' : '';
  const label = c.env && c.entry.short ? cardTitle(c) + ': ' + c.entry.short : cardTitle(c);
  return `id=${q(prefix + slug(c.id))} class=${q(cls)} URL=${q('#c-' + slug(c.id))} tooltip=${q(cardTitle(c))} label=${q(wrap(label) + flags)}`;
};

// Paper edges: \ref in the statement or its printed proof to a card whose Lean
// counterpart is a theorem. Lean edges: mapped results the Lean proof uses.
// Definition edges: statement context through mapped definitions.
export function cardEdges({ cards, labelEntry, doc, refsIn, isResult }) {
  const byId = new Map(cards.map((c) => [c.id, c]));
  const edges = new Map();
  const add = (from, to, side) => {
    if (from === to || !byId.has(from) || !byId.has(to)) return;
    const k = from + '\0' + to;
    if (!edges.has(k)) edges.set(k, { from, to, paper: false, lean: false, def: false });
    edges.get(k)[side] = true;
  };
  for (const c of cards) {
    const spans = [[c.start, c.end]];
    for (const [a, b] of spans) for (const r of refsIn(doc.text, a, b)) {
      const owner = labelEntry.get(r.label);
      if (owner && isResult(owner)) add(owner.id, c.id, 'paper');
    }
    const usedIds = c.account ? c.account.used : (c.usedCards ?? []);
    for (const id of usedIds) add(id, c.id, 'lean');
    const ctx = new Set(c.decls.flatMap((x) => x.d.context ?? []));
    for (const o of cards) if (o !== c && o.decls.some((x) => ctx.has(x.name) && x.d.kind !== 'theorem')) add(o.id, c.id, 'def');
  }
  // Definition edges implied by a longer chain of definition edges are dropped.
  const defOut = new Map();
  for (const e of edges.values()) if (e.def) { if (!defOut.has(e.from)) defOut.set(e.from, []); defOut.get(e.from).push(e.to); }
  const reachesAvoiding = (from, to) => {
    const stack = (defOut.get(from) ?? []).filter((x) => x !== to), seen = new Set(stack);
    while (stack.length) {
      const x = stack.pop();
      if (x === to) return true;
      for (const y of defOut.get(x) ?? []) if (!seen.has(y)) { seen.add(y); stack.push(y); }
    }
    return false;
  };
  for (const [k, e] of edges) if (e.def && !e.paper && !e.lean && reachesAvoiding(e.from, e.to)) edges.delete(k);
  const order = new Map(cards.map((c, i) => [c.id, i]));
  return [...edges.values()].sort((x, y) => order.get(x.from) - order.get(y.from) || order.get(x.to) - order.get(y.to)).map((e) => {
    const owner = byId.get(e.to);
    // Only a printed proof can be compared with the Lean uses.
    const compared = !!owner.account;
    const kind = e.paper && e.lean ? 'both' : e.paper ? (compared ? 'paper-only' : 'paper') : e.lean ? (compared ? 'lean-only' : 'lean') : 'def';
    return { from: e.from, to: e.to, kind };
  });
}

const EDGE_STYLE = {
  both: 'color="#333333" penwidth=1.4',
  paper: 'color="#2b6cb0"',
  lean: 'color="#666666" style=dashed',
  'paper-only': 'color="#c53030" penwidth=2.2',
  'lean-only': 'color="#c05621" penwidth=2.2 style=dashed',
  def: 'color="#a0aec0" style=dotted arrowhead=empty',
};

export function buildGraphs({ cards, cardTitle, labelEntry, doc, refsIn, isResult }) {
  const edges = cardEdges({ cards, labelEntry, doc, refsIn, isResult });
  const common = 'graph [rankdir=TB ordering=out nodesep=0.25 ranksep=0.35 fontname="Helvetica"];\n  node [shape=box style="rounded,filled" fillcolor="white" fontname="Helvetica" fontsize=10 margin="0.08,0.04"];\n  edge [arrowsize=0.6];\n';
  let dot = 'digraph overall {\n  ' + common;
  for (const c of cards) dot += `  ${q(c.id)} [${nodeAttrs(c, cardTitle)}];\n`;
  for (const e of edges) dot += `  ${q(e.from)} -> ${q(e.to)} [class=${q('edge-' + e.kind)} ${EDGE_STYLE[e.kind]} tooltip=${q(e.kind)}];\n`;
  dot += '}\n';
  let html = `<section class="graph" id="graph"><h2>Graph</h2>` +
    `<p class="legend">Nodes are the cards above; colours show the kind and your review marks. Edges: <span class="e both">cited and used</span> · <span class="e paper">cited</span> · <span class="e lean">used by Lean</span> · <span class="e paper-only">cited, not used by Lean</span> · <span class="e lean-only">used by Lean, not cited</span> · <span class="e def">definition used by the statement</span>. Edges into a printed proof are compared with its account; one-sided ones are highlighted.</p>` +
    `<div class="fig">${dotSvg(dot)}</div>`;
  // Per-proof graphs: inputs, sentences in order, Lean-added steps, result.
  for (const c of cards) {
    if (!c.proofRows?.length) continue;
    let pd = `digraph ${q('proof-' + c.id)} {\n  ${common}`;
    const inputs = [...new Set(c.proofRows.flatMap((r) => [...r.refs, ...r.uses]))].filter((id) => id !== c.id);
    const byId = new Map(cards.map((x) => [x.id, x]));
    for (const id of inputs) if (byId.has(id)) pd += `  ${q('in:' + id)} [${nodeAttrs(byId.get(id), cardTitle, 'gp-' + slug(c.id) + '-')} fillcolor="#f7fafc"];\n`;
    c.proofRows.forEach((r, i) => {
      const style = r.kind === 'prose' ? 'fillcolor="#fefcbf"' : r.kind === 'lean-adds' ? 'fillcolor="#feebc8" style="rounded,filled,dashed"' : 'fillcolor="#ffffff"';
      pd += `  ${q('s' + i)} [label=${q(wrap(r.label, 34))} class=${q('row-' + r.kind)} ${style} URL=${q('#' + r.anchor)}];\n`;
    });
    pd += `  "result" [${nodeAttrs(c, cardTitle, 'gr-')} penwidth=2];\n`;
    c.proofRows.forEach((r, i) => pd += `  ${q('s' + i)} -> ${q(i + 1 < c.proofRows.length ? 's' + (i + 1) : 'result')} [color="#a0aec0"];\n`);
    c.proofRows.forEach((r, i) => {
      for (const id of [...new Set([...r.refs, ...r.uses])]) {
        if (!byId.has(id) || id === c.id) continue;
        const kind = r.refs.includes(id) && r.uses.includes(id) ? 'both' : r.refs.includes(id) ? 'paper-only' : 'lean-only';
        pd += `  ${q('in:' + id)} -> ${q('s' + i)} [class=${q('edge-' + kind)} ${EDGE_STYLE[kind]}];\n`;
      }
    });
    pd += '}\n';
    html += `<div class="proof-graph" id="gp-${slug(c.id)}"><h3><a href="#c-${slug(c.id)}">${escapeHtml(cardTitle(c))}</a>: proof</h3><div class="fig">${dotSvg(pd)}</div></div>`;
  }
  html += '</section>';
  return { html, edges: { overall: edges, graphviz: dotVersion() } };
}
