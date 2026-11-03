// LaTeX structure needed by the side-by-side view: theorem-like environments
// with their numbers, proofs, sections, labels, equation tags, quotes and
// sentences. All offsets are into the original source; comments are masked by
// spaces of the same length so offsets never shift.

export function maskComments(tex) {
  const out = tex.split('');
  for (let i = 0; i < tex.length; i++) {
    if (tex[i] === '\\') { i++; continue; }
    if (tex[i] === '%') {
      while (i < tex.length && tex[i] !== '\n') out[i++] = ' ';
    }
  }
  return out.join('');
}

const escaped = (s, i) => {
  let n = 0;
  for (let j = i - 1; j >= 0 && s[j] === '\\'; j--) n++;
  return n % 2 === 1;
};

export function readGroupAt(s, i) {
  if (s[i] !== '{') return null;
  let depth = 0;
  for (let j = i; j < s.length; j++) {
    if (s[j] === '\\') { j++; continue; }
    if (s[j] === '{') depth++;
    else if (s[j] === '}' && --depth === 0) return { content: s.slice(i + 1, j), start: i + 1, end: j + 1 };
  }
  return null;
}

function readOptionalAt(s, i) {
  let j = i;
  while (s[j] === ' ' || s[j] === '\t') j++;
  if (s[j] !== '[') return null;
  let depth = 0, brace = 0;
  for (let k = j; k < s.length; k++) {
    if (s[k] === '\\') { k++; continue; }
    if (s[k] === '{') brace++;
    else if (s[k] === '}') brace--;
    else if (brace === 0 && s[k] === '[') depth++;
    else if (brace === 0 && s[k] === ']' && --depth === 0) return { content: s.slice(j + 1, k), start: j + 1, end: k + 1 };
  }
  return null;
}

export const lineAt = (text, offset) => {
  let line = 1;
  for (let i = 0; i < offset && i < text.length; i++) if (text[i] === '\n') line++;
  return line;
};

export const MATH_ENVS = new Set(['equation', 'equation*', 'align', 'align*', 'gather', 'gather*', 'multline', 'multline*', 'eqnarray', 'eqnarray*']);

export function parsePaper(raw) {
  const text = maskComments(raw);
  const theoremTypes = new Map();
  for (const m of text.matchAll(/\\newtheorem\s*(\*?)\s*\{([^{}]+)\}\s*(?:\[([^\]]*)\])?\s*\{([^{}]*)\}\s*(?:\[([^\]]*)\])?/g)) {
    theoremTypes.set(m[2].trim(), { title: m[4].trim(), counter: (m[3] ?? m[2]).trim(), within: m[5]?.trim() ?? null, starred: m[1] === '*' });
  }
  const docMatch = /\\begin\s*\{document\}/.exec(text);
  const docStart = docMatch ? docMatch.index + docMatch[0].length : 0;
  const events = [];
  for (const m of text.matchAll(/\\(begin|end)\s*\{([^{}]+)\}|\\(section|subsection|subsubsection)(\*?)\s*(?=[{[])|\\appendix\b|\\label\s*\{([^{}]+)\}/g)) {
    if (escaped(text, m.index) || m.index < docStart) continue;
    events.push(m);
  }
  const sections = [], envs = [], proofs = [], labels = new Map(), maths = [];
  const stack = [];
  const counters = new Map();
  const sectionCount = [0, 0, 0];
  let appendix = false;
  const sectionNumber = (level) => {
    const top = appendix ? String.fromCharCode(64 + sectionCount[0]) : String(sectionCount[0]);
    return [top, ...sectionCount.slice(1, level + 1).map(String)].join('.');
  };
  for (const m of events) {
    if (m[0].startsWith('\\appendix')) { appendix = true; sectionCount.fill(0); continue; }
    if (m[3]) {
      const level = { section: 0, subsection: 1, subsubsection: 2 }[m[3]];
      const opt = readOptionalAt(text, m.index + m[0].length);
      const g = readGroupAt(text, opt ? opt.end : m.index + m[0].length);
      const starred = m[4] === '*';
      if (!starred) {
        sectionCount[level]++;
        for (let l = level + 1; l < 3; l++) sectionCount[l] = 0;
        if (level === 0) for (const [name, t] of theoremTypes) if (t.within === 'section') counters.set(name, 0);
      }
      sections.push({ level, number: starred ? null : sectionNumber(level), top: appendix ? String.fromCharCode(64 + sectionCount[0]) : String(sectionCount[0]),
        title: g?.content ?? '', start: m.index, titleStart: g?.start ?? m.index, end: g?.end ?? m.index + m[0].length, labels: [] });
      continue;
    }
    if (m[5] !== undefined) {
      const owner = stack.at(-1) ?? null;
      const label = m[5].trim();
      const info = { label, at: m.index, owner };
      labels.set(label, info);
      if (owner) owner.labels.push(label);
      else if (sections.length && !envBetween(envs, sections.at(-1).end, m.index)) sections.at(-1).labels.push(label);
      continue;
    }
    const name = m[2].trim();
    if (m[1] === 'begin') {
      const node = { name, start: m.index, bodyStart: m.index + m[0].length, labels: [] };
      if (theoremTypes.has(name)) {
        const t = theoremTypes.get(name);
        const opt = readOptionalAt(text, node.bodyStart);
        if (opt) { node.optArg = opt.content; node.optStart = opt.start; node.bodyStart = opt.end; }
        node.kind = 'theorem';
        node.title = t.title;
        if (!t.starred) {
          const c = (counters.get(t.counter) ?? 0) + 1;
          counters.set(t.counter, c);
          const within = theoremTypes.get(t.counter)?.within ?? t.within;
          node.number = within === 'section' ? `${sectionNumber(0)}.${c}` : String(c);
        }
      } else if (name === 'proof') {
        node.kind = 'proof';
        const opt = readOptionalAt(text, node.bodyStart);
        if (opt) { node.optArg = opt.content; node.optStart = opt.start; node.bodyStart = opt.end; }
      } else if (MATH_ENVS.has(name)) node.kind = 'math';
      else node.kind = 'other';
      stack.push(node);
    } else {
      let k = stack.length - 1;
      while (k >= 0 && stack[k].name !== name) k--;
      if (k < 0) continue;
      const node = stack[k];
      stack.length = k;
      node.bodyEnd = m.index;
      node.end = m.index + m[0].length;
      node.section = [...sections].reverse().find((s) => s.start < node.start && s.level === 0) ?? null;
      if (node.kind === 'theorem') envs.push(node);
      else if (node.kind === 'proof') proofs.push(node);
      else if (node.kind === 'math') maths.push(node);
      // Labels inside a math environment belong to the enclosing environment too.
      if (stack.length && node.labels.length) stack.at(-1).labels.push(...node.labels.map((l) => l));
    }
  }
  envs.sort((a, b) => a.start - b.start);
  proofs.sort((a, b) => a.start - b.start);
  const docEnd = (() => { const i = text.search(/\\end\s*\{document\}/); return i < 0 ? text.length : i; })();
  return { raw, text, theoremTypes, sections, envs, proofs, labels, maths, docStart, docEnd };
}

function envBetween(envs, a, b) {
  return envs.some((e) => e.start > a && e.start < b);
}

// Equation numbers as the document prints them, including section resets and
// rows suppressed by \notag/\nonumber. Returns tags keyed by environment start
// offset and label -> printed tag.
export function equationTags(doc) {
  const text = doc.text;
  const sectionNumbered = /\\numberwithin\s*\{\s*equation\s*\}\s*\{\s*section\s*\}/.test(text);
  const events = [
    ...doc.maths.map((m) => ({ type: 'math', at: m.start, m })),
    ...doc.sections.filter((s) => s.level === 0).map((s) => ({ type: 'section', at: s.start, s })),
  ].sort((a, b) => a.at - b.at);
  let counter = 0, current = '0';
  const eqAuto = new Map(), labels = {};
  for (const ev of events) {
    if (ev.type === 'section') { if (ev.s.number) { current = ev.s.number; counter = 0; } continue; }
    const m = ev.m;
    const body = text.slice(m.bodyStart, m.bodyEnd);
    const starred = m.name.endsWith('*');
    const rows = splitRows(body);
    let rendered = null;
    for (const row of rows) {
      const explicit = /\\tag\*?\s*\{([^}]*)\}/.exec(row)?.[1] ?? null;
      const suppressed = /\\(?:notag|nonumber)\b/.test(row);
      let tag = explicit;
      if (!starred && !suppressed && !m.name.startsWith('multline')) {
        counter++;
        if (explicit === null) tag = sectionNumbered ? `${current}.${counter}` : String(counter);
      }
      if (tag) rendered = tag;
      for (const l of row.matchAll(/\\label\s*\{([^}]*)\}/g)) labels[l[1].trim()] = tag ?? '';
    }
    if (m.name.startsWith('multline') && !starred) {
      counter++;
      rendered = sectionNumbered ? `${current}.${counter}` : String(counter);
      for (const l of body.matchAll(/\\label\s*\{([^}]*)\}/g)) labels[l[1].trim()] = rendered;
    }
    if (rendered) eqAuto.set(m.start, rendered);
  }
  return { eqAuto, labels };
}

function splitRows(body) {
  const rows = [];
  let start = 0, braces = 0, envs = 0;
  for (let i = 0; i < body.length; i++) {
    if (body[i] === '\\') {
      const env = /^\\(begin|end)\s*\{[^{}]+\}/.exec(body.slice(i));
      if (env) { envs += env[1] === 'begin' ? 1 : -1; i += env[0].length - 1; }
      else if (body[i + 1] === '\\') { if (braces === 0 && envs === 0) { rows.push(body.slice(start, i)); start = i + 2; } i++; }
      else i++;
    } else if (body[i] === '{') braces++;
    else if (body[i] === '}') braces = Math.max(0, braces - 1);
  }
  rows.push(body.slice(start));
  return rows;
}

// All occurrences of `quote` in raw[from, to); exact match, no normalisation.
export function findQuote(raw, quote, from = 0, to = raw.length) {
  const hits = [];
  for (let i = raw.indexOf(quote, from); i >= 0 && i + quote.length <= to; i = raw.indexOf(quote, i + 1)) hits.push(i);
  return hits;
}

// Occurrences inside comments do not count: `masked` is the comment-masked text.
export function resolveQuote(raw, anchor, from = 0, to = raw.length, masked = null) {
  const hits = findQuote(raw, anchor.quote, from, to).filter((h) => !masked || masked.slice(h, h + anchor.quote.length) === anchor.quote);
  if (!hits.length) return { error: 'quote not found' };
  if (anchor.occurrence === undefined && hits.length > 1) return { error: `quote occurs ${hits.length} times; give "occurrence"` };
  const n = anchor.occurrence ?? 1;
  if (n > hits.length) return { error: `occurrence ${n} requested, quote occurs ${hits.length} times` };
  return { start: hits[n - 1], end: hits[n - 1] + anchor.quote.length, count: hits.length };
}

const ABBREVIATIONS = new Set(['e.g', 'i.e', 'cf', 'resp', 'etc', 'vs', 'viz', 'Thm', 'Prop', 'Lem', 'Cor', 'Def', 'Defn', 'Rem', 'Ex',
  'Eq', 'Eqs', 'Sec', 'Ch', 'Chap', 'Fig', 'Tab', 'p', 'pp', 'no', 'No', 'Vol', 'ed', 'eds', 'Prop', 'Props', 'Thms', 'Cors', 'Lemm', 'Ref', 'al', 'ff']);

// Sentences of a text span, as [start, end) offsets into `text`. A sentence
// ends at '.', '?' or '!' outside mathematics and braces, followed by space
// and not by a lower-case word, unless the word before is an abbreviation or
// the period is followed by `\ `; a period at the end of displayed
// mathematics ends the sentence after the display. Blank lines and \item
// also end sentences.
export function sentences(text, from, to) {
  const out = [];
  let start = from;
  let braces = 0;
  let math = null; // '$', '$$', '\\(', '\\[', or an environment name
  const push = (end) => {
    let a = start, b = end;
    while (a < b && /\s/.test(text[a])) a++;
    while (b > a && /\s/.test(text[b - 1])) b--;
    if (b > a && /[^\s{}]/.test(text.slice(a, b))) out.push({ start: a, end: b });
    start = end;
  };
  const nextNonSpace = (i) => { while (i < to && /\s/.test(text[i])) i++; return i; };
  const endsSentence = (i) => {
    // text[i] is '.', '?' or '!' in text mode.
    const word = /([A-Za-z.]+)$/.exec(text.slice(Math.max(from, i - 12), i))?.[1] ?? '';
    if (text[i] === '.' && ABBREVIATIONS.has(word.replace(/^\./, ''))) return false;
    if (text[i] === '.' && /^[A-Z]$/.test(word)) return false;
    if (text[i + 1] === '\\' && text[i + 2] === ' ') return false;
    if (text[i + 1] === '~') return false;
    const j = nextNonSpace(i + 1);
    if (j >= to) return true;
    if (j === i + 1 && !/[}\s]/.test(text[i + 1])) return false;
    if (/[a-z]/.test(text[j])) return false;
    return true;
  };
  for (let i = from; i < to; i++) {
    const c = text[i];
    if (c === '\\') {
      const env = /^\\(begin|end)\s*\{([^{}]+)\}/.exec(text.slice(i, i + 40));
      if (env) {
        const name = env[2];
        if (env[1] === 'begin' && math === null && MATH_ENVS.has(name)) math = name;
        else if (env[1] === 'end' && math === name) {
          math = null;
          // A display that ends with a period inside ends the sentence.
          const inner = text.slice(Math.max(from, i - 20), i).trimEnd();
          if (/[.?!]\s*(?:\\label\{[^}]*\})?$/.test(inner) || /\.\s*$/.test(inner)) {
            const j = i + env[0].length;
            if (nextNonSpace(j) >= to || /[A-Z\\$]/.test(text[nextNonSpace(j)])) { push(j); }
          }
        } else if (env[1] === 'begin' && math === null && /^(itemize|enumerate)$/.test(name)) push(i);
        i += env[0].length - 1;
        continue;
      }
      if (math === null && text.startsWith('\\[', i)) { math = '\\['; i++; continue; }
      if (math === '\\[' && text.startsWith('\\]', i)) {
        math = null;
        const inner = text.slice(Math.max(from, i - 10), i).trimEnd();
        if (/\.$/.test(inner)) { const j = i + 2; if (nextNonSpace(j) >= to || /[A-Z\\$]/.test(text[nextNonSpace(j)])) push(j); }
        i++; continue;
      }
      if (math === null && text.startsWith('\\(', i)) { math = '\\('; i++; continue; }
      if (math === '\\(' && text.startsWith('\\)', i)) { math = null; i++; continue; }
      if (math === null && /^\\item\b/.test(text.slice(i, i + 6))) { push(i); i += 4; continue; }
      i++;
      continue;
    }
    if (c === '$') {
      const dbl = text[i + 1] === '$';
      if (math === null) { math = dbl ? '$$' : '$'; if (dbl) i++; continue; }
      if (math === '$' && !dbl) { math = null; continue; }
      if (math === '$$' && dbl) { math = null; i++; continue; }
      continue;
    }
    if (math !== null) continue;
    if (c === '{') braces++;
    else if (c === '}') braces = Math.max(0, braces - 1);
    else if (c === '\n' && /^\n[ \t]*\n/.test(text.slice(i, i + 40))) push(i);
    else if (braces === 0 && /[.?!]/.test(c) && endsSentence(i)) push(i + 1);
  }
  push(to);
  return out;
}

// \ref, \eqref, \cref and \autoref labels in a span.
export function refsIn(text, from, to) {
  const out = [];
  for (const m of text.slice(from, to).matchAll(/\\(?:ref|eqref|cref|Cref|autoref)\s*\{([^{}]+)\}/g)) {
    for (const l of m[1].split(',')) out.push({ label: l.trim(), at: from + m.index });
  }
  return out;
}
