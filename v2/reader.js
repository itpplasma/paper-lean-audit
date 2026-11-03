// Reader controller: review marks keyed by card fingerprints, hover previews
// of definitions shown earlier, and graph highlighting. Marks stay in this
// browser until exported.
(function () {
  'use strict';
  const meta = window.READER_META || { stem: 'reader', cards: [] };
  const key = 'paper-lean-audit:marks:' + meta.stem;
  const fps = new Map(meta.cards.map((c) => [c.id, c.fp]));
  const slug = (s) => String(s).replace(/[^A-Za-z0-9_.:-]/g, '-');

  function load() {
    try { return JSON.parse(localStorage.getItem(key) || '{}') || {}; } catch (e) { return {}; }
  }
  function save(marks) {
    try { localStorage.setItem(key, JSON.stringify(marks)); } catch (e) { /* storage unavailable */ }
  }
  let marks = load();

  // A mark is valid only while the card's fingerprint is unchanged.
  function state(id) {
    const m = marks[id];
    if (!m || !m.reviewed) return 'open';
    return m.fp === fps.get(id) ? 'reviewed' : 'stale';
  }

  function graphNodes(id) {
    const s = slug(id);
    return Array.from(document.querySelectorAll('g.card-node')).filter((g) => g.id === 'g-' + s || g.id === 'gr-' + s || g.id.endsWith('-' + s) && g.id.startsWith('gp-'));
  }

  function render() {
    let done = 0;
    for (const id of fps.keys()) {
      const st = state(id);
      if (st === 'reviewed') done++;
      const box = document.querySelector('input[data-mark="' + CSS.escape(id) + '"]');
      if (box) box.checked = st === 'reviewed';
      const label = document.querySelector('[data-mark-state="' + CSS.escape(id) + '"]');
      if (label) label.textContent = st === 'stale' ? 'mark invalidated: the card changed since it was reviewed' : '';
      const card = document.querySelector('section.card[data-card="' + CSS.escape(id) + '"]');
      if (card) { card.classList.toggle('reviewed', st === 'reviewed'); card.classList.toggle('stale', st === 'stale'); }
      for (const g of graphNodes(id)) {
        g.classList.toggle('reviewed', st === 'reviewed');
        g.classList.toggle('stale', st === 'stale');
      }
    }
    const p = document.getElementById('progress');
    if (p) p.textContent = done + ' of ' + fps.size + ' cards reviewed';
  }

  document.addEventListener('change', (ev) => {
    const t = ev.target;
    if (t.matches && t.matches('input[data-mark]')) {
      const id = t.getAttribute('data-mark');
      marks[id] = { fp: fps.get(id), reviewed: t.checked };
      save(marks);
      render();
    }
  });

  const exportButton = document.getElementById('export');
  if (exportButton) exportButton.addEventListener('click', () => {
    const data = { schema: 'paper-lean-audit/marks-2', stem: meta.stem, paper: meta.paper, formal: meta.formal, marks };
    const blob = new Blob([JSON.stringify(data, null, 1) + '\n'], { type: 'application/json' });
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = meta.stem + '-marks.json';
    document.body.appendChild(a);
    a.click();
    a.remove();
  });
  const importInput = document.getElementById('import');
  if (importInput) importInput.addEventListener('change', async () => {
    const f = importInput.files && importInput.files[0];
    if (!f) return;
    try {
      const data = JSON.parse(await f.text());
      if (data.schema !== 'paper-lean-audit/marks-2' || typeof data.marks !== 'object') throw new Error('not a marks file');
      marks = Object.assign({}, marks, data.marks);
      save(marks);
      render();
    } catch (e) {
      alert('Import failed: ' + e.message);
    }
    importInput.value = '';
  });

  // Hover and focus previews of definitions shown on an earlier card.
  const preview = document.getElementById('preview');
  function show(link) {
    const target = document.getElementById(link.getAttribute('data-preview'));
    if (!target || !preview) return;
    preview.innerHTML = target.innerHTML;
    preview.hidden = false;
    const r = link.getBoundingClientRect();
    const w = Math.min(640, window.innerWidth - 32);
    preview.style.width = w + 'px';
    preview.style.left = Math.max(16, Math.min(r.left, window.innerWidth - w - 16)) + 'px';
    const below = r.bottom + 8;
    preview.style.top = (below + preview.offsetHeight > window.innerHeight ? Math.max(8, r.top - preview.offsetHeight - 8) : below) + 'px';
  }
  function hide() { if (preview) preview.hidden = true; }
  document.addEventListener('mouseover', (ev) => { const l = ev.target.closest && ev.target.closest('a.backref'); if (l) show(l); });
  document.addEventListener('mouseout', (ev) => { const l = ev.target.closest && ev.target.closest('a.backref'); if (l) hide(); });
  document.addEventListener('focusin', (ev) => { const l = ev.target.closest && ev.target.closest('a.backref'); if (l) show(l); else hide(); });

  // A card's "graph" link highlights its node.
  document.addEventListener('click', (ev) => {
    const l = ev.target.closest && ev.target.closest('a.graph-link');
    if (!l) return;
    const id = l.closest('section.card').getAttribute('data-card');
    for (const g of document.querySelectorAll('g.card-node.focus')) g.classList.remove('focus');
    for (const g of graphNodes(id)) g.classList.add('focus');
  });

  render();
})();
