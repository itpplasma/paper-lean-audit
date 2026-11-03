import crypto from 'node:crypto';

// JSON with object keys sorted at every level, so equal data gives equal bytes.
export function stableStringify(value, indent = 1) {
  const sort = (v) => {
    if (Array.isArray(v)) return v.map(sort);
    if (v && typeof v === 'object') return Object.fromEntries(Object.keys(v).sort().map((k) => [k, sort(v[k])]));
    return v;
  };
  return JSON.stringify(sort(value), null, indent);
}

export const sha256 = (s) => crypto.createHash('sha256').update(s).digest('hex');

export function escapeHtml(s) {
  return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

export const slug = (s) => String(s).replace(/[^A-Za-z0-9_.:-]/g, '-');
