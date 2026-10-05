// Resolve only names with explicit namespace evidence and known source owners.
// This lexical resolver does not replace Lean elaboration.
export function resolveDefinitionRef(info, token, refs) {
  const lookup = token.replace(/\.$/, '').replace(/^_root_\./, '');
  if (!lookup || info.bindings?.includes(lookup.split('.')[0])) return null;
  const namespace = (info.name ?? '').split('.').slice(0, -1);
  const choose = (name) => {
    const candidates = refs.filter((ref) => ref.name === name);
    const local = candidates.filter((ref) => (ref.repo ?? 'formal') === info.repo && ref.file === info.file);
    const owners = local.length ? local : candidates;
    const unique = [...new Map(owners.map((ref) => [
      `${ref.repo ?? 'formal'}:${ref.file}:${ref.name}`, ref,
    ])).values()];
    return { found: candidates.length > 0, ref: unique.length === 1 ? unique[0] : null };
  };
  const qualified = (name) => {
    for (let depth = namespace.length; depth >= 0; depth--) {
      const result = choose([...namespace.slice(0, depth), name].join('.'));
      if (result.found) return result;
    }
    return { found: false, ref: null };
  };
  const direct = token.startsWith('_root_.') ? choose(lookup) : qualified(lookup);
  if (direct.found) return direct.ref;
  const opened = new Map();
  for (const entry of info.context ?? []) {
    const command = /^\s*open\s+(.+?)\s*$/.exec(entry.text);
    if (!command || /\b(?:scoped|hiding|renaming|in)\b/.test(command[1])) continue;
    const selected = /^([A-Za-z_][A-Za-z0-9_'.]*)\s*\(([^()]*)\)$/.exec(command[1]);
    let namespaces;
    if (selected) {
      if (!selected[2].trim().split(/\s+/).includes(lookup.split('.')[0])) continue;
      namespaces = [selected[1]];
    } else {
      if (!/^[A-Za-z_][A-Za-z0-9_'.\s]*$/.test(command[1])) continue;
      namespaces = command[1].trim().split(/\s+/);
    }
    for (const name of namespaces) {
      const result = qualified(`${name}.${lookup}`);
      if (result.found && !result.ref) return null;
      if (result.ref) opened.set(`${result.ref.repo ?? 'formal'}:${result.ref.file}:${result.ref.name}`, result.ref);
    }
  }
  return opened.size === 1 ? [...opened.values()][0] : null;
}
