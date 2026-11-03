#!/usr/bin/env node
// Runs the Lean extractor (lean/Extract.lean) inside a built Lean project for
// the declarations named by a v2 map and writes one deterministic JSON file.
//
//   node v2/extract.mjs --map map.json --project DIR --out extraction.json
//        [--wrap /path/to/memory-cap.sh] [--jobs N]
//
// The statement pass imports the project once at the private level (proof
// bodies are needed for unused binders and uses). Each module with traced
// proofs is then re-elaborated in its own process, because a second import in
// one Lean process does not give a usable environment.
import { execFileSync, spawn } from 'node:child_process';
import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { loadMap, mapDeclarations, mapTraces } from './map.mjs';
import { stableStringify } from './util.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const extractor = path.resolve(here, '../lean/Extract.lean');

function runLean(project, wrap, args) {
  const cmd = wrap ? [wrap, 'lake', 'env', 'lean', '--run', extractor, ...args] : ['lake', 'env', 'lean', '--run', extractor, ...args];
  return new Promise((resolve, reject) => {
    const child = spawn(cmd[0], cmd.slice(1), { cwd: project, stdio: ['ignore', 'inherit', 'pipe'] });
    let err = '';
    child.stderr.on('data', (d) => { err += d; });
    child.on('close', (code) => code === 0 ? resolve() : reject(new Error(`Lean extractor failed (${code}) for ${args.join(' ')}:\n${err}`)));
  });
}

export async function extract({ mapPath, project, out, wrap = null, jobs = 2, log = () => {} }) {
  const map = loadMap(mapPath);
  const lean = map.lean ?? {};
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'pla-extract-'));
  try {
    const base = {
      imports: lean.imports ?? [], project_modules: lean.project_modules ?? [],
      boundary_modules: lean.boundary_modules ?? [], boundary_namespaces: lean.boundary_namespaces ?? [],
      open: lean.open ?? [], skip_earlier_proofs: lean.skip_earlier_proofs ?? true,
      follow_instances: lean.follow_instances ?? false,
    };
    const declarations = mapDeclarations(map);
    const cfg = { ...base, declarations, mapped: declarations, trace: mapTraces(map) };
    fs.writeFileSync(path.join(tmp, 'extract.json'), JSON.stringify(cfg));
    let t0 = Date.now();
    await runLean(project, wrap, ['extract', path.join(tmp, 'extract.json'), path.join(tmp, 'extract.out.json')]);
    const result = JSON.parse(fs.readFileSync(path.join(tmp, 'extract.out.json'), 'utf8'));
    const timings = { statements_s: (Date.now() - t0) / 1000, traces: {} };
    log(`statements: ${timings.statements_s.toFixed(1)} s`);

    const byModule = new Map();
    for (const name of mapTraces(map)) {
      const d = result.declarations[name];
      if (!d) throw new Error(`traced declaration ${name} is not extracted`);
      if (!byModule.has(d.module)) byModule.set(d.module, []);
      byModule.get(d.module).push({ name, start: d.range.start, end: d.range.end });
    }
    result.traces = {};
    const modules = [...byModule.keys()].sort();
    const queue = [...modules];
    const worker = async () => {
      while (queue.length) {
        const mod = queue.shift();
        const file = path.join(tmp, `trace-${modules.indexOf(mod)}.json`);
        fs.writeFileSync(file, JSON.stringify({ ...base, module: mod, targets: byModule.get(mod) }));
        const t = Date.now();
        await runLean(project, wrap, ['trace', file, file + '.out']);
        timings.traces[mod] = (Date.now() - t) / 1000;
        log(`trace ${mod}: ${timings.traces[mod].toFixed(1)} s`);
        Object.assign(result.traces, JSON.parse(fs.readFileSync(file + '.out', 'utf8')));
      }
    };
    await Promise.all(Array.from({ length: Math.max(1, jobs) }, worker));

    const read = (f) => { try { return fs.readFileSync(path.join(project, f), 'utf8'); } catch { return null; } };
    const manifest = read('lake-manifest.json');
    result.environment.toolchain = (read('lean-toolchain') ?? '').trim();
    result.environment.manifest_sha256 = manifest ? crypto.createHash('sha256').update(manifest).digest('hex') : null;
    let commit = null, dirty = null;
    try {
      // Only a project that is its own repository has a commit of its own.
      const top = execFileSync('git', ['-C', project, 'rev-parse', '--show-toplevel'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim();
      if (fs.realpathSync(top) === fs.realpathSync(project)) {
        commit = execFileSync('git', ['-C', project, 'rev-parse', 'HEAD'], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim();
        dirty = execFileSync('git', ['-C', project, 'status', '--porcelain', '--untracked-files=no'], { encoding: 'utf8' }).trim() !== '';
      }
    } catch { /* not a git checkout */ }
    result.environment.commit = commit;
    result.environment.dirty = dirty;
    fs.writeFileSync(out, stableStringify(result) + '\n');
    return { result, timings };
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const argv = process.argv.slice(2);
  const opt = (name, fallback) => { const i = argv.indexOf(name); return i >= 0 ? argv[i + 1] : fallback; };
  const mapPath = opt('--map'), project = opt('--project'), out = opt('--out');
  if (!mapPath || !project || !out) {
    console.error('usage: node v2/extract.mjs --map MAP --project DIR --out FILE [--wrap SCRIPT] [--jobs N]');
    process.exit(2);
  }
  const { timings } = await extract({ mapPath, project: path.resolve(project), out: path.resolve(out),
    wrap: opt('--wrap', null), jobs: Number(opt('--jobs', '2')), log: (m) => console.error(m) });
  console.error(JSON.stringify(timings));
}
