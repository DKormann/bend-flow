import { createRequire as __createRequire } from "node:module"; const require = __createRequire(import.meta.url);

// src/checker-worker.ts
import { parentPort } from "node:worker_threads";

// src/checker-core.ts
import * as fs2 from "node:fs";
import * as os2 from "node:os";
import * as path2 from "node:path";
import { pathToFileURL } from "node:url";

// ../vendor/bend2/bend2/bend.ts
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as url from "node:url";
function Var(k, i, s, v) {
  return { $: "Var", k, i, s, v };
}
function Ref(k, s, b) {
  return { $: "Ref", k, s, b };
}
function Sub(i, v, f, s) {
  return { $: "Sub", i, v, f, s };
}
function Let(k, i, v, f, s, q) {
  return { $: "Let", k, i, q: q ?? k.map(() => Lone()), v, f, s };
}
function Typ(g, s) {
  return { $: "Typ", g, s };
}
function Qnt(s) {
  return { $: "Qnt", s };
}
function Qua(q, s) {
  return { $: "Qua", q, s };
}
function Min(a, b, s) {
  return { $: "Min", a, b, s };
}
function All(q, k, i, A, B, s) {
  return { $: "All", q, k, i, A, B, s };
}
function Lam(k, i, f, s, q) {
  return { $: "Lam", k, i, f, s, q };
}
function App(f, x, s) {
  return { $: "App", f, x, s };
}
function ADT(k, x, s, r = []) {
  return { $: "ADT", k, x, r, s };
}
function Ctr(k, x, s) {
  return { $: "Ctr", k, x, s };
}
function Lit(k, v, s) {
  return { $: "Lit", k, v, s };
}
function Mat(k, h, m, s) {
  return { $: "Mat", k, h, m, s };
}
function Efq(s) {
  return { $: "Efq", s };
}
function Eql(a, b, T, s) {
  return { $: "Eql", a, b, T, s };
}
function Rfl(s) {
  return { $: "Rfl", s };
}
function Rwt(e, p, f, s) {
  return { $: "Rwt", e, p, f, s };
}
function Hol(k, s) {
  return { $: "Hol", k, s };
}
function Ann(x, T, s) {
  return { $: "Ann", x, T, s };
}
function Emp() {
  return { $: "Emp" };
}
function Bin(v, l, r) {
  return { $: "Bin", v, l, r };
}
function None() {
  return { $: "None" };
}
function Lone() {
  return { $: "Lone" };
}
function Many() {
  return { $: "Many" };
}
function Infer(tm, ty, us, x) {
  return { tm: Ann(tm, Var("_", -1, void 0, ty)), ty, us, x };
}
function Check(tm, ty, us) {
  return { tm: Ann(tm, Var("_", -1, void 0, ty)), us };
}
function Err(bok, ctx, exp, obs, spn, def, nte) {
  return { $: "Err", bok, ctx, exp, obs, spn, def, nte };
}
function char_is_head(c) {
  const n = c.charCodeAt(0);
  return n >= 65 && n <= 90 || n >= 97 && n <= 122 || n === 95;
}
function char_is_name(c) {
  const n = c.charCodeAt(0);
  return char_is_head(c) || n >= 48 && n <= 57 || n === 46;
}
function pmap_get(map, key2) {
  let m = map;
  let k = key2;
  while (true) {
    switch (m.$) {
      case "Emp": {
        return null;
      }
      case "Bin": {
        if (k === 0) {
          return m.v;
        }
        const odd = k % 2 === 1;
        m = odd ? m.l : m.r;
        k = odd ? (k - 1) / 2 : (k - 2) / 2;
        break;
      }
    }
  }
}
function pmap_set(map, key2, val) {
  switch (map.$) {
    case "Emp": {
      return pmap_set(Bin(null, map, map), key2, val);
    }
    case "Bin": {
      if (key2 === 0) {
        return Bin(val, map.l, map.r);
      }
      if (key2 % 2 === 1) {
        const l = pmap_set(map.l, (key2 - 1) / 2, val);
        return Bin(map.v, l, map.r);
      }
      const r = pmap_set(map.r, (key2 - 2) / 2, val);
      return Bin(map.v, map.l, r);
    }
  }
}
function pmap_union(a, b, f) {
  if (a.$ === "Emp") {
    return b;
  }
  if (b.$ === "Emp") {
    return a;
  }
  const v = a.v === null ? b.v : b.v === null ? a.v : f(a.v, b.v);
  const l = pmap_union(a.l, b.l, f);
  const r = pmap_union(a.r, b.r, f);
  return Bin(v, l, r);
}
function pmap_to_array(map, acc = 0, scl = 1) {
  switch (map.$) {
    case "Emp": {
      return [];
    }
    case "Bin": {
      const v = map.v === null ? [] : [[acc, map.v]];
      const l = pmap_to_array(map.l, acc + scl * 1, scl * 2);
      const r = pmap_to_array(map.r, acc + scl * 2, scl * 2);
      return v.concat(l, r);
    }
  }
}
function list_get(list, key2) {
  for (let l = list; l !== null; l = l.n) {
    if (l.k === key2) {
      return l.v;
    }
  }
  return null;
}
function list_set(list, key2, val) {
  return { k: key2, v: val, n: list };
}
function quant_add(a, b) {
  if (a.$ === "None") {
    return b;
  }
  if (b.$ === "None") {
    return a;
  }
  return Many();
}
function quant_join(a, b) {
  if (a.$ === "Many" || b.$ === "Many") {
    return Many();
  }
  if (a.$ === "None") {
    return b;
  }
  return a;
}
function quant_dem(q, qt) {
  if (q.$ === "None") {
    return None();
  }
  return qt;
}
function uses_nil() {
  return Emp();
}
function uses_add(a, b) {
  return pmap_union(a, b, quant_add);
}
function lhs_ext(lhs, k, n, xs = []) {
  if (n === 0) {
    return term_apply(lhs, Ctr(k, xs));
  } else {
    return Lam("_", 0, (x) => {
      return lhs_ext(lhs, k, n - 1, [...xs, x]);
    });
  }
}
function lhs_kind(lhs, q) {
  return lhs.u === true && q.$ === "Many" ? Lone() : q;
}
function term_apply(fn, tm, s) {
  const f = term_strip(fn);
  if (f.$ === "Lam") {
    return f.f(tm);
  }
  return App(f, tm, s);
}
function term_unapply(tm) {
  const xs = [];
  let cur = tm;
  while (cur.$ === "App") {
    xs.push(cur.x);
    cur = cur.f;
  }
  return [cur, xs.reverse()];
}
function term_cell(t, k = "_") {
  if (t.$ === "Var" && t.i < 0) {
    return t;
  }
  return Var(k, -1, t.s, t);
}
function term_force(t) {
  while (t.$ === "Var" && t.v !== void 0) {
    t = t.v;
  }
  return t;
}
function term_strip(tm) {
  let t = term_force(tm);
  while (t.$ === "Ann") {
    t = term_force(t.x);
  }
  return t;
}
function term_higher(tm, env = null) {
  switch (tm.$) {
    case "Var": {
      if (tm.i < 0) {
        return tm;
      }
      const v = list_get(env, tm.i);
      if (v === null) {
        return tm.v ?? Ref(tm.k, tm.s);
      } else if (typeof v === "function") {
        return v(tm.s);
      } else {
        return v.s !== void 0 || tm.s === void 0 || v.$ === "Var" && v.i < 0 ? v : { ...v, s: tm.s };
      }
    }
    case "Ref": {
      if (tm.k.lastIndexOf(".") === 0) {
        const op = tm.s === void 0 ? tm.k : tm.s.src.slice(tm.s.beg, tm.s.end);
        throw Err(
          book_nil(),
          ctx_nil(),
          "a type for this operator (write (a " + op + " b : Nat))",
          void 0,
          tm.s,
          void 0,
          "Note: we broke this after launch, sorry. Until 2.0.16 a bare operator meant Nat.\nThat was a bug: operators demand annotation. Wrap the expression and it'll work again."
        );
      }
      return Ref(tm.k, tm.s, tm.b);
    }
    case "Sub": {
      return term_higher(tm.f, list_set(env, tm.i, (s) => term_higher(patt_term(tm.v, s), env)));
    }
    case "Let": {
      const b = tm;
      const v = b.v.map((x) => term_higher(x, env));
      return Let(b.k, b.i, v, (xs) => {
        let e = env;
        for (let j = 0; j < xs.length; j++) {
          e = list_set(e, b.i[j], xs[j]);
        }
        return term_higher(b.f, e);
      }, b.s, b.q);
    }
    case "All": {
      const b = tm;
      const A = term_higher(b.A, env);
      return All(b.q, b.k, b.i, A, (x) => {
        return term_higher(b.B, list_set(env, b.i, x));
      }, b.s);
    }
    case "Lam": {
      const b = tm;
      return Lam(b.k, b.i, (x) => {
        return term_higher(b.f, list_set(env, b.i, x));
      }, b.s, b.q);
    }
    case "Typ": {
      return Typ(term_higher(tm.g, env), tm.s);
    }
    case "Min": {
      return Min(term_higher(tm.a, env), term_higher(tm.b, env), tm.s);
    }
    case "App": {
      const f = term_higher(tm.f, env);
      const x = term_higher(tm.x, env);
      if (f.$ === "Lam") {
        return f.f(x);
      }
      return App(f, x, tm.s);
    }
    case "ADT": {
      return ADT(tm.k, tm.x.map((x) => term_higher(x, env)), tm.s, tm.r);
    }
    case "Ctr": {
      return Ctr(tm.k, tm.x.map((x) => term_higher(x, env)), tm.s);
    }
    case "Mat": {
      return Mat(tm.k, term_higher(tm.h, env), term_higher(tm.m, env), tm.s);
    }
    case "Eql": {
      return Eql(term_higher(tm.a, env), term_higher(tm.b, env), term_higher(tm.T, env), tm.s);
    }
    case "Rwt": {
      return Rwt(term_higher(tm.e, env), term_higher(tm.p, env), term_higher(tm.f, env), tm.s);
    }
    case "Ann": {
      return Ann(term_higher(tm.x, env), term_higher(tm.T, env), tm.s);
    }
    default: {
      return tm;
    }
  }
}
function term_lower(term, d = 0) {
  const tm = term_force(term);
  switch (tm.$) {
    case "Let": {
      const xs = tm.k.map((k, j) => Var(k, d + j));
      const vs = tm.v.map((v) => term_lower(v, d));
      return Let(tm.k, xs.map((_, j) => d + j), vs, term_lower(tm.f(xs), d + tm.k.length), tm.s, tm.q);
    }
    case "Typ": {
      return Typ(term_lower(tm.g, d), tm.s);
    }
    case "Min": {
      return Min(term_lower(tm.a, d), term_lower(tm.b, d), tm.s);
    }
    case "All": {
      const x = Var(tm.k, d);
      return All(tm.q, tm.k, d, term_lower(tm.A, d), term_lower(tm.B(x), d + 1), tm.s);
    }
    case "Lam": {
      const x = Var(tm.k, d);
      return Lam(tm.k, d, term_lower(tm.f(x), d + 1), tm.s, tm.q);
    }
    case "App": {
      return App(term_lower(tm.f, d), term_lower(tm.x, d), tm.s);
    }
    case "ADT": {
      return ADT(tm.k, tm.x.map((x) => term_lower(x, d)), tm.s, tm.r);
    }
    case "Ctr": {
      return Ctr(tm.k, tm.x.map((x) => term_lower(x, d)), tm.s);
    }
    case "Mat": {
      return Mat(tm.k, term_lower(tm.h, d), term_lower(tm.m, d), tm.s);
    }
    case "Eql": {
      return Eql(term_lower(tm.a, d), term_lower(tm.b, d), term_lower(tm.T, d), tm.s);
    }
    case "Rwt": {
      return Rwt(term_lower(tm.e, d), term_lower(tm.p, d), term_lower(tm.f, d), tm.s);
    }
    case "Ann": {
      return Ann(term_lower(tm.x, d), term_lower(tm.T, d), tm.s);
    }
    default: {
      return tm;
    }
  }
}
function ctx_nil() {
  return Emp();
}
function ctx_bind(ctx, i, q, k, T) {
  return pmap_set(ctx, i, { q, k, T });
}
function ctx_dead(book, ctx) {
  for (const [, a] of pmap_to_array(ctx)) {
    if (a.q.$ === "None") {
      continue;
    }
    const t = term_wnf(book, a.T);
    if (t.$ === "ADT" && book_adt(book, t, ctx).c.length === 0) {
      return true;
    }
  }
  return false;
}
function ctx_scope(ctx) {
  const bnd = [];
  for (const [i, a] of pmap_to_array(ctx)) {
    bnd[i] = a.k;
  }
  return Array.from(bnd, (k) => k ?? "_");
}
function book_nil() {
  return { tlds: /* @__PURE__ */ Object.create(null), ctrs: /* @__PURE__ */ Object.create(null), order: [], hols: 0, tmps: /* @__PURE__ */ Object.create(null) };
}
function book_ctr(book, k) {
  return book.ctrs[k] ?? null;
}
function book_fam(book, k) {
  const t = tele_unbind(book, book_ctr(book, k).T).ret;
  return t.$ === "ADT" ? t.k : k;
}
function book_adt(book, tm, ctx, def) {
  const tld = book.tlds[tm.k];
  if (tld === void 0 || tld.$ !== "ADT") {
    throw Err(book, ctx, "a declared datatype (unknown: " + tm.k + ")", void 0, tm.s, def);
  }
  if (tm.r.length === 0) {
    return tld;
  }
  const r = new Set(tm.r);
  return { $: "ADT", n: tld.n, g: tld.g, T: tld.T, c: tld.c.filter((c) => !r.has(c.k)) };
}
var BEND_DIR = import.meta.url.startsWith("file:///$bunfs/") ? path.join(path.dirname(fs.realpathSync(process.execPath)), "..", "bend2") : url.fileURLToPath(new URL(".", import.meta.url));
var BASE_BEND = fs.realpathSync(path.join(BEND_DIR, "base.bend"));
var BEND_LIB = path.resolve(process.env.BEND_LIB ?? path.join(os.homedir(), ".bend", "lib"));
var BEND_HUB = process.env.BEND_HUB ?? "https://hub.bend-lang.com";
var NAMED = /^([a-z][a-z0-9-]{0,63})@((?:0|[1-9][0-9]*)(?:\.(?:0|[1-9][0-9]*)){3})$/;
async function hub_get(book, sub, hash, spn) {
  const res = await fetch(BEND_HUB + "/" + sub);
  const src = res.ok ? await res.text() : "";
  const sum = Buffer.from(await crypto.subtle.digest("SHA-256", new TextEncoder().encode(src))).toString("hex");
  if (!res.ok || hash.length < 32 || sum.slice(0, hash.length) !== hash || path.posix.normalize("/" + sub) !== "/" + sub) {
    throw Err(book, ctx_nil(), "a file at " + BEND_HUB + "/" + sub + " hashing to " + hash, void 0, spn);
  }
  return src;
}
async function name_hash(book, nv, spn) {
  if (!NAMED.test(nv)) {
    throw Err(book, ctx_nil(), "a package as <name>@<version>: a-z, 0-9 and -, 1 to 64 characters, at four numbers like 1.0.0.0", "'" + nv + "'", spn);
  }
  const at = path.join(BEND_LIB, "names", nv);
  const old = fs.existsSync(at) ? fs.readFileSync(at, "utf8").trim() : "";
  if (/^0x[0-9a-f]{32}$/.test(old)) {
    return old;
  }
  const res = await fetch(BEND_HUB + "/name/" + nv).catch(() => null);
  const got = res?.ok ? (await res.text()).trim() : "";
  if (!/^0x[0-9a-f]{32}$/.test(got)) {
    throw Err(book, ctx_nil(), "a package named " + nv + " on " + BEND_HUB + (res?.status === 410 ? " (it was taken down)" : ""), void 0, spn);
  }
  fs.mkdirSync(path.dirname(at), { recursive: true });
  fs.writeFileSync(at, got + "\n");
  return got;
}
async function book_file(book, file, spn) {
  if (file.startsWith(BEND_LIB + "/") && !fs.existsSync(file)) {
    const pkg = file.slice(BEND_LIB.length + 1).split("/")[0];
    const man = await hub_get(book, pkg + "/manifest", pkg.slice(2), spn);
    const fls = man.trim().split("\n").map((l) => l.split(" "));
    const srs = await Promise.all(fls.map(([h, p]) => hub_get(book, pkg + "/" + p, h, spn)));
    fls.forEach(([, p], i) => {
      const at = BEND_LIB + "/" + pkg + "/" + p;
      fs.mkdirSync(path.dirname(at), { recursive: true });
      fs.writeFileSync(at, srs[i]);
    });
  }
  if (!fs.existsSync(file)) {
    throw Err(book, ctx_nil(), "no such file: " + file, void 0, spn);
  }
  return fs.realpathSync(file);
}
async function book_load(book, file, ns, seen, spn) {
  const real = await book_file(book, file, spn);
  if (seen.has(real)) {
    if (seen.get(real) === null) {
      throw Err(book, ctx_nil(), "an import cycle through " + file, void 0, spn);
    }
    return book.order.length;
  }
  seen.set(real, null);
  const dir = real.slice(0, real.lastIndexOf("/") + 1);
  const text = fs.readFileSync(real, "utf8");
  const lines = text.split("\n");
  const body = lines.slice();
  const al = /* @__PURE__ */ Object.create(null);
  const hub = (s) => /^0x[0-9a-f]+\//.test(s);
  const ok = (s, lib) => hub(s) === lib && /^(\/|(\.\.\/)*)([A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*$/.test(s.replace(/^0x[0-9a-f]+\//, ""));
  for (let i = 0, at = 0; i < lines.length; at += lines[i].length + 1, i++) {
    const line = lines[i].trim();
    if (line === "" || line.startsWith("#")) {
      continue;
    }
    if (!/^import(\s|$)/.test(line)) {
      break;
    }
    const m = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(line);
    const beg = at + lines[i].indexOf(m?.[1] ?? line);
    const sp = { src: text, beg, end: beg };
    if (m === null || m[2] === void 0 && m[1] !== "Base") {
      throw Err(book, ctx_nil(), "an import ('import Base', or 'import <path> as <Name>')", "'" + line + "'", sp);
    }
    body[i] = "";
    if (m[2] === void 0) {
      await book_load(book, BASE_BEND, "", seen, sp);
      continue;
    }
    if (!m[1].endsWith(".bend")) {
      throw Err(book, ctx_nil(), "an import of a .bend file", "'" + m[1] + "'", sp);
    }
    if (m[2] in al) {
      throw Err(book, ctx_nil(), "a fresh alias (" + m[2] + " names an earlier import)", "'" + line + "'", sp);
    }
    const bad = () => Err(book, ctx_nil(), "an import path of plain names (letters, digits, _ and -; the hub's files import the hub's)", "'" + m[1] + "'", sp);
    const nv = /^([^/]*@[^/]*)\//.exec(m[1]);
    const as = nv === null ? m[1] : await name_hash(book, nv[1], sp) + m[1].slice(nv[1].length);
    const rel = path.posix.normalize(as);
    if (!ok(as.replace(/^\.\//, "").slice(0, -5), hub(as))) {
      throw bad();
    }
    const got = await book_file(book, hub(as) ? BEND_LIB + "/" + rel : path.posix.resolve(dir, rel), sp);
    const lib = fs.existsSync(BEND_LIB) ? fs.realpathSync(BEND_LIB) + "/" : "\0";
    const sub = (got.startsWith(lib) ? got.slice(lib.length) : path.posix.join(path.posix.dirname(ns), path.posix.relative(dir, got))).replace(/\.bend$/, "");
    if (!ok(sub, got.startsWith(lib)) || hub(ns) && !got.startsWith(lib)) {
      throw bad();
    }
    al[m[2]] = sub;
    await book_load(book, got, sub, seen, sp);
  }
  const n0 = book.order.length;
  parse_book(book, dir, body.join("\n"), ns, al);
  if (real === BASE_BEND) {
    for (const k of book.order.slice(n0)) {
      book.tlds[k].b = true;
    }
  }
  seen.set(real, ns);
  return n0;
}
function tele_bind(tele, end) {
  return tele.reduceRight((out, [q, k, i, T, s]) => All(q, k, i, T, out, s), end);
}
function tele_open(book, tel) {
  const t = term_wnf(book, tel);
  return t.$ === "All" ? t : null;
}
function tele_head(book, tel, ctx, def, s) {
  const t = tele_open(book, tel);
  if (t === null) {
    throw Err(book, ctx, "unreachable (a telescope binds its parameters and fields)", void 0, s, def);
  }
  return t;
}
function tele_fill(book, tel, xs, ctx, def, s) {
  let out = tel;
  for (const x of xs) {
    out = tele_head(book, out, ctx, def, s).B(x);
  }
  return out;
}
function tele_unbind(book, T) {
  const doms = [];
  let tel = T;
  for (let t = tele_open(book, tel); t !== null; t = tele_open(book, tel)) {
    doms.push([t.q, t.k, t.A]);
    tel = t.B(Var(t.k, doms.length - 1));
  }
  return { doms, ret: term_wnf(book, tel) };
}
function word_to_term(n, s) {
  let out = Ctr("WNil", [], s);
  for (let i = 31; i >= 0; i--) {
    out = Ctr("WCon", [Ctr(n >>> i & 1 ? "True" : "False", [], s), out], s);
  }
  return out;
}
function lit_of(cs, s) {
  if (cs.every((c) => c <= 1114111 && (c < 55296 || c > 57343))) {
    return Lit("String", cs.map((c) => String.fromCodePoint(c)).join(""), s);
  }
  return cs.reduceRight((out, c) => Ctr("SCon", [Ctr("Chr", [Lit("U32", c, s)], s), out], s), Ctr("SNil", [], s));
}
function lit_step({ k, v, s }) {
  if (k === "String") {
    const c = v.codePointAt(0);
    return c === void 0 ? Ctr("SNil", [], s) : Ctr("SCon", [Ctr("Chr", [Lit("U32", c, s)], s), Lit(k, v.slice(c > 65535 ? 2 : 1), s)], s);
  }
  if (k !== "Nat") {
    return Ctr(k, [word_to_term(v, s)], s);
  }
  return v === 0 ? Ctr("Zero", [], s) : Ctr("Succ", [Lit(k, v - 1, s)], s);
}
var NAT_LITERAL_MAX = 256;
function nat_from_term(t) {
  let n = 0;
  while (t.$ === "Ctr" && t.k === "Succ" && t.x.length === 1) {
    n += 1;
    t = t.x[0];
  }
  return t.$ === "Ctr" && t.k === "Zero" && t.x.length === 0 ? n : t.$ === "Lit" && t.k === "Nat" && n + t.v <= 4294967295 ? n + t.v : null;
}
function u32_from_term(tm, k = "U32") {
  const w0 = term_strip(tm);
  if (w0.$ === "Lit") {
    return w0.k === k ? w0.v : null;
  }
  if (w0.$ !== "Ctr" || w0.k !== k || w0.x.length !== 1) {
    return null;
  }
  let n = 0;
  let i = 0;
  let w = term_strip(w0.x[0]);
  while (w.$ === "Ctr" && w.k === "WCon" && w.x.length === 2) {
    const b = term_strip(w.x[0]);
    if (b.$ !== "Ctr" || b.x.length !== 0 || b.k !== "True" && b.k !== "False") {
      return null;
    }
    n += b.k === "True" ? 2 ** i : 0;
    i += 1;
    w = term_strip(w.x[1]);
  }
  if (i !== 32 || w.$ !== "Ctr" || w.k !== "WNil" || w.x.length !== 0) {
    return null;
  }
  return n;
}
var F32_VIEW = new DataView(new ArrayBuffer(4));
function f32_to_bits(v) {
  F32_VIEW.setFloat32(0, v);
  return F32_VIEW.getUint32(0);
}
function f32_from_bits(n) {
  F32_VIEW.setUint32(0, n);
  return F32_VIEW.getFloat32(0);
}
function quant_show(q) {
  return { None: "-", Lone: "", Many: "+" }[q.$];
}
var ESCAPES = {
  "n": 10,
  "t": 9,
  "r": 13,
  "0": 0,
  "\\": 92,
  "'": 39,
  '"': 34
};
function term_key(tm) {
  return JSON.stringify(tm, (k, v) => k === "s" ? void 0 : v);
}
function f32_show(x) {
  let s = "nan";
  for (let p = 1; x === x && p <= 9 && Math.fround(Number(s)) !== x; p += 1) {
    s = String(Number(x.toExponential(p - 1)));
  }
  return (Object.is(x, -0) ? "-0" : s).replace(/^-?\d+(?=e|$)/, "$&.0").replace("Infinity", "inf");
}
function term_show(term, top = -1, bnd = []) {
  function term_show_sugar_exi(tm, prc) {
    const [h, xs] = term_unapply(tm);
    const b = xs[1];
    if (h.$ !== "Ref" || h.k !== "Exists" || xs.length !== 2 || b.$ !== "Lam") {
      return null;
    }
    const A = go(xs[0], 2);
    bnd.push(b.k);
    const f = go(b.f, 1);
    bnd.pop();
    const s = "&" + b.k + ":" + A + " -> " + f;
    return prc > 1 ? "(" + s + ")" : s;
  }
  function term_show_chain(tm, k, n) {
    const xs = [];
    let t = tm;
    while (t.$ === "Ctr" && t.k === k && t.x.length === n) {
      xs.push(t.x[0]);
      t = t.x[n - 1];
    }
    return [xs, t];
  }
  function term_show_sugar_nat(tm, prc) {
    const k = nat_from_term(tm);
    if (k !== null) {
      return String(k) + "n";
    }
    const [xs, t] = term_show_chain(tm, "Succ", 1);
    const n = xs.length;
    if (n === 0) {
      return null;
    }
    const s = String(n) + "n+" + go(t, 1);
    return prc > 1 ? "(" + s + ")" : s;
  }
  function term_show_sugar_lst(tm, prc) {
    const [xs, t] = term_show_chain(tm, "Con", 2);
    if (t.$ === "Ctr" && t.k === "Nil" && t.x.length === 0) {
      return "[" + xs.map((x) => go(x, 0)).join(", ") + "]";
    }
    if (xs.length === 0) {
      return null;
    }
    const s = xs.map((x) => go(x, 2)).join(" <> ") + " <> " + go(t, 1);
    return prc > 1 ? "(" + s + ")" : s;
  }
  function term_show_sugar_tup(tm) {
    const [xs, t] = term_show_chain(tm, "Tuple", 2);
    if (xs.length === 0) {
      return null;
    }
    return "(" + xs.concat(t).map((x) => go(x, 0)).join(", ") + ")";
  }
  function term_show_sugar_arr(tm) {
    if (tm.$ === "Ctr" && tm.k === "ALeaf" && tm.x.length === 1) {
      return [go(tm.x[0], 0)];
    }
    if (tm.$ !== "Ctr" || tm.k !== "ANode" || tm.x.length !== 2) {
      return null;
    }
    const l = term_show_sugar_arr(tm.x[0]);
    const r = term_show_sugar_arr(tm.x[1]);
    if (l === null || r === null) {
      return null;
    }
    return l.concat(r);
  }
  function chr_show(n, quote) {
    const k = Object.keys(ESCAPES).find((k2) => ESCAPES[k2] === n && (k2 !== "'" && k2 !== '"' || k2 === quote));
    if (k !== void 0) {
      return "\\" + k;
    }
    if (n < 32 || n === 127 || n >= 55296 && n <= 57343 || n > 1114111) {
      return "\\u{" + n.toString(16) + "}";
    }
    return String.fromCodePoint(n);
  }
  function lit_text(v) {
    return [...v].map((c) => chr_show(c.codePointAt(0), '"')).join("");
  }
  function term_show_sugar_chr(tm, quote) {
    const n = tm.$ === "Ctr" && tm.k === "Chr" && tm.x.length === 1 ? u32_from_term(tm.x[0]) : null;
    return n === null ? null : chr_show(n, quote);
  }
  function term_show_sugar_str(tm) {
    const [cs, t] = term_show_chain(tm, "SCon", 2);
    const ss = cs.map((c) => term_show_sugar_chr(c, '"'));
    const tl = t.$ === "Lit" && t.k === "String" ? lit_text(t.v) : t.$ === "Ctr" && t.k === "SNil" && t.x.length === 0 ? "" : null;
    if (tl === null || ss.includes(null)) {
      return null;
    }
    return '"' + ss.join("") + tl + '"';
  }
  function go(tm, prc) {
    switch (tm.$) {
      case "Var": {
        return bnd.lastIndexOf(tm.k) === tm.i ? tm.k : tm.k + "^" + String(tm.i);
      }
      case "Ref": {
        return (bnd.includes(tm.k) ? tm.k + "^" : tm.k) + (tm.b === true ? "!" : "");
      }
      case "Sub": {
        return go(tm.f, prc);
      }
      case "Let": {
        const vs = tm.v.map((v) => go(v, 1));
        for (const k of tm.k) {
          bnd.push(k);
        }
        const f = go(tm.f, -1);
        bnd.length -= tm.k.length;
        const ks = tm.k.map((k, j) => quant_show(tm.q[j]) + k);
        const s = ks.join(" ") + " = " + vs.join(" ") + "; " + f;
        return prc >= 0 ? "(" + s + ")" : s;
      }
      case "Typ": {
        const g = tm.g;
        if (g.$ === "Qua" && g.q.$ === "Lone") {
          return "Type";
        }
        if (g.$ === "Qua" && g.q.$ === "Many") {
          return "Data";
        }
        return "Kind(" + go(tm.g, 0) + ")";
      }
      case "Qnt": {
        return "Quant";
      }
      case "Qua": {
        return { None: "&0", Lone: "&1", Many: "&2" }[tm.q.$];
      }
      case "Min": {
        const s = go(tm.a, 2) + " <&> " + go(tm.b, 2);
        return prc > 1 ? "(" + s + ")" : s;
      }
      case "All": {
        const A = go(tm.A, 2);
        bnd.push(tm.k);
        const B = go(tm.B, 1);
        bnd.pop();
        const s = "@" + quant_show(tm.q) + tm.k + ":" + A + " -> " + B;
        return prc > 1 ? "(" + s + ")" : s;
      }
      case "Lam": {
        bnd.push(tm.k);
        const f = go(tm.f, -1);
        bnd.pop();
        const s = quant_show(tm.q ?? Lone()) + tm.k + " => " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "App": {
        const sug = term_show_sugar_exi(tm, prc);
        if (sug !== null) {
          return sug;
        }
        const [h, xs] = term_unapply(tm);
        const hs = go(h, 2);
        const as = xs.map((x) => go(x, 0));
        return hs + "(" + as.join(", ") + ")";
      }
      case "ADT": {
        const as = tm.x.map((x) => go(x, 0));
        const rs = tm.r.map((c) => " - " + c + "{}").join("");
        const s = tm.k + (as.length === 0 && rs === "" ? "" : "<" + as.join(", ") + ">") + rs;
        return rs !== "" && prc > 1 ? "(" + s + ")" : s;
      }
      case "Ctr": {
        const u32 = u32_from_term(tm);
        const f32 = u32_from_term(tm, "F32");
        const chr = term_show_sugar_chr(tm, "'");
        const arr = term_show_sugar_arr(tm);
        const sug = u32 !== null ? String(u32) : f32 !== null ? f32_show(f32_from_bits(f32)) : term_show_sugar_nat(tm, prc) ?? (chr !== null ? "'" + chr + "'" : null) ?? term_show_sugar_str(tm) ?? term_show_sugar_lst(tm, prc) ?? term_show_sugar_tup(tm) ?? (arr !== null ? "[" + arr.join(", ") + "]" : null);
        if (sug !== null) {
          return sug;
        }
        const as = tm.x.map((x) => go(x, 0));
        return tm.k + "{" + as.join(", ") + "}";
      }
      case "Lit": {
        return go(lit_step(tm), prc);
      }
      case "Mat": {
        const arms = [];
        let m = tm;
        while (m.$ === "Mat") {
          arms.push(m.k + ": " + go(m.h, 1));
          m = m.m;
        }
        if (m.$ !== "Efq") {
          arms.push(go(m, 1));
        }
        return "\\{" + arms.join("; ") + "}";
      }
      case "Efq": {
        return "\\{}";
      }
      case "Eql": {
        return "{" + go(tm.a, 1) + " == " + go(tm.b, 1) + " : " + go(tm.T, 1) + "}";
      }
      case "Rfl": {
        return "{==}";
      }
      case "Hol": {
        return "?" + tm.k;
      }
      case "Rwt": {
        const e = go(tm.e, 1);
        const mp = term_strip(tm.p);
        const mb = mp.$ === "Lam" ? term_strip(mp.f) : mp;
        let n = "";
        let P;
        if (mp.$ === "Lam" && mb.$ === "Lam") {
          bnd.push(mp.k, mb.k);
          P = go(mb.f, 1);
          bnd.length -= 2;
          n = mb.k === "" ? "" : mb.k + "@";
        } else {
          P = go(tm.p, 1);
        }
        const f = go(tm.f, -1);
        const s = "%" + n + e + " : " + P + "; " + f;
        return prc > 0 ? "(" + s + ")" : s;
      }
      case "Ann": {
        return "{" + go(tm.x, 1) + " : " + go(tm.T, 1) + "}";
      }
    }
  }
  return go(term, top);
}
function expr_show(book, x, bnd = []) {
  if (typeof x === "string") {
    return x;
  } else {
    const t = term_lower(term_snf(book, x), bnd.length);
    return term_show(t, -1, bnd);
  }
}
function err_show(err) {
  const bnd = ctx_scope(err.ctx);
  const anns = pmap_to_array(err.ctx).sort((a, b) => a[0] - b[0]);
  const wid = Math.max(0, ...anns.map(([, a]) => a.k.length));
  const msg = err.obs === void 0 ? "\n- message  : " + expr_show(err.bok, err.exp, bnd) : "\n- expected : " + expr_show(err.bok, err.exp, bnd) + "\n- observed : " + expr_show(err.bok, err.obs, bnd);
  const ctx = anns.map(([i, a]) => "\n- " + a.k.padEnd(wid) + " : " + expr_show(err.bok, a.T, bnd.slice(0, i))).join("");
  const def = err.def === void 0 ? "" : " " + err.def;
  let spn = "";
  if (err.spn !== void 0) {
    const lns = err.spn.src.split("\n");
    const pre = err.spn.src.slice(0, err.spn.beg).split("\n");
    const at = pre.length;
    const beg = Math.max(1, at - 1);
    const end = Math.min(lns.length, at + 1);
    const num = String(end).length;
    const lft = pre[at - 1];
    const car = " ".repeat(num) + " | " + lft.replace(/[^\t]/g, " ") + "^".repeat(Math.max(1, Math.min(err.spn.end - err.spn.beg, lns[at - 1].length - lft.length)));
    spn = "\n" + lns.slice(beg - 1, end).map((l, j) => String(beg + j).padStart(num) + (beg + j === at ? ">| " + l + "\n" + car : " | " + l)).join("\n");
  }
  const loc = def === "" && spn === "" ? "" : "\nLocation:" + def + spn;
  const nte = err.nte === void 0 ? "" : "\n" + err.nte;
  return "Error:" + msg + (anns.length === 0 ? "" : "\nContext:") + ctx + loc + nte;
}
var KEYWORDS = /* @__PURE__ */ new Set([
  "def",
  "type",
  "law",
  "match",
  "case",
  "do",
  "return",
  "for",
  "exs",
  "where",
  "is",
  "import",
  "Type",
  "Data",
  "Kind",
  "Quant"
]);
var QUAS = { "0": None(), "1": Lone(), "2": Many() };
function parse_col(src, pos) {
  return pos - src.lastIndexOf("\n", pos - 1);
}
function parse_span(p, beg) {
  return { src: p.str, beg, end: p.pos };
}
function parse_fail(p, exp, beg = p.pos, end = p.pos) {
  const obs = beg < end ? "'" + p.str.slice(beg, end) + "'" : p.pos < p.str.length ? "'" + p.str[p.pos] + "'" : "end of input";
  throw Err(p.book, ctx_nil(), exp, obs, { src: p.str, beg, end });
}
function parse_peek(p) {
  return p.pos < p.str.length ? p.str[p.pos] : "";
}
function parse_bump(p) {
  const c = parse_peek(p);
  p.pos += 1;
  return c;
}
function parse_at(p, s) {
  if (p.str.charCodeAt(p.pos) !== s.charCodeAt(0)) {
    return false;
  }
  return s.length === 1 || p.str.startsWith(s, p.pos);
}
function parse_take(p, s) {
  if (!parse_at(p, s)) {
    return false;
  }
  p.pos += s.length;
  return true;
}
function parse_skip(p) {
  const s = p.str;
  while (p.pos < s.length) {
    const n = s.charCodeAt(p.pos);
    if (n === 32 || n === 10 || n === 13 || n === 9) {
      p.pos += 1;
      continue;
    }
    if (n === 35) {
      while (p.pos < s.length && s.charCodeAt(p.pos) !== 10) {
        p.pos += 1;
      }
      continue;
    }
    return;
  }
}
function parse_eat(p, s) {
  parse_skip(p);
  if (!parse_take(p, s)) {
    parse_fail(p, "'" + s + "'");
  }
}
function parse_at_word(p, w) {
  parse_skip(p);
  if (!parse_at(p, w)) {
    return false;
  }
  return !char_is_name(p.str[p.pos + w.length] ?? "");
}
function parse_word(p, w) {
  if (!parse_at_word(p, w)) {
    return false;
  }
  parse_take(p, w);
  return true;
}
function parse_lexeme(p) {
  parse_skip(p);
  if (!char_is_head(parse_peek(p))) {
    parse_fail(p, "a name");
  }
  const beg = p.pos;
  while (p.pos < p.str.length && char_is_name(p.str[p.pos])) {
    p.pos += 1;
  }
  const k = p.str.slice(beg, p.pos);
  if (!/^[A-Za-z_]\w*(\.[A-Za-z_]\w*)*$/.test(k)) {
    parse_fail(p, "a name (words joined by dots, got '" + k + "')", beg);
  }
  return k;
}
function parse_name(p) {
  const k = parse_lexeme(p);
  if (KEYWORDS.has(k)) {
    parse_fail(p, "a name (got the keyword '" + k + "')", p.pos - k.length);
  }
  return k;
}
function parse_char(p) {
  if (parse_take(p, "\\")) {
    const u = /^u\{([0-9a-f]+)\}/i.exec(p.str.slice(p.pos, p.pos + 11));
    if (u !== null) {
      p.pos += u[0].length;
      return parseInt(u[1], 16);
    }
    const c = ESCAPES[parse_bump(p)];
    if (c === void 0) {
      parse_fail(p, `an escape (\\n \\t \\r \\0 \\\\ \\' \\" \\u{1F600})`);
    }
    return c;
  }
  const n = p.str.codePointAt(p.pos);
  if (n === void 0) {
    parse_fail(p, "a character");
  }
  p.pos += n > 65535 ? 2 : 1;
  return n;
}
function parse_open(p, k) {
  const i = p.frs++;
  if (k !== "_") {
    p.stk.push([k, i]);
  }
  return i;
}
function parse_close(p, n) {
  p.stk.length = n;
}
function parse_var(p, k, s) {
  for (let j = p.stk.length - 1; j >= 0; j--) {
    if (p.stk[j][0] === k) {
      return Var(k, p.stk[j][1], s);
    }
  }
  const q = parse_reso(p, k);
  if (k.includes(".")) {
    return Ref(q, s);
  }
  return Var(k, p.frs++, s, Ref(q, s));
}
function parse_qual(p, k) {
  return p.ns === "" ? k : p.ns + "." + k;
}
function parse_reso(p, k) {
  const dot = k.indexOf(".");
  let q = parse_qual(p, k);
  if (dot !== -1 && k.slice(0, dot) in p.al) {
    q = p.al[k.slice(0, dot)] + k.slice(dot);
    if ((q in p.book.tlds || q in p.book.ctrs) && (k in p.book.tlds || k in p.book.ctrs)) {
      parse_fail(p, "an unambiguous name (the alias " + k.slice(0, dot) + " shadows " + k + ")");
    }
  }
  const own = q in p.book.tlds || q in p.book.ctrs;
  const far = k in p.book.tlds || k in p.book.ctrs;
  return own || !far ? q : k;
}
function parse_call(p, k, xs, s) {
  return xs.reduce((f, x) => App(f, x, s), Ref(parse_reso(p, k), s));
}
function parse_quant(p) {
  parse_skip(p);
  if (parse_take(p, "-")) {
    return None();
  }
  if (parse_take(p, "+")) {
    return Many();
  }
  return Lone();
}
function parse_bind(p, t) {
  if (t.$ !== "Var") {
    parse_fail(p, "a lambda binder (one name: k => body)");
  }
  return { $: "PVar", k: t.k, i: parse_open(p, t.k), q: t.i < 0 ? Many() : Lone(), s: t.s };
}
function parse_patt(p, t) {
  const book = p.book;
  switch (t.$) {
    case "Var": {
      if (book_ctr(book, parse_reso(p, t.k)) !== null) {
        throw Err(book, ctx_nil(), "a braced constructor pattern (" + t.k + " is a constructor: write " + t.k + "{}, or rename the binder)", void 0, t.s);
      }
      return parse_bind(p, t);
    }
    case "Ctr": {
      const ctr = book_ctr(book, t.k);
      if (ctr === null) {
        throw Err(book, ctx_nil(), "a declared constructor (unknown: " + t.k + ")", void 0, t.s);
      }
      if (ctr.n !== t.x.length) {
        throw Err(book, ctx_nil(), "a " + t.k + " pattern with " + String(ctr.n) + (ctr.n === 1 ? " field" : " fields"), void 0, t.s);
      }
      return { $: "PCtr", k: t.k, x: t.x.map((x) => parse_patt(p, x)), s: t.s };
    }
    case "Lit": {
      return parse_patt(p, lit_step(t));
    }
    default: {
      throw Err(book, ctx_nil(), "a pattern (a binder or a constructor)", term_show(term_lower(term_higher(t), 0)), t.s);
    }
  }
}
function parse_term(p, lvl = 0) {
  parse_skip(p);
  const beg = p.pos;
  const base = parse_term_base(p, beg);
  base.s ??= parse_span(p, beg);
  return parse_term_ops(p, base, base.s.beg, lvl);
}
function parse_term_base(p, beg) {
  const c = parse_peek(p);
  if (char_is_head(c)) {
    const k = parse_lexeme(p);
    if (k === "Type") {
      return Typ(Qua(Lone()));
    }
    if (k === "Data") {
      return Typ(Qua(Many()));
    }
    if (k === "Quant") {
      return Qnt();
    }
    if (k === "Kind") {
      parse_eat(p, "(");
      const g = parse_term(p);
      parse_eat(p, ")");
      return Typ(g);
    }
    if (k === "do") {
      const m = parse_name(p);
      parse_eat(p, "<");
      const ts = parse_fill(
        p,
        parse_reso(p, m),
        parse_term_args(p, ">"),
        parse_span(p, beg)
      );
      parse_eat(p, ":");
      parse_skip(p);
      return parse_term_do_stmt(p, m, ts, parse_col(p.str, p.pos));
    }
    if (k === "match") {
      parse_fail(p, "a term (a match heads a def body, not a term)", beg);
    }
    if (k === "case") {
      parse_fail(p, "a match heading this case (this case is orphaned)", beg);
    }
    if (k === "return") {
      parse_fail(p, "a do-block heading this return", beg);
    }
    if (KEYWORDS.has(k)) {
      parse_fail(p, "a term (the keyword '" + k + "' cannot head one)", beg);
    }
    if (parse_take(p, "{")) {
      const xs = parse_term_args(p, "}");
      return Ctr(parse_reso(p, k), xs);
    }
    return parse_var(p, k, parse_span(p, beg));
  }
  if (/[0-9]/.test(c)) {
    return parse_term_num(p);
  }
  switch (c) {
    case "@": {
      return parse_term_all(p, false);
    }
    case "&": {
      const q = QUAS[p.str[p.pos + 1] ?? ""];
      if (q !== void 0) {
        parse_bump(p);
        parse_bump(p);
        return Qua(q);
      }
      return parse_term_all(p, true);
    }
    case "+": {
      parse_bump(p);
      const t = parse_term(p, 12);
      const s = parse_span(p, beg);
      const k = t.$ === "ADT" ? t.k : t.$ === "Var" || t.$ === "Ref" ? parse_reso(p, t.k) : "";
      const tld = p.book.tlds[k];
      if (t.$ === "Var" && (tld === void 0 || tld.$ !== "ADT")) {
        return Var(t.k, -1, s);
      }
      if (tld === void 0 || tld.$ !== "ADT" || tld.g === 0 || tld.g < tld.n && t.$ !== "ADT") {
        parse_fail(p, "a quantified datatype after + (+D<..> sets D's leading quantities to &2)");
      }
      const xs = t.$ === "ADT" ? t.x : Array.from({ length: tld.n }, () => Qua(Lone(), s));
      return ADT(k, xs.map((x, i) => i < tld.g ? Qua(Many(), s) : x), s);
    }
    case "\\": {
      parse_bump(p);
      parse_eat(p, "{");
      const arms = [];
      let tail = Efq();
      while (true) {
        parse_skip(p);
        if (parse_take(p, "}")) {
          break;
        }
        const t = parse_term(p);
        parse_skip(p);
        if ((t.$ === "Var" || t.$ === "Ref") && parse_take(p, ":")) {
          const h = parse_term(p);
          arms.push([parse_reso(p, t.k), h]);
          parse_skip(p);
          parse_take(p, ";");
          continue;
        }
        tail = t;
        parse_skip(p);
        parse_take(p, ";");
        parse_eat(p, "}");
        break;
      }
      const s = parse_span(p, beg);
      tail.s ??= s;
      return arms.reduceRight((out, arm) => Mat(arm[0], arm[1], out, s), tail);
    }
    case "%": {
      parse_bump(p);
      const e0 = parse_term(p);
      parse_skip(p);
      let k = "";
      let e = e0;
      if (parse_take(p, "@")) {
        if (e0.$ !== "Var") {
          parse_fail(p, "a name before @ (a rewrite binder is one name: %e@E : P)");
        }
        k = e0.k;
        e = parse_term(p);
      }
      parse_eat(p, ":");
      const n0 = p.stk.length;
      const xi = p.frs++;
      p.stk.push(["_", xi]);
      const ei = parse_open(p, k);
      const P = parse_term(p);
      parse_close(p, n0);
      parse_skip(p);
      parse_take(p, ";");
      const f = parse_block(p);
      const s = parse_span(p, beg);
      return Rwt(e, Lam("_", xi, Lam(k, ei, P, e0.s), s), f, s);
    }
    case "{": {
      parse_bump(p);
      parse_skip(p);
      if (parse_take(p, "==")) {
        parse_eat(p, "}");
        return Rfl();
      }
      const a = parse_term(p);
      parse_skip(p);
      const ne = parse_take(p, "!=");
      const ns = parse_span(p, p.pos - 2);
      const b = ne || parse_take(p, "==") ? parse_term(p) : null;
      parse_eat(p, ":");
      const T = parse_term(p);
      parse_eat(p, "}");
      if (b === null) {
        return Ann(a, T);
      }
      if (!ne) {
        return Eql(a, b, T);
      }
      const s = parse_span(p, beg);
      return All(Lone(), "_", parse_open(p, "_"), Eql(a, b, T, s), Ref("Empty", ns), s);
    }
    case "(": {
      parse_bump(p);
      return parse_term_tup(p, beg);
    }
    case "[": {
      parse_bump(p);
      parse_skip(p);
      const xs = parse_at(p, "]") ? [] : [parse_term(p)];
      parse_skip(p);
      if (xs.length !== 0 && parse_take(p, ":")) {
        const T = parse_term(p, 12);
        parse_skip(p);
        const cnt = parse_take(p, "*");
        if (!cnt) {
          parse_eat(p, "^");
        }
        const n = parse_term(p);
        parse_eat(p, "]");
        const s = parse_span(p, beg);
        parse_term_ns(p, xs[0], T);
        let d = n;
        if (cnt) {
          const k = Math.log2(nat_from_term(n) ?? 0);
          if (!Number.isInteger(k)) {
            throw Err(p.book, ctx_nil(), "a power of two count (^d takes a depth)", void 0, n.s);
          }
          d = Lit("Nat", k, n.s);
        }
        return App(App(App(Ref("Array.new", s), T, s), d, s), xs[0], s);
      }
      parse_take(p, ",");
      const ys = xs.concat(parse_term_args(p, "]"));
      const spn = parse_span(p, beg);
      return ys.reduceRight((t, x) => Ctr("Con", [x, t], spn), Ctr("Nil", [], spn));
    }
    case "'": {
      parse_bump(p);
      const n = parse_char(p);
      if (!parse_take(p, "'")) {
        parse_fail(p, "a closing '");
      }
      const spn = parse_span(p, beg);
      return Ctr("Chr", [Lit("U32", n, spn)], spn);
    }
    case '"': {
      parse_bump(p);
      const cs = [];
      while (!parse_take(p, '"')) {
        if (p.pos >= p.str.length) {
          parse_fail(p, 'a closing "');
        }
        cs.push(parse_char(p));
      }
      return lit_of(cs, parse_span(p, beg));
    }
    case "?": {
      parse_bump(p);
      const k = parse_name(p);
      if (k === "TODO") {
        p.book.hols += 1;
      }
      return Hol(k);
    }
    default: {
      parse_fail(p, "a term");
    }
  }
}
var INFIX = {
  "<-": [-1, false, ""],
  "->": [0, true, ""],
  "&": [1, true, "Pair"],
  "|": [1, true, "Or"],
  "||": [2, false, "Bool.or"],
  "&&": [3, false, "Bool.and"],
  "<": [4, false, ".is_lt"],
  "<=": [4, false, ".is_le"],
  ">": [4, false, ".is_gt"],
  ">=": [4, false, ".is_ge"],
  "<>": [5, true, "Con"],
  "++": [5, true, "String.append"],
  "<&>": [5, true, ""],
  ".|.": [6, false, ".or"],
  ".^.": [7, false, ".xor"],
  ".&.": [8, false, ".and"],
  "<<": [9, false, ".shln"],
  ">>": [9, false, ".shrn"],
  "+": [10, false, ".add"],
  "-": [10, false, ".sub"],
  "*": [11, false, ".mul"],
  "/": [11, false, ".div"],
  "%": [11, false, ".mod"]
};
function parse_nl(p) {
  for (let j = p.pos - 1; j >= 0; j--) {
    const c = p.str[j];
    if (c === "\n") {
      return true;
    }
    if (c !== " " && c !== "\r" && c !== "	") {
      return false;
    }
  }
  return true;
}
function parse_term_ops(p, tm, beg, lvl) {
  let out = tm;
  while (true) {
    parse_skip(p);
    if (parse_nl(p) && (parse_at(p, "(") || parse_at(p, "["))) {
      return out;
    }
    if (parse_at(p, "(") || parse_at(p, "!(")) {
      if (out.$ === "Var" && out.v !== void 0) {
        out = out.v;
      }
      if (parse_at(p, "!")) {
        if (out.$ !== "Ref") {
          parse_fail(p, "a named def before ! (only f!(..) offloads)");
        }
        parse_bump(p);
        out.b = true;
        continue;
      }
      parse_bump(p);
      const hd = p.book.tlds[out.$ === "Ref" ? out.k : ""];
      const x = hd?.$ === "Def" ? hd.x : 0;
      const ts = [];
      for (parse_skip(p); x > 0 && parse_at(p, "~"); parse_skip(p)) {
        if (ts.length === x) {
          parse_fail(p, "a term (" + out.k + " takes " + String(x) + " ~)");
        }
        parse_bump(p);
        ts.push(parse_term(p));
        parse_skip(p);
        parse_take(p, ",");
      }
      const xs = ts.concat(parse_term_args(p, ")"));
      const s2 = parse_span(p, beg);
      for (const a of xs) {
        out = App(out, a, s2);
      }
      continue;
    }
    if (parse_at(p, "[")) {
      parse_bump(p);
      const ix = parse_term(p);
      parse_eat(p, "]");
      const s2 = parse_span(p, beg);
      parse_term_ns(p, ix, Ref("U32", s2));
      parse_skip(p);
      if (!parse_nl(p) && parse_take(p, "<-")) {
        const v = parse_term(p, 2);
        out = App(App(App(
          App(Ref("Array.set", s2), Ref("U32", s2), s2),
          out,
          s2
        ), ix, s2), v, s2);
      } else {
        out = App(App(
          App(Ref("Array.get", s2), Ref("U32", s2), s2),
          out,
          s2
        ), ix, s2);
      }
      continue;
    }
    if (lvl === 0 && parse_take(p, "=>")) {
      const n0 = p.stk.length;
      const x = parse_bind(p, out);
      const f = parse_block(p);
      parse_close(p, n0);
      out = Lam(x.k, x.i, f, x.s, x.q);
      continue;
    }
    let op = p.str.slice(p.pos, p.pos + 3);
    while (op !== "" && INFIX[op] === void 0) {
      op = op.slice(0, -1);
    }
    if (op === "") {
      return out;
    }
    const [prc, right, k] = INFIX[op];
    const nx = p.str[p.pos + op.length] ?? "";
    const gl = /\S/.test(p.str[p.pos - 1] ?? "");
    if (prc < lvl && !(op === "<" && gl) || (op === "-" || op === "+") && (nx === ">" || char_is_head(nx)) || op[0] === ">" && gl || op === "%" && !/\s/.test(nx)) {
      return out;
    }
    p.pos += op.length;
    const t = parse_span(p, p.pos - op.length);
    const b = parse_term(p, right ? prc : prc + 1);
    const s = parse_span(p, beg);
    parse_skip(p);
    if (op === "<" && (parse_at(p, ">") || parse_at(p, ","))) {
      if (out.$ !== "Var" && out.$ !== "Ref") {
        parse_fail(p, "a family name before <..> (a comparison here needs parens)");
      }
      parse_take(p, ",");
      const d = parse_reso(p, out.k);
      out = ADT(d, parse_fill(p, d, [b, ...parse_term_args(p, ">")], s), s);
    } else if (op === "->") {
      out = All(Lone(), "_", parse_open(p, "_"), out, b, s);
    } else if (op === "<&>") {
      out = Min(out, b, s);
    } else if (op === "<>") {
      out = Ctr(k, [out, b], s);
    } else if (op === "&" || op === "|") {
      out = App(App(Ref(k, s), out, s), b, s);
    } else {
      out = App(App(Ref(k, t), out, s), b, s);
    }
  }
}
function parse_term_ns(p, tm, T) {
  if (tm.$ === "Let") {
    return parse_term_ns(p, tm.f, T);
  }
  const [f, xs] = term_unapply(tm);
  if (f.$ !== "Ref") {
    return;
  }
  if (f.k.lastIndexOf(".") === 0) {
    const h = term_unapply(T)[0];
    if (h.$ !== "Var" && h.$ !== "Ref" && h.$ !== "ADT") {
      throw Err(p.book, ctx_nil(), "a type name after : (the operators' namespace)", void 0, h.s);
    }
    f.k = parse_reso(p, h.k + f.k);
  } else if (f.k !== "Bool.and" && f.k !== "Bool.or" && f.k !== "String.append") {
    return;
  }
  for (const x of xs) {
    parse_term_ns(p, x, T);
  }
}
function parse_term_args(p, close) {
  const xs = [];
  while (true) {
    parse_skip(p);
    if (parse_take(p, close)) {
      return xs;
    }
    const x = parse_term(p);
    xs.push(x);
    parse_skip(p);
    parse_take(p, ",");
  }
}
function parse_term_all(p, exi) {
  const beg = p.pos;
  parse_bump(p);
  const q = exi ? Lone() : parse_quant(p);
  const k = parse_name(p);
  parse_eat(p, ":");
  const A = parse_term(p, 1);
  parse_eat(p, "->");
  const n0 = p.stk.length;
  const i = parse_open(p, k);
  const B = parse_term(p);
  parse_close(p, n0);
  if (exi) {
    const s = parse_span(p, beg);
    return App(App(Ref("Exists", s), A, s), Lam(k, i, B, s), s);
  }
  return All(q, k, i, A, B);
}
function parse_term_tup(p, beg) {
  parse_skip(p);
  const b = parse_body(p, parse_col(p.str, p.pos) - 1);
  parse_skip(p);
  if (b.$ !== "Match" && b.$ !== "Local" && parse_take(p, ",")) {
    const rest = parse_term_tup(p, beg);
    return Ctr("Tuple", [b, rest], parse_span(p, beg));
  }
  const out = body_flatten(b, [], () => p.frs++);
  if (parse_take(p, ":")) {
    parse_term_ns(p, out, parse_term(p));
  }
  parse_eat(p, ")");
  return out;
}
var NUMBER = /(\d+)(n|\.\d+([eE][+-]?\d+)?)?/y;
function parse_term_num(p) {
  const beg = p.pos;
  NUMBER.lastIndex = p.pos;
  const m = NUMBER.exec(p.str);
  const n = Number(m[1]);
  p.pos += m[0].length;
  if (m[2] !== void 0 && m[2] !== "n") {
    const v = Math.fround(Number(m[0]));
    if (!isFinite(v)) {
      parse_fail(p, "a float literal with a finite f32 value (got " + m[0] + ")", beg);
    }
    return Lit("F32", f32_to_bits(v));
  }
  if (m[2] === void 0) {
    if (char_is_name(parse_peek(p))) {
      parse_fail(p, "a numeric literal (NUMBER is U32, NUMBER n is Nat)");
    }
    if (n > 4294967295) {
      parse_fail(p, "a u32 literal up to 4294967295 (got " + m[1] + ")", beg);
    }
    return Lit("U32", n);
  }
  if (n > 4294967295) {
    parse_fail(p, "a nat literal up to 4294967295n (got " + m[1] + "n)");
  }
  if (parse_take(p, "+")) {
    let out = parse_term(p);
    const spn = parse_span(p, beg);
    if (out.$ === "Lit" && out.k === "Nat" && n + out.v <= 4294967295) {
      return Lit("Nat", n + out.v, spn);
    }
    if (n > NAT_LITERAL_MAX) {
      return App(App(Ref("Nat.add", spn), Lit("Nat", n, spn), spn), out, spn);
    }
    for (let i = 0; i < n; i++) {
      out = Ctr("Succ", [out], spn);
    }
    return out;
  }
  if (char_is_name(parse_peek(p))) {
    parse_fail(p, "a nat literal (NUMBER n)");
  }
  return Lit("Nat", n);
}
function parse_fill(p, k, xs, s) {
  const tld = p.book.tlds[k];
  return tld?.$ !== "ADT" || xs.length + tld.g !== tld.n ? xs : Array.from({ length: tld.g }, () => Qua(Lone(), s)).concat(xs);
}
function parse_term_do_stmt(p, m, ts, col) {
  parse_skip(p);
  const beg = p.pos;
  if (parse_word(p, "return")) {
    const e = parse_term(p);
    return parse_call(p, m + ".pure", [...ts, e], parse_span(p, beg));
  }
  const t = parse_term(p);
  parse_skip(p);
  const typed = t.$ === "Var" && parse_take(p, ":");
  const step = !typed && parse_more(p, col);
  const A = typed ? parse_term(p, 1) : step ? parse_var(p, "Unit", t.s) : t;
  parse_skip(p);
  const asg = typed && !parse_at(p, "==") && parse_take(p, "=");
  if (typed && !asg) {
    parse_eat(p, "<-");
  } else if (!typed && !step && !parse_take(p, "<-")) {
    const k = parse_reso(p, m);
    return Ann(t, p.book.tlds[k]?.$ === "ADT" ? ADT(k, ts, t.s) : parse_call(p, m, ts, t.s), t.s);
  }
  const v = step ? t : parse_term(p);
  parse_skip(p);
  parse_take(p, ";");
  const s = parse_span(p, beg);
  const n0 = p.stk.length;
  const x = parse_bind(p, typed ? t : Var("_", 0));
  const f = parse_term_do_stmt(p, m, ts, col);
  parse_close(p, n0);
  if (asg) {
    return Let([x.k], [x.i], [Ann(v, A, s)], f, s, [x.q]);
  }
  return parse_call(p, m + ".bind", [...ts.slice(0, -1), A, ...ts.slice(-1), v, Lam(x.k, x.i, f, s, x.q)], s);
}
function parse_body(p, col = 0) {
  parse_skip(p);
  const beg = p.pos;
  if (parse_word(p, "match")) {
    const es = parse_terms(p);
    parse_skip(p);
    const ccol = parse_col(p.str, p.pos);
    const rows = [];
    while (ccol > col && parse_at_word(p, "case") && parse_col(p.str, p.pos) >= ccol) {
      const rcol = parse_col(p.str, p.pos);
      parse_word(p, "case");
      parse_skip(p);
      const qbeg = p.pos;
      const qs = parse_terms(p);
      if (qs.length !== es.length) {
        parse_fail(p, String(es.length) + " patterns (one per scrutinee)", qbeg, p.pos - 1);
      }
      const n02 = p.stk.length;
      const pp = qs.map((q2) => parse_patt(p, q2));
      const f2 = parse_body(p, rcol);
      parse_close(p, n02);
      rows.push({ p: pp, f: f2 });
    }
    return { $: "Match", e: es, r: rows, s: parse_span(p, beg) };
  }
  const q = parse_take(p, "-") ? None() : Lone();
  const vs = [];
  let ts = [q.$ === "None" ? Var(parse_name(p), 0, parse_span(p, beg)) : parse_term(p)];
  parse_skip(p);
  while (!parse_nl(p) && (char_is_head(parse_peek(p)) || q.$ === "Lone" && parse_at(p, "+")) && !KEYWORDS.has(p.str.slice(p.pos).match(/^[A-Za-z0-9_.]*/)?.[0] ?? "")) {
    ts.push(parse_term(p));
    parse_skip(p);
  }
  const at = p.pos;
  let T = ts.length === 1 && parse_take(p, ":") ? parse_term(p) : null;
  parse_skip(p);
  if (T !== null && !parse_at(p, "=")) {
    [p.pos, T] = [at, null];
  }
  if (T === null && q.$ === "Lone" && ts.length === 1 && !(parse_at(p, "=") && !parse_at(p, "=="))) {
    const w = term_write(ts[0]);
    if (w === null || !parse_more(p, parse_col(p.str, beg))) {
      return ts[0];
    }
    vs.push(ts[0]);
    ts = [w];
  } else {
    parse_eat(p, "=");
    T !== null && vs.push(Ann(parse_term(p), T, parse_span(p, beg)));
  }
  while (vs.length < ts.length) {
    vs.push(parse_term(p));
  }
  parse_skip(p);
  parse_take(p, ";");
  const n0 = p.stk.length;
  const ks = ts.map((x) => {
    if ((ts.length > 1 || T !== null) && x.$ !== "Var") {
      throw Err(p.book, ctx_nil(), "a name (a parallel or typed let binds names; destructure in its body)", void 0, x.s);
    }
    return parse_patt(p, x);
  });
  const f = parse_body(p, col);
  parse_close(p, n0);
  return { $: "Local", k: ks, q, v: vs, f };
}
function term_write(t) {
  const [h, xs] = term_unapply(t);
  if (h.$ === "Ref" && h.k === "Array.set" && xs.length === 4 && xs[1].$ === "Var") {
    return xs[1];
  }
  return null;
}
function parse_more(p, col) {
  return parse_at(p, ";") || p.pos < p.str.length && parse_col(p.str, p.pos) === col;
}
function parse_block(p) {
  parse_skip(p);
  const b = parse_body(p, parse_col(p.str, p.pos) - 1);
  return body_flatten(b, [], () => p.frs++);
}
function parse_terms(p) {
  const xs = [];
  while (true) {
    xs.push(parse_term(p));
    parse_skip(p);
    if (parse_take(p, ":")) {
      return xs;
    }
    parse_take(p, ",");
  }
}
function parse_tele(p, close, tk = []) {
  const tele = [];
  while (true) {
    parse_skip(p);
    if (parse_take(p, close)) {
      return tele;
    }
    if (close === ")" && parse_at(p, "~") && tk.length < tele.length) {
      parse_fail(p, "a plain binder (only leading binders take ~)");
    }
    const ct = close === ")" && parse_take(p, "~");
    const q = ct ? None() : parse_quant(p);
    const beg = p.pos;
    const k = parse_name(p);
    if (close === "}" && tele.some((cell) => cell[1] === k)) {
      parse_fail(p, "a fresh field name (duplicate declaration: " + k + ")", p.pos - k.length);
    }
    const s = parse_span(p, beg);
    parse_skip(p);
    const bare = q.$ === "Lone" && !parse_at(p, ":");
    if (!bare) {
      parse_eat(p, ":");
    }
    const T = bare ? Qnt(s) : parse_term(p);
    if (ct) {
      tk.push(k);
    }
    tele.push([bare ? None() : q, k, parse_open(p, k), T, s]);
    parse_skip(p);
    parse_take(p, ",");
  }
}
function parse_fresh(p, nm, tab = p.book.tlds, what = "a fresh name") {
  const k = parse_qual(p, nm);
  const a = nm.includes(".") ? nm.slice(0, nm.indexOf(".")) : "";
  if (k in tab || nm in tab || a in p.al) {
    parse_fail(p, what + " (" + (a in p.al ? a + " is an import's alias" : "duplicate declaration: " + nm) + ")", p.pos - nm.length);
  }
  return k;
}
function parse_def(p, u) {
  const book = p.book;
  const nm = parse_name(p);
  const q = parse_reso(p, nm);
  const tld = book.tlds[q];
  const law = tld?.$ === "Def" && tld.v === null && tld.b !== true && !tld.i ? tld : void 0;
  const k = law ? q : parse_fresh(p, nm);
  const un = parse_take(p, "?") || u;
  parse_eat(p, "(");
  parse_skip(p);
  if (law && parse_at(p, "~")) {
    parse_fail(p, "a name");
  }
  const tk = [];
  const tele = parse_tele(p, ")", tk);
  parse_skip(p);
  let def;
  if (law) {
    if (tele.some((cell) => cell[3].$ !== "Qnt")) {
      parse_fail(p, "a name");
    }
    if (tele.length < law.x) {
      parse_fail(p, "a name for each ~ clause of the law (" + String(law.x) + ")");
    }
    def = law;
    def.n = tele.length;
  } else {
    if (!parse_take(p, "->")) {
      parse_fail(p, "'->' (a def with no return type fills a law; no law named " + nm + " is in scope)");
    }
    def = book.tlds[k] = { $: "Def", n: tele.length, x: tk.length, T: term_higher(tele_bind(tele, parse_term(p))), v: null, m: p.ns };
  }
  def.u ||= un;
  parse_eat(p, ":");
  if (parse_at_word(p, "import")) {
    if (def.x > 0) {
      parse_fail(p, "a body (a template is not foreign)");
    }
    def.i = [];
    while (parse_word(p, "import")) {
      parse_eat(p, '"');
      let eff = "";
      while (parse_peek(p) !== '"' && parse_peek(p) !== "") {
        eff += parse_bump(p);
      }
      parse_eat(p, '"');
      if (!/\.(c|js)$/.test(eff)) {
        parse_fail(p, "a .c or .js path");
      }
      def.i.push(p.dir + eff);
    }
  } else {
    const vars = tele.map((cell) => ({ $: "PVar", k: cell[1], i: cell[2], q: Lone(), s: cell[4] }));
    def.v = term_higher(term_lower(term_higher(body_flatten(parse_body(p), vars, () => p.frs++))));
  }
  book.order.push(k);
}
function parse_book(book, dir, src, ns, al) {
  const p = { book, dir, str: src, pos: 0, stk: [], frs: 0, ns, al };
  while (true) {
    parse_skip(p);
    if (p.pos >= p.str.length) {
      return;
    }
    p.frs = 0;
    parse_close(p, 0);
    if (parse_take(p, "@")) {
      if (!parse_word(p, "unsafe")) {
        parse_fail(p, "'unsafe' (the one decorator)");
      }
      if (!parse_word(p, "def")) {
        parse_fail(p, "'def' (@unsafe marks the def below it)");
      }
      parse_def(p, true);
      continue;
    }
    if (parse_word(p, "def")) {
      parse_def(p, false);
      continue;
    }
    if (parse_word(p, "type")) {
      const k = parse_fresh(p, parse_name(p));
      parse_skip(p);
      const params = parse_take(p, "<") ? parse_tele(p, ">") : [];
      if (!parse_word(p, "is")) {
        parse_fail(p, "'is'");
      }
      const K = parse_term(p);
      parse_eat(p, ":");
      const cs = [];
      const g = params.findIndex((cell) => cell[3].$ !== "Qnt");
      book.tlds[k] = { $: "ADT", n: params.length, g: g < 0 ? params.length : g, T: term_higher(tele_bind(params, K)), c: cs };
      while (true) {
        parse_skip(p);
        if (!char_is_head(parse_peek(p)) || ["def", "type", "law"].some((w) => parse_at_word(p, w))) {
          break;
        }
        const c = parse_fresh(p, parse_name(p), book.ctrs, "a fresh constructor name");
        parse_eat(p, "{");
        const n1 = p.stk.length;
        const fs3 = parse_tele(p, "}");
        const tip = ADT(k, params.map((cell) => Var(cell[1], cell[2])));
        const ctr = { k: c, n: fs3.length, T: term_higher(tele_bind(params.concat(fs3), tip)) };
        parse_close(p, n1);
        cs.push(ctr);
        book.ctrs[c] = ctr;
      }
      book.order.push(k);
      continue;
    }
    if (parse_word(p, "law")) {
      const k = parse_fresh(p, parse_name(p));
      parse_eat(p, ":");
      const cls = [];
      let tc = 0;
      while (parse_at_word(p, "for") || parse_at_word(p, "exs")) {
        const all = parse_word(p, "for");
        if (!all) {
          parse_word(p, "exs");
        }
        parse_skip(p);
        if (all && parse_at(p, "~") && tc < cls.length) {
          parse_fail(p, "a plain clause (only leading clauses take ~)");
        }
        const ct = all && parse_take(p, "~");
        const q = ct ? None() : all ? parse_quant(p) : Lone();
        const beg = p.pos;
        const c = parse_name(p);
        const s = parse_span(p, beg);
        if (ct) {
          tc += 1;
        }
        parse_eat(p, ":");
        let A = parse_term(p);
        if (parse_at_word(p, "where")) {
          const beg2 = p.pos;
          parse_word(p, "where");
          const ws = parse_span(p, beg2);
          const n1 = p.stk.length;
          const i = parse_open(p, c);
          const w = parse_term(p);
          parse_close(p, n1);
          A = App(App(Ref("Exists", ws), A, s), Lam(c, i, w, s), s);
        }
        cls.push([all, q, c, parse_open(p, c), A, s]);
      }
      const T = cls.reduceRight((T2, [all, q, c, i, A, s]) => all ? All(q, c, i, A, T2, s) : App(App(Ref("Exists", s), A, s), Lam(c, i, T2, s), s), parse_block(p));
      const n = cls.findIndex((c) => !c[0]);
      book.tlds[k] = { $: "Def", n: n < 0 ? cls.length : n, T: term_higher(T), v: null, x: tc, m: p.ns };
      book.order.push(k);
      continue;
    }
    parse_fail(p, "'def', 'type' or 'law'");
  }
}
function body_sub(b, i, v) {
  function scrut(e) {
    if (e.$ === "Var") {
      return e.i !== i ? e : patt_term(v, e.s);
    } else {
      return Sub(i, v, e);
    }
  }
  switch (b.$) {
    case "Match": {
      const es = b.e.map(scrut);
      const rs = b.r.map((row) => ({ p: row.p, f: body_sub(row.f, i, v) }));
      return { $: "Match", e: es, r: rs, s: b.s };
    }
    case "Local": {
      const w = b.v.map(scrut);
      const f = body_sub(b.f, i, v);
      return { $: "Local", k: b.k, q: b.q, v: w, f };
    }
    default: {
      return Sub(i, v, b);
    }
  }
}
function match_flatten(m, vars, fr) {
  if (m.e.length === 0 && m.r.length > 0) {
    return body_flatten(m.r[0].f, vars, fr);
  } else if (m.e.length === 0) {
    throw Err(book_nil(), ctx_nil(), "a case (this match has no row to return)", void 0, m.s);
  } else if (vars.length === 0) {
    let e = m.e[0];
    while (e.$ === "Sub") {
      e = e.f;
    }
    switch (e.$) {
      case "Var": {
        throw Err(
          book_nil(),
          ctx_nil(),
          "a match on a parameter or field (this name is a def or a consumed binder: give the value its own def)",
          void 0,
          e.s
        );
      }
      case "Ctr":
      case "Lit": {
        throw Err(book_nil(), ctx_nil(), "an undestructed scrutinee (this value is already a constructor: bind its fields directly; if an outer match destructed it, fold the pattern into the outer case)", void 0, m.s);
      }
      default: {
        throw Err(book_nil(), ctx_nil(), "a parameter or field scrutinee (a match cannot scrutinize a computed value: give it its own def)", void 0, e.s ?? m.s);
      }
    }
  } else {
    const x = vars[0];
    const scu = m.e[0];
    const c = m.r.map((row) => row.p[0]).find((q) => q.$ === "PCtr") ?? null;
    const v = vars.find((w) => scu.$ === "Var" && w.i === scu.i);
    if (v !== void 0 && c === null && m.r.length > 0) {
      const w = { ...v, q: patt_mark(v, m.r) };
      const rs = m.r.map((row) => {
        const p0 = row.p[0];
        if (p0.$ !== "PVar") {
          throw Err(book_nil(), ctx_nil(), "a variable pattern (this column has no constructor row)", void 0, p0.s);
        }
        return { p: row.p.slice(1), f: body_sub(row.f, p0.i, w) };
      });
      return match_flatten({ $: "Match", e: m.e.slice(1), r: rs, s: m.s }, vars.map((u) => u === v ? w : u), fr);
    } else if (v === x) {
      if (c === null) {
        return Efq(m.s);
      } else {
        const xq = patt_mark(x, m.r);
        const xs = c.x.map((q) => {
          if (q.$ === "PVar") {
            return { ...q, q: quant_join(q.q, xq) };
          }
          const i = fr();
          return { $: "PVar", k: "_" + String(i), i, q: xq, s: q.s };
        });
        const kx = { $: "PCtr", k: c.k, x: xs, s: x.s };
        const ps = m.r.flatMap((row) => {
          const p0 = row.p[0];
          switch (p0.$) {
            case "PCtr": {
              if (p0.k !== c.k) {
                return [];
              }
              const f = body_sub(row.f, x.i, kx);
              return [{ p: [...p0.x, ...row.p.slice(1)], f }];
            }
            case "PVar": {
              const g = body_sub(row.f, p0.i, x);
              const f = body_sub(g, x.i, kx);
              return [{ p: [...xs, ...row.p.slice(1)], f }];
            }
          }
        });
        const pe = xs.map((q) => patt_term(q)).concat(m.e.slice(1));
        const pv = xs.concat(vars.slice(1));
        const pt = match_flatten({ $: "Match", e: pe, r: ps, s: m.s }, pv, fr);
        const ds = m.r.filter((row) => row.p[0].$ !== "PCtr" || row.p[0].k !== c.k);
        const dt = match_flatten({ $: "Match", e: m.e, r: ds, s: m.s }, vars, fr);
        return Mat(c.k, pt, dt, c.s);
      }
    } else {
      const t = match_flatten(m, vars.slice(1), fr);
      return Lam(x.k, x.i, t, x.s, x.q);
    }
  }
}
function patt_mark(x, rows) {
  return rows.map((row) => row.p[0]).reduce((q, p) => p.$ === "PVar" ? quant_join(q, p.q) : q, x.q);
}
function patt_term(q, s) {
  switch (q.$) {
    case "PVar": {
      return Var(q.k, q.i, s ?? q.s);
    }
    case "PCtr": {
      const xs = q.x.map((x) => patt_term(x, s));
      return Ctr(q.k, xs, s ?? q.s);
    }
  }
}
function body_flatten(b, vars, fr) {
  switch (b.$) {
    case "Local": {
      if (b.k.length === 1 && b.k[0].$ === "PCtr") {
        const r = { p: [b.k[0]], f: b.f };
        return match_flatten({ $: "Match", e: [b.v[0]], r: [r], s: b.v[0].s }, vars, fr);
      }
      const ws = b.k;
      let g = body_flatten(b.f, ws, fr);
      for (const w of ws) {
        if (g.$ !== "Lam") {
          throw Err(book_nil(), ctx_nil(), "a parameter or field scrutinee (a match cannot scrutinize a local binder: give it its own def)", void 0, w.s);
        }
        g = g.f;
      }
      const x = Let(ws.map((w) => w.k), ws.map((w) => w.i), b.v, g, ws[0].s, ws.map((w) => quant_dem(b.q, w.q)));
      return body_flatten(x, vars, fr);
    }
    case "Match": {
      return match_flatten(b, vars, fr);
    }
    default: {
      if (vars.length === 0) {
        return b;
      } else {
        const v = vars[0];
        const f = body_flatten(b, vars.slice(1), fr);
        return Lam(v.k, v.i, f, v.s, v.q);
      }
    }
  }
}
function term_wnf(book, term) {
  const frs = [];
  let tm = term;
  let lhs = null;
  main: while (true) {
    focus: switch (tm.$) {
      case "Var": {
        if (tm.v === void 0) {
          break focus;
        } else {
          if (tm.i === -1) {
            frs.push({ $: "VAR", l: tm, a: tm.v.$ === "Ann" ? tm.v : void 0 });
          }
          lhs = null;
          tm = tm.v;
          continue main;
        }
      }
      case "Ann": {
        tm = tm.x;
        continue main;
      }
      case "Min": {
        frs.push({ $: "MNA", b: tm.b, s: tm.s });
        tm = tm.a;
        continue main;
      }
      case "Let": {
        const l = tm;
        tm = l.f(l.v.map((v, j) => term_cell(v, l.k[j])));
        continue main;
      }
      case "App": {
        frs.push({ $: "APP", x: term_cell(tm.x), s: tm.s });
        lhs = null;
        tm = tm.f;
        continue main;
      }
      case "Lam": {
        if (frs.length === 0 || frs[frs.length - 1].$ !== "APP") {
          break focus;
        } else {
          const fr = frs.pop();
          if (lhs !== null && lhs.n === 0) {
            lhs = null;
          } else if (lhs !== null) {
            const pt = lhs.t;
            const pn = lhs.n;
            lhs = { t: () => term_apply(pt(), fr.x, fr.s), n: pn - 1 };
          }
          tm = tm.f(fr.x);
          continue main;
        }
      }
      case "Mat": {
        if (frs.length === 0 || frs[frs.length - 1].$ !== "APP") {
          break focus;
        } else {
          const fr = frs.pop();
          frs.push({ $: "MAT", t: tm, e: fr.x, lhs, s: fr.s });
          tm = fr.x;
          lhs = null;
          continue main;
        }
      }
      case "Efq": {
        if (lhs !== null && lhs.n > 0 && frs.length > 0 && frs[frs.length - 1].$ === "APP") {
          tm = lhs.t();
        }
        break focus;
      }
      case "Rwt": {
        const e = term_wnf(book, tm.e);
        if (e.$ === "Rfl") {
          tm = tm.f;
          continue main;
        }
        break focus;
      }
      case "Ref": {
        const tld = book.tlds[tm.k];
        if (tld === void 0) {
          break focus;
        }
        if (tld.$ === "ADT") {
          if (tld.n === 0) {
            tm = ADT(tm.k, [], tm.s);
          }
          break focus;
        }
        let run = 0;
        while (run < tld.n && run < frs.length && frs[frs.length - 1 - run].$ === "APP") {
          run += 1;
        }
        if (run < tld.n || tld.v === null) {
          break focus;
        }
        const rf = tm;
        lhs = { t: () => rf, n: tld.n };
        tm = tld.v;
        continue main;
      }
      default: {
        break focus;
      }
    }
    lhs = null;
    back: while (true) {
      const fr = frs.pop();
      if (fr === void 0) {
        return tm;
      } else {
        switch (fr.$) {
          case "VAR": {
            switch (tm.$) {
              case "Ctr":
                tm = Ctr(tm.k, tm.x.map((x) => term_cell(x)), tm.s);
                break;
              case "ADT":
                tm = ADT(tm.k, tm.x.map((x) => term_cell(x)), tm.s, tm.r);
                break;
              case "All":
                tm = All(tm.q, tm.k, tm.i, term_cell(tm.A), tm.B, tm.s);
                break;
              case "Mat":
                tm = Mat(tm.k, term_cell(tm.h), term_cell(tm.m), tm.s);
                break;
              case "Eql":
                tm = Eql(term_cell(tm.a), term_cell(tm.b), term_cell(tm.T), tm.s);
                break;
              case "Min":
                tm = Min(term_cell(tm.a), term_cell(tm.b), tm.s);
                break;
              case "Typ":
                tm = Typ(term_cell(tm.g), tm.s);
                break;
              default:
                break;
            }
            fr.l.v = fr.a === void 0 ? tm : Ann(tm, term_cell(fr.a.T), fr.a.s);
            fr.l.i = -2;
            continue main;
          }
          case "APP": {
            tm = term_apply(tm, fr.x, fr.s);
            continue back;
          }
          case "MNA": {
            if (tm.$ === "Qua" && tm.q.$ === "Many") {
              tm = fr.b;
              continue main;
            }
            if (tm.$ === "Qua" && tm.q.$ === "None") {
              continue back;
            }
            frs.push({ $: "MNB", a: tm, s: fr.s });
            tm = fr.b;
            continue main;
          }
          case "MNB": {
            if (tm.$ === "Qua" && tm.q.$ === "Many") {
              tm = fr.a;
            } else if (tm.$ !== "Qua" || tm.q.$ === "Lone" && fr.a.$ !== "Qua") {
              tm = Min(fr.a, tm, fr.s);
            }
            continue back;
          }
          case "MAT": {
            if (tm.$ === "Lit") {
              tm = lit_step(tm);
            }
            if (tm.$ === "Ctr") {
              const ctr = tm;
              let t = fr.t;
              walk: while (true) {
                switch (t.$) {
                  case "Ann": {
                    t = t.x;
                    continue walk;
                  }
                  case "Mat": {
                    if (t.k === ctr.k) {
                      const fl = fr.lhs;
                      if (fl === null) {
                        lhs = null;
                      } else {
                        lhs = { t: () => lhs_ext(fl.t(), ctr.k, ctr.x.length), n: fl.n - 1 + ctr.x.length };
                      }
                      for (let j = ctr.x.length - 1; j >= 0; j--) {
                        frs.push({ $: "APP", x: term_cell(ctr.x[j]) });
                      }
                      tm = t.h;
                      continue main;
                    } else {
                      t = t.m;
                      continue walk;
                    }
                  }
                  case "Efq": {
                    break walk;
                  }
                  default: {
                    lhs = fr.lhs;
                    frs.push({ $: "APP", x: ctr });
                    tm = t;
                    continue main;
                  }
                }
              }
            }
            tm = term_apply(fr.lhs === null ? fr.t : fr.lhs.t(), fr.e, fr.s);
            continue back;
          }
        }
      }
    }
  }
}
function term_snf(book, term) {
  const tm = term_wnf(book, term);
  switch (tm.$) {
    case "Typ": {
      return Typ(term_snf(book, tm.g), tm.s);
    }
    case "Min": {
      return Min(term_snf(book, tm.a), term_snf(book, tm.b), tm.s);
    }
    case "All": {
      return All(tm.q, tm.k, tm.i, term_snf(book, tm.A), (x) => {
        return term_snf(book, tm.B(x));
      }, tm.s);
    }
    case "Lam": {
      return Lam(tm.k, tm.i, (x) => {
        return term_snf(book, tm.f(x));
      }, tm.s);
    }
    case "App": {
      return App(tm.f.$ === "Ref" ? tm.f : term_snf(book, tm.f), term_snf(book, tm.x), tm.s);
    }
    case "ADT": {
      return ADT(tm.k, tm.x.map((x) => term_snf(book, x)), tm.s, tm.r);
    }
    case "Ctr": {
      return Ctr(tm.k, tm.x.map((x) => term_snf(book, x)), tm.s);
    }
    case "Mat": {
      return Mat(tm.k, term_snf(book, tm.h), term_snf(book, tm.m), tm.s);
    }
    case "Eql": {
      return Eql(term_snf(book, tm.a), term_snf(book, tm.b), term_snf(book, tm.T), tm.s);
    }
    case "Rwt": {
      return Rwt(term_snf(book, tm.e), term_snf(book, tm.p), term_snf(book, tm.f), tm.s);
    }
    default: {
      return tm;
    }
  }
}
function term_compare(mode, book, lhs, rhs, dep = 0) {
  if (lhs === rhs) {
    return true;
  }
  let a = term_wnf(book, lhs);
  let b = term_wnf(book, rhs);
  if (a === b) {
    return true;
  }
  if (a.$ === "Lam" || b.$ === "Lam") {
    const x = Var("_", dep);
    return term_compare(mode, book, term_apply(a, x), term_apply(b, x), dep + 1);
  }
  if (a.$ === "Lit" && b.$ === "Ctr") {
    a = lit_step(a);
  }
  if (b.$ === "Lit" && a.$ === "Ctr") {
    b = lit_step(b);
  }
  switch (a.$) {
    case "Var": {
      return b.$ === "Var" && a.i === b.i;
    }
    case "Ref": {
      return b.$ === "Ref" && a.k === b.k;
    }
    case "Typ": {
      if (b.$ !== "Typ") {
        return false;
      }
      if (mode === "EQ") {
        return term_compare("EQ", book, a.g, b.g, dep);
      }
      const g = term_wnf(book, a.g);
      const h = term_wnf(book, b.g);
      if (g.$ === "Qua" && g.q.$ === "Many" || h.$ === "Qua" && h.q.$ !== "Many") {
        return true;
      }
      if (g.$ === "Min") {
        const fa = term_compare("LE", book, Typ(g.a), b, dep);
        const fb = term_compare("LE", book, Typ(g.b), b, dep);
        return fa && fb;
      }
      if (h.$ === "Min") {
        const fa = term_compare("LE", book, a, Typ(h.a), dep);
        const fb = term_compare("LE", book, a, Typ(h.b), dep);
        return fa || fb;
      }
      return term_compare("LE", book, g, h, dep);
    }
    case "Qnt":
    case "Efq":
    case "Rfl": {
      return b.$ === a.$;
    }
    case "Qua": {
      return b.$ === "Qua" && a.q.$ === b.q.$;
    }
    case "Min": {
      return b.$ === "Min" && term_compare("EQ", book, a.a, b.a, dep) && term_compare("EQ", book, a.b, b.b, dep);
    }
    case "All": {
      const x = Var(a.k, dep);
      return b.$ === "All" && a.q.$ === b.q.$ && term_compare(mode, book, b.A, a.A, dep) && term_compare(mode, book, a.B(x), b.B(x), dep + 1);
    }
    case "App": {
      return b.$ === "App" && term_compare("EQ", book, a.f, b.f, dep) && term_compare("EQ", book, a.x, b.x, dep);
    }
    case "ADT": {
      if (b.$ !== "ADT" || a.k !== b.k || a.x.length !== b.x.length) {
        return false;
      }
      if (mode === "EQ" && a.r.length !== b.r.length) {
        return false;
      }
      return b.r.every((c) => a.r.includes(c)) && a.x.every((x, j) => term_compare("EQ", book, x, b.x[j], dep));
    }
    case "Ctr": {
      return b.$ === "Ctr" && a.k === b.k && a.x.length === b.x.length && a.x.every((x, j) => term_compare("EQ", book, x, b.x[j], dep));
    }
    case "Lit": {
      return b.$ === "Lit" && a.k === b.k && a.v === b.v;
    }
    case "Mat": {
      return b.$ === "Mat" && a.k === b.k && term_compare("EQ", book, a.h, b.h, dep) && term_compare("EQ", book, a.m, b.m, dep);
    }
    case "Eql": {
      return b.$ === "Eql" && term_compare("EQ", book, a.a, b.a, dep) && term_compare("EQ", book, a.b, b.b, dep) && term_compare("EQ", book, a.T, b.T, dep);
    }
    case "Hol": {
      return b.$ === "Hol" && a.k === b.k;
    }
    case "Rwt": {
      return b.$ === "Rwt" && term_compare("EQ", book, a.e, b.e, dep) && term_compare("EQ", book, a.p, b.p, dep) && term_compare("EQ", book, a.f, b.f, dep);
    }
    default: {
      return false;
    }
  }
}
function term_descend(q, arg, col) {
  if (q.$ === "None") {
    return "EQ";
  }
  const s = term_strip(arg);
  const p = term_strip(col);
  const a = s.$ === "Lit" && p.$ === "Ctr" ? lit_step(s) : s;
  switch (p.$) {
    case "Var": {
      if (a.$ === "Var" && a.i === p.i) {
        return "EQ";
      } else {
        return "GT";
      }
    }
    case "Ctr": {
      let bad = -1;
      if (a.$ === "Ctr" && a.k === p.k && a.x.length === p.x.length) {
        let ord = "EQ";
        for (let j = 0; j < a.x.length && bad < 0; j++) {
          const fld = term_descend(Lone(), a.x[j], p.x[j]);
          ord = fld === "EQ" ? ord : fld;
          bad = fld === "GT" ? j : bad;
        }
        if (bad < 0) {
          return ord;
        }
      }
      for (let j = 0; j < p.x.length; j++) {
        if (j !== bad && term_descend(Lone(), a, p.x[j]) !== "GT") {
          return "LT";
        }
      }
      return "GT";
    }
    default: {
      return "GT";
    }
  }
}
function term_infer(book, lhs, tm, qt, ctx, d, sp = []) {
  switch (tm.$) {
    // Γ[x] = q A
    // where x is bound in Γ (a ~ argument checks in the empty context,
    //       so a variable of the caller's is unbound there)
    // ----------------- infer-var
    // Γ ⊢ x : A ~ {x:q}
    case "Var": {
      if (tm.i < 0 && tm.v !== void 0) {
        return term_infer(book, lhs, term_force(tm), qt, ctx, d, sp);
      }
      const ann = pmap_get(ctx, tm.i);
      if (ann === null) {
        throw Err(book, ctx, "a bound variable", tm, tm.s, lhs.def);
      } else {
        return Infer(Var(tm.k, tm.i, tm.s), ann.T, pmap_set(uses_nil(), tm.i, qt));
      }
    }
    // Book(k) : T
    // where a live k that is the lhs head descends: its pending
    //       arguments sp (the spine above it) compare EQ against the
    //       lhs columns left to right until one is LT; an erased (-)
    //       column is skipped; a bare or non-shrinking self-reference
    //       is an error, so a self-reference never escapes as a value
    //       k has a body in a live region, unless base declared it, it
    //       is a template's ~ parameter, or the def is @unsafe (an
    //       unfilled law is a dead claim; base's are native, a ~
    //       parameter an opaque constant, and an unsafe body trusts it)
    //       a template k in a live region outside a template's own text
    //       takes its x ~ arguments here: the call is k~n, the instance
    //       at them (def_inst), and the x applications above pass
    //       (infer-app)
    //       k is not a parameterized family: D<..> is the one
    //       spelling, a bare family head is an error
    // -------------------------------------------------------- infer-ref
    // Γ ⊢ k : T ~ {}
    case "Ref": {
      const tld = book.tlds[tm.k];
      if (tld === void 0) {
        throw Err(book, ctx, "a defined name", tm, tm.s, lhs.def);
      }
      let k = tm.k;
      let x = 0;
      if (qt.$ !== "None") {
        const gen = tld.$ === "Def" && tld.x > 0 && !book.tlds[lhs.def].x ? tld : null;
        if (tld.$ === "Def" && tld.v === null && !tld.i && (tld.b !== true && lhs.u !== true || gen !== null) && k !== lhs.def) {
          throw Err(book, ctx, "a filled definition (an unfilled law is a dead claim: live code cannot use it)", tm, tm.s, lhs.def);
        }
        if (gen !== null) {
          k = def_inst(book, lhs, tm, gen, sp, ctx, d);
          x = gen.x;
          sp = sp.slice(x);
        }
        if (k === lhs.def && lhs.u !== true) {
          const cols = term_unapply(lhs.t)[1];
          let ord = "EQ";
          for (let j = 0; j < cols.length && j < sp.length && ord === "EQ"; j++) {
            ord = term_descend(lhs.qs[j], sp[j], cols[j]);
          }
          if (ord !== "LT") {
            throw Err(book, ctx, "a decreasing self-call (arguments are read left to right: each passed unchanged until one shrinks)", tm, tm.s, lhs.def);
          }
        }
      }
      if (tld.$ === "ADT" && tld.n > 0) {
        throw Err(book, ctx, "a family instance (write " + tm.k + "<..>)", tm, tm.s, lhs.def);
      }
      return Infer(Ref(k, tm.s, tm.b), book.tlds[k].T, uses_nil(), x);
    }
    // Γ ⊢ q : Quant
    // where q is dead
    // ------------------- infer-typ
    // Γ ⊢ Kind(q) : Type
    case "Typ": {
      const g_chk = term_check(book, lhs, tm.g, None(), Qnt(tm.s), ctx, d);
      return Infer(Typ(g_chk.tm, tm.s), Typ(Qua(Lone()), tm.s), uses_nil());
    }
    // ∅
    // ------------------------------------ infer-qnt
    // Γ ⊢ Quant : Type    Γ ⊢ &1, &2 : Quant
    case "Qnt": {
      return Infer(tm, Typ(Qua(Lone()), tm.s), uses_nil());
    }
    case "Qua": {
      return Infer(tm, Qnt(tm.s), uses_nil());
    }
    // Γ ⊢ a : Quant ~ au    Γ ⊢ b : Quant ~ bu
    // ------------------------------------- infer-min
    // Γ ⊢ a <&> b : Quant ~ au + bu
    case "Min": {
      const a_chk = term_check(book, lhs, tm.a, qt, Qnt(tm.s), ctx, d);
      const b_chk = term_check(book, lhs, tm.b, qt, Qnt(tm.s), ctx, d);
      return Infer(Min(a_chk.tm, b_chk.tm, tm.s), Qnt(tm.s), uses_add(a_chk.us, b_chk.us));
    }
    // Γ ⊢ A : Kind(q)
    // Γ , x : qA ⊢ B(x) : Type
    // ----------------------------------------------- infer-all
    // Γ ⊢ @q x:A -> B : Type
    case "All": {
      const B_ctx = ctx_bind(ctx, d, tm.q, tm.k, tm.A);
      const A_chk = term_check(book, lhs, tm.A, None(), Typ(Qua(lhs_kind(lhs, tm.q)), tm.s), ctx, d);
      const B_chk = term_check(book, lhs, tm.B(Var(tm.k, d)), None(), Typ(Qua(Lone()), tm.s), B_ctx, d + 1);
      return Infer(All(tm.q, tm.k, d, A_chk.tm, B_chk.tm, tm.s), Typ(Qua(Lone()), tm.s), uses_nil());
    }
    // Γ ⊢ f : @q x:A -> B ~ fu
    // Γ ⊢ a : A ~ au
    // where a is dead if q is -, and consumed once otherwise: its
    //       measure adds unscaled (certify-once), a + callee copies it
    //       f infers with a on its pending spine, for infer-ref's descent
    //       a family head is not a function: infer-ref rejects it,
    //       so D(x) is an error and D<x> the one spelling
    //       (x => f)(a) never arrives: term_higher builds it as f(a) (a
    //       substituted lambda, a Sigma field type B(fst) say, makes one)
    //       a template head took a as a ~ argument (infer-ref, x of
    //       them): the application passes, its instance stands for both
    // --------------------------------------------------------------- infer-app
    // Γ ⊢ f(a) : B(a) ~ fu + au
    case "App": {
      const f_inf = term_infer(book, lhs, tm.f, qt, ctx, d, [tm.x, ...sp]);
      if (f_inf.x) {
        return { ...f_inf, x: f_inf.x - 1 };
      }
      const f_wnf = term_wnf(book, f_inf.ty);
      if (f_wnf.$ !== "All") {
        throw Err(book, ctx, "a function type", f_inf.ty, tm.s, lhs.def);
      }
      const x_chk = term_check(book, lhs, tm.x, quant_dem(f_wnf.q, qt), f_wnf.A, ctx, d);
      return Infer(App(f_inf.tm, x_chk.tm, tm.s), f_wnf.B(tm.x), uses_add(f_inf.us, x_chk.us));
    }
    // book[k].T = @q1 p1:K1 -> .. -> Kind(G)
    // Γ ⊢ xi : Ki ~ ui
    // where xi is dead if qi is -
    // ------------------------------------------------- infer-adt
    // Γ ⊢ k<x1, .., xn> : Kind(G[x..]) ~ u1 + .. + un
    case "ADT": {
      const adt = book_adt(book, tm, ctx, lhs.def);
      if (tm.x.length !== adt.n) {
        throw Err(book, ctx, tm.k + " with " + String(adt.n) + (adt.n === 1 ? " parameter" : " parameters"), tm, tm.s, lhs.def);
      }
      const { xs, us, tel } = tele_check(book, lhs, adt.T, tm.x, qt, ctx, d, tm.s);
      return Infer(ADT(tm.k, xs, tm.s, tm.r), tel, us);
    }
    // Γ ⊢ A : Type    Γ ⊢ a : A    Γ ⊢ b : A
    // where A, a and b are dead; evidence is erased, so Data
    // ------------------------------------------------------ infer-eql
    // Γ ⊢ {a == b : A} : Data ~ {}
    case "Eql": {
      const T_chk = term_check(book, lhs, tm.T, None(), Typ(Qua(Lone()), tm.s), ctx, d);
      const a_chk = term_check(book, lhs, tm.a, None(), tm.T, ctx, d);
      const b_chk = term_check(book, lhs, tm.b, None(), tm.T, ctx, d);
      return Infer(Eql(a_chk.tm, b_chk.tm, T_chk.tm, tm.s), Typ(Qua(Many()), tm.s), uses_nil());
    }
    // Γ ⊢ T : Type
    // Γ ⊢ x : T ~ u
    // where T is dead
    // ------------------- infer-ann
    // Γ ⊢ {x : T} : T ~ u
    case "Ann": {
      term_check(book, lhs, tm.T, None(), Typ(Qua(Lone()), tm.s), ctx, d);
      const x_chk = term_check(book, lhs, tm.x, qt, tm.T, ctx, d);
      return { tm: x_chk.tm, ty: tm.T, us: x_chk.us };
    }
    // x is a Lam, Let, Ctr, Lit, Mat, Efq, Rfl, Rwt or Hol
    // ------------------------------------------- infer-err
    // Γ ⊢ x : ⊥ (a goal is needed)
    default: {
      const t = tm.$ === "Lit" ? lit_step(tm) : tm;
      if (t.$ === "Ctr" && book_ctr(book, t.k) === null) {
        throw Err(book, ctx, "a declared constructor", tm, tm.s, lhs.def);
      }
      throw Err(book, ctx, "an annotated term (cannot infer)", tm, tm.s, lhs.def);
    }
  }
}
function tele_check(book, lhs, tel, xs, qt, ctx, d, s) {
  const out = [];
  let us = uses_nil();
  for (const x of xs) {
    const t_all = tele_head(book, tel, ctx, lhs.def, s);
    const t_dem = quant_dem(t_all.q, qt);
    const x_chk = term_check(book, lhs, x, t_dem, t_all.A, ctx, d);
    out.push(x_chk.tm);
    us = uses_add(us, x_chk.us);
    tel = t_all.B(x);
  }
  return { xs: out, us, tel };
}
function term_check_kind(book, lhs, T, q, ctx, d, s) {
  const kind = Typ(Qua(lhs_kind(lhs, q)), s);
  try {
    term_check(book, lhs, T, None(), kind, ctx, d);
  } catch (e) {
    const err = e;
    throw err?.$ === "Err" && err.exp === kind ? { ...err, spn: s ?? err.spn } : e;
  }
}
function uses_close(book, ctx, us, i, k, q, s, def) {
  const u = pmap_get(us, i) ?? None();
  if (quant_join(u, q).$ !== q.$) {
    let obs = quant_show(u) + k;
    if (u.$ === "Many") {
      obs = k + " (consumed more than once)";
    }
    throw Err(book, ctx, quant_show(q) + k, obs, s, def);
  }
  return pmap_set(us, i, None());
}
function term_check(book, lhs, tm, qt, ty, ctx, d) {
  switch (tm.$) {
    case "Var": {
      if (tm.i < 0 && tm.v !== void 0) {
        return term_check(book, lhs, term_force(tm), qt, ty, ctx, d);
      }
      break;
    }
    // T == @q x:A -> B
    // Γ , x : q'A ⊢ f(x) : B(x) ~ u
    // where q' is q, or + at a + binder when q is 1 and A : Kind(+)
    //       u[x] <= q'
    //       lhs steps by x while a parameter remains
    // ---------------------------------------------- check-lam
    // Γ ⊢ x => f : T ~ u - x
    case "Lam": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(book, ctx, ty, "non-inferrable term", tm.s, lhs.def);
      }
      const x = Var(tm.k, d);
      let f_lhs = lhs;
      if (lhs.n > 0) {
        f_lhs = { ...lhs, t: term_apply(lhs.t, x), n: lhs.n - 1 };
      }
      let q = t_wnf.q;
      if (tm.q?.$ === "Many" && q.$ === "Lone") {
        q = tm.q;
        term_check_kind(book, lhs, t_wnf.A, q, ctx, d, tm.s);
      }
      const f_ctx = ctx_bind(ctx, d, q, tm.k, t_wnf.A);
      const f_chk = term_check(book, f_lhs, tm.f(x), qt, t_wnf.B(x), f_ctx, d + 1);
      return Check(Lam(tm.k, d, f_chk.tm, tm.s), ty, uses_close(book, ctx, f_chk.us, d, tm.k, q, tm.s, lhs.def));
    }
    // Γ ⊢ vj : Aj ~ vuj  (each value in Γ: the binders are parallel)
    // Γ ⊢ Aj : Kind(qj)
    // Γ , x1 : q1A1 , .. , xn : qnAn ⊢ f(x1, .., xn) : T ~ fu
    // where vj is dead if qj is -
    //       fu[xj] <= qj
    // ------------------------------------------------------------ check-let
    // Γ ⊢ q1 x1 .. qn xn = v1 .. vn; f : T ~ vu1 + .. + vun + fu - x⃗
    case "Let": {
      const n = tm.k.length;
      const vx = [];
      let us = uses_nil();
      let f_ctx = ctx;
      for (let j = 0; j < n; j++) {
        const v_dem = quant_dem(tm.q[j], qt);
        const v_inf = term_infer(book, lhs, tm.v[j], v_dem, ctx, d);
        term_check_kind(book, lhs, v_inf.ty, tm.q[j], ctx, d, tm.s);
        vx.push(v_inf.tm);
        us = uses_add(us, v_inf.us);
        f_ctx = ctx_bind(f_ctx, d + j, tm.q[j], tm.k[j], v_inf.ty);
      }
      const xs = tm.k.map((k, j) => Var(k, d + j, void 0, tm.v[j]));
      const f_chk = term_check(book, lhs, tm.f(xs), qt, ty, f_ctx, d + n);
      let fu = f_chk.us;
      for (let j = 0; j < n; j++) {
        fu = uses_close(book, ctx, fu, d + j, tm.k[j], tm.q[j], tm.s, lhs.def);
      }
      return Check(Let(tm.k, xs.map((_, j) => d + j), vx, f_chk.tm, tm.s, tm.q), ty, uses_add(us, fu));
    }
    // T == D<p1, .., pm>
    // D.c[k] = @q1 x1:F1 -> .. -> D<p1, .., pm>
    // Γ ⊢ xi : Fi ~ ui
    // where xi is dead if qi is -
    // ------------------------------------------ check-ctr
    // Γ ⊢ k{x1, .., xn} : T ~ u1 + .. + un
    case "Ctr": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "ADT") {
        const fam = book_ctr(book, tm.k) === null ? null : book_fam(book, tm.k);
        const nte = fam === null && book.tlds[tm.k]?.$ === "ADT" ? "Note: " + tm.k + " is a datatype: write its arguments as <>" : void 0;
        throw Err(book, ctx, ty, fam === null ? "non-inferrable term" : Ref(fam, tm.s), tm.s, lhs.def, nte);
      }
      const adt = book_adt(book, t_wnf, ctx, lhs.def);
      const ctr = adt.c.find((c) => c.k === tm.k);
      if (ctr === void 0) {
        if (book_ctr(book, tm.k) === null) {
          throw Err(book, ctx, "a declared constructor (" + t_wnf.k + " declares " + adt.c.map((c) => c.k).join(", ") + ")", tm, tm.s, lhs.def);
        }
        throw Err(book, ctx, ty, Ref(book_fam(book, tm.k), tm.s), tm.s, lhs.def);
      }
      if (tm.x.length !== ctr.n) {
        throw Err(book, ctx, tm.k + " with " + String(ctr.n) + (ctr.n === 1 ? " field" : " fields"), tm, tm.s, lhs.def);
      }
      const tel = tele_fill(book, ctr.T, t_wnf.x, ctx, lhs.def, tm.s);
      const { xs, us } = tele_check(book, lhs, tel, tm.x, qt, ctx, d, tm.s);
      return Check(Ctr(tm.k, xs, tm.s), ty, us);
    }
    // T == Base's type k of the literal, no constructor removed
    // where any other T checks the literal's first step, which reports
    //       as the constructor it is
    // ----------------------------------------------------------- check-lit
    // Γ ⊢ "text" : T ~ {}    Γ ⊢ 3n : T ~ {}
    case "Lit": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ === "ADT" && t_wnf.k === tm.k && t_wnf.r.length === 0 && book.tlds[tm.k]?.b === true) {
        return Check(tm, ty, uses_nil());
      }
      return term_check(book, lhs, lit_step(tm), qt, ty, ctx, d);
    }
    // T == @q s:D<p..> -> P
    // D.c[k] = @r1 x1:F1 -> .. -> D<p..>
    // Γ ⊢ h : @s1 x1:F1 -> .. -> P(k{x1, .., xn}) ~ hu
    // Γ ⊢ m : @q s:(D - k)<p..> -> P ~ mu
    // where q is not - in a live region
    //       si = ri · q (a field's quantity times its scrutinee's)
    //       h's lhs steps by k{x1, .., xn} while a parameter remains
    // -------------------------------------------------------------- check-mat
    // Γ ⊢ \ {k: h; m} : T ~ hu | mu
    //
    // T == @q s:D<p..> -> P    D.c = [] or live x:E ∈ Γ with E.c = []
    // where q is not - in a live region; a LIVE binder at an emptied
    //       ADT makes the region unreachable (a flattened match's
    //       default chain past its last constructor) - an erased one
    //       proves nothing, dead code inhabits it - so residue is dead
    // ------------------------------------------------------------- check-efq
    // Γ ⊢ \ {} : T ~ {}
    case "Mat":
    case "Efq": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "All") {
        throw Err(book, ctx, ty, "non-inferrable term", tm.s, lhs.def);
      }
      if (qt.$ !== "None" && t_wnf.q.$ === "None") {
        throw Err(book, ctx, "a live scrutinee (a - scrutinee matches only in a dead region)", void 0, tm.s, lhs.def);
      }
      const a_wnf = term_wnf(book, t_wnf.A);
      if (a_wnf.$ !== "ADT") {
        throw Err(book, ctx, "a datatype", t_wnf.A, tm.s, lhs.def);
      }
      const rem = book_adt(book, a_wnf, ctx, lhs.def).c;
      switch (tm.$) {
        case "Efq": {
          if (rem.length !== 0 && !ctx_dead(book, ctx)) {
            throw Err(book, ctx, "cases for " + rem.map((c) => c.k).join(", "), tm, tm.s, lhs.def);
          }
          return Check(tm, ty, uses_nil());
        }
        case "Mat": {
          let term_check_mat_goal = function(cur, n, xs) {
            if (n === 0) {
              return t_all.B(Ctr(b.k, xs, b.s));
            } else {
              const c_all = tele_head(book, cur, ctx, lhs.def, b.s);
              const c_dem = c_all.q.$ === "None" ? None() : c_all.q.$ === "Lone" ? t_all.q : quant_add(t_all.q, t_all.q);
              return All(c_dem, c_all.k, c_all.i, c_all.A, (x) => {
                return term_check_mat_goal(c_all.B(x), n - 1, xs.concat([x]));
              }, b.s);
            }
          };
          const b = tm;
          const t_all = t_wnf;
          const ctr = rem.find((c) => c.k === tm.k);
          if (ctr === void 0) {
            throw Err(book, ctx, "a constructor of " + a_wnf.k + " (missing, or already matched)", tm, tm.s, lhs.def);
          }
          const tel = tele_fill(book, ctr.T, a_wnf.x, ctx, lhs.def, tm.s);
          let h_lhs = lhs;
          if (lhs.n > 0) {
            h_lhs = { ...lhs, t: lhs_ext(lhs.t, tm.k, ctr.n), n: lhs.n - 1 + ctr.n };
          }
          const h_chk = term_check(book, h_lhs, tm.h, qt, term_check_mat_goal(tel, ctr.n, []), ctx, d);
          const m_gol = All(t_wnf.q, t_wnf.k, t_wnf.i, ADT(a_wnf.k, a_wnf.x, tm.s, a_wnf.r.concat([ctr.k])), t_wnf.B, tm.s);
          const m_chk = term_check(book, lhs, tm.m, qt, m_gol, ctx, d);
          return Check(Mat(tm.k, h_chk.tm, m_chk.tm, tm.s), ty, pmap_union(h_chk.us, m_chk.us, quant_join));
        }
      }
    }
    // T == {a == b : A}    a == b
    // ---------------------------- check-rfl
    // Γ ⊢ {==} : T ~ {}
    case "Rfl": {
      const t_wnf = term_wnf(book, ty);
      if (t_wnf.$ !== "Eql") {
        throw Err(book, ctx, ty, "non-inferrable term", tm.s, lhs.def);
      }
      if (!term_compare("EQ", book, t_wnf.a, t_wnf.b, d)) {
        throw Err(book, ctx, t_wnf.a, t_wnf.b, tm.s, lhs.def);
      }
      return Check(tm, ty, uses_nil());
    }
    // T
    // ------------------- check-hol
    // Γ ⊢ ?TODO : T ~ {}
    case "Hol": {
      if (tm.k === "TODO") {
        return Check(tm, ty, uses_nil());
      }
      throw Err(book, ctx, ty, tm, tm.s, lhs.def);
    }
    // Γ ⊢ E : {a == b : A} ~ eu
    // Γ ⊢ P : @x:A -> @e:{a == x : A} -> Type    P(b, E) <= T
    // Γ ⊢ f : P(a, {==}) ~ fu
    // where P is dead; this is the J axiom: elimination
    //       specializes both the equation and its second endpoint
    // ------------------------------------------------------------ check-rwt
    // Γ ⊢ %e@E : P; f : T ~ eu + fu
    case "Rwt": {
      const e_inf = term_infer(book, lhs, tm.e, qt, ctx, d);
      const e_wnf = term_wnf(book, e_inf.ty);
      if (e_wnf.$ !== "Eql") {
        throw Err(book, ctx, "an equation {a == b : T}", e_inf.ty, tm.e.s ?? tm.s, lhs.def);
      }
      const p_typ = All(Lone(), "_", 0, e_wnf.T, (x) => All(Lone(), "e", 0, Eql(e_wnf.a, x, e_wnf.T), () => Typ(Qua(Lone())), tm.s), tm.s);
      const p_chk = term_check(book, lhs, tm.p, None(), p_typ, ctx, d);
      const b_gol = term_apply(term_apply(tm.p, e_wnf.b), tm.e);
      if (!term_compare("LE", book, b_gol, ty, d)) {
        throw Err(book, ctx, ty, b_gol, tm.s, lhs.def);
      }
      const a_gol = term_apply(term_apply(tm.p, e_wnf.a), Rfl(tm.s));
      const f_chk = term_check(book, lhs, tm.f, qt, a_gol, ctx, d);
      return Check(Rwt(e_inf.tm, p_chk.tm, f_chk.tm, tm.s), ty, uses_add(e_inf.us, f_chk.us));
    }
    // Γ ⊢ x : A ~ u    A <= T
    // ---------------------- check-any
    // Γ ⊢ x : T ~ u
    default: {
      break;
    }
  }
  const x_inf = term_infer(book, lhs, tm, qt, ctx, d);
  if (term_compare("LE", book, x_inf.ty, ty, d)) {
    return x_inf;
  }
  throw Err(book, ctx, ty, x_inf.ty, tm.s, lhs.def);
}
function def_check(book, k, def, z) {
  const qs = tele_unbind(book, def.T).doms.map((dom) => dom[0]);
  const gen = def.x === 0 ? book : { ...book, tlds: Object.create(book.tlds) };
  let [t, v, T] = [Ref(k), def.v, def.T];
  for (let j = 0; j < def.x; j++) {
    const h = tele_head(gen, T, ctx_nil(), k);
    const o = k + "~" + h.k;
    if (o in gen.tlds) {
      throw Err(book, ctx_nil(), "a fresh ~ binder name", h.k, h.s);
    }
    gen.tlds[o] = { $: "Def", n: 0, x: 0, T: h.A, v: null, b: true };
    t = App(t, Ref(o));
    v = term_apply(v, Ref(o));
    T = h.B(Ref(o));
  }
  return term_check(gen, { t, n: def.n - def.x, def: k, qs, u: def.u, z }, v, Lone(), T, ctx_nil(), 0).tm;
}
function def_inst(book, lhs, tm, def, sp, ctx, d) {
  const xs = sp.slice(0, def.x);
  if (xs.length < def.x) {
    throw Err(book, ctx, "a template applied to closed ~ arguments (a def parameter is not comptime)", tm, tm.s, lhs.def);
  }
  let T;
  try {
    T = tele_check(book, lhs, def.T, xs, None(), ctx_nil(), d, tm.s).tel;
  } catch (e) {
    const v = e?.obs;
    if (typeof v === "object" && v.$ === "Var" && v.i >= 0 && v.i < d) {
      throw Err(book, ctx, "a template applied to closed ~ arguments (" + v.k + " is a variable here, not comptime: pass it at run time)", tm, tm.s, lhs.def);
    }
    throw e;
  }
  const key2 = xs.map((a) => term_key(term_lower(a))).join("\n");
  if (key2.length > 32768) {
    throw Err(book, ctx, "a ~ argument that stops growing", tm, tm.s, lhs.def);
  }
  const is = book.tmps[tm.k] ??= /* @__PURE__ */ Object.create(null);
  if (is[key2] === void 0) {
    const z = (lhs.z ?? 0) + 1;
    if (z > 64) {
      throw Err(book, ctx, "a template that stops instantiating itself (64 levels at most)", tm, tm.s, lhs.def);
    }
    const o = is[key2] = tm.k + "~" + String(Object.keys(is).length);
    const inst = { $: "Def", n: def.n - def.x, x: 0, T, v: xs.reduce((v, a) => term_apply(v, a), def.v), u: def.u };
    book.tlds[o] = { ...inst, v: null };
    inst.e = def_check(book, o, inst, z);
    book.tlds[o] = inst;
  } else if (book.tlds[is[key2]].v === null && is[key2] !== lhs.def) {
    throw Err(book, ctx, "a decreasing self-call (arguments are read left to right: each passed unchanged until one shrinks)", tm, tm.s, lhs.def);
  }
  return is[key2];
}
function book_valid(book, done = 0) {
  const tlds = book.tlds;
  const last = /* @__PURE__ */ new Map();
  for (let i = 0; i < book.order.length; i++) {
    last.set(book.order[i], i);
  }
  book.tlds = /* @__PURE__ */ Object.create(null);
  for (const k in tlds) {
    const t = tlds[k];
    book.tlds[k] = last.has(k) && t.$ === "Def" ? { ...t, v: null } : t;
  }
  for (let i = 0; i < book.order.length; i++) {
    const k = book.order[i];
    const tld = tlds[k];
    const fin = last.get(k) === i;
    if (tld.$ === "ADT") {
      if (i >= done) {
        term_check(book, { t: Ref(k), n: 0, def: k, qs: [] }, tld.T, None(), Typ(Qua(Lone())), ctx_nil(), 0);
        const { doms, ret: kind } = tele_unbind(book, tld.T);
        if (kind.$ !== "Typ") {
          let ctx = ctx_nil();
          for (const [d, [q, x, A]] of doms.entries()) {
            ctx = ctx_bind(ctx, d, q, x, A);
          }
          throw Err(book, ctx, "a kind (type " + k + "<..> is Kind(g))", kind, kind.s ?? tld.T.s, k);
        }
        for (const ctr of tld.c) {
          let tel = ctr.T;
          let ctx = ctx_nil();
          for (let d = 0; d < tld.n + ctr.n; d++) {
            const t_all = tele_head(book, tel, ctx, ctr.k);
            let goal = Typ(Qua(t_all.q));
            if (d >= tld.n && t_all.q.$ === "Lone") {
              goal = kind;
            }
            term_check(book, { t: Ref(ctr.k), n: 0, def: ctr.k, qs: [] }, t_all.A, None(), goal, ctx, d);
            ctx = ctx_bind(ctx, d, t_all.q, t_all.k, t_all.A);
            tel = t_all.B(Var(t_all.k, d));
          }
          const exp = "a telescope tipped at " + k + " applied to its own parameters";
          const tip = term_wnf(book, tel);
          if (tip.$ !== "ADT" || tip.k !== k || tip.x.length !== tld.n || tip.r.length !== 0) {
            throw Err(book, ctx, exp, tip, void 0, ctr.k);
          }
          for (let d = 0; d < tld.n; d++) {
            const x = term_wnf(book, tip.x[d]);
            if (x.$ !== "Var" || x.i !== d) {
              throw Err(book, ctx, exp, tip, void 0, ctr.k);
            }
          }
        }
      }
      continue;
    }
    if (i >= done) {
      if (fin && tld.v === null && tld.b !== true && !tld.i) {
        book.hols += 1;
      }
      term_check(book, { t: Ref(k), n: 0, def: k, qs: [], u: tld.u }, tld.T, None(), Typ(Qua(Lone())), ctx_nil(), 0);
      if (tld.i) {
        let tel = term_strip(tld.T);
        for (let d = 0; tel.$ === "All"; d++) {
          tel = term_strip(tel.B(Var(tel.k, d)));
        }
        const [h] = term_unapply(tel);
        const io = book.tlds["IO"];
        if (h.$ !== "Ref" || h.k !== "IO" || io === void 0 || io.$ !== "Def" || io.b !== true) {
          throw Err(book, ctx_nil(), "a foreign definition returning base IO(...) directly (return type aliases are not unfolded)", k, tel.s, k);
        }
      }
      if (fin && tld.v !== null) {
        tld.e = def_check(book, k, tld);
      }
    }
    if (fin) {
      book.tlds[k] = tld;
    }
  }
}

// src/expression-parser.ts
var FlowParseError = class extends Error {
  constructor(message2, span) {
    super(message2);
    this.span = span;
    this.name = "FlowParseError";
  }
};
function tokenize(source, base) {
  const tokens = [];
  let index = 0;
  while (index < source.length) {
    const char = source[index];
    if (/\s/.test(char)) {
      index++;
      continue;
    }
    if (char === "#") break;
    if (/[A-Za-z_]/.test(char)) {
      const match = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(source.slice(index));
      tokens.push({ kind: "name", text: match[0], start: base + index, end: base + index + match[0].length });
      index += match[0].length;
      continue;
    }
    if (/[0-9]/.test(char)) {
      const match = /^(?:[0-9]+\.[0-9]+(?:[eE][+-]?[0-9]+)?|[0-9]+n?)/.exec(source.slice(index));
      tokens.push({ kind: "number", text: match[0], start: base + index, end: base + index + match[0].length });
      index += match[0].length;
      continue;
    }
    if (char === '"') {
      let end = index + 1;
      while (end < source.length && source[end] !== '"') {
        if (source[end] === "\\") end++;
        end++;
      }
      if (end >= source.length) throw new FlowParseError("Unterminated string literal", { start: base + index, end: base + source.length });
      end++;
      tokens.push({ kind: "string", text: source.slice(index, end), start: base + index, end: base + end });
      index = end;
      continue;
    }
    const pair = source.slice(index, index + 2);
    if (["->", "==", "=>"].includes(pair)) {
      tokens.push({ kind: "symbol", text: pair, start: base + index, end: base + index + 2 });
      index += 2;
      continue;
    }
    if ("(){}<>,:|+-~".includes(char)) {
      tokens.push({ kind: "symbol", text: char, start: base + index, end: base + index + 1 });
      index++;
      continue;
    }
    throw new FlowParseError(`Unexpected character '${char}'`, { start: base + index, end: base + index + 1 });
  }
  tokens.push({ kind: "eof", text: "", start: base + source.length, end: base + source.length });
  return tokens;
}
var ExpressionParser = class {
  tokens;
  index = 0;
  constructor(source, baseOffset = 0) {
    this.tokens = tokenize(source, baseOffset);
  }
  current() {
    return this.tokens[this.index];
  }
  peek(distance = 1) {
    return this.tokens[Math.min(this.index + distance, this.tokens.length - 1)];
  }
  take(text) {
    const token = this.current();
    if (text !== void 0 && token.text !== text) return null;
    this.index++;
    return token;
  }
  expect(text) {
    const token = this.take(text);
    if (!token) throw new FlowParseError(`Expected '${text}'`, { start: this.current().start, end: this.current().end });
    return token;
  }
  expectEnd() {
    if (this.current().kind !== "eof") {
      throw new FlowParseError(`Unexpected '${this.current().text}'`, { start: this.current().start, end: this.current().end });
    }
  }
  parse() {
    const expression = this.current().text === "|" ? this.parseUnion() : this.parseExpression();
    this.expectEnd();
    return expression;
  }
  parseExpression(minimumBindingPower = 0) {
    let left = this.parsePrimary();
    while (true) {
      if (this.current().text === "<") {
        const start = left.span.start;
        const arguments_ = this.parseDelimited("<", ">");
        left = { kind: "TypeApplicationExpression", callee: left, arguments: arguments_, span: { start, end: this.tokens[this.index - 1].end } };
        continue;
      }
      if (this.current().text === "(") {
        const start = left.span.start;
        const arguments_ = this.parseDelimited("(", ")");
        left = { kind: "CallExpression", callee: left, arguments: arguments_, span: { start, end: this.tokens[this.index - 1].end } };
        continue;
      }
      if (this.current().text === "{") {
        const start = left.span.start;
        const arguments_ = this.parseDelimited("{", "}");
        left = { kind: "ConstructorExpression", callee: left, arguments: arguments_, span: { start, end: this.tokens[this.index - 1].end } };
        continue;
      }
      const operator = this.current();
      const bindingPower = operator.text === "->" ? 1 : operator.text === "==" ? 2 : -1;
      if (bindingPower < minimumBindingPower) break;
      this.index++;
      const right = this.parseExpression(operator.text === "->" ? bindingPower : bindingPower + 1);
      left = operator.text === "->" ? { kind: "ArrowExpression", domain: left, codomain: right, span: { start: left.span.start, end: right.span.end } } : { kind: "EqualityExpression", left, right, span: { start: left.span.start, end: right.span.end } };
    }
    return left;
  }
  parseFields(open, close) {
    this.expect(open);
    const fields = [];
    while (this.current().text !== close) {
      if (this.current().kind === "eof") throw new FlowParseError(`Expected '${close}'`, { start: this.current().start, end: this.current().end });
      const start = this.current().start;
      const { quantity, span: quantitySpan } = this.parseQuantity();
      let name;
      if (this.current().kind === "name" && this.peek().text === ":") {
        const token = this.take();
        name = { kind: "Identifier", name: token.text, span: { start: token.start, end: token.end } };
        this.expect(":");
      }
      const type = this.parseExpression();
      fields.push({ kind: "Field", name, quantity, quantitySpan, type, span: { start, end: type.span.end } });
      if (!this.take(",")) break;
    }
    this.expect(close);
    return fields;
  }
  parseUnion() {
    const variants = [];
    while (this.take("|")) {
      variants.push(this.parseVariant());
    }
    if (variants.length === 0) throw new FlowParseError("Expected a union variant", { start: this.current().start, end: this.current().end });
    return { kind: "UnionExpression", variants, span: { start: variants[0].span.start, end: variants.at(-1).span.end } };
  }
  parseVariant() {
    const nameToken = this.current();
    if (nameToken.kind !== "name") throw new FlowParseError("Expected a constructor name", { start: nameToken.start, end: nameToken.end });
    this.index++;
    const name = { kind: "Identifier", name: nameToken.text, span: { start: nameToken.start, end: nameToken.end } };
    const fields = this.current().text === "{" ? this.parseFields("{", "}") : [];
    return { kind: "Variant", name, fields, span: { start: name.span.start, end: fields.at(-1)?.span.end ?? name.span.end } };
  }
  parseQuantity() {
    const token = this.current();
    const quantity = token.text === "+" ? "many" : token.text === "-" ? "none" : token.text === "~" ? "comptime" : void 0;
    if (!quantity) return { quantity: "lone" };
    this.index++;
    return { quantity, span: { start: token.start, end: token.end } };
  }
  parsePrimary() {
    const token = this.current();
    if (token.kind === "name") {
      this.index++;
      return { kind: "Identifier", name: token.text, span: { start: token.start, end: token.end } };
    }
    if (token.kind === "number") {
      this.index++;
      return { kind: "NumberExpression", value: token.text, span: { start: token.start, end: token.end } };
    }
    if (token.kind === "string") {
      this.index++;
      let value;
      try {
        value = JSON.parse(token.text);
      } catch {
        value = token.text.slice(1, -1);
      }
      return { kind: "StringExpression", value, raw: token.text, span: { start: token.start, end: token.end } };
    }
    if (this.take("{")) {
      const open = token;
      if (this.take("==")) {
        const close2 = this.expect("}");
        return { kind: "ReflexivityExpression", span: { start: open.start, end: close2.end } };
      }
      const value = this.parseExpression();
      this.expect(":");
      const type = this.parseExpression();
      const close = this.expect("}");
      if (value.kind === "EqualityExpression") {
        return { kind: "TypedEqualityExpression", left: value.left, right: value.right, type, span: { start: open.start, end: close.end } };
      }
      return { kind: "AnnotationExpression", value, type, span: { start: open.start, end: close.end } };
    }
    if (this.take("(")) {
      const open = token;
      const fields = [];
      while (this.current().text !== ")") {
        const start = this.current().start;
        const { quantity, span: quantitySpan } = this.parseQuantity();
        let name;
        if (this.current().kind === "name" && this.peek().text === ":") {
          const nameToken = this.take();
          name = { kind: "Identifier", name: nameToken.text, span: { start: nameToken.start, end: nameToken.end } };
          this.expect(":");
        }
        const type = this.parseExpression();
        fields.push({ kind: "Field", name, quantity, quantitySpan, type, span: { start, end: type.span.end } });
        if (!this.take(",")) break;
      }
      const close = this.expect(")");
      if (fields.length === 1 && !fields[0].name) return fields[0].type;
      return { kind: "TupleExpression", fields, span: { start: open.start, end: close.end } };
    }
    throw new FlowParseError("Expected an expression", { start: token.start, end: token.end });
  }
  parseDelimited(open, close) {
    this.expect(open);
    const values = [];
    while (this.current().text !== close) {
      values.push(this.parseExpression());
      if (!this.take(",")) break;
    }
    this.expect(close);
    return values;
  }
};
function expressionToPattern(expression) {
  if (expression.kind === "Identifier") {
    return { kind: "NamePattern", name: expression.name, span: expression.span };
  }
  if (expression.kind === "ConstructorExpression") {
    let callee = expression.callee;
    let typeArguments = [];
    if (callee.kind === "TypeApplicationExpression") {
      typeArguments = callee.arguments;
      callee = callee.callee;
    }
    if (callee.kind !== "Identifier") throw new FlowParseError("Expected a constructor name in pattern", expression.callee.span);
    return {
      kind: "ConstructorPattern",
      constructor: callee.name,
      typeArguments,
      fields: expression.arguments.map(expressionToPattern),
      span: expression.span
    };
  }
  throw new FlowParseError("Expected a name or constructor pattern", expression.span);
}

// src/parser.ts
function linesOf(source) {
  const result = [];
  let offset = 0;
  for (const [index, rawLine] of source.split("\n").entries()) {
    const raw = rawLine.endsWith("\r") ? rawLine.slice(0, -1) : rawLine;
    const whitespace = /^[ \t]*/.exec(raw)[0];
    if (whitespace.includes("	")) {
      throw new FlowParseError("Flow indentation must use spaces", { start: offset, end: offset + whitespace.length });
    }
    result.push({
      raw,
      content: raw.slice(whitespace.length),
      indent: whitespace.length,
      start: offset,
      end: offset + raw.length,
      number: index
    });
    offset += rawLine.length + 1;
  }
  return result;
}
function isTrivia(line) {
  const content = line.content.trim();
  return content === "" || content.startsWith("#");
}
function topLevelIndex(source, wanted) {
  let round = 0;
  let curly = 0;
  let angle = 0;
  let string = false;
  for (let index = 0; index < source.length; index++) {
    const char = source[index];
    if (string) {
      if (char === "\\") index++;
      else if (char === '"') string = false;
      continue;
    }
    if (char === '"') {
      string = true;
      continue;
    }
    if (char === "(") round++;
    else if (char === ")") round--;
    else if (char === "{") curly++;
    else if (char === "}") curly--;
    else if (char === "<") angle++;
    else if (char === ">" && source[index - 1] !== "-") angle--;
    else if (char === wanted && round === 0 && curly === 0 && angle === 0) {
      if (wanted === "=" && (source[index + 1] === "=" || source[index - 1] === "=" || source[index - 1] === ">")) continue;
      return index;
    }
  }
  return -1;
}
function matching(source, start, open, close) {
  let depth = 0;
  for (let index = start; index < source.length; index++) {
    if (source[index] === open) depth++;
    else if (source[index] === close && --depth === 0) return index;
  }
  return -1;
}
var FlowParser = class {
  constructor(source) {
    this.source = source;
    this.lines = linesOf(source);
  }
  lines;
  index = 0;
  parse() {
    const statements = this.parseBlockStatements(0);
    return { kind: "Program", statements, span: { start: 0, end: this.source.length } };
  }
  parseBlockStatements(indent2) {
    const statements = [];
    while (this.index < this.lines.length) {
      const line = this.lines[this.index];
      if (isTrivia(line)) {
        this.index++;
        continue;
      }
      if (line.indent < indent2) break;
      if (line.indent > indent2) {
        throw new FlowParseError(`Unexpected indentation on line ${line.number + 1}`, { start: line.start, end: line.start + line.indent });
      }
      statements.push(this.parseStatement(indent2));
    }
    return statements;
  }
  parseStatement(indent2) {
    const line = this.lines[this.index];
    if (/^import\b/.test(line.content)) return this.parseImport();
    if (/^(?:@unsafe\s+)?def\b|^law\b|^type\b/.test(line.content)) return this.parseRawBend(indent2);
    if (/^do\b/.test(line.content)) {
      const expression2 = this.parseDo(indent2);
      return { kind: "ExpressionStatement", expression: expression2, span: expression2.span };
    }
    if (/^match\b/.test(line.content)) {
      const expression2 = this.parseMatch(indent2);
      return { kind: "ExpressionStatement", expression: expression2, span: expression2.span };
    }
    if (topLevelIndex(line.content, "=") >= 0) return this.parseDeclaration(indent2);
    this.index++;
    const expression = this.parseExpression(line.content, line.start + line.indent);
    return { kind: "ExpressionStatement", expression, span: expression.span };
  }
  parseImport() {
    const line = this.lines[this.index++];
    const match = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(line.content);
    if (!match) throw new FlowParseError("Expected 'import Base' or 'import <path> as <Name>'", { start: line.start + line.indent, end: line.end });
    const pathStart = line.start + line.indent + line.content.indexOf(match[1]);
    const aliasStart = match[2] ? line.start + line.indent + line.content.lastIndexOf(match[2]) : 0;
    return {
      kind: "ImportStatement",
      path: match[1],
      alias: match[2] ? { kind: "Identifier", name: match[2], span: { start: aliasStart, end: aliasStart + match[2].length } } : void 0,
      pathSpan: { start: pathStart, end: pathStart + match[1].length },
      span: { start: line.start + line.indent, end: line.end }
    };
  }
  parseRawBend(indent2) {
    const first = this.index;
    this.index++;
    while (this.index < this.lines.length) {
      const line = this.lines[this.index];
      if (!isTrivia(line) && line.indent <= indent2) break;
      this.index++;
    }
    const start = this.lines[first].start;
    const end = this.index < this.lines.length ? this.lines[this.index].start : this.source.length;
    return { kind: "RawBendDefinition", source: this.source.slice(start, end).replace(/\n+$/, ""), span: { start, end } };
  }
  parseDeclaration(indent2) {
    const line = this.lines[this.index++];
    const equals = topLevelIndex(line.content, "=");
    const header = line.content.slice(0, equals).trimEnd();
    const inlineBody = line.content.slice(equals + 1).trim();
    const parsed = this.parseDeclarationHeader(header, line.start + line.indent);
    let body;
    if (inlineBody) {
      const bodyColumn = line.content.indexOf(inlineBody, equals + 1);
      body = this.parseExpression(inlineBody, line.start + line.indent + bodyColumn);
    } else {
      const childIndent = this.nextContentIndent();
      if (childIndent === null || childIndent <= indent2) {
        throw new FlowParseError(`Expected an indented body for '${parsed.name.name}'`, { start: line.end, end: line.end });
      }
      if (this.lines[this.index].content.trimStart().startsWith("|")) {
        body = this.parseMultilineUnion(childIndent);
      } else {
        const statements = this.parseBlockStatements(childIndent);
        body = {
          kind: "Block",
          statements,
          span: { start: statements[0]?.span.start ?? line.end, end: statements.at(-1)?.span.end ?? line.end }
        };
      }
    }
    return {
      kind: "Declaration",
      ...parsed,
      body,
      span: { start: line.start + line.indent, end: body.span.end }
    };
  }
  parseDeclarationHeader(header, base) {
    const marker = /^[+\-~]/.exec(header)?.[0];
    const quantity = marker === "+" ? "many" : marker === "-" ? "none" : marker === "~" ? "comptime" : "lone";
    const quantitySpan = marker ? { start: base, end: base + 1 } : void 0;
    const nameOffset = marker ? 1 : 0;
    const nameMatch = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(header.slice(nameOffset));
    if (!nameMatch) throw new FlowParseError("Expected a declaration name", { start: base + nameOffset, end: base + header.length });
    let cursor = nameOffset + nameMatch[0].length;
    const name = { kind: "Identifier", name: nameMatch[0], span: { start: base + nameOffset, end: base + cursor } };
    let typeParameters = [];
    let parameters = [];
    while (/\s/.test(header[cursor] ?? "")) cursor++;
    if (header[cursor] === "<") {
      const close = matching(header, cursor, "<", ">");
      if (close < 0) throw new FlowParseError("Expected '>'", { start: base + cursor, end: base + header.length });
      typeParameters = this.parseFieldText(header.slice(cursor, close + 1), base + cursor, "<", ">");
      cursor = close + 1;
    }
    while (/\s/.test(header[cursor] ?? "")) cursor++;
    if (header[cursor] === "(") {
      const close = matching(header, cursor, "(", ")");
      if (close < 0) throw new FlowParseError("Expected ')'", { start: base + cursor, end: base + header.length });
      parameters = this.parseFieldText(header.slice(cursor, close + 1), base + cursor, "(", ")");
      cursor = close + 1;
    }
    while (/\s/.test(header[cursor] ?? "")) cursor++;
    if (header[cursor] !== ":") throw new FlowParseError("Expected ':' before the declaration type", { start: base + cursor, end: base + cursor + 1 });
    cursor++;
    while (/\s/.test(header[cursor] ?? "")) cursor++;
    const returnSource = header.slice(cursor);
    if (!returnSource) throw new FlowParseError("Expected a declaration type", { start: base + cursor, end: base + cursor });
    const returnType = this.parseExpression(returnSource, base + cursor);
    return { name, quantity, quantitySpan, typeParameters, parameters, returnType };
  }
  parseFieldText(source, base, open, close) {
    const parser = new ExpressionParser(source, base);
    const fields = parser.parseFields(open, close);
    parser.expectEnd();
    return fields;
  }
  parseMultilineUnion(indent2) {
    const variants = [];
    while (this.index < this.lines.length) {
      const line = this.lines[this.index];
      if (isTrivia(line)) {
        this.index++;
        continue;
      }
      if (line.indent !== indent2 || !line.content.startsWith("|")) break;
      const expression = this.parseExpression(line.content, line.start + line.indent);
      if (expression.kind !== "UnionExpression") throw new FlowParseError("Expected a union variant", expression.span);
      variants.push(...expression.variants);
      this.index++;
    }
    if (!variants.length) throw new FlowParseError("Expected at least one union variant", { start: this.lines[this.index]?.start ?? this.source.length, end: this.lines[this.index]?.end ?? this.source.length });
    return { kind: "UnionExpression", variants, span: { start: variants[0].span.start, end: variants.at(-1).span.end } };
  }
  parseDo(indent2) {
    const line = this.lines[this.index++];
    const match = /^do\s+(.+):\s*(?:#.*)?$/.exec(line.content);
    if (!match) throw new FlowParseError("Expected 'do <effect>:'", { start: line.start + line.indent, end: line.end });
    const effectColumn = line.content.indexOf(match[1]);
    const effect = this.parseExpression(match[1], line.start + line.indent + effectColumn);
    const bodyIndent = this.nextContentIndent();
    if (bodyIndent === null || bodyIndent <= indent2) throw new FlowParseError("Expected an indented do body", { start: line.end, end: line.end });
    const statements = [];
    while (this.index < this.lines.length) {
      const bodyLine = this.lines[this.index];
      if (!isTrivia(bodyLine) && bodyLine.indent < bodyIndent) break;
      this.index++;
      if (!bodyLine.raw.trim()) continue;
      const start = bodyLine.start + Math.min(bodyIndent, bodyLine.raw.length);
      statements.push({ kind: "DoStatement", source: bodyLine.raw.slice(Math.min(bodyIndent, bodyLine.raw.length)), span: { start, end: bodyLine.end } });
    }
    if (!statements.length) throw new FlowParseError("A do block requires at least one statement", { start: line.end, end: line.end });
    return { kind: "DoExpression", effect, statements, span: { start: line.start + line.indent, end: statements.at(-1).span.end } };
  }
  parseMatch(indent2) {
    const line = this.lines[this.index++];
    const match = /^match\s+(.+):\s*(?:#.*)?$/.exec(line.content);
    if (!match) throw new FlowParseError("Expected 'match <expression>:'", { start: line.start + line.indent, end: line.end });
    const expressionColumn = line.content.indexOf(match[1]);
    const scrutinee = this.parseExpression(match[1], line.start + line.indent + expressionColumn);
    const caseIndent = this.nextContentIndent();
    if (caseIndent === null || caseIndent <= indent2) throw new FlowParseError("Expected indented match cases", { start: line.end, end: line.end });
    const cases = [];
    while (this.index < this.lines.length) {
      const caseLine = this.lines[this.index];
      if (isTrivia(caseLine)) {
        this.index++;
        continue;
      }
      if (caseLine.indent !== caseIndent || !caseLine.content.startsWith("|")) break;
      const arrow = topLevelIndex(caseLine.content, "=");
      if (arrow < 0 || caseLine.content[arrow + 1] !== ">") {
        throw new FlowParseError("Expected '| <pattern> => <body>'", { start: caseLine.start + caseLine.indent, end: caseLine.end });
      }
      const patternSource = caseLine.content.slice(1, arrow).trim();
      const patternColumn = caseLine.content.indexOf(patternSource);
      const pattern = expressionToPattern(this.parseExpression(patternSource, caseLine.start + caseLine.indent + patternColumn));
      const bodySource = caseLine.content.slice(arrow + 2).trim();
      this.index++;
      let body;
      if (bodySource) {
        const bodyColumn = caseLine.content.indexOf(bodySource, arrow + 2);
        body = this.parseExpression(bodySource, caseLine.start + caseLine.indent + bodyColumn);
      } else {
        const bodyIndent = this.nextContentIndent();
        if (bodyIndent === null || bodyIndent <= caseIndent) throw new FlowParseError("Expected an indented case body", { start: caseLine.end, end: caseLine.end });
        const statements = this.parseBlockStatements(bodyIndent);
        body = { kind: "Block", statements, span: { start: statements[0].span.start, end: statements.at(-1).span.end } };
      }
      cases.push({ kind: "MatchCase", pattern, body, span: { start: caseLine.start + caseLine.indent, end: body.span.end } });
    }
    if (!cases.length) throw new FlowParseError("A match requires at least one case", { start: line.end, end: line.end });
    return { kind: "MatchExpression", scrutinee, cases, span: { start: line.start + line.indent, end: cases.at(-1).span.end } };
  }
  parseExpression(source, base) {
    return new ExpressionParser(source, base).parse();
  }
  nextContentIndent() {
    while (this.index < this.lines.length && isTrivia(this.lines[this.index])) this.index++;
    return this.index < this.lines.length ? this.lines[this.index].indent : null;
  }
};
function parseFlow(source) {
  return new FlowParser(source).parse();
}

// src/lower.ts
var Writer = class {
  text = "";
  mappings = [];
  write(text, span) {
    const start = this.text.length;
    this.text += text;
    if (span && text.length) this.mappings.push({ generatedStart: start, generatedEnd: this.text.length, flowStart: span.start, flowEnd: span.end });
  }
  line(text = "", span) {
    this.write(text, span);
    this.write("\n");
  }
};
function append(output, snippet) {
  const offset = output.text.length;
  output.text += snippet.text;
  output.mappings.push(...snippet.mappings.map((mapping) => ({
    ...mapping,
    generatedStart: mapping.generatedStart + offset,
    generatedEnd: mapping.generatedEnd + offset
  })));
}
function indent(text, spaces = 2) {
  const prefix = " ".repeat(spaces);
  return text.split("\n").map((line) => line ? prefix + line : line).join("\n");
}
var FlowLowerer = class {
  constructor(program) {
    this.program = program;
  }
  imports = [];
  hoisted = [];
  regular = [];
  global = /* @__PURE__ */ new Map();
  hasBaseImport = false;
  lower() {
    for (const statement of this.program.statements) this.lowerTopStatement(statement);
    const output = new Writer();
    if (this.hasBaseImport) output.line("import Base");
    for (const imported of this.imports) append(output, imported);
    if (this.hasBaseImport || this.imports.length) output.line();
    for (const snippet of [...this.hoisted, ...this.regular]) {
      append(output, snippet);
      if (!output.text.endsWith("\n\n")) output.line();
    }
    return { bend: output.text, mappings: output.mappings, program: this.program };
  }
  lowerTopStatement(statement) {
    if (statement.kind === "ImportStatement") {
      if (statement.path === "Base") {
        this.hasBaseImport = true;
        return;
      }
      const writer2 = new Writer();
      const importedPath = statement.path.endsWith(".flow") ? statement.path.slice(0, -5) + ".bend" : statement.path;
      writer2.write("import ");
      writer2.write(importedPath, statement.pathSpan);
      if (statement.alias) {
        writer2.write(" as ");
        writer2.write(statement.alias.name, statement.alias.span);
      }
      writer2.line();
      this.imports.push({ text: writer2.text, mappings: writer2.mappings });
      return;
    }
    if (statement.kind === "RawBendDefinition") {
      const found = /^\s*(?:@unsafe\s+)?(?:def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/m.exec(statement.source);
      if (found) {
        const kind = /^\s*type\b/.test(statement.source) ? "type" : "function";
        this.global.set(found[1], { kind, target: found[1], span: statement.span });
      }
      const writer2 = new Writer();
      writer2.line(statement.source, statement.span);
      this.regular.push({ text: writer2.text, mappings: writer2.mappings });
      return;
    }
    if (statement.kind === "Declaration") {
      this.lowerDeclaration(statement, statement.name.name, this.global, false);
      return;
    }
    const type = this.expressionType(statement.expression, this.global) ?? "Type";
    const writer = new Writer();
    writer.line(`def main() -> ${type}:`, statement.span);
    writer.line("  " + this.renderExpression(statement.expression, this.global), statement.expression.span);
    this.regular.push({ text: writer.text, mappings: writer.mappings });
  }
  lowerDeclaration(node, target, outer, nested) {
    const typeDeclaration = node.body.kind === "UnionExpression" || node.body.kind === "TupleExpression";
    const kind = typeDeclaration ? "type" : node.parameters.length ? "function" : "value";
    outer.set(node.name.name, { kind, target, span: node.name.span, type: node.returnType });
    const scope = new Map(outer);
    this.bindFields(node.typeParameters, scope);
    this.bindFields(node.parameters, scope);
    const snippet = typeDeclaration ? this.lowerTypeDeclaration(node, target, scope, outer) : this.lowerValueDeclaration(node, target, scope);
    (nested ? this.hoisted : this.regular).push(snippet);
  }
  lowerTypeDeclaration(node, target, scope, outer) {
    const writer = new Writer();
    const parameters = this.renderTypeParameters(node.typeParameters, scope);
    writer.write("type ");
    writer.write(target, node.name.span);
    writer.write(parameters);
    writer.write(" is ");
    writer.write(this.renderExpression(node.returnType, scope), node.returnType.span);
    writer.line(":");
    if (node.body.kind === "UnionExpression") {
      for (const variant of node.body.variants) {
        const constructor = target.includes(".") ? `${target}.${variant.name.name}` : variant.name.name;
        outer.set(variant.name.name, { kind: "constructor", target: constructor, owner: target, span: variant.name.span });
        scope.set(variant.name.name, { kind: "constructor", target: constructor, owner: target, span: variant.name.span });
        writer.write("  ");
        writer.write(constructor, variant.name.span);
        writer.write("{");
        const fieldScope = new Map(scope);
        variant.fields.forEach((field, index) => {
          if (index) writer.write(", ");
          const name = field.name?.name ?? `field${index}`;
          writer.write(this.quantityMarker(field.quantity), field.quantitySpan);
          writer.write(name, field.name?.span ?? field.span);
          writer.write(": ");
          writer.write(this.renderType(field.type, fieldScope), field.type.span);
          if (field.name) fieldScope.set(field.name.name, { kind: "binding", target: field.name.name, span: field.name.span, type: field.type });
        });
        writer.line("}");
      }
    } else if (node.body.kind === "TupleExpression") {
      const constructor = `${target}.mk`;
      outer.set(`${node.name.name}.mk`, { kind: "constructor", target: constructor, owner: target, span: node.name.span });
      writer.write("  ");
      writer.write(constructor, node.name.span);
      writer.write("{");
      const fieldScope = new Map(scope);
      node.body.fields.forEach((field, index) => {
        if (index) writer.write(", ");
        const name = field.name?.name ?? (field.type.kind === "EqualityExpression" ? "proof" : `field${index}`);
        writer.write(this.quantityMarker(field.quantity), field.quantitySpan);
        writer.write(name, field.name?.span ?? field.span);
        writer.write(": ");
        writer.write(this.renderType(field.type, fieldScope), field.type.span);
        if (field.name) fieldScope.set(field.name.name, { kind: "binding", target: field.name.name, span: field.name.span, type: field.type });
      });
      writer.line("}");
    }
    return { text: writer.text, mappings: writer.mappings };
  }
  lowerValueDeclaration(node, target, scope) {
    const writer = new Writer();
    writer.write("def ");
    writer.write(target, node.name.span);
    writer.write("(");
    node.parameters.forEach((field, index) => {
      if (index) writer.write(", ");
      writer.write(this.quantityMarker(field.quantity), field.quantitySpan);
      writer.write(field.name?.name ?? `arg${index}`, field.name?.span ?? field.span);
      writer.write(": ");
      writer.write(this.renderType(field.type, scope), field.type.span);
    });
    writer.write(") -> ");
    writer.write(this.renderType(node.returnType, scope), node.returnType.span);
    writer.line(":");
    if (node.body.kind === "Block") {
      const body = this.renderBlock(node.body, scope, target);
      writer.write(indent(body.text), node.body.span);
      if (!writer.text.endsWith("\n")) writer.line();
    } else {
      writer.line("  " + this.renderExpression(node.body, scope), node.body.span);
    }
    return { text: writer.text, mappings: writer.mappings };
  }
  renderBlock(block, parent, owner) {
    const writer = new Writer();
    const scope = new Map(parent);
    for (const statement of block.statements) {
      if (statement.kind === "ImportStatement") {
        throw new Error("Flow imports must be at the top level");
      } else if (statement.kind === "RawBendDefinition") {
        writer.line(statement.source, statement.span);
      } else if (statement.kind === "ExpressionStatement") {
        writer.line(this.renderExpression(statement.expression, scope), statement.span);
      } else {
        const needsLift = statement.parameters.length > 0 || statement.body.kind === "UnionExpression" || statement.body.kind === "TupleExpression";
        if (needsLift) {
          const target = `${owner}.${statement.name.name}`;
          this.lowerDeclaration(statement, target, scope, true);
        } else {
          scope.set(statement.name.name, { kind: "binding", target: statement.name.name, span: statement.name.span, type: statement.returnType, quantity: statement.quantity });
          writer.write(this.quantityMarker(statement.quantity), statement.quantitySpan);
          writer.write(statement.name.name, statement.name.span);
          writer.write(": ");
          writer.write(this.renderType(statement.returnType, scope), statement.returnType.span);
          writer.write(" = ");
          if (statement.body.kind === "Block") {
            const helper = `${owner}.${statement.name.name}`;
            const free = this.freeBlockNames(statement.body);
            const captures = [...scope.entries()].filter(([name, symbol]) => name !== statement.name.name && free.has(name) && symbol.kind === "binding" && symbol.type);
            const lifted = new Writer();
            lifted.write("def ");
            lifted.write(helper, statement.name.span);
            lifted.write("(");
            captures.forEach(([name, symbol], index) => {
              if (index) lifted.write(", ");
              lifted.write(this.quantityMarker(symbol.quantity ?? "lone"));
              lifted.write(name, symbol.span);
              lifted.write(": ");
              lifted.write(this.renderType(symbol.type, scope), symbol.type?.span);
            });
            lifted.write(") -> ");
            lifted.write(this.renderType(statement.returnType, scope), statement.returnType.span);
            lifted.line(":");
            const nested = this.renderBlock(statement.body, scope, helper);
            lifted.write(indent(nested.text), statement.body.span);
            if (!lifted.text.endsWith("\n")) lifted.line();
            this.hoisted.push({ text: lifted.text, mappings: lifted.mappings });
            writer.line(`${helper}(${captures.map(([name]) => name).join(", ")})`, statement.body.span);
          } else {
            writer.line(this.renderExpression(statement.body, scope), statement.body.span);
          }
        }
      }
    }
    return { text: writer.text, mappings: writer.mappings };
  }
  renderExpression(node, scope) {
    switch (node.kind) {
      case "Identifier": {
        const symbol = scope.get(node.name);
        if (!symbol) return node.name;
        if (symbol.kind === "value") return `${symbol.target}()`;
        if (symbol.kind === "constructor") return `${symbol.target}{}`;
        return symbol.target;
      }
      case "NumberExpression":
        return node.value;
      case "StringExpression":
        return node.raw;
      case "ArrowExpression":
        return `${this.renderExpression(node.domain, scope)} -> ${this.renderExpression(node.codomain, scope)}`;
      case "EqualityExpression": {
        const type = this.inferEqualityType(node.left, node.right, scope);
        return `{${this.renderExpression(node.left, scope)} == ${this.renderExpression(node.right, scope)} : ${type}}`;
      }
      case "TypedEqualityExpression":
        return `{${this.renderExpression(node.left, scope)} == ${this.renderExpression(node.right, scope)} : ${this.renderType(node.type, scope)}}`;
      case "ReflexivityExpression":
        return "{==}";
      case "AnnotationExpression":
        return `{${this.renderExpression(node.value, scope)} : ${this.renderType(node.type, scope)}}`;
      case "CallExpression":
        return `${this.renderExpression(node.callee, scope)}(${node.arguments.map((item) => this.renderExpression(item, scope)).join(", ")})`;
      case "TypeApplicationExpression":
        return `${this.renderExpression(node.callee, scope)}<${node.arguments.map((item) => this.renderType(item, scope)).join(", ")}>`;
      case "ConstructorExpression": {
        let callee = node.callee;
        let typeArguments = [];
        if (callee.kind === "TypeApplicationExpression") {
          typeArguments = callee.arguments;
          callee = callee.callee;
        }
        const renderedCallee = this.renderExpression(callee, scope).replace(/\{\}$/, "");
        const value = `${renderedCallee}{${node.arguments.map((item) => this.renderExpression(item, scope)).join(", ")}}`;
        if (typeArguments.length && callee.kind === "Identifier") {
          const symbol = scope.get(callee.name);
          if (symbol?.owner) return `{${value} : ${symbol.owner}<${typeArguments.map((item) => this.renderType(item, scope)).join(", ")}>}`;
        }
        return value;
      }
      case "TupleExpression":
        return `(${node.fields.map((field) => this.renderType(field.type, scope)).join(", ")})`;
      case "UnionExpression":
        throw new Error("An inline union must be lifted before expression rendering");
      case "MatchExpression": {
        const lines = [`match ${this.renderExpression(node.scrutinee, scope)}:`];
        for (const item of node.cases) lines.push(...this.renderCase(item, scope).split("\n").map((line) => "  " + line));
        return lines.join("\n");
      }
      case "DoExpression":
        return [`do ${this.renderExpression(node.effect, scope)}:`, ...node.statements.map((statement) => "  " + statement.source)].join("\n");
    }
  }
  renderCase(item, parent) {
    const scope = new Map(parent);
    const pattern = this.renderPattern(item.pattern, scope);
    const body = item.body.kind === "Block" ? this.renderBlock(item.body, scope, "case").text : this.renderExpression(item.body, scope);
    return `case ${pattern}:
${indent(body)}`;
  }
  renderPattern(node, scope) {
    if (node.kind === "NamePattern") {
      if (node.name === "_") return "_";
      const symbol2 = scope.get(node.name);
      if (symbol2?.kind === "constructor") return `${symbol2.target}{}`;
      scope.set(node.name, { kind: "binding", target: node.name, span: node.span });
      return node.name;
    }
    const symbol = scope.get(node.constructor);
    const constructor = symbol?.kind === "constructor" ? symbol.target : node.constructor;
    return `${constructor}{${node.fields.map((field) => this.renderPattern(field, scope)).join(", ")}}`;
  }
  renderType(node, scope) {
    return this.renderExpression(node, scope);
  }
  renderTypeParameters(fields, scope) {
    if (!fields.length) return "";
    return `<${fields.map((field, index) => `${this.quantityMarker(field.quantity)}${field.name?.name ?? `T${index}`}: ${this.renderType(field.type, scope)}`).join(", ")}>`;
  }
  freeBlockNames(block) {
    const names = /* @__PURE__ */ new Set();
    const visit = (node, bound = /* @__PURE__ */ new Set()) => {
      switch (node.kind) {
        case "Identifier":
          if (!bound.has(node.name)) names.add(node.name);
          return;
        case "NumberExpression":
        case "StringExpression":
          return;
        case "ArrowExpression":
          visit(node.domain, bound);
          visit(node.codomain, bound);
          return;
        case "EqualityExpression":
          visit(node.left, bound);
          visit(node.right, bound);
          return;
        case "TypedEqualityExpression":
          visit(node.left, bound);
          visit(node.right, bound);
          visit(node.type, bound);
          return;
        case "AnnotationExpression":
          visit(node.value, bound);
          visit(node.type, bound);
          return;
        case "ReflexivityExpression":
          return;
        case "CallExpression":
        case "TypeApplicationExpression":
        case "ConstructorExpression":
          visit(node.callee, bound);
          node.arguments.forEach((item) => visit(item, bound));
          return;
        case "TupleExpression":
          node.fields.forEach((field) => visit(field.type, bound));
          return;
        case "UnionExpression":
          node.variants.forEach((variant) => variant.fields.forEach((field) => visit(field.type, bound)));
          return;
        case "MatchExpression":
          visit(node.scrutinee, bound);
          for (const item of node.cases) {
            const inner = new Set(bound);
            const bindPattern = (pattern) => {
              if (pattern.kind === "NamePattern") {
                if (pattern.name !== "_") inner.add(pattern.name);
              } else pattern.fields.forEach(bindPattern);
            };
            bindPattern(item.pattern);
            if (item.body.kind === "Block") visitBlock(item.body, inner);
            else visit(item.body, inner);
          }
          return;
        case "DoExpression":
          visit(node.effect, bound);
          for (const statement of node.statements) {
            for (const match of statement.source.matchAll(/[A-Za-z_][A-Za-z0-9_.]*/g)) if (!bound.has(match[0])) names.add(match[0]);
          }
          return;
      }
    };
    const visitBlock = (value, inherited = /* @__PURE__ */ new Set()) => {
      const bound = new Set(inherited);
      for (const statement of value.statements) {
        if (statement.kind === "ExpressionStatement") visit(statement.expression, bound);
        else if (statement.kind === "Declaration") {
          statement.typeParameters.forEach((field) => visit(field.type, bound));
          statement.parameters.forEach((field) => visit(field.type, bound));
          visit(statement.returnType, bound);
          if (statement.body.kind === "Block") visitBlock(statement.body, bound);
          else visit(statement.body, bound);
          bound.add(statement.name.name);
        }
      }
    };
    visitBlock(block);
    return names;
  }
  quantityMarker(quantity) {
    return quantity === "many" ? "+" : quantity === "none" ? "-" : quantity === "comptime" ? "~" : "";
  }
  bindFields(fields, scope) {
    for (const field of fields) if (field.name) scope.set(field.name.name, { kind: "binding", target: field.name.name, span: field.name.span, type: field.type, quantity: field.quantity });
  }
  inferEqualityType(left, right, scope) {
    for (const side of [left, right]) {
      if (side.kind === "Identifier") {
        const type = scope.get(side.name)?.type;
        if (type) return this.renderType(type, scope);
      }
      if (side.kind === "NumberExpression") return side.value.endsWith("n") ? "Nat" : side.value.includes(".") ? "F32" : "U32";
      if (side.kind === "StringExpression") return "String";
    }
    return "Type";
  }
  expressionType(node, scope) {
    if (node.kind === "Identifier") {
      const type = scope.get(node.name)?.type;
      return type ? this.renderType(type, scope) : null;
    }
    if (node.kind === "StringExpression") return "String";
    if (node.kind === "NumberExpression") return node.value.endsWith("n") ? "Nat" : node.value.includes(".") ? "F32" : "U32";
    return null;
  }
};
function lowerFlow(source) {
  return new FlowLowerer(parseFlow(source)).lower();
}
function originalFlowSpan(lowered, generatedOffset) {
  const containing = lowered.mappings.filter((mapping) => mapping.generatedStart <= generatedOffset && generatedOffset <= mapping.generatedEnd).sort((left, right) => left.generatedEnd - left.generatedStart - (right.generatedEnd - right.generatedStart))[0];
  if (containing) return { start: containing.flowStart, end: containing.flowEnd };
  const nearest = lowered.mappings.slice().sort((left, right) => Math.abs(left.generatedStart - generatedOffset) - Math.abs(right.generatedStart - generatedOffset))[0];
  return nearest ? { start: nearest.flowStart, end: nearest.flowEnd } : null;
}

// src/navigation.ts
function childScope(scope) {
  return new Map(scope);
}
function definition(span) {
  return { start: span.start, end: span.end };
}
var NavigationBuilder = class {
  occurrences = [];
  build(program) {
    this.visitStatements(program.statements, /* @__PURE__ */ new Map());
    return this.occurrences;
  }
  bind(scope, name, span, kind) {
    const target = definition(span);
    scope.set(name, { kind, definition: target });
    this.occurrences.push({ ...span, definition: target });
  }
  reference(scope, name, span) {
    const symbol = scope.get(name);
    if (symbol) this.occurrences.push({ ...span, definition: symbol.definition });
  }
  visitStatements(statements, scope) {
    for (const statement of statements) this.visitStatement(statement, scope);
  }
  visitStatement(statement, scope) {
    switch (statement.kind) {
      case "ImportStatement":
        if (statement.alias) this.bind(scope, statement.alias.name, statement.alias.span, "declaration");
        return;
      case "Declaration":
        this.visitDeclaration(statement, scope);
        return;
      case "ExpressionStatement":
        this.visitExpression(statement.expression, scope);
        return;
      case "RawBendDefinition": {
        const declaration = /^\s*(?:@unsafe\s+)?(?:def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/m.exec(statement.source);
        if (declaration) {
          const start = statement.span.start + declaration.index + declaration[0].lastIndexOf(declaration[1]);
          this.bind(scope, declaration[1], { start, end: start + declaration[1].length }, "declaration");
        }
      }
    }
  }
  visitDeclaration(node, outer) {
    this.bind(outer, node.name.name, node.name.span, "declaration");
    const scope = childScope(outer);
    this.visitFields(node.typeParameters, scope, true);
    this.visitFields(node.parameters, scope, true);
    this.visitExpression(node.returnType, scope);
    this.visitBody(node.body, scope);
    if (node.body.kind === "UnionExpression") {
      for (const variant of node.body.variants) this.bind(outer, variant.name.name, variant.name.span, "constructor");
    }
  }
  visitFields(fields, scope, bindNames) {
    for (const field of fields) {
      this.visitExpression(field.type, scope);
      if (bindNames && field.name) this.bind(scope, field.name.name, field.name.span, "binding");
    }
  }
  visitBody(body, scope) {
    if (body.kind === "Block") this.visitStatements(body.statements, childScope(scope));
    else this.visitExpression(body, scope);
  }
  visitExpression(node, scope) {
    switch (node.kind) {
      case "Identifier":
        this.reference(scope, node.name, node.span);
        return;
      case "NumberExpression":
      case "StringExpression":
        return;
      case "ArrowExpression":
        this.visitExpression(node.domain, scope);
        this.visitExpression(node.codomain, scope);
        return;
      case "EqualityExpression":
        this.visitExpression(node.left, scope);
        this.visitExpression(node.right, scope);
        return;
      case "TypedEqualityExpression":
        this.visitExpression(node.left, scope);
        this.visitExpression(node.right, scope);
        this.visitExpression(node.type, scope);
        return;
      case "AnnotationExpression":
        this.visitExpression(node.value, scope);
        this.visitExpression(node.type, scope);
        return;
      case "ReflexivityExpression":
        return;
      case "CallExpression":
      case "TypeApplicationExpression":
      case "ConstructorExpression":
        this.visitExpression(node.callee, scope);
        node.arguments.forEach((argument) => this.visitExpression(argument, scope));
        return;
      case "TupleExpression": {
        const tupleScope = childScope(scope);
        this.visitFields(node.fields, tupleScope, true);
        return;
      }
      case "UnionExpression":
        this.visitUnion(node, scope);
        return;
      case "MatchExpression":
        this.visitExpression(node.scrutinee, scope);
        node.cases.forEach((item) => this.visitCase(item, scope));
        return;
      case "DoExpression": {
        this.visitExpression(node.effect, scope);
        const doScope = childScope(scope);
        for (const statement of node.statements) {
          const binding = /^([A-Za-z_]\w*)\s*(?::[^<=>]+)?\s*(?:<-|=(?!=))/.exec(statement.source);
          for (const match of statement.source.matchAll(/[A-Za-z_][A-Za-z0-9_.]*/g)) {
            if (binding && match.index === binding.index) continue;
            this.reference(doScope, match[0], { start: statement.span.start + match.index, end: statement.span.start + match.index + match[0].length });
          }
          if (binding) {
            const start = statement.span.start + binding.index;
            this.bind(doScope, binding[1], { start, end: start + binding[1].length }, "binding");
          }
        }
        return;
      }
    }
  }
  visitUnion(node, scope) {
    for (const variant of node.variants) {
      const fieldScope = childScope(scope);
      this.visitFields(variant.fields, fieldScope, true);
    }
  }
  visitCase(node, outer) {
    const scope = childScope(outer);
    this.visitPattern(node.pattern, scope);
    this.visitBody(node.body, scope);
  }
  visitPattern(node, scope) {
    if (node.kind === "ConstructorPattern") {
      this.reference(scope, node.constructor, this.constructorNameSpan(node.span, node.constructor));
      node.typeArguments.forEach((argument) => this.visitExpression(argument, scope));
      node.fields.forEach((field) => this.visitPattern(field, scope));
      return;
    }
    if (node.name === "_") return;
    const existing = scope.get(node.name);
    if (existing?.kind === "constructor") this.reference(scope, node.name, node.span);
    else this.bind(scope, node.name, node.span, "binding");
  }
  constructorNameSpan(span, name) {
    return { start: span.start, end: Math.min(span.end, span.start + name.length) };
  }
};
function flowOccurrences(program) {
  return new NavigationBuilder().build(program);
}

// src/checker-core.ts
function message(error) {
  return err_show(error).replace(/\nLocation:[\s\S]*$/, "").trim();
}
function key(file) {
  const value = path2.resolve(file).replaceAll("\\", "/");
  return process.platform === "win32" ? value.toLowerCase() : value;
}
function mirrorPath(file, root, extension) {
  const absolute = path2.resolve(file);
  const parsed = path2.parse(absolute);
  const volume = parsed.root.replace(/[^A-Za-z0-9]/g, "") || "root";
  const relative = absolute.slice(parsed.root.length);
  const mirrored = path2.join(root, volume, relative);
  return extension ? mirrored.replace(/\.[^.\/]+$/, extension) : mirrored;
}
function compilerSource(text) {
  const lines = text.split("\n");
  for (let index = 0; index < lines.length; index++) {
    const value = lines[index].trim();
    if (!value || value.startsWith("#")) continue;
    if (/^import(?:\s|$)/.test(value)) lines[index] = "";
    else break;
  }
  return lines.join("\n");
}
function compilerOffset(text, compilerText, offset) {
  if (text === compilerText) return offset;
  const before = compilerText.slice(0, offset);
  const line = before.split("\n").length - 1;
  const column = offset - before.lastIndexOf("\n") - 1;
  const lines = text.split("\n");
  let result = 0;
  for (let index = 0; index < line; index++) result += (lines[index]?.length ?? 0) + 1;
  return result + column;
}
function renderFlowTypedHovers(source, program) {
  const declarations = /* @__PURE__ */ new Map();
  const visitStatements = (statements, depth) => {
    for (const statement of statements) if (statement.kind === "Declaration") visitDeclaration(statement, depth);
  };
  const visitDeclaration = (node, depth) => {
    if (depth > 0 && node.parameters.length === 0 && node.body.kind !== "UnionExpression" && node.body.kind !== "TupleExpression") {
      declarations.set(node.name.span.start, { name: node.name.name, type: node.returnType });
    }
    for (const field of [...node.typeParameters, ...node.parameters]) {
      if (field.name) declarations.set(field.name.span.start, { name: field.name.name, type: field.type });
    }
    if (node.body.kind === "Block") visitStatements(node.body.statements, depth + 1);
    else if (node.body.kind === "MatchExpression") {
      for (const item of node.body.cases) if (item.body.kind === "Block") visitStatements(item.body.statements, depth + 1);
    }
  };
  visitStatements(program.statements, 0);
  return flowOccurrences(program).flatMap((occurrence) => {
    const declared = declarations.get(occurrence.definition.start);
    if (!declared) return [];
    const type = source.slice(declared.type.span.start, declared.type.span.end);
    return [{ start: occurrence.start, end: occurrence.end, value: `\`\`\`bend
${declared.name} : ${type}
\`\`\`` }];
  });
}
function renderHovers(book) {
  const hovers = /* @__PURE__ */ Object.create(null);
  const add = (name, kind, term) => {
    try {
      const signature = term_show(term_lower(term));
      const value = `**${kind} ${name}**

\`\`\`bend
${name} : ${signature}
\`\`\``;
      hovers[name] = value;
      const leaf = name.split(".").at(-1);
      if (!(leaf in hovers)) hovers[leaf] = value;
    } catch {
    }
  };
  for (const [name, tld] of Object.entries(book.tlds)) add(name, tld.$ === "ADT" ? "type" : "def", tld.T);
  for (const [name, constructor] of Object.entries(book.ctrs)) add(name, "constructor", constructor.T);
  return hovers;
}
function localFlowImports(program) {
  return program.statements.filter((item) => item.kind === "ImportStatement" && item.path !== "Base");
}
function bendImports(text) {
  const result = [];
  for (const line of text.split("\n")) {
    const value = line.trim();
    if (!value || value.startsWith("#")) continue;
    const match = /^import\s+(\S+)(?:\s+as\s+[A-Za-z_]\w*)?/.exec(value);
    if (!match) break;
    if (match[1] !== "Base") result.push(match[1]);
  }
  return result;
}
function isHub(imported) {
  return /^0x[0-9a-f]+\//.test(imported) || /^[^/]+@[^/]+\//.test(imported);
}
function stageProject(request, root) {
  const overlays = new Map(request.overlays.map((item) => [key(item.path), item]));
  overlays.set(key(request.path), { path: request.path, uri: request.uri, text: request.text, version: request.version });
  const flows = [];
  const bends = [];
  const seen = /* @__PURE__ */ new Set();
  const stageBend = (file) => {
    const id = `bend:${key(file)}`;
    if (seen.has(id) || !fs2.existsSync(file)) return;
    seen.add(id);
    const text = fs2.readFileSync(file, "utf8");
    const staged = mirrorPath(file, root);
    fs2.mkdirSync(path2.dirname(staged), { recursive: true });
    fs2.writeFileSync(staged, text);
    bends.push({ original: path2.resolve(file), staged, uri: pathToFileURL(file).href, text });
    for (const imported of bendImports(text)) if (!isHub(imported)) stageBend(path2.resolve(path2.dirname(file), imported));
  };
  const stageFlow = (file) => {
    const id = `flow:${key(file)}`;
    if (seen.has(id)) return;
    const overlay = overlays.get(key(file));
    if (!overlay && !fs2.existsSync(file)) return;
    seen.add(id);
    const text = overlay?.text ?? fs2.readFileSync(file, "utf8");
    const lowered = lowerFlow(text);
    const staged = mirrorPath(file, root, ".bend");
    fs2.mkdirSync(path2.dirname(staged), { recursive: true });
    fs2.writeFileSync(staged, lowered.bend);
    flows.push({ original: path2.resolve(file), staged, uri: overlay?.uri ?? pathToFileURL(file).href, text, lowered });
    for (const imported of localFlowImports(lowered.program)) {
      if (isHub(imported.path)) continue;
      const child = path2.resolve(path2.dirname(file), imported.path);
      if (imported.path.endsWith(".flow")) stageFlow(child);
      else if (imported.path.endsWith(".bend")) stageBend(child);
    }
  };
  stageFlow(request.path);
  return { entry: mirrorPath(request.path, root, ".bend"), flows, bends };
}
async function checkFlow(request) {
  const directory = fs2.mkdtempSync(path2.join(os2.tmpdir(), "flow-check-"));
  let diagnostics = [];
  let hovers = {};
  let typedHovers = [];
  try {
    const staged = stageProject(request, directory);
    const root = staged.flows.find((item) => key(item.original) === key(request.path));
    if (!root) throw new Error(`Unable to read ${request.path}`);
    typedHovers = renderFlowTypedHovers(root.text, root.lowered.program);
    const book = book_nil();
    let checking = false;
    try {
      await book_load(book, staged.entry.replaceAll("\\", "/"), "", /* @__PURE__ */ new Map());
      checking = true;
      book_valid(book);
      if (book.hols > 0) {
        for (const source of staged.flows) {
          const hole = /\?[A-Za-z_][A-Za-z0-9_]*/.exec(source.text);
          if (hole) {
            diagnostics = [{ uri: source.uri, start: hole.index, end: hole.index + hole[0].length, message: `Unresolved hole '${hole[0]}'.`, code: "holes" }];
            break;
          }
        }
      }
    } catch (caught) {
      const candidate = caught;
      if (candidate.$ === "Err" && candidate.bok && candidate.ctx && candidate.exp !== void 0) {
        const error = candidate;
        const flow = staged.flows.find((item) => compilerSource(item.lowered.bend) === error.spn?.src || item.lowered.bend === error.spn?.src);
        if (flow) {
          const generatedOffset = compilerOffset(flow.lowered.bend, error.spn?.src ?? flow.lowered.bend, error.spn?.beg ?? 0);
          const original = originalFlowSpan(flow.lowered, generatedOffset) ?? { start: 0, end: 1 };
          diagnostics = [{ uri: flow.uri, start: original.start, end: Math.max(original.end, original.start + 1), message: message(error), code: checking ? "checking" : "bend-parsing" }];
        } else {
          const bend = staged.bends.find((item) => compilerSource(item.text) === error.spn?.src || item.text === error.spn?.src);
          diagnostics = [{ uri: bend?.uri ?? request.uri, start: error.spn?.beg ?? 0, end: Math.max(error.spn?.end ?? 0, (error.spn?.beg ?? 0) + 1), message: message(error), code: checking ? "checking" : "bend-parsing" }];
        }
      } else {
        diagnostics = [{ uri: request.uri, start: 0, end: 1, message: caught instanceof Error ? caught.message : String(caught), code: checking ? "checking" : "lowering" }];
      }
    }
    hovers = renderHovers(book);
  } catch (error) {
    diagnostics = [{ uri: request.uri, start: 0, end: 1, message: error instanceof Error ? error.message : String(error), code: "lowering" }];
  } finally {
    fs2.rmSync(directory, { recursive: true, force: true });
  }
  return { id: request.id, uri: request.uri, version: request.version, diagnostics, hovers, typedHovers };
}

// src/checker-worker.ts
var queue = Promise.resolve();
parentPort?.on("message", (request) => {
  queue = queue.then(async () => parentPort?.postMessage(await checkFlow(request))).catch((error) => {
    parentPort?.postMessage({
      id: request.id,
      uri: request.uri,
      version: request.version,
      diagnostics: [{ uri: request.uri, start: 0, end: 1, message: error instanceof Error ? error.message : String(error), code: "lowering" }],
      hovers: {},
      typedHovers: []
    });
  });
});
//# sourceMappingURL=flow-checker-worker.js.map
