// JS host: string events + string labels for the proof-state fiber UI.

const appEl = document.getElementById("app");
const statusEl = document.getElementById("status");

const TAG = ["div", "button", "span", "ul", "li"];

/** @type {Map<number, Node>} */
const nodes = new Map();
nodes.set(0, appEl);

/** @type {WebAssembly.Instance["exports"] | null} */
let exp = null;
/** @type {WebAssembly.Memory | null} */
let mem = null;
/** @type {number} */
let model = 0;

function setStatus(msg, isError = false) {
  statusEl.textContent = msg;
  statusEl.classList.toggle("error", isError);
}

function makeWasiImports(getMemory) {
  const view = () => new DataView(getMemory().buffer);
  const u8 = () => new Uint8Array(getMemory().buffer);
  const ret0 = () => 0;
  const ebadf = () => 8;
  return {
    wasi_snapshot_preview1: {
      environ_get: ret0,
      environ_sizes_get(c, b) {
        view().setUint32(c, 0, true);
        view().setUint32(b, 0, true);
        return 0;
      },
      fd_close: ret0,
      fd_fdstat_get: ebadf,
      fd_prestat_get: ebadf,
      fd_prestat_dir_name: ebadf,
      fd_read: ebadf,
      fd_seek: ebadf,
      fd_write(fd, iovs, iovsLen, nwrittenPtr) {
        let written = 0;
        const v = view();
        const bytes = u8();
        for (let i = 0; i < iovsLen; i++) {
          const ptr = v.getUint32(iovs + i * 8, true);
          const len = v.getUint32(iovs + i * 8 + 4, true);
          if (fd === 1 || fd === 2) {
            const t = new TextDecoder().decode(bytes.subarray(ptr, ptr + len));
            if (t.trim()) console.log(t);
          }
          written += len;
        }
        v.setUint32(nwrittenPtr, written, true);
        return 0;
      },
      proc_exit(code) {
        throw new Error(`WASI proc_exit(${code})`);
      },
      random_get(buf, len) {
        crypto.getRandomValues(u8().subarray(buf, buf + len));
        return 0;
      },
      clock_time_get(_id, _p, resultPtr) {
        view().setBigUint64(resultPtr, BigInt(Date.now()) * 1000000n, true);
        return 0;
      },
    },
  };
}

function readInternedString(exports, memory, strId) {
  const id = strId >>> 0;
  if (id === 0 && exports.lean_ui_string_len(0) === 0) {
    // id 0 can be a valid interned empty or unused — check len
  }
  const ptr = exports.lean_ui_string_ptr(id) >>> 0;
  const len = exports.lean_ui_string_len(id) >>> 0;
  if (!ptr || len === 0) return "";
  const buf = memory.buffer;
  if (ptr + len > buf.byteLength) {
    console.warn("string OOB", { ptr, len, mem: buf.byteLength, id });
    return "";
  }
  return new TextDecoder().decode(new Uint8Array(buf, ptr, len));
}

function wireClick(el, evName) {
  if (!evName) return;
  el.dataset.ev = evName;
  el.addEventListener("click", (e) => {
    e.preventDefault();
    e.stopPropagation();
    if (el.classList.contains("disabled")) return;
    onDomEvent(evName);
  });
}

function applyEffects(exports, memory) {
  const count = exports.lean_ui_effect_count(0) >>> 0;
  let created = 0,
    updated = 0,
    removed = 0;
  for (let i = 0; i < count; i++) {
    const op = exports.lean_ui_effect_at(i, 0) >>> 0;
    const id = exports.lean_ui_effect_at(i, 1) >>> 0;
    const parent = exports.lean_ui_effect_at(i, 2) >>> 0;
    const a = exports.lean_ui_effect_at(i, 3) >>> 0;
    const b = exports.lean_ui_effect_at(i, 4) >>> 0;
    const index = exports.lean_ui_effect_at(i, 5) >>> 0;
    const d = exports.lean_ui_effect_at(i, 6) >>> 0; // onClick string id (create)
    const parentNode = nodes.get(parent) || appEl;

    if (op === 1) {
      const tag = TAG[a] || "div";
      const prev = nodes.get(id);
      if (prev && prev.parentNode) prev.parentNode.removeChild(prev);
      const el = document.createElement(tag);
      el.dataset.fid = String(id);
      const cls = readInternedString(exports, memory, b);
      if (cls) el.className = cls;
      const evName = d ? readInternedString(exports, memory, d) : "";
      if (evName) wireClick(el, evName);
      insertAt(parentNode, el, index);
      nodes.set(id, el);
      created++;
    } else if (op === 2) {
      // text: a==255, b=interned string
      const prev = nodes.get(id);
      if (prev && prev.parentNode) prev.parentNode.removeChild(prev);
      const wrap = document.createElement("span");
      wrap.dataset.fid = String(id);
      wrap.textContent = readInternedString(exports, memory, b);
      insertAt(parentNode, wrap, index);
      nodes.set(id, wrap);
      created++;
    } else if (op === 3) {
      const n = nodes.get(id);
      if (n) {
        n.textContent = readInternedString(exports, memory, b);
        updated++;
      }
    } else if (op === 4) {
      const n = nodes.get(id);
      if (n && n.parentNode) n.parentNode.removeChild(n);
      nodes.delete(id);
      removed++;
    } else if (op === 5) {
      const n = nodes.get(id);
      if (n) {
        n.className = readInternedString(exports, memory, a);
        updated++;
      }
    }
  }
  return { count, created, updated, removed };
}

function insertAt(parent, node, index) {
  const ref = parent.childNodes[index] || null;
  parent.insertBefore(node, ref);
}

function nGoals(m) {
  return (m >>> 0) & 0xffff;
}
function isSolved(m) {
  return ((m >>> 0) >>> 16) & 1;
}

/** Dispatch a UTF-8 event name through the scratch buffer. */
function dispatchEvent(name) {
  if (!exp || !mem) return;
  const bytes = new TextEncoder().encode(name);
  const ptr = exp.lean_ui_scratch_ptr() >>> 0;
  const cap = exp.lean_ui_scratch_cap() >>> 0;
  if (bytes.length > cap) throw new Error(`event too long (${bytes.length} > ${cap})`);
  new Uint8Array(mem.buffer, ptr, bytes.length).set(bytes);
  model = exp.lean_ui_dispatch_s(model >>> 0, ptr, bytes.length) >>> 0;
  const stats = applyEffects(exp, mem);
  const g = nGoals(model);
  const s = isSolved(model) ? "solved" : `${g} open goal(s)`;
  setStatus(
    `event="${name}"  ${s}  effects=${stats.count} ` +
      `(+${stats.created} ~${stats.updated} -${stats.removed})  ` +
      `mem=${mem.buffer.byteLength >> 10}KiB`
  );
}

function onDomEvent(evName) {
  try {
    dispatchEvent(evName);
  } catch (e) {
    console.error(e);
    setStatus(String(e.message || e), true);
  }
}

async function main() {
  let memory = null;
  const imports = makeWasiImports(() => memory);
  const res = await fetch("./ui.wasm");
  if (!res.ok) throw new Error(`fetch ui.wasm failed (${res.status})`);
  const { instance } = await WebAssembly.instantiate(await res.arrayBuffer(), imports);
  memory = instance.exports.memory;
  if (!(memory instanceof WebAssembly.Memory)) throw new Error("missing memory");
  if (typeof instance.exports._initialize === "function") instance.exports._initialize();
  exp = instance.exports;
  mem = memory;
  for (const name of [
    "lean_ui_boot",
    "lean_ui_dispatch_s",
    "lean_ui_effect_count",
    "lean_ui_effect_at",
    "lean_ui_string_ptr",
    "lean_ui_string_len",
    "lean_ui_scratch_ptr",
    "lean_ui_scratch_cap",
  ]) {
    if (typeof exp[name] !== "function") throw new Error(`missing export ${name}`);
  }

  appEl.replaceChildren();
  nodes.clear();
  nodes.set(0, appEl);
  model = exp.lean_ui_boot(0) >>> 0;
  const stats = applyEffects(exp, mem);
  setStatus(
    `Booted. ${nGoals(model)} goal(s). effects=${stats.count}. ` +
      `Use tactics or click a hypothesis to exact.`
  );
}

main().catch((e) => {
  console.error(e);
  setStatus(String(e.message || e), true);
});
