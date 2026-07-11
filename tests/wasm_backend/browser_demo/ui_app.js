// JS host for the typed Lean UI wire ABI.
import { UI_ABI, readUiBatch } from "./ui_abi.js";

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
    env: {
      __cpp_exception: new WebAssembly.Tag({ parameters: ["i32"] }),
    },
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

function readString(memory, ptr, len) {
  if (!ptr || len === 0) return "";
  const buf = memory.buffer;
  if (ptr + len > buf.byteLength) {
    console.warn("string OOB", { ptr, len, mem: buf.byteLength });
    return "";
  }
  return new TextDecoder().decode(new Uint8Array(buf, ptr, len));
}

function wireClick(el, handlerId) {
  el.onclick = null;
  delete el.dataset.handler;
  if (!handlerId) return;
  el.dataset.handler = String(handlerId);
  el.onclick = (e) => {
    e.preventDefault();
    e.stopPropagation();
    if (el.classList.contains("disabled")) return;
    onDomEvent(handlerId);
  };
}

function applyEffects(exports, memory) {
  const header = readUiBatch(memory, exports.lean_ui_batch(0) >>> 0);
  if (header.overflowed) throw new Error("Lean UI effect batch overflowed");
  const count = header.count;
  const view = new DataView(memory.buffer);
  const word = (i, field) => view.getUint32(header.recordsPtr + i * header.recordSize + field * 4, true);
  let created = 0,
    updated = 0,
    removed = 0;
  for (let i = 0; i < count; i++) {
    const op = word(i, 0), id = word(i, 1), parent = word(i, 2), index = word(i, 3);
    const payload0 = word(i, 4), payload1 = word(i, 5), textPtr = word(i, 6), textLen = word(i, 7);
    const parentNode = nodes.get(parent) || appEl;

    if (op === UI_ABI.effect.createElement) {
      const tag = TAG[payload0] || "div";
      const prev = nodes.get(id);
      if (prev && prev.parentNode) prev.parentNode.removeChild(prev);
      const el = document.createElement(tag);
      el.dataset.fid = String(id);
      const cls = readString(memory, textPtr, textLen);
      if (cls) el.className = cls;
      if (payload1) wireClick(el, payload1);
      insertAt(parentNode, el, index);
      nodes.set(id, el);
      created++;
    } else if (op === UI_ABI.effect.createText) {
      const prev = nodes.get(id);
      if (prev && prev.parentNode) prev.parentNode.removeChild(prev);
      const wrap = document.createElement("span");
      wrap.dataset.fid = String(id);
      wrap.textContent = readString(memory, textPtr, textLen);
      insertAt(parentNode, wrap, index);
      nodes.set(id, wrap);
      created++;
    } else if (op === UI_ABI.effect.setText) {
      const n = nodes.get(id);
      if (n) {
        n.textContent = readString(memory, textPtr, textLen);
        updated++;
      }
    } else if (op === UI_ABI.effect.remove) {
      const n = nodes.get(id);
      if (n && n.parentNode) n.parentNode.removeChild(n);
      nodes.delete(id);
      removed++;
    } else if (op === UI_ABI.effect.setClass) {
      const n = nodes.get(id);
      if (n) {
        n.className = readString(memory, textPtr, textLen);
        updated++;
      }
    } else if (op === UI_ABI.effect.setHandler) {
      const n = nodes.get(id);
      if (n instanceof HTMLElement) {
        wireClick(n, payload0);
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

function dispatchEvent(handlerId) {
  if (!exp || !mem) return;
  model = exp.lean_ui_dispatch(model >>> 0, handlerId >>> 0, 0, 0) >>> 0;
  const stats = applyEffects(exp, mem);
  const g = nGoals(model);
  const s = isSolved(model) ? "solved" : `${g} open goal(s)`;
  setStatus(
    `handler=${handlerId}  ${s}  effects=${stats.count} ` +
      `(+${stats.created} ~${stats.updated} -${stats.removed})  ` +
      `mem=${mem.buffer.byteLength >> 10}KiB`
  );
}

function onDomEvent(handlerId) {
  try {
    dispatchEvent(handlerId);
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
    "lean_ui_dispatch",
    "lean_ui_batch",
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
