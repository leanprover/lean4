// JS host for the typed Lean UI wire ABI.
import { UI_ABI, readUiBatch } from "./ui_abi.js";

const appEl = document.getElementById("app");
const statusEl = document.getElementById("status");

const TAG = ["div", "button", "span", "ul", "li", "canvas"];

/** @type {Map<number, Node>} */
const nodes = new Map();
nodes.set(0, appEl);

/** @type {WebAssembly.Instance["exports"] | null} */
let exp = null;
/** @type {WebAssembly.Memory | null} */
let mem = null;
/** @type {number} */
let model = 0;
let frame = 0;

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
  drawCustomSurfaces();
  return { count, created, updated, removed };
}

function drawCustomSurfaces() {
  for (const canvas of document.querySelectorAll("canvas.demo-canvas")) {
    canvas.width = Math.max(640, canvas.clientWidth * devicePixelRatio);
    canvas.height = 220 * devicePixelRatio;
    const ctx = canvas.getContext("2d");
    ctx.scale(devicePixelRatio, devicePixelRatio);
    ctx.fillStyle = "#0b111b";
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    if (canvas.classList.contains("automaton")) {
      for (let y = 0; y < 9; y++) for (let x = 0; x < 28; x++) {
        const alive = ((x * 13 + y * 7 + frame) % 11) < 4;
        ctx.fillStyle = alive ? "#9ece6a" : "#1a2b38";
        ctx.fillRect(8 + x * 21, 8 + y * 21, 17, 17);
      }
    } else {
      const colors = ["#7aa2f7", "#bb9af7", "#9ece6a", "#e0af68"];
      colors.forEach((color, row) => {
        ctx.strokeStyle = color; ctx.lineWidth = 2; ctx.beginPath();
        for (let x = 0; x <= 600; x += 20) {
          const y = 30 + row * 42 + (((x / 20 + row + frame) % (3 + row)) ? 0 : 22);
          ctx.lineTo(10 + x, y);
        }
        ctx.stroke();
      });
    }
  }
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

function dispatchEvent(handlerId, payload = "") {
  if (!exp || !mem) return;
  const bytes = new TextEncoder().encode(payload);
  const ptr = exp.lean_ui_event_ptr() >>> 0;
  const cap = exp.lean_ui_event_capacity() >>> 0;
  if (bytes.length > cap) throw new Error(`event payload exceeds ${cap} bytes`);
  if (bytes.length) new Uint8Array(mem.buffer, ptr, bytes.length).set(bytes);
  model = exp.lean_ui_dispatch(model >>> 0, handlerId >>> 0, ptr, bytes.length) >>> 0;
  frame++;
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
    "lean_ui_event_ptr",
    "lean_ui_event_capacity",
  ]) {
    if (typeof exp[name] !== "function") throw new Error(`missing export ${name}`);
  }

  appEl.replaceChildren();
  nodes.clear();
  nodes.set(0, appEl);
  model = exp.lean_ui_boot(0) >>> 0;
  let stats = applyEffects(exp, mem);
  setStatus(
    `Booted persistent tree. effects=${stats.count}. Select any version to branch from it.`
  );
}

main().catch((e) => {
  console.error(e);
  setStatus(String(e.message || e), true);
});

document.getElementById("demo-input")?.addEventListener("input", (event) => {
  dispatchEvent(UI_ABI.handler.input, event.currentTarget.value);
});
