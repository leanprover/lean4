import { readFile } from "node:fs/promises";
import { UI_ABI, readUiBatch } from "./ui_abi.js";

let memory;
const imports = {
  env: { __cpp_exception: new WebAssembly.Tag({ parameters: ["i32"] }) },
  wasi_snapshot_preview1: {
    environ_get: () => 0,
    environ_sizes_get: (count, size) => {
      const view = new DataView(memory.buffer);
      view.setUint32(count, 0, true);
      view.setUint32(size, 0, true);
      return 0;
    },
    fd_close: () => 0,
    fd_fdstat_get: () => 8,
    fd_prestat_get: () => 8,
    fd_prestat_dir_name: () => 8,
    fd_read: () => 8,
    fd_seek: () => 8,
    fd_write: (_fd, _iovs, _count, written) => {
      new DataView(memory.buffer).setUint32(written, 0, true);
      return 0;
    },
    proc_exit: (code) => { throw new Error(`proc_exit(${code})`); },
    random_get: (ptr, len) => { new Uint8Array(memory.buffer, ptr, len).fill(0x5a); return 0; },
    clock_time_get: (_id, _precision, ptr) => {
      new DataView(memory.buffer).setBigUint64(ptr, 0n, true);
      return 0;
    },
  },
};

const { instance } = await WebAssembly.instantiate(await readFile(new URL("ui.wasm", import.meta.url)), imports);
memory = instance.exports.memory;
instance.exports._initialize?.();

let model = instance.exports.lean_ui_boot(0) >>> 0;
const boot = readUiBatch(memory, instance.exports.lean_ui_batch(0) >>> 0);
if (boot.count === 0 || boot.overflowed) throw new Error("invalid boot effect batch");
if (boot.recordsPtr + boot.count * boot.recordSize > memory.buffer.byteLength) throw new Error("effect batch OOB");

const setInput = (text) => {
  const bytes = new TextEncoder().encode(text);
  const ptr = instance.exports.lean_ui_event_ptr() >>> 0;
  new Uint8Array(memory.buffer, ptr, bytes.length).set(bytes);
  model = instance.exports.lean_ui_dispatch(model, UI_ABI.handler.input, ptr, bytes.length) >>> 0;
};

setInput("4");
model = instance.exports.lean_ui_dispatch(model, UI_ABI.handler.actionBase + 4 * 16, 0, 0) >>> 0;
const click = readUiBatch(memory, instance.exports.lean_ui_batch(0) >>> 0);
if (click.count === 0 || click.overflowed) throw new Error("invalid click effect batch");

setInput("12");
model = instance.exports.lean_ui_dispatch(model, UI_ABI.handler.actionBase + 4 * 16, 0, 0) >>> 0;
model = instance.exports.lean_ui_dispatch(model, UI_ABI.handler.selectBase + 1, 0, 0) >>> 0;

const payload = new TextEncoder().encode("6");
const payloadPtr = instance.exports.lean_ui_event_ptr() >>> 0;
new Uint8Array(memory.buffer, payloadPtr, payload.length).set(payload);
model = instance.exports.lean_ui_dispatch(model, UI_ABI.handler.input, payloadPtr, payload.length) >>> 0;
model = instance.exports.lean_ui_dispatch(model, UI_ABI.handler.actionBase + 4 * 16, 0, 0) >>> 0;
const branch = readUiBatch(memory, instance.exports.lean_ui_batch(0) >>> 0);
if (branch.count === 0 || branch.overflowed) throw new Error("invalid branch effect batch");
console.log(`boot=${boot.count} insert=${click.count} branch=${branch.count} payload=${payload.length} model=${model}`);
