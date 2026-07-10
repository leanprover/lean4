// Minimal WASI reactor host for Lean language-core wasm modules.

const statusEl = document.getElementById("status");
const runBtn = document.getElementById("run");

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
      environ_sizes_get(environCountPtr, environBufSizePtr) {
        view().setUint32(environCountPtr, 0, true);
        view().setUint32(environBufSizePtr, 0, true);
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
            const text = new TextDecoder().decode(bytes.subarray(ptr, ptr + len));
            if (text.trim()) console.log(text);
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
      clock_time_get(_id, _precision, resultPtr) {
        view().setBigUint64(resultPtr, BigInt(Date.now()) * 1000000n, true);
        return 0;
      },
    },
  };
}

async function main() {
  let memory = null;
  const imports = makeWasiImports(() => memory);
  const response = await fetch("./core_rt.wasm");
  if (!response.ok) {
    throw new Error(
      `Failed to fetch core_rt.wasm (${response.status}). Run ./build_core_rt.sh first.`
    );
  }
  const { instance } = await WebAssembly.instantiate(
    await response.arrayBuffer(),
    imports
  );
  memory = instance.exports.memory;
  if (!(memory instanceof WebAssembly.Memory)) {
    throw new Error("Module did not export WebAssembly.Memory as `memory`");
  }
  if (typeof instance.exports._initialize === "function") {
    instance.exports._initialize();
  }
  const coreRt = instance.exports.lean_wasm_core_rt;
  if (typeof coreRt !== "function") {
    throw new Error("Missing export lean_wasm_core_rt");
  }

  setStatus("Loaded. coreRt(x, y) = 2x + 2y via constructors + RC.");
  runBtn.disabled = false;
  runBtn.addEventListener("click", () => {
    const x = Number(document.getElementById("x").value) >>> 0;
    const y = Number(document.getElementById("y").value) >>> 0;
    const r = coreRt(x, y) >>> 0;
    setStatus(
      `coreRt(${x}, ${y}) = ${r}\nexpected 2*x + 2*y = ${(2 * x + 2 * y) >>> 0}`
    );
  });
}

main().catch((err) => {
  console.error(err);
  setStatus(String(err.message || err), true);
});
