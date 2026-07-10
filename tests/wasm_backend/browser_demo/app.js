// Browser host for pure-scalar Lean WebAssembly exports (no WASI / no runtime).

const statusEl = document.getElementById("status");
const runBtn = document.getElementById("run");

function setStatus(msg, isError = false) {
  statusEl.textContent = msg;
  statusEl.classList.toggle("error", isError);
}

async function main() {
  const response = await fetch("./demo.wasm");
  if (!response.ok) {
    throw new Error(
      `Failed to fetch demo.wasm (${response.status}). Run ./build.sh and serve this directory over HTTP.`
    );
  }
  const bytes = await response.arrayBuffer();
  // Pure scalar objects import nothing once linked.
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const exp = instance.exports;

  const required = [
    "lean_wasm_demo_add",
    "lean_wasm_demo_answer",
    "lean_wasm_demo_choose",
  ];
  for (const name of required) {
    if (typeof exp[name] !== "function") {
      throw new Error(`Missing export ${name}`);
    }
  }

  setStatus(
    `Loaded. answer() = ${exp.lean_wasm_demo_answer() >>> 0}. Enter x, y and click Run.`
  );
  runBtn.disabled = false;

  runBtn.addEventListener("click", () => {
    const x = Number(document.getElementById("x").value) >>> 0;
    const y = Number(document.getElementById("y").value) >>> 0;
    const sum = exp.lean_wasm_demo_add(x, y) >>> 0;
    const chooseX = exp.lean_wasm_demo_choose(x) >>> 0;
    const chooseY = exp.lean_wasm_demo_choose(y) >>> 0;
    setStatus(
      `add(${x}, ${y}) = ${sum}\n` +
        `choose(${x}) = ${chooseX}  (0 → 7, else 9)\n` +
        `choose(${y}) = ${chooseY}\n` +
        `answer() = ${exp.lean_wasm_demo_answer() >>> 0}`
    );
  });
}

main().catch((err) => {
  console.error(err);
  setStatus(String(err.message || err), true);
});
