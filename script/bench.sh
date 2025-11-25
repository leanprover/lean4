#!/usr/bin/env bash
set -euxo pipefail

cmake --preset release 1>&2

# We benchmark against stage2/bin to test new optimizations.
timeout -s KILL 1h time make -C build/release -j$(nproc) stage3 1>&2
export PATH=$PWD/build/release/stage2/bin:$PATH

# The extra opts used to be passed to the Makefile during benchmarking only but with Lake it is
# easier to configure them statically.
cmake -B build/release/stage3 -S src -DLEAN_EXTRA_LAKEFILE_TOML='weakLeanArgs=["-Dprofiler=true", "-Dprofiler.threshold=9999999", "--stats"]' 1>&2

(
cd tests/bench
timeout -s KILL 1h time temci exec --config speedcenter.yaml --in speedcenter.exec.velcom.yaml 1>&2
temci report run_output.yaml --reporter codespeed2
)

if [ -d .git ]; then
    DIR="$(git rev-parse @)"
    BASE_URL="https://speed.lean-lang.org/lean4-out/$DIR"
    {
        cat <<'EOF'
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Lakeprof Report</title>
</head>
<h1>Lakeprof Report</h1>
<button type="button" id="btn_fetch">View build trace in Perfetto</button>
<script type="text/javascript">
const ORIGIN = 'https://ui.perfetto.dev';

const btnFetch = document.getElementById('btn_fetch');

async function fetchAndOpen(traceUrl) {
  const resp = await fetch(traceUrl);
  // Error checking is left as an exercise to the reader.
  const blob = await resp.blob();
  const arrayBuffer = await blob.arrayBuffer();
  openTrace(arrayBuffer, traceUrl);
}

function openTrace(arrayBuffer, traceUrl) {
  const win = window.open(ORIGIN);
  if (!win) {
    btnFetch.style.background = '#f3ca63';
  	btnFetch.onclick = () => openTrace(arrayBuffer);
    btnFetch.innerText = 'Popups blocked, click here to open the trace file';
    return;
  }

  const timer = setInterval(() => win.postMessage('PING', ORIGIN), 50);

  const onMessageHandler = (evt) => {
    if (evt.data !== 'PONG') return;

    // We got a PONG, the UI is ready.
    window.clearInterval(timer);
    window.removeEventListener('message', onMessageHandler);

    const reopenUrl = new URL(location.href);
    reopenUrl.hash = `#reopen=${traceUrl}`;
    win.postMessage({
      perfetto: {
        buffer: arrayBuffer,
        title: 'Lake Build Trace',
        url: reopenUrl.toString(),
    }}, ORIGIN);
  };

  window.addEventListener('message', onMessageHandler);
}

// This is triggered when following the link from the Perfetto UI's sidebar.
if (location.hash.startsWith('#reopen=')) {
 const traceUrl = location.hash.substr(8);
 fetchAndOpen(traceUrl);
}
EOF
        cat <<EOF
btnFetch.onclick = () => fetchAndOpen("$BASE_URL/lakeprof.trace_event");
</script>
EOF
        echo "<pre><code>"
        (cd src; lakeprof report -prc)
        echo "</code></pre>"
        echo "</body></html>"
    } | tee index.html

    curl -T index.html $BASE_URL/index.html
    curl -T src/lakeprof.log $BASE_URL/lakeprof.log
    curl -T src/lakeprof.trace_event $BASE_URL/lakeprof.trace_event
fi
