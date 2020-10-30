#!/usr/bin/env bash
cat <(curl -L https://cdn.jsdelivr.net/gh/highlightjs/cdn-release@10.3.2/build/highlight.min.js) <(curl -L https://unpkg.com/highlightjs-lean/dist/lean.min.js) > highlight.js
