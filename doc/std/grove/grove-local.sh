#!/bin/sh
set -e

lake exe grove-stdlib --full metadata.json
cd .lake/packages/grove/frontend
npm install
cp ../../../../metadata.json public/metadata.json
if [ -f "../../../../invalidated.json" ]; then
    cp ../../../../invalidated.json public/invalidated.json
fi
npm run dev
