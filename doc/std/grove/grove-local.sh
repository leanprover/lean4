#!/bin/sh

lake exe grove-stdlib --full metadata.json
cd .lake/packages/grove/frontend
npm install
cp ../../../../metadata.json public/metadata.json
if [ -f "../../../../invalidated.json" ]; then
    cp ../../../../invalidated.json public/invalidated.json
    GROVE_DATA_LOCATION=public/metadata.json GROVE_UPSTREAM_INVALIDATED_FACTS_LOCATION=public/invalidated.json npm run dev
else
    GROVE_DATA_LOCATION=public/metadata.json npm run dev
fi
