#!/bin/sh

lake exe grove-stdlib --full metadata.json
cd .lake/packages/grove/frontend
npm install
if [ -f "../../../../invalidated.json" ]; then
    GROVE_DATA_LOCATION=../../../../metadata.json GROVE_UPSTREAM_INVALIDATED_FACTS_LOCATION=../../../../invalidated.json npm run dev
else
    GROVE_DATA_LOCATION=../../../../metadata.json npm run dev
fi