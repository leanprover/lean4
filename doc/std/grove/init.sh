#!/bin/sh
set -e

lake update
lake build
cd .lake/packages/grove/frontend
npm install
