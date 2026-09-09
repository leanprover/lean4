#!/bin/sh
set -e

lake build
cd .lake/packages/grove/frontend
npm install
