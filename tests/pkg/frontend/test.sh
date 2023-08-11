#!/usr/bin/env bash

rm -rf build
lake build
lake exe frontend Frontend.Import1 Frontend.Import2
