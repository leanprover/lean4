#!/usr/bin/env bash
ctest -D ExperimentalBuild
yes "C" | ctest -VV
exit 0
