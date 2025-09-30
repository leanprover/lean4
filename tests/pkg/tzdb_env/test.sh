#!/usr/bin/env bash

if [ "$OS" = "Windows_NT" ]; then
	exit 0
fi

rm -rf .lake/build
[ "$(TZ=UTC lake exe release)" = "{ second := 0 }" ] || exit 1
[ "$(TZ=America/Sao_Paulo lake exe release)" = "{ second := -11188 }" ] || exit 1
exit 0
