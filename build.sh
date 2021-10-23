#!/usr/bin/env sh
if [ "$OS" = "Windows_NT" ]; then
  LINK_OPTS=
else
  LINK_OPTS=-rdynamic
fi
leanmake PKG=Lake OLEAN_OUT=build/lib TEMP_OUT=build/ir BIN_NAME=lake LEAN_PATH=./build/lib bin LINK_OPTS=${LINK_OPTS} "$@"
