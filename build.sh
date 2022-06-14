#!/usr/bin/env sh

if [ "$OS" = "Windows_NT" ]; then
  LINK_OPTS=
else
  LINK_OPTS=-rdynamic
fi

LEAN_SYSROOT=${LEAN_SYSROOT:-`lean --print-prefix`}
LEAN_MAKEFILE="$LEAN_SYSROOT/share/lean/lean.mk"
EXTRA_ARGS="PKG=Lake OLEAN_OUT=build/lib TEMP_OUT=build/ir BIN_NAME=lake LEAN_PATH=./build/lib LINK_OPTS=$LINK_OPTS"
PATH="$LEAN_SYSROOT/bin:$PATH" ${MAKE:-make} -f "$LEAN_MAKEFILE" $EXTRA_ARGS bin "$@"
