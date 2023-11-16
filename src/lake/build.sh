#!/usr/bin/env sh

if [ "$OS" = "Windows_NT" ]; then
  LINK_OPTS=
else
  LINK_OPTS=-rdynamic
fi

LEAN_SYSROOT=${LEAN_SYSROOT:-`lean --print-prefix`}
LEAN_MAKEFILE="$LEAN_SYSROOT/share/lean/lean.mk"
EXTRA_ARGS="PKG=Lake OLEAN_OUT=.lake/build/lib TEMP_OUT=.lake/build/ir BIN_NAME=lake LEAN_PATH=./.lake/build/lib LINK_OPTS=$LINK_OPTS"
PATH="$LEAN_SYSROOT/bin:$PATH" ${MAKE:-make} -f "$LEAN_MAKEFILE" $EXTRA_ARGS bin "$@"
