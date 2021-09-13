if [[ "$OS" == "Windows_NT" ]]; then
  LINK_OPTS=-Wl,--export-all
else
  LINK_OPTS=-rdynamic
fi
leanmake PKG=Lake BIN_NAME=lake LEAN_PATH=./build bin LINK_OPTS=${LINK_OPTS} "$@"
