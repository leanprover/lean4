if [[ "$OSTYPE" == "cygwin" || "$OSTYPE" == "msys" ]]; then
  echo "Skipped: uses SIGWINCH and usleep"
  exit 0
fi
leanc ${LEANC_OPTS-} -o uv_restart.produced uv_restart.c
run ./uv_restart.produced
