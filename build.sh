if [[ "$OSTYPE" == "msys" ]]; then
  ./build-msys2.sh "$@"
else
  ./build-unix.sh "$@"
fi
