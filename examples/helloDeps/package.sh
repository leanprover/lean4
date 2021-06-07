cd b
export LEAN_PATH=../../../build
lean --run ../../../Lake.lean build bin LINK_OPTS=../a/build/lib/libA.a
