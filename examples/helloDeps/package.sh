cd b
export LEAN_PATH=../../../build
lean --run ../../../Leanpkg2.lean build bin LINK_OPTS=../a/build/lib/libA.a
