leanmake --always-make bin

capture ./build/bin/test hello world
check_out_contains "[hello, world]"
