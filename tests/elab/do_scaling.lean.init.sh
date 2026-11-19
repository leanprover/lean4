# The `do` blocks of this test need more than the 16MB thread stack of sanitizer builds.
export LEAN_STACK_SIZE_KB=1048576
