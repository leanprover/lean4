// A C `main` that calls Lean without passing its `argv` to `lean_setup_args`, so
// `IO.getProgramName` has no name to return and must throw.
#include <lean/lean.h>

// `leanc` ships no C library headers, but links the C library.
int printf(char const * fmt, ...);

void lean_initialize_runtime_module(void);
lean_object * lean_io_get_program_name(void);

int main(void) {
    lean_initialize_runtime_module();
    lean_object * res = lean_io_get_program_name();
    if (lean_io_result_is_ok(res)) {
        printf("unexpected program name: %s\n", lean_string_cstr(lean_io_result_get_value(res)));
        return 1;
    }
    lean_dec_ref(res);
    printf("unknown\n");
    return 0;
}
