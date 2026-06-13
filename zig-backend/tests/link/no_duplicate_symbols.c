#include <lean/lean.h>

char ** lean_setup_args(int argc, char ** argv);

static void * volatile keep_symbols[] = {
    (void *)&lean_alloc_object,
    (void *)&lean_task_pure,
    (void *)&lean_decode_io_error,
    (void *)&lean_run_main,
    (void *)&lean_setup_args,
    (void *)&lean_float_to_string,
    (void *)&lean_float32_to_string,
};

int main(void) {
    return keep_symbols[0] == 0;
}
