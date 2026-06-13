#include <lean/lean.h>

#ifndef EMITZIG_INIT_FN
#error "EMITZIG_INIT_FN must name the module initializer"
#endif

#ifndef EMITZIG_MAIN_FN
#error "EMITZIG_MAIN_FN must name the emitted private main function"
#endif

char ** lean_setup_args(int argc, char ** argv);

lean_object * EMITZIG_INIT_FN(uint8_t builtin);
lean_object * EMITZIG_MAIN_FN(void);

static lean_object * run_main(int argc, char ** argv) {
  (void)argc;
  (void)argv;
  return EMITZIG_MAIN_FN();
}

int main(int argc, char ** argv) {
  lean_object * res;
  argv = lean_setup_args(argc, argv);
  res = EMITZIG_INIT_FN(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    return 0;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
