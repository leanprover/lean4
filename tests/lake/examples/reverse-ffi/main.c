#include <stdio.h>
#include <lean/lean.h>

extern uint64_t my_length(lean_obj_arg);

// see https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=ffi-initialization
extern void lean_initialize_runtime_module();
extern void lean_initialize();
extern void lean_io_mark_end_initialization();
extern lean_object * initialize_rffi_RFFI(uint8_t builtin);

int main() {
  lean_initialize_runtime_module();
  lean_object * res;
  // use same default as for Lean executables
  uint8_t builtin = 1;
  res = initialize_rffi_RFFI(builtin);
  if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
  } else {
      lean_io_result_show_error(res);
      lean_dec(res);
      return 1;  // do not access Lean declarations if initialization failed
  }
  lean_io_mark_end_initialization();

  // actual program

  lean_object * s = lean_mk_string("hello!");
  uint64_t l = my_length(s);
  printf("output: %ld\n", l);
}
