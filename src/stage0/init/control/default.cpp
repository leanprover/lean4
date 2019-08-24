// Lean compiler output
// Module: init.control.default
// Imports: init.control.applicative init.control.functor init.control.alternative init.control.monad init.control.lift init.control.state init.control.id init.control.except init.control.reader init.control.option init.control.combinators init.control.conditional
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_init_control_applicative(lean_object*);
lean_object* initialize_init_control_functor(lean_object*);
lean_object* initialize_init_control_alternative(lean_object*);
lean_object* initialize_init_control_monad(lean_object*);
lean_object* initialize_init_control_lift(lean_object*);
lean_object* initialize_init_control_state(lean_object*);
lean_object* initialize_init_control_id(lean_object*);
lean_object* initialize_init_control_except(lean_object*);
lean_object* initialize_init_control_reader(lean_object*);
lean_object* initialize_init_control_option(lean_object*);
lean_object* initialize_init_control_combinators(lean_object*);
lean_object* initialize_init_control_conditional(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_control_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_applicative(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_functor(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_state(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_id(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_except(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_option(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
