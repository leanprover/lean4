// Lean compiler output
// Module: init.control.default
// Imports: init.control.applicative init.control.functor init.control.alternative init.control.monad init.control.lift init.control.state init.control.id init.control.except init.control.reader init.control.option init.control.combinators init.control.conditional
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* initialize_init_control_applicative(obj*);
obj* initialize_init_control_functor(obj*);
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_control_monad(obj*);
obj* initialize_init_control_lift(obj*);
obj* initialize_init_control_state(obj*);
obj* initialize_init_control_id(obj*);
obj* initialize_init_control_except(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_control_option(obj*);
obj* initialize_init_control_combinators(obj*);
obj* initialize_init_control_conditional(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_default(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_applicative(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_functor(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_lift(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_state(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_id(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_except(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_option(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_conditional(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
