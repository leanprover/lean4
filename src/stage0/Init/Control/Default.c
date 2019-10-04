// Lean compiler output
// Module: Init.Control.Default
// Imports: Init.Control.Applicative Init.Control.Functor Init.Control.Alternative Init.Control.Monad Init.Control.Lift Init.Control.State Init.Control.Id Init.Control.Except Init.Control.Reader Init.Control.Option Init.Control.Combinators Init.Control.Conditional
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
lean_object* initialize_Init_Control_Applicative(lean_object*);
lean_object* initialize_Init_Control_Functor(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Control_Monad(lean_object*);
lean_object* initialize_Init_Control_Lift(lean_object*);
lean_object* initialize_Init_Control_State(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Control_Except(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_Option(lean_object*);
lean_object* initialize_Init_Control_Combinators(lean_object*);
lean_object* initialize_Init_Control_Conditional(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Applicative(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Functor(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Alternative(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Monad(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Lift(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_State(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Id(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Except(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Reader(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Option(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Combinators(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Conditional(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
