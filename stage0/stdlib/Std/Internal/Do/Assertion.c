// Lean compiler output
// Module: Std.Internal.Do.Assertion
// Imports: public import Init.Internal.Order public import Std.Internal.Do.Order.Basic public import Std.Internal.Do.Order.Heyting public import Std.Internal.Do.Order.Instances
#include <lean/lean.h>
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
LEAN_EXPORT lean_object* l_Std_Internal_Do_Assertion_instNondetFunForall___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Assertion_instNondetFunForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Assertion_instNondetFunForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Assertion_instNondetFunForall___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_f_2_, lean_object* v_a_3_, lean_object* v_s_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v_f_2_, v_s_4_);
v___x_6_ = lean_apply_2(v_inst_1_, v___x_5_, v_a_3_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_Assertion_instNondetFunForall___redArg(lean_object* v_inst_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = lean_alloc_closure((void*)(l_Std_Internal_Do_Assertion_instNondetFunForall___redArg___lam__0), 4, 1);
lean_closure_set(v___f_8_, 0, v_inst_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_Assertion_instNondetFunForall(lean_object* v_00_u03c3_9_, lean_object* v_Pred_10_, lean_object* v_Fun_11_, lean_object* v_00_u03b1_12_, lean_object* v_inst_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v___f_15_; 
v___f_15_ = lean_alloc_closure((void*)(l_Std_Internal_Do_Assertion_instNondetFunForall___redArg___lam__0), 4, 1);
lean_closure_set(v___f_15_, 0, v_inst_14_);
return v___f_15_;
}
}
lean_object* runtime_initialize_Init_Internal_Order(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Heyting(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Instances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Assertion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Internal_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Assertion(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Internal_Order(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Order_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Order_Heyting(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Order_Instances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Assertion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Internal_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Order_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Assertion(builtin);
}
#ifdef __cplusplus
}
#endif
