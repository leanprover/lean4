// Lean compiler output
// Module: Std.Internal.Do.Triple.Gadget
// Imports: public import Std.Internal.Do.Triple.Basic public import Std.Internal.Do.Frame
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
LEAN_EXPORT lean_object* l_Std_Internal_Do_assertGadget___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_assertGadget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_assertGadget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_assertGadget___redArg(lean_object* v_inst_1_){
_start:
{
lean_object* v_toApplicative_2_; lean_object* v_toPure_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_toApplicative_2_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toApplicative_2_);
lean_dec_ref(v_inst_1_);
v_toPure_3_ = lean_ctor_get(v_toApplicative_2_, 1);
lean_inc(v_toPure_3_);
lean_dec_ref(v_toApplicative_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_2(v_toPure_3_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_assertGadget(lean_object* v_m_6_, lean_object* v_Pred_7_, lean_object* v_EPred_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_name_13_, lean_object* v_as_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_Internal_Do_assertGadget___redArg(v_inst_9_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_assertGadget___boxed(lean_object* v_m_16_, lean_object* v_Pred_17_, lean_object* v_EPred_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_name_23_, lean_object* v_as_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Internal_Do_assertGadget(v_m_16_, v_Pred_17_, v_EPred_18_, v_inst_19_, v_inst_20_, v_inst_21_, v_inst_22_, v_name_23_, v_as_24_);
lean_dec(v_as_24_);
lean_dec(v_name_23_);
lean_dec(v_inst_22_);
return v_res_25_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Frame(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Triple_Gadget(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Frame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Triple_Gadget(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_Triple_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Frame(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Triple_Gadget(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Frame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Triple_Gadget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Triple_Gadget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Triple_Gadget(builtin);
}
#ifdef __cplusplus
}
#endif
