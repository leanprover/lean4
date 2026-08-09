// Lean compiler output
// Module: Std.Internal.Do.Gadget.ForIn
// Imports: public import Std.Internal.Do.Triple.SpecLemmas public import Std.Internal.ForIn
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
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant___redArg(lean_object* v_inst_1_, lean_object* v_xs_2_, lean_object* v_init_3_, lean_object* v_f_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_4(v_inst_1_, lean_box(0), v_xs_2_, v_init_3_, v_f_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_m_8_, lean_object* v_Pred_9_, lean_object* v_00_u03c1_10_, lean_object* v_inst_11_, lean_object* v_xs_12_, lean_object* v_init_13_, lean_object* v_f_14_, lean_object* v_inv_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_4(v_inst_11_, lean_box(0), v_xs_12_, v_init_13_, v_f_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant___boxed(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_m_19_, lean_object* v_Pred_20_, lean_object* v_00_u03c1_21_, lean_object* v_inst_22_, lean_object* v_xs_23_, lean_object* v_init_24_, lean_object* v_f_25_, lean_object* v_inv_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Std_Internal_Do_ForIn_forInWithInvariant(v_00_u03b1_17_, v_00_u03b2_18_, v_m_19_, v_Pred_20_, v_00_u03c1_21_, v_inst_22_, v_xs_23_, v_init_24_, v_f_25_, v_inv_26_);
lean_dec(v_inv_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___redArg(lean_object* v_inst_28_, lean_object* v_xs_29_, lean_object* v_init_30_, lean_object* v_f_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_4(v_inst_28_, lean_box(0), v_xs_29_, v_init_30_, v_f_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_m_35_, lean_object* v_Pred_36_, lean_object* v_00_u03c1_37_, lean_object* v_d_38_, lean_object* v_inst_39_, lean_object* v_xs_40_, lean_object* v_init_41_, lean_object* v_f_42_, lean_object* v_inv_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_apply_4(v_inst_39_, lean_box(0), v_xs_40_, v_init_41_, v_f_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___boxed(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_m_47_, lean_object* v_Pred_48_, lean_object* v_00_u03c1_49_, lean_object* v_d_50_, lean_object* v_inst_51_, lean_object* v_xs_52_, lean_object* v_init_53_, lean_object* v_f_54_, lean_object* v_inv_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27(v_00_u03b1_45_, v_00_u03b2_46_, v_m_47_, v_Pred_48_, v_00_u03c1_49_, v_d_50_, v_inst_51_, v_xs_52_, v_init_53_, v_f_54_, v_inv_55_);
lean_dec(v_inv_55_);
return v_res_56_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_Triple_SpecLemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_ForIn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_Gadget_ForIn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_Gadget_ForIn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_Triple_SpecLemmas(uint8_t builtin);
lean_object* initialize_Std_Internal_ForIn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Gadget_ForIn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Gadget_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_Gadget_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_Gadget_ForIn(builtin);
}
#ifdef __cplusplus
}
#endif
