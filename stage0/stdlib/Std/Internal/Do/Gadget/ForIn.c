// Lean compiler output
// Module: Std.Internal.Do.Gadget.ForIn
// Imports: public import Std.Internal.Do.Triple.SpecLemmas import Init.Data.Array.Bootstrap import Init.Data.List.Monadic
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
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant___redArg(lean_object* v_inst_1_, lean_object* v_xs_2_, lean_object* v_init_3_, lean_object* v_f_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_4(v_inst_1_, lean_box(0), v_xs_2_, v_init_3_, v_f_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_m_8_, lean_object* v_Pred_9_, lean_object* v_00_u03c1_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_xs_13_, lean_object* v_init_14_, lean_object* v_f_15_, lean_object* v_inv_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_apply_4(v_inst_11_, lean_box(0), v_xs_13_, v_init_14_, v_f_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_forInWithInvariant___boxed(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_m_20_, lean_object* v_Pred_21_, lean_object* v_00_u03c1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_xs_25_, lean_object* v_init_26_, lean_object* v_f_27_, lean_object* v_inv_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Internal_Do_ForIn_forInWithInvariant(v_00_u03b1_18_, v_00_u03b2_19_, v_m_20_, v_Pred_21_, v_00_u03c1_22_, v_inst_23_, v_inst_24_, v_xs_25_, v_init_26_, v_f_27_, v_inv_28_);
lean_dec(v_inv_28_);
lean_dec(v_inst_24_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___redArg(lean_object* v_inst_30_, lean_object* v_xs_31_, lean_object* v_init_32_, lean_object* v_f_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_apply_4(v_inst_30_, lean_box(0), v_xs_31_, v_init_32_, v_f_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_m_37_, lean_object* v_Pred_38_, lean_object* v_00_u03c1_39_, lean_object* v_d_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_xs_43_, lean_object* v_init_44_, lean_object* v_f_45_, lean_object* v_inv_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_4(v_inst_41_, lean_box(0), v_xs_43_, v_init_44_, v_f_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27___boxed(lean_object* v_00_u03b1_48_, lean_object* v_00_u03b2_49_, lean_object* v_m_50_, lean_object* v_Pred_51_, lean_object* v_00_u03c1_52_, lean_object* v_d_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_xs_56_, lean_object* v_init_57_, lean_object* v_f_58_, lean_object* v_inv_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Internal_Do_ForIn_x27_forInWithInvariant_x27(v_00_u03b1_48_, v_00_u03b2_49_, v_m_50_, v_Pred_51_, v_00_u03c1_52_, v_d_53_, v_inst_54_, v_inst_55_, v_xs_56_, v_init_57_, v_f_58_, v_inv_59_);
lean_dec(v_inv_59_);
lean_dec(v_inst_55_);
return v_res_60_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_Triple_SpecLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Monadic(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Monadic(builtin);
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
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_Gadget_ForIn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin);
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
