// Lean compiler output
// Module: Init.Data.Nat.Div.Basic
// Imports: public import Init.Data.NeZero public import Init.WF meta import Init.MetaTypes import Init.WFTactics
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instDvd;
LEAN_EXPORT lean_object* l_Nat_div_inductionOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div_exact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_instDvd(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn___redArg(lean_object* v_x_2_, lean_object* v_y_3_, lean_object* v_ind_4_, lean_object* v_base_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_nat_dec_lt(v___x_6_, v_y_3_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
lean_dec(v_ind_4_);
v___x_8_ = lean_apply_3(v_base_5_, v_x_2_, v_y_3_, lean_box(0));
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_le(v_y_3_, v_x_2_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_ind_4_);
v___x_10_ = lean_apply_3(v_base_5_, v_x_2_, v_y_3_, lean_box(0));
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_nat_sub(v_x_2_, v_y_3_);
lean_inc(v_ind_4_);
lean_inc(v_y_3_);
v___x_12_ = l_Nat_div_inductionOn___redArg(v___x_11_, v_y_3_, v_ind_4_, v_base_5_);
v___x_13_ = lean_apply_4(v_ind_4_, v_x_2_, v_y_3_, lean_box(0), v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_y_16_, lean_object* v_ind_17_, lean_object* v_base_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Nat_div_inductionOn___redArg(v_x_15_, v_y_16_, v_ind_17_, v_base_18_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Nat_divExact_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_20_ = stack[0].m_obj;
lean_object* v_y_21_ = stack[1].m_obj;
lean_object* v_res_23_;
v_res_23_ = lean_nat_div_exact(v_x_20_, v_y_21_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object* v_x_24_, lean_object* v_y_25_, lean_object* v_h_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lean_nat_div_exact(v_x_24_, v_y_25_);
lean_dec(v_y_25_);
lean_dec(v_x_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object* v_x_28_, lean_object* v_y_29_, lean_object* v_ind_30_, lean_object* v_base_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Nat_div_inductionOn___redArg(v_x_28_, v_y_29_, v_ind_30_, v_base_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object* v_motive_33_, lean_object* v_x_34_, lean_object* v_y_35_, lean_object* v_ind_36_, lean_object* v_base_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Nat_div_inductionOn___redArg(v_x_34_, v_y_35_, v_ind_36_, v_base_37_);
return v___x_38_;
}
}
lean_object* runtime_initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_NeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_instDvd = _init_l_Nat_instDvd();
lean_mark_persistent(l_Nat_instDvd);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_NeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Div_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
