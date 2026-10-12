// Lean compiler output
// Module: Lake.Util.Exit
// Imports: public import Init.Notation import Init.Data.UInt.BasicAux
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___redArg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode(lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadExitOfMonadLift___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_00_u03b1_3_, uint32_t v_rc_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_box_uint32(v_rc_4_);
v___x_6_ = lean_apply_2(v_inst_1_, lean_box(0), v___x_5_);
v___x_7_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Lake_instMonadExitOfMonadLift___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
uint32_t v_rc_4_ = stack[3].m_num;
lean_object* v_res_8_;
v_res_8_ = l_Lake_instMonadExitOfMonadLift___redArg___lam__0(v_inst_1_, v_inst_2_, lean_box(0), v_rc_4_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed(lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_00_u03b1_11_, lean_object* v_rc_12_){
_start:
{
uint32_t v_rc_boxed_13_; lean_object* v_res_14_; 
v_rc_boxed_13_ = lean_unbox_uint32(v_rc_12_);
lean_dec(v_rc_12_);
v_res_14_ = l_Lake_instMonadExitOfMonadLift___redArg___lam__0(v_inst_9_, v_inst_10_, v_00_u03b1_11_, v_rc_boxed_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg(lean_object* v_inst_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___f_17_; 
v___f_17_ = lean_alloc_closure((void*)(l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_17_, 0, v_inst_16_);
lean_closure_set(v___f_17_, 1, v_inst_15_);
return v___f_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift(lean_object* v_m_18_, lean_object* v_n_19_, lean_object* v_inst_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = lean_alloc_closure((void*)(l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_22_, 0, v_inst_21_);
lean_closure_set(v___f_22_, 1, v_inst_20_);
return v___f_22_;
}
}
lean_object* l_Lake_exitIfErrorCode___redArg(lean_object* v_inst_23_, lean_object* v_inst_24_, uint32_t v_rc_25_){
_start:
{
uint32_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = 0;
v___x_27_ = lean_uint32_dec_eq(v_rc_25_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec(v_inst_23_);
v___x_28_ = lean_box_uint32(v_rc_25_);
v___x_29_ = lean_apply_2(v_inst_24_, lean_box(0), v___x_28_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
lean_dec(v_inst_24_);
v___x_30_ = lean_box(0);
v___x_31_ = lean_apply_2(v_inst_23_, lean_box(0), v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT void l_Lake_exitIfErrorCode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_23_ = stack[0].m_obj;
lean_object* v_inst_24_ = stack[1].m_obj;
uint32_t v_rc_25_ = stack[2].m_num;
lean_object* v_res_32_;
v_res_32_ = l_Lake_exitIfErrorCode___redArg(v_inst_23_, v_inst_24_, v_rc_25_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___redArg___boxed(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_rc_35_){
_start:
{
uint32_t v_rc_boxed_36_; lean_object* v_res_37_; 
v_rc_boxed_36_ = lean_unbox_uint32(v_rc_35_);
lean_dec(v_rc_35_);
v_res_37_ = l_Lake_exitIfErrorCode___redArg(v_inst_33_, v_inst_34_, v_rc_boxed_36_);
return v_res_37_;
}
}
lean_object* l_Lake_exitIfErrorCode(lean_object* v_m_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, uint32_t v_rc_41_){
_start:
{
uint32_t v___x_42_; uint8_t v___x_43_; 
v___x_42_ = 0;
v___x_43_ = lean_uint32_dec_eq(v_rc_41_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_inst_39_);
v___x_44_ = lean_box_uint32(v_rc_41_);
v___x_45_ = lean_apply_2(v_inst_40_, lean_box(0), v___x_44_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_inst_40_);
v___x_46_ = lean_box(0);
v___x_47_ = lean_apply_2(v_inst_39_, lean_box(0), v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT void l_Lake_exitIfErrorCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_39_ = stack[1].m_obj;
lean_object* v_inst_40_ = stack[2].m_obj;
uint32_t v_rc_41_ = stack[3].m_num;
lean_object* v_res_48_;
v_res_48_ = l_Lake_exitIfErrorCode(lean_box(0), v_inst_39_, v_inst_40_, v_rc_41_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___boxed(lean_object* v_m_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_rc_52_){
_start:
{
uint32_t v_rc_boxed_53_; lean_object* v_res_54_; 
v_rc_boxed_53_ = lean_unbox_uint32(v_rc_52_);
lean_dec(v_rc_52_);
v_res_54_ = l_Lake_exitIfErrorCode(v_m_49_, v_inst_50_, v_inst_51_, v_rc_boxed_53_);
return v_res_54_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Exit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Exit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Exit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Exit(builtin);
}
#ifdef __cplusplus
}
#endif
