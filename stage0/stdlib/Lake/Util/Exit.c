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
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_00_u03b1_3_, uint32_t v_rc_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_box_uint32(v_rc_4_);
v___x_6_ = lean_apply_2(v_inst_1_, lean_box(0), v___x_5_);
v___x_7_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed(lean_object* v_inst_8_, lean_object* v_inst_9_, lean_object* v_00_u03b1_10_, lean_object* v_rc_11_){
_start:
{
uint32_t v_rc_boxed_12_; lean_object* v_res_13_; 
v_rc_boxed_12_ = lean_unbox_uint32(v_rc_11_);
lean_dec(v_rc_11_);
v_res_13_ = l_Lake_instMonadExitOfMonadLift___redArg___lam__0(v_inst_8_, v_inst_9_, v_00_u03b1_10_, v_rc_boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___redArg(lean_object* v_inst_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = lean_alloc_closure((void*)(l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_16_, 0, v_inst_15_);
lean_closure_set(v___f_16_, 1, v_inst_14_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift(lean_object* v_m_17_, lean_object* v_n_18_, lean_object* v_inst_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = lean_alloc_closure((void*)(l_Lake_instMonadExitOfMonadLift___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_21_, 0, v_inst_20_);
lean_closure_set(v___f_21_, 1, v_inst_19_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___redArg(lean_object* v_inst_22_, lean_object* v_inst_23_, uint32_t v_rc_24_){
_start:
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 0;
v___x_26_ = lean_uint32_dec_eq(v_rc_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_inst_22_);
v___x_27_ = lean_box_uint32(v_rc_24_);
v___x_28_ = lean_apply_2(v_inst_23_, lean_box(0), v___x_27_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_inst_23_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_apply_2(v_inst_22_, lean_box(0), v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___redArg___boxed(lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_rc_33_){
_start:
{
uint32_t v_rc_boxed_34_; lean_object* v_res_35_; 
v_rc_boxed_34_ = lean_unbox_uint32(v_rc_33_);
lean_dec(v_rc_33_);
v_res_35_ = l_Lake_exitIfErrorCode___redArg(v_inst_31_, v_inst_32_, v_rc_boxed_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode(lean_object* v_m_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, uint32_t v_rc_39_){
_start:
{
uint32_t v___x_40_; uint8_t v___x_41_; 
v___x_40_ = 0;
v___x_41_ = lean_uint32_dec_eq(v_rc_39_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_inst_37_);
v___x_42_ = lean_box_uint32(v_rc_39_);
v___x_43_ = lean_apply_2(v_inst_38_, lean_box(0), v___x_42_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_inst_38_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_apply_2(v_inst_37_, lean_box(0), v___x_44_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___boxed(lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_rc_49_){
_start:
{
uint32_t v_rc_boxed_50_; lean_object* v_res_51_; 
v_rc_boxed_50_ = lean_unbox_uint32(v_rc_49_);
lean_dec(v_rc_49_);
v_res_51_ = l_Lake_exitIfErrorCode(v_m_46_, v_inst_47_, v_inst_48_, v_rc_boxed_50_);
return v_res_51_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_BasicAux(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Exit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
