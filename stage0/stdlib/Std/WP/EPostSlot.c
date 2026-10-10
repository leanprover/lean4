// Lean compiler output
// Module: Std.WP.EPostSlot
// Imports: public import Std.WP.Assertion public import Std.WP.EStack
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
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_WP_instEPostSlotFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_WP_instEPostSlotFun___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_WP_instEPostSlotFun___redArg___closed__0 = (const lean_object*)&l_Std_WP_instEPostSlotFun___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg();
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_WP_instEPostSlotHead___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_WP_instEPostSlotHead___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_WP_instEPostSlotHead___redArg___closed__0 = (const lean_object*)&l_Std_WP_instEPostSlotHead___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg();
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg___lam__0(lean_object* v_R_1_, lean_object* v_x_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_1(v_R_1_, v___y_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg___lam__0___boxed(lean_object* v_R_5_, lean_object* v_x_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_WP_instEPostSlotFun___redArg___lam__0(v_R_5_, v_x_6_, v___y_7_);
lean_dec(v_x_6_);
return v_res_8_;
}
}
lean_object* l_Std_WP_instEPostSlotFun___redArg(){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(l_Std_WP_instEPostSlotFun___redArg___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT void l_Std_WP_instEPostSlotFun___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_12_;
v_res_12_ = l_Std_WP_instEPostSlotFun___redArg();
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_WP_instEPostSlotFun___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun(lean_object* v_00_u03b5_15_, lean_object* v_EPred_16_){
_start:
{
lean_object* v___f_17_; 
v___f_17_ = ((lean_object*)(l_Std_WP_instEPostSlotFun___redArg___closed__0));
return v___f_17_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg___lam__0(lean_object* v_R_18_, lean_object* v_eposts_19_){
_start:
{
lean_object* v_snd_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
v_snd_20_ = lean_ctor_get(v_eposts_19_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_eposts_19_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v_eposts_19_, 0);
lean_dec(v_unused_28_);
v___x_22_ = v_eposts_19_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_snd_20_);
lean_dec(v_eposts_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v_R_18_);
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_R_18_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_snd_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
lean_object* l_Std_WP_instEPostSlotHead___redArg(){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = ((lean_object*)(l_Std_WP_instEPostSlotHead___redArg___closed__0));
return v___f_31_;
}
}
LEAN_EXPORT void l_Std_WP_instEPostSlotHead___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_32_;
v_res_32_ = l_Std_WP_instEPostSlotHead___redArg();
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_WP_instEPostSlotHead___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead(lean_object* v_00_u03b5_35_, lean_object* v_EPred_36_, lean_object* v_EPosts_37_){
_start:
{
lean_object* v___f_38_; 
v___f_38_ = ((lean_object*)(l_Std_WP_instEPostSlotHead___redArg___closed__0));
return v___f_38_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail___redArg___lam__0(lean_object* v_inst_39_, lean_object* v_R_40_, lean_object* v_eposts_41_){
_start:
{
lean_object* v_fst_42_; lean_object* v_snd_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_fst_42_ = lean_ctor_get(v_eposts_41_, 0);
v_snd_43_ = lean_ctor_get(v_eposts_41_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_eposts_41_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v_eposts_41_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_snd_43_);
lean_inc(v_fst_42_);
lean_dec(v_eposts_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_apply_2(v_inst_39_, v_R_40_, v_snd_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_fst_42_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail___redArg(lean_object* v_inst_52_){
_start:
{
lean_object* v___f_53_; 
v___f_53_ = lean_alloc_closure((void*)(l_Std_WP_instEPostSlotTail___redArg___lam__0), 3, 1);
lean_closure_set(v___f_53_, 0, v_inst_52_);
return v___f_53_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail(lean_object* v_00_u03b5_54_, lean_object* v_00_u03b5_x27_55_, lean_object* v_EPred_56_, lean_object* v_EPred_x27_57_, lean_object* v_EPosts_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v___f_60_; 
v___f_60_ = lean_alloc_closure((void*)(l_Std_WP_instEPostSlotTail___redArg___lam__0), 3, 1);
lean_closure_set(v___f_60_, 0, v_inst_59_);
return v___f_60_;
}
}
lean_object* runtime_initialize_Std_WP_Assertion(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_EStack(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_WP_EPostSlot(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_WP_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_EStack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_WP_EPostSlot(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_WP_Assertion(uint8_t builtin);
lean_object* initialize_Std_WP_EStack(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_WP_EPostSlot(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_WP_Assertion(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_EStack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_EPostSlot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_WP_EPostSlot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_WP_EPostSlot(builtin);
}
#ifdef __cplusplus
}
#endif
