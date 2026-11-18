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
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg(){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(l_Std_WP_instEPostSlotFun___redArg___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_WP_instEPostSlotFun___redArg();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotFun(lean_object* v_00_u03b5_14_, lean_object* v_EPred_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = ((lean_object*)(l_Std_WP_instEPostSlotFun___redArg___closed__0));
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg___lam__0(lean_object* v_R_17_, lean_object* v_eposts_18_){
_start:
{
lean_object* v_snd_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
v_snd_19_ = lean_ctor_get(v_eposts_18_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_eposts_18_);
if (v_isSharedCheck_26_ == 0)
{
lean_object* v_unused_27_; 
v_unused_27_ = lean_ctor_get(v_eposts_18_, 0);
lean_dec(v_unused_27_);
v___x_21_ = v_eposts_18_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snd_19_);
lean_dec(v_eposts_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v_R_17_);
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_R_17_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_snd_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg(){
_start:
{
lean_object* v___f_30_; 
v___f_30_ = ((lean_object*)(l_Std_WP_instEPostSlotHead___redArg___closed__0));
return v___f_30_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead___redArg___boxed(lean_object* v___dummy_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_WP_instEPostSlotHead___redArg();
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotHead(lean_object* v_00_u03b5_33_, lean_object* v_EPred_34_, lean_object* v_EPosts_35_){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = ((lean_object*)(l_Std_WP_instEPostSlotHead___redArg___closed__0));
return v___f_36_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail___redArg___lam__0(lean_object* v_inst_37_, lean_object* v_R_38_, lean_object* v_eposts_39_){
_start:
{
lean_object* v_fst_40_; lean_object* v_snd_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_49_; 
v_fst_40_ = lean_ctor_get(v_eposts_39_, 0);
v_snd_41_ = lean_ctor_get(v_eposts_39_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_eposts_39_);
if (v_isSharedCheck_49_ == 0)
{
v___x_43_ = v_eposts_39_;
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_snd_41_);
lean_inc(v_fst_40_);
lean_dec(v_eposts_39_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_45_ = lean_apply_2(v_inst_37_, v_R_38_, v_snd_41_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v___x_45_);
v___x_47_ = v___x_43_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_fst_40_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_45_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail___redArg(lean_object* v_inst_50_){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = lean_alloc_closure((void*)(l_Std_WP_instEPostSlotTail___redArg___lam__0), 3, 1);
lean_closure_set(v___f_51_, 0, v_inst_50_);
return v___f_51_;
}
}
LEAN_EXPORT lean_object* l_Std_WP_instEPostSlotTail(lean_object* v_00_u03b5_52_, lean_object* v_00_u03b5_x27_53_, lean_object* v_EPred_54_, lean_object* v_EPred_x27_55_, lean_object* v_EPosts_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___f_58_; 
v___f_58_ = lean_alloc_closure((void*)(l_Std_WP_instEPostSlotTail___redArg___lam__0), 3, 1);
lean_closure_set(v___f_58_, 0, v_inst_57_);
return v___f_58_;
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
