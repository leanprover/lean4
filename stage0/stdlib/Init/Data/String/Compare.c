// Lean compiler output
// Module: Init.Data.String.Compare
// Imports: public import Init.Data.ByteArray.Lex import Init.Data.String.Basic
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
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLT;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLE;
LEAN_EXPORT uint8_t l_String_decLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instOrd___closed__0 = (const lean_object*)&l_String_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instOrd = (const lean_object*)&l_String_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instLinearOrderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instLinearOrderPackage___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instLinearOrderPackage___closed__0 = (const lean_object*)&l_String_instLinearOrderPackage___closed__0_value;
static const lean_closure_object l_String_instLinearOrderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instLinearOrderPackage___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instLinearOrderPackage___closed__1 = (const lean_object*)&l_String_instLinearOrderPackage___closed__1_value;
static const lean_closure_object l_String_instLinearOrderPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decLE___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instLinearOrderPackage___closed__2 = (const lean_object*)&l_String_instLinearOrderPackage___closed__2_value;
static lean_once_cell_t l_String_instLinearOrderPackage___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_instLinearOrderPackage___closed__3;
static const lean_closure_object l_String_instLinearOrderPackage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instLinearOrderPackage___closed__4 = (const lean_object*)&l_String_instLinearOrderPackage___closed__4_value;
static lean_once_cell_t l_String_instLinearOrderPackage___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_instLinearOrderPackage___closed__5;
static lean_once_cell_t l_String_instLinearOrderPackage___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_instLinearOrderPackage___closed__6;
static lean_once_cell_t l_String_instLinearOrderPackage___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_instLinearOrderPackage___closed__7;
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage;
static lean_object* _init_l_String_instLT(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_String_decidableLT___boxed(lean_object* v_s_u2081_4_, lean_object* v_s_u2082_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = lean_string_dec_lt(v_s_u2081_4_, v_s_u2082_5_);
lean_dec_ref(v_s_u2082_5_);
lean_dec_ref(v_s_u2081_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
static lean_object* _init_l_String_instLE(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT uint8_t l_String_decLE(lean_object* v_s_u2081_9_, lean_object* v_s_u2082_10_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = lean_string_dec_lt(v_s_u2082_10_, v_s_u2081_9_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; 
v___x_12_ = 1;
return v___x_12_;
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_String_decLE___boxed(lean_object* v_s_u2081_14_, lean_object* v_s_u2082_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_String_decLE(v_s_u2081_14_, v_s_u2082_15_);
lean_dec_ref(v_s_u2082_15_);
lean_dec_ref(v_s_u2081_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT lean_object* l_String_compare___boxed(lean_object* v_s_u2081_20_, lean_object* v_s_u2082_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = lean_string_compare(v_s_u2081_20_, v_s_u2082_21_);
lean_dec_ref(v_s_u2082_21_);
lean_dec_ref(v_s_u2081_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__0(lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l_String_decLE(v_a_26_, v_b_27_);
if (v___x_28_ == 0)
{
lean_inc_ref(v_b_27_);
return v_b_27_;
}
else
{
lean_inc_ref(v_a_26_);
return v_a_26_;
}
}
}
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__0___boxed(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_String_instLinearOrderPackage___lam__0(v_a_29_, v_b_30_);
lean_dec_ref(v_b_30_);
lean_dec_ref(v_a_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__1(lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_String_decLE(v_b_33_, v_a_32_);
if (v___x_34_ == 0)
{
lean_inc_ref(v_b_33_);
return v_b_33_;
}
else
{
lean_inc_ref(v_a_32_);
return v_a_32_;
}
}
}
LEAN_EXPORT lean_object* l_String_instLinearOrderPackage___lam__1___boxed(lean_object* v_a_35_, lean_object* v_b_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_String_instLinearOrderPackage___lam__1(v_a_35_, v_b_36_);
lean_dec_ref(v_b_36_);
lean_dec_ref(v_a_35_);
return v_res_37_;
}
}
static lean_object* _init_l_String_instLinearOrderPackage___closed__3(void){
_start:
{
lean_object* v___x_41_; lean_object* v___f_42_; 
v___x_41_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_42_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_42_, 0, v___x_41_);
return v___f_42_;
}
}
static lean_object* _init_l_String_instLinearOrderPackage___closed__5(void){
_start:
{
lean_object* v___x_44_; lean_object* v_this_45_; lean_object* v___f_46_; lean_object* v_this_47_; lean_object* v_this_48_; lean_object* v___x_49_; 
v___x_44_ = ((lean_object*)(l_String_instLinearOrderPackage___closed__4));
v_this_45_ = ((lean_object*)(l_String_instLinearOrderPackage___closed__2));
v___f_46_ = lean_obj_once(&l_String_instLinearOrderPackage___closed__3, &l_String_instLinearOrderPackage___closed__3_once, _init_l_String_instLinearOrderPackage___closed__3);
v_this_47_ = lean_box(0);
v_this_48_ = lean_box(0);
v___x_49_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_49_, 0, v_this_48_);
lean_ctor_set(v___x_49_, 1, v_this_47_);
lean_ctor_set(v___x_49_, 2, v___f_46_);
lean_ctor_set(v___x_49_, 3, v_this_45_);
lean_ctor_set(v___x_49_, 4, v___x_44_);
return v___x_49_;
}
}
static lean_object* _init_l_String_instLinearOrderPackage___closed__6(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((lean_object*)(l_String_instOrd___closed__0));
v___x_51_ = lean_obj_once(&l_String_instLinearOrderPackage___closed__5, &l_String_instLinearOrderPackage___closed__5_once, _init_l_String_instLinearOrderPackage___closed__5);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_String_instLinearOrderPackage___closed__7(void){
_start:
{
lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___f_53_ = ((lean_object*)(l_String_instLinearOrderPackage___closed__1));
v___f_54_ = ((lean_object*)(l_String_instLinearOrderPackage___closed__0));
v___x_55_ = lean_obj_once(&l_String_instLinearOrderPackage___closed__6, &l_String_instLinearOrderPackage___closed__6_once, _init_l_String_instLinearOrderPackage___closed__6);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___f_54_);
lean_ctor_set(v___x_56_, 2, v___f_53_);
return v___x_56_;
}
}
static lean_object* _init_l_String_instLinearOrderPackage(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_String_instLinearOrderPackage___closed__7, &l_String_instLinearOrderPackage___closed__7_once, _init_l_String_instLinearOrderPackage___closed__7);
return v___x_57_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Lex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Compare(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instLT = _init_l_String_instLT();
lean_mark_persistent(l_String_instLT);
l_String_instLE = _init_l_String_instLE();
lean_mark_persistent(l_String_instLE);
l_String_instLinearOrderPackage = _init_l_String_instLinearOrderPackage();
lean_mark_persistent(l_String_instLinearOrderPackage);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Compare(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Compare(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Compare(builtin);
}
#ifdef __cplusplus
}
#endif
