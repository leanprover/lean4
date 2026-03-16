// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Int
// Imports: public import Init.Data.Range.Polymorphic.Instances import Init.Omega
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_once_cell_t l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instUpwardEnumerableInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableInt___closed__0 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__0_value;
static const lean_closure_object l_Std_PRange_instUpwardEnumerableInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableInt___closed__1 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__1_value;
static const lean_ctor_object l_Std_PRange_instUpwardEnumerableInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__0_value),((lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__1_value)}};
static const lean_object* l_Std_PRange_instUpwardEnumerableInt___closed__2 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instUpwardEnumerableInt = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__2_value;
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeInt___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeInt = (const lean_object*)&l_Std_PRange_instHasSizeInt___closed__0_value;
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeInt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeInt__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeInt__1___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeInt__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeInt__1 = (const lean_object*)&l_Std_PRange_instHasSizeInt__1___closed__0_value;
static lean_object* _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0(lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0, &l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once, _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0);
v___x_5_ = lean_int_add(v_x_3_, v___x_4_);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_PRange_instUpwardEnumerableInt___lam__0(v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1(lean_object* v_n_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_nat_to_int(v_n_9_);
v___x_12_ = lean_int_add(v_x_10_, v___x_11_);
lean_dec(v___x_11_);
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(lean_object* v_n_14_, lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_PRange_instUpwardEnumerableInt___lam__1(v_n_14_, v_x_15_);
lean_dec(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0(lean_object* v_lo_23_, lean_object* v_hi_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_25_ = lean_obj_once(&l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0, &l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once, _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0);
v___x_26_ = lean_int_add(v_hi_24_, v___x_25_);
v___x_27_ = lean_int_sub(v___x_26_, v_lo_23_);
lean_dec(v___x_26_);
v___x_28_ = l_Int_toNat(v___x_27_);
lean_dec(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0___boxed(lean_object* v_lo_29_, lean_object* v_hi_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_PRange_instHasSizeInt___lam__0(v_lo_29_, v_hi_30_);
lean_dec(v_hi_30_);
lean_dec(v_lo_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0(lean_object* v_lo_34_, lean_object* v_hi_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_obj_once(&l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0, &l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once, _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0);
v___x_38_ = lean_int_add(v_hi_35_, v___x_37_);
v___x_39_ = lean_int_sub(v___x_38_, v_lo_34_);
lean_dec(v___x_38_);
v___x_40_ = l_Int_toNat(v___x_39_);
lean_dec(v___x_39_);
v___x_41_ = lean_nat_sub(v___x_40_, v___x_36_);
lean_dec(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0___boxed(lean_object* v_lo_42_, lean_object* v_hi_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_PRange_instHasSizeInt__1___lam__0(v_lo_42_, v_hi_43_);
lean_dec(v_hi_43_);
lean_dec(v_lo_42_);
return v_res_44_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Int(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Int(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Int(builtin);
}
#ifdef __cplusplus
}
#endif
