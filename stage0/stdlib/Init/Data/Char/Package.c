// Lean compiler output
// Module: Init.Data.Char.Package
// Imports: public import Init.Data.Order.PackageFactories import Init.Data.Char.Order
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_instOrdChar___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Char_instDecidableLt___boxed(lean_object*, lean_object*);
lean_object* l_Char_instDecidableLe___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Char_instLinearOrderPackage___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instLinearOrderPackage___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Char_instLinearOrderPackage___lam__1(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Char_instLinearOrderPackage___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Char_instLinearOrderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_instLinearOrderPackage___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instLinearOrderPackage___closed__0 = (const lean_object*)&l_Char_instLinearOrderPackage___closed__0_value;
static const lean_closure_object l_Char_instLinearOrderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_instLinearOrderPackage___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instLinearOrderPackage___closed__1 = (const lean_object*)&l_Char_instLinearOrderPackage___closed__1_value;
static const lean_closure_object l_Char_instLinearOrderPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instLinearOrderPackage___closed__2 = (const lean_object*)&l_Char_instLinearOrderPackage___closed__2_value;
static const lean_closure_object l_Char_instLinearOrderPackage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_instDecidableLe___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instLinearOrderPackage___closed__3 = (const lean_object*)&l_Char_instLinearOrderPackage___closed__3_value;
static lean_once_cell_t l_Char_instLinearOrderPackage___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_instLinearOrderPackage___closed__4;
static const lean_closure_object l_Char_instLinearOrderPackage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_instDecidableLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Char_instLinearOrderPackage___closed__5 = (const lean_object*)&l_Char_instLinearOrderPackage___closed__5_value;
static lean_once_cell_t l_Char_instLinearOrderPackage___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_instLinearOrderPackage___closed__6;
static lean_once_cell_t l_Char_instLinearOrderPackage___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_instLinearOrderPackage___closed__7;
static lean_once_cell_t l_Char_instLinearOrderPackage___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Char_instLinearOrderPackage___closed__8;
LEAN_EXPORT lean_object* l_Char_instLinearOrderPackage;
LEAN_EXPORT uint32_t l_Char_instLinearOrderPackage___lam__0(uint32_t v_a_1_, uint32_t v_b_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_uint32_dec_le(v_a_1_, v_b_2_);
if (v___x_3_ == 0)
{
return v_b_2_;
}
else
{
return v_a_1_;
}
}
}
LEAN_EXPORT lean_object* l_Char_instLinearOrderPackage___lam__0___boxed(lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint32_t v_a_boxed_6_; uint32_t v_b_boxed_7_; uint32_t v_res_8_; lean_object* v_r_9_; 
v_a_boxed_6_ = lean_unbox_uint32(v_a_4_);
lean_dec(v_a_4_);
v_b_boxed_7_ = lean_unbox_uint32(v_b_5_);
lean_dec(v_b_5_);
v_res_8_ = l_Char_instLinearOrderPackage___lam__0(v_a_boxed_6_, v_b_boxed_7_);
v_r_9_ = lean_box_uint32(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint32_t l_Char_instLinearOrderPackage___lam__1(uint32_t v_a_10_, uint32_t v_b_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = lean_uint32_dec_le(v_b_11_, v_a_10_);
if (v___x_12_ == 0)
{
return v_b_11_;
}
else
{
return v_a_10_;
}
}
}
LEAN_EXPORT lean_object* l_Char_instLinearOrderPackage___lam__1___boxed(lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
uint32_t v_a_boxed_15_; uint32_t v_b_boxed_16_; uint32_t v_res_17_; lean_object* v_r_18_; 
v_a_boxed_15_ = lean_unbox_uint32(v_a_13_);
lean_dec(v_a_13_);
v_b_boxed_16_ = lean_unbox_uint32(v_b_14_);
lean_dec(v_b_14_);
v_res_17_ = l_Char_instLinearOrderPackage___lam__1(v_a_boxed_15_, v_b_boxed_16_);
v_r_18_ = lean_box_uint32(v_res_17_);
return v_r_18_;
}
}
static lean_object* _init_l_Char_instLinearOrderPackage___closed__4(void){
_start:
{
lean_object* v___x_23_; lean_object* v___f_24_; 
v___x_23_ = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
v___f_24_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_24_, 0, v___x_23_);
return v___f_24_;
}
}
static lean_object* _init_l_Char_instLinearOrderPackage___closed__6(void){
_start:
{
lean_object* v___x_26_; lean_object* v_this_27_; lean_object* v___f_28_; lean_object* v_this_29_; lean_object* v_this_30_; lean_object* v___x_31_; 
v___x_26_ = ((lean_object*)(l_Char_instLinearOrderPackage___closed__5));
v_this_27_ = ((lean_object*)(l_Char_instLinearOrderPackage___closed__3));
v___f_28_ = lean_obj_once(&l_Char_instLinearOrderPackage___closed__4, &l_Char_instLinearOrderPackage___closed__4_once, _init_l_Char_instLinearOrderPackage___closed__4);
v_this_29_ = lean_box(0);
v_this_30_ = lean_box(0);
v___x_31_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_31_, 0, v_this_30_);
lean_ctor_set(v___x_31_, 1, v_this_29_);
lean_ctor_set(v___x_31_, 2, v___f_28_);
lean_ctor_set(v___x_31_, 3, v_this_27_);
lean_ctor_set(v___x_31_, 4, v___x_26_);
return v___x_31_;
}
}
static lean_object* _init_l_Char_instLinearOrderPackage___closed__7(void){
_start:
{
lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___f_32_ = ((lean_object*)(l_Char_instLinearOrderPackage___closed__2));
v___x_33_ = lean_obj_once(&l_Char_instLinearOrderPackage___closed__6, &l_Char_instLinearOrderPackage___closed__6_once, _init_l_Char_instLinearOrderPackage___closed__6);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___f_32_);
return v___x_34_;
}
}
static lean_object* _init_l_Char_instLinearOrderPackage___closed__8(void){
_start:
{
lean_object* v___f_35_; lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___f_35_ = ((lean_object*)(l_Char_instLinearOrderPackage___closed__1));
v___f_36_ = ((lean_object*)(l_Char_instLinearOrderPackage___closed__0));
v___x_37_ = lean_obj_once(&l_Char_instLinearOrderPackage___closed__7, &l_Char_instLinearOrderPackage___closed__7_once, _init_l_Char_instLinearOrderPackage___closed__7);
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___f_36_);
lean_ctor_set(v___x_38_, 2, v___f_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Char_instLinearOrderPackage(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_Char_instLinearOrderPackage___closed__8, &l_Char_instLinearOrderPackage___closed__8_once, _init_l_Char_instLinearOrderPackage___closed__8);
return v___x_39_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Order(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Char_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_instLinearOrderPackage = _init_l_Char_instLinearOrderPackage();
lean_mark_persistent(l_Char_instLinearOrderPackage);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Char_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Char_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Char_Package(builtin);
}
#ifdef __cplusplus
}
#endif
