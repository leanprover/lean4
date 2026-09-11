// Lean compiler output
// Module: Init.Data.Int.Package
// Imports: public import Init.Data.Order.PackageFactories import Init.Data.Int.Order import Init.Data.Int.Compare import Init.Data.Order.Lemmas
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
lean_object* l_Int_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Int_instMin___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Int_instMax___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Int_decLe___boxed(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Int_instLinearOrderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instLinearOrderPackage___closed__0 = (const lean_object*)&l_Int_instLinearOrderPackage___closed__0_value;
static const lean_closure_object l_Int_instLinearOrderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instLinearOrderPackage___closed__1 = (const lean_object*)&l_Int_instLinearOrderPackage___closed__1_value;
static const lean_closure_object l_Int_instLinearOrderPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instLinearOrderPackage___closed__2 = (const lean_object*)&l_Int_instLinearOrderPackage___closed__2_value;
static const lean_closure_object l_Int_instLinearOrderPackage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_decLe___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instLinearOrderPackage___closed__3 = (const lean_object*)&l_Int_instLinearOrderPackage___closed__3_value;
static lean_once_cell_t l_Int_instLinearOrderPackage___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_instLinearOrderPackage___closed__4;
static const lean_closure_object l_Int_instLinearOrderPackage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instLinearOrderPackage___closed__5 = (const lean_object*)&l_Int_instLinearOrderPackage___closed__5_value;
static lean_once_cell_t l_Int_instLinearOrderPackage___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_instLinearOrderPackage___closed__6;
static lean_once_cell_t l_Int_instLinearOrderPackage___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_instLinearOrderPackage___closed__7;
static lean_once_cell_t l_Int_instLinearOrderPackage___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_instLinearOrderPackage___closed__8;
LEAN_EXPORT lean_object* l_Int_instLinearOrderPackage;
static lean_object* _init_l_Int_instLinearOrderPackage___closed__4(void){
_start:
{
lean_object* v___x_5_; lean_object* v___f_6_; 
v___x_5_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___f_6_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_6_, 0, v___x_5_);
return v___f_6_;
}
}
static lean_object* _init_l_Int_instLinearOrderPackage___closed__6(void){
_start:
{
lean_object* v___x_8_; lean_object* v_this_9_; lean_object* v___f_10_; lean_object* v_this_11_; lean_object* v_this_12_; lean_object* v___x_13_; 
v___x_8_ = ((lean_object*)(l_Int_instLinearOrderPackage___closed__5));
v_this_9_ = ((lean_object*)(l_Int_instLinearOrderPackage___closed__3));
v___f_10_ = lean_obj_once(&l_Int_instLinearOrderPackage___closed__4, &l_Int_instLinearOrderPackage___closed__4_once, _init_l_Int_instLinearOrderPackage___closed__4);
v_this_11_ = lean_box(0);
v_this_12_ = lean_box(0);
v___x_13_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_13_, 0, v_this_12_);
lean_ctor_set(v___x_13_, 1, v_this_11_);
lean_ctor_set(v___x_13_, 2, v___f_10_);
lean_ctor_set(v___x_13_, 3, v_this_9_);
lean_ctor_set(v___x_13_, 4, v___x_8_);
return v___x_13_;
}
}
static lean_object* _init_l_Int_instLinearOrderPackage___closed__7(void){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___f_14_ = ((lean_object*)(l_Int_instLinearOrderPackage___closed__0));
v___x_15_ = lean_obj_once(&l_Int_instLinearOrderPackage___closed__6, &l_Int_instLinearOrderPackage___closed__6_once, _init_l_Int_instLinearOrderPackage___closed__6);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___f_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Int_instLinearOrderPackage___closed__8(void){
_start:
{
lean_object* v___f_17_; lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___f_17_ = ((lean_object*)(l_Int_instLinearOrderPackage___closed__2));
v___f_18_ = ((lean_object*)(l_Int_instLinearOrderPackage___closed__1));
v___x_19_ = lean_obj_once(&l_Int_instLinearOrderPackage___closed__7, &l_Int_instLinearOrderPackage___closed__7_once, _init_l_Int_instLinearOrderPackage___closed__7);
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___f_18_);
lean_ctor_set(v___x_20_, 2, v___f_17_);
return v___x_20_;
}
}
static lean_object* _init_l_Int_instLinearOrderPackage(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Int_instLinearOrderPackage___closed__8, &l_Int_instLinearOrderPackage___closed__8_once, _init_l_Int_instLinearOrderPackage___closed__8);
return v___x_21_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Compare(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_instLinearOrderPackage = _init_l_Int_instLinearOrderPackage();
lean_mark_persistent(l_Int_instLinearOrderPackage);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Compare(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Package(builtin);
}
#ifdef __cplusplus
}
#endif
