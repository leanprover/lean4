// Lean compiler output
// Module: Init.Data.Fin.Package
// Imports: public import Init.Data.Order.PackageFactories public import Init.Data.Fin.MinMax import Init.Data.Fin.Lemmas import Init.Data.Order.Lemmas import Init.Data.Nat.Compare import Init.ByCases import Init.Data.Nat.Order
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
lean_object* l_Fin_instMin___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Fin_decLe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_decLt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Fin_instMax___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instLinearOrderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instLinearOrderPackage___closed__0 = (const lean_object*)&l_Fin_instLinearOrderPackage___closed__0_value;
static const lean_closure_object l_Fin_instLinearOrderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instMin___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instLinearOrderPackage___closed__1 = (const lean_object*)&l_Fin_instLinearOrderPackage___closed__1_value;
static const lean_closure_object l_Fin_instLinearOrderPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instMax___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instLinearOrderPackage___closed__2 = (const lean_object*)&l_Fin_instLinearOrderPackage___closed__2_value;
LEAN_EXPORT lean_object* l_Fin_instLinearOrderPackage(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLinearOrderPackage(lean_object* v_n_4_){
_start:
{
lean_object* v_this_5_; lean_object* v_this_6_; lean_object* v_this_7_; lean_object* v___x_8_; lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_this_5_ = lean_box(0);
lean_inc_n(v_n_4_, 2);
v_this_6_ = lean_alloc_closure((void*)(l_Fin_decLe___boxed), 3, 1);
lean_closure_set(v_this_6_, 0, v_n_4_);
v_this_7_ = lean_box(0);
v___x_8_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_8_, 0, v_n_4_);
v___f_9_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_9_, 0, v___x_8_);
v___x_10_ = lean_alloc_closure((void*)(l_Fin_decLt___boxed), 3, 1);
lean_closure_set(v___x_10_, 0, v_n_4_);
v___f_11_ = ((lean_object*)(l_Fin_instLinearOrderPackage___closed__0));
v___f_12_ = ((lean_object*)(l_Fin_instLinearOrderPackage___closed__1));
v___f_13_ = ((lean_object*)(l_Fin_instLinearOrderPackage___closed__2));
v___x_14_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_14_, 0, v_this_5_);
lean_ctor_set(v___x_14_, 1, v_this_7_);
lean_ctor_set(v___x_14_, 2, v___f_9_);
lean_ctor_set(v___x_14_, 3, v_this_6_);
lean_ctor_set(v___x_14_, 4, v___x_10_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___f_11_);
v___x_16_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___f_12_);
lean_ctor_set(v___x_16_, 2, v___f_13_);
return v___x_16_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Fin_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Fin_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Fin_Package(builtin);
}
#ifdef __cplusplus
}
#endif
