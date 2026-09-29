// Lean compiler output
// Module: Init.Data.BitVec.Package
// Imports: public import Init.Data.Order.PackageFactories import Init.Data.BitVec.Lemmas
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instOrdBitVec___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableLeBitVec___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqBitVec___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableLtBitVec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instLinearOrderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instLinearOrderPackage___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instLinearOrderPackage___closed__0 = (const lean_object*)&l_BitVec_instLinearOrderPackage___closed__0_value;
static const lean_closure_object l_BitVec_instLinearOrderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instLinearOrderPackage___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instLinearOrderPackage___closed__1 = (const lean_object*)&l_BitVec_instLinearOrderPackage___closed__1_value;
static const lean_closure_object l_BitVec_instLinearOrderPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdBitVec___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instLinearOrderPackage___closed__2 = (const lean_object*)&l_BitVec_instLinearOrderPackage___closed__2_value;
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__0(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_le(v_a_1_, v_b_2_);
if (v___x_3_ == 0)
{
lean_inc(v_b_2_);
return v_b_2_;
}
else
{
lean_inc(v_a_1_);
return v_a_1_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__0___boxed(lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_BitVec_instLinearOrderPackage___lam__0(v_a_4_, v_b_5_);
lean_dec(v_b_5_);
lean_dec(v_a_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__1(lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_le(v_b_8_, v_a_7_);
if (v___x_9_ == 0)
{
lean_inc(v_b_8_);
return v_b_8_;
}
else
{
lean_inc(v_a_7_);
return v_a_7_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage___lam__1___boxed(lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_BitVec_instLinearOrderPackage___lam__1(v_a_10_, v_b_11_);
lean_dec(v_b_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instLinearOrderPackage(lean_object* v_w_16_){
_start:
{
lean_object* v___f_17_; lean_object* v___f_18_; lean_object* v_this_19_; lean_object* v_this_20_; lean_object* v_this_21_; lean_object* v___x_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___f_17_ = ((lean_object*)(l_BitVec_instLinearOrderPackage___closed__0));
v___f_18_ = ((lean_object*)(l_BitVec_instLinearOrderPackage___closed__1));
v_this_19_ = lean_box(0);
lean_inc_n(v_w_16_, 2);
v_this_20_ = lean_alloc_closure((void*)(l_instDecidableLeBitVec___boxed), 3, 1);
lean_closure_set(v_this_20_, 0, v_w_16_);
v_this_21_ = lean_box(0);
v___x_22_ = lean_alloc_closure((void*)(l_instDecidableEqBitVec___boxed), 3, 1);
lean_closure_set(v___x_22_, 0, v_w_16_);
v___f_23_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_23_, 0, v___x_22_);
v___x_24_ = lean_alloc_closure((void*)(l_instDecidableLtBitVec___boxed), 3, 1);
lean_closure_set(v___x_24_, 0, v_w_16_);
v___f_25_ = ((lean_object*)(l_BitVec_instLinearOrderPackage___closed__2));
v___x_26_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_26_, 0, v_this_19_);
lean_ctor_set(v___x_26_, 1, v_this_21_);
lean_ctor_set(v___x_26_, 2, v___f_23_);
lean_ctor_set(v___x_26_, 3, v_this_20_);
lean_ctor_set(v___x_26_, 4, v___x_24_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___f_25_);
v___x_28_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___f_17_);
lean_ctor_set(v___x_28_, 2, v___f_18_);
return v___x_28_;
}
}
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Package(builtin);
}
#ifdef __cplusplus
}
#endif
