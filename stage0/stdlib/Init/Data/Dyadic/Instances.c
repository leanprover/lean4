// Lean compiler output
// Module: Init.Data.Dyadic.Instances
// Imports: public import Init.Data.Dyadic.Basic public import Init.Grind.Ordered.Ring import Init.Data.Rat.Lemmas
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
lean_object* l_Dyadic_pow(lean_object*, lean_object*);
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Dyadic_instNatCast___lam__0(lean_object*);
lean_object* l_Dyadic_sub(lean_object*, lean_object*);
lean_object* l_Dyadic_ofInt(lean_object*);
lean_object* l_Dyadic_mul(lean_object*, lean_object*);
lean_object* l_Dyadic_neg(lean_object*);
lean_object* l_Dyadic_instOfNat(lean_object*);
lean_object* l_Dyadic_mul___boxed(lean_object*, lean_object*);
lean_object* l_Dyadic_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instCommRing___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instCommRing___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instCommRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_instCommRing___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__0 = (const lean_object*)&l_Dyadic_instCommRing___closed__0_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_instCommRing___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__1 = (const lean_object*)&l_Dyadic_instCommRing___closed__1_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__2 = (const lean_object*)&l_Dyadic_instCommRing___closed__2_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__3 = (const lean_object*)&l_Dyadic_instCommRing___closed__3_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_instNatCast___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__4 = (const lean_object*)&l_Dyadic_instCommRing___closed__4_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_pow, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__5 = (const lean_object*)&l_Dyadic_instCommRing___closed__5_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Dyadic_instCommRing___closed__5_value)} };
static const lean_object* l_Dyadic_instCommRing___closed__6 = (const lean_object*)&l_Dyadic_instCommRing___closed__6_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__7 = (const lean_object*)&l_Dyadic_instCommRing___closed__7_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_sub, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__8 = (const lean_object*)&l_Dyadic_instCommRing___closed__8_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_ofInt, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__9 = (const lean_object*)&l_Dyadic_instCommRing___closed__9_value;
static const lean_closure_object l_Dyadic_instCommRing___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_instOfNat, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instCommRing___closed__10 = (const lean_object*)&l_Dyadic_instCommRing___closed__10_value;
static const lean_ctor_object l_Dyadic_instCommRing___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Dyadic_instCommRing___closed__2_value),((lean_object*)&l_Dyadic_instCommRing___closed__3_value),((lean_object*)&l_Dyadic_instCommRing___closed__4_value),((lean_object*)&l_Dyadic_instCommRing___closed__10_value),((lean_object*)&l_Dyadic_instCommRing___closed__0_value),((lean_object*)&l_Dyadic_instCommRing___closed__6_value)}};
static const lean_object* l_Dyadic_instCommRing___closed__11 = (const lean_object*)&l_Dyadic_instCommRing___closed__11_value;
static const lean_ctor_object l_Dyadic_instCommRing___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Dyadic_instCommRing___closed__11_value),((lean_object*)&l_Dyadic_instCommRing___closed__7_value),((lean_object*)&l_Dyadic_instCommRing___closed__8_value),((lean_object*)&l_Dyadic_instCommRing___closed__9_value),((lean_object*)&l_Dyadic_instCommRing___closed__1_value)}};
static const lean_object* l_Dyadic_instCommRing___closed__12 = (const lean_object*)&l_Dyadic_instCommRing___closed__12_value;
LEAN_EXPORT const lean_object* l_Dyadic_instCommRing = (const lean_object*)&l_Dyadic_instCommRing___closed__12_value;
LEAN_EXPORT lean_object* l_Dyadic_instCommRing___lam__0(lean_object* v_x1_1_, lean_object* v_x2_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Dyadic_instNatCast___lam__0(v_x1_1_);
v___x_4_ = l_Dyadic_mul(v___x_3_, v_x2_2_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instCommRing___lam__1(lean_object* v_x1_5_, lean_object* v_x2_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = l_Dyadic_ofInt(v_x1_5_);
v___x_8_ = l_Dyadic_mul(v___x_7_, v_x2_6_);
lean_dec(v___x_7_);
return v___x_8_;
}
}
lean_object* runtime_initialize_Init_Data_Dyadic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Dyadic_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Dyadic_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Dyadic_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Dyadic_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Dyadic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Dyadic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Dyadic_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
