// Lean compiler output
// Module: Init.GrindInstances.Ring.Int
// Imports: public import Init.Grind.Ring.Basic public import Init.Data.Int.Lemmas public import Init.Data.Int.Pow import Init.Data.Int.DivMod.Lemmas import Init.Meta
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
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__0_value;
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__1_value;
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__2_value;
lean_object* l_Int_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__3_value;
lean_object* l_instPowNat___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instPowNat___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt___closed__3_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__4_value;
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__5_value;
lean_object* l_Int_neg___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__6_value;
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__7_value;
lean_object* l_instIntCastInt___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instIntCastInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__8_value;
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt___closed__2_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__9_value;
lean_object* l_instOfNat(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOfNat, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt___closed__10_value;
lean_object* l_Int_ofNat___boxed(lean_object*);
static lean_object* l_Lean_Grind_instCommRingInt___closed__11;
static lean_object* l_Lean_Grind_instCommRingInt___closed__12;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt;
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_to_int(x_1);
x_4 = lean_int_mul(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_instCommRingInt___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__5));
x_2 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__0));
x_3 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__10));
x_4 = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
x_5 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__2));
x_6 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__1));
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__9));
x_2 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__8));
x_3 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__7));
x_4 = ((lean_object*)(l_Lean_Grind_instCommRingInt___closed__6));
x_5 = l_Lean_Grind_instCommRingInt___closed__11;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Grind_instCommRingInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instCommRingInt___closed__12;
return x_1;
}
}
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instCommRingInt___closed__11 = _init_l_Lean_Grind_instCommRingInt___closed__11();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__11);
l_Lean_Grind_instCommRingInt___closed__12 = _init_l_Lean_Grind_instCommRingInt___closed__12();
lean_mark_persistent(l_Lean_Grind_instCommRingInt___closed__12);
l_Lean_Grind_instCommRingInt = _init_l_Lean_Grind_instCommRingInt();
lean_mark_persistent(l_Lean_Grind_instCommRingInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
