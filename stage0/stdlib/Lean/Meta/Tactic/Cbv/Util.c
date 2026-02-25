// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.Util
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.InferType import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.LitValues
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__14___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__14___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__14_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__15_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__16_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__17_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__18_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__19_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__20 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__20_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__21_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__22_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__23 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__23_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__24 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__24_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__25 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__25_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__26 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_isVal___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__26_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__27 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__27_value;
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_4);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
lean_inc(x_4);
lean_inc_ref(x_2);
x_18 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_10 = x_4;
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Expr_app___override(x_1, x_2);
x_13 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_12, x_10);
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_13);
x_14 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
else
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
if (x_12 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_11);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(x_2, x_16, x_17, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(x_2, x_19, x_20, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Tactic_Cbv_mkAppNS(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getStringValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getBitVecValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getFinValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getCharValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getRatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt8Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt16Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt32Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt64Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt8Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt16Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt32Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt64Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_2, x_1);
x_4 = lean_unbox(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getStringValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getBitVecValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getFinValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getCharValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt8Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt16Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt32Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getUInt64Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt8Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt16Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt32Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__13(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getInt64Value_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__14___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal___lam__14(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_isVal___closed__27));
x_4 = l_List_any___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_Cbv_isVal(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Tactic_Cbv_isVal(x_1);
x_4 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_3);
x_14 = lean_apply_1(x_1, x_3);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_16 = lean_alloc_ctor(0, 0, 1);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, 0, x_17);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_apply_11(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Tactic_Cbv_guardSimproc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(x_3);
if (x_5 == 0)
{
return x_5;
}
else
{
x_1 = x_4;
goto _start;
}
}
case 3:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
x_1 = x_7;
goto _start;
}
default: 
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_instantiate_level_mvars(x_5, x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_st_ref_take(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_7);
x_12 = lean_st_ref_set(x_2, x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 2);
x_16 = lean_ctor_get(x_9, 3);
x_17 = lean_ctor_get(x_9, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(x_1, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_isPropQuick(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
switch (x_12) {
case 0:
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
case 1:
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
default: 
{
lean_object* x_17; 
lean_free_object(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_17 = l_Lean_Meta_Sym_inferType___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_5);
x_19 = l_Lean_Meta_whnfD(x_18, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 3)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(x_22, x_5);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(x_25);
lean_dec(x_25);
x_27 = lean_box(x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; 
lean_dec(x_21);
lean_dec(x_5);
x_32 = 0;
x_33 = lean_box(x_32);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
if (lean_obj_tag(x_34) == 3)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(x_35, x_5);
lean_dec(x_5);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(x_37);
lean_dec(x_37);
x_40 = lean_box(x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
lean_dec(x_5);
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_19);
if (x_45 == 0)
{
return x_19;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
return x_17;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_17, 0);
lean_inc(x_49);
lean_dec(x_17);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
switch (x_52) {
case 0:
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
case 1:
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_56 = 1;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
default: 
{
lean_object* x_59; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_59 = l_Lean_Meta_Sym_inferType___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc(x_5);
x_61 = l_Lean_Meta_whnfD(x_60, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_obj_tag(x_62) == 3)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(x_64, x_5);
lean_dec(x_5);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(x_66);
lean_dec(x_66);
x_69 = lean_box(x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_62);
lean_dec(x_5);
x_71 = 0;
x_72 = lean_box(x_71);
if (lean_is_scalar(x_63)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_63;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_5);
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_77 = lean_ctor_get(x_59, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_78 = x_59;
} else {
 lean_dec_ref(x_59);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_9);
if (x_80 == 0)
{
return x_9;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_9, 0);
lean_inc(x_81);
lean_dec(x_9);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_9 = l_Lean_Meta_isProofQuick(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
switch (x_12) {
case 0:
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
case 1:
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
default: 
{
lean_object* x_17; 
lean_free_object(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_17 = l_Lean_Meta_Sym_inferType___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(x_18, x_2, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
switch (x_24) {
case 0:
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
case 1:
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
default: 
{
lean_object* x_31; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_31 = l_Lean_Meta_Sym_inferType___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 0, 1);
x_13 = lean_unbox(x_11);
lean_dec(x_11);
lean_ctor_set_uint8(x_12, 0, x_13);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 0, 1);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_15, 0, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_Cbv_isProofTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
