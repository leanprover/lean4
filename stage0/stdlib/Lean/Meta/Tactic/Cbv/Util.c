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
lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*7);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
lean_inc_ref(v_f_1_);
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref(v___x_16_);
lean_inc_ref(v_a_2_);
v___x_17_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_dec_ref(v___x_17_);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_26_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_16_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_16_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Expr_app___override(v_f_1_, v_a_2_);
v___x_13_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_12_, v___y_11_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0___boxed(lean_object* v_f_34_, lean_object* v_a_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(v_f_34_, v_a_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(lean_object* v_as_44_, size_t v_i_45_, size_t v_stop_46_, lean_object* v_b_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = lean_usize_dec_eq(v_i_45_, v_stop_46_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_array_uget_borrowed(v_as_44_, v_i_45_);
lean_inc(v___x_56_);
v___x_57_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__0(v_b_47_, v___x_56_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; size_t v___x_59_; size_t v___x_60_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref(v___x_57_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_45_, v___x_59_);
v_i_45_ = v___x_60_;
v_b_47_ = v_a_58_;
goto _start;
}
else
{
return v___x_57_;
}
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v_b_47_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1___boxed(lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
size_t v_i_boxed_74_; size_t v_stop_boxed_75_; lean_object* v_res_76_; 
v_i_boxed_74_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_75_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_res_76_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(v_as_63_, v_i_boxed_74_, v_stop_boxed_75_, v_b_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec_ref(v_as_63_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS(lean_object* v_f_77_, lean_object* v_args_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_array_get_size(v_args_78_);
v___x_88_ = lean_nat_dec_lt(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v_f_77_);
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = lean_nat_dec_le(v___x_87_, v___x_87_);
if (v___x_90_ == 0)
{
if (v___x_88_ == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v_f_77_);
return v___x_91_;
}
else
{
size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_87_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(v_args_78_, v___x_92_, v___x_93_, v_f_77_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
return v___x_94_;
}
}
else
{
size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; 
v___x_95_ = ((size_t)0ULL);
v___x_96_ = lean_usize_of_nat(v___x_87_);
v___x_97_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_mkAppNS_spec__1(v_args_78_, v___x_95_, v___x_96_, v_f_77_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS___boxed(lean_object* v_f_98_, lean_object* v_args_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Meta_Tactic_Cbv_mkAppNS(v_f_98_, v_args_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec_ref(v_args_99_);
return v_res_107_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(lean_object* v_e_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
lean_dec_ref(v___x_109_);
v___x_111_ = 1;
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(lean_object* v_e_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(v_e_112_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(lean_object* v_e_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Meta_Sym_getStringValue_x3f(v_e_115_);
if (lean_obj_tag(v___x_116_) == 0)
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
else
{
uint8_t v___x_118_; 
lean_dec_ref(v___x_116_);
v___x_118_ = 1;
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(lean_object* v_e_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(v_e_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(lean_object* v_e_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_122_);
if (lean_obj_tag(v___x_123_) == 0)
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
lean_dec_ref(v___x_123_);
v___x_125_ = 1;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(lean_object* v_e_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(v_e_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(lean_object* v_e_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
lean_dec_ref(v___x_130_);
v___x_132_ = 1;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(lean_object* v_e_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(v_e_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(lean_object* v_e_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
uint8_t v___x_138_; 
v___x_138_ = 0;
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
lean_dec_ref(v___x_137_);
v___x_139_ = 1;
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(lean_object* v_e_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(v_e_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(lean_object* v_e_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_143_);
if (lean_obj_tag(v___x_144_) == 0)
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
lean_dec_ref(v___x_144_);
v___x_146_ = 1;
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(lean_object* v_e_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(v_e_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(lean_object* v_e_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Sym_getRatValue_x3f(v_e_150_);
if (lean_obj_tag(v___x_151_) == 0)
{
uint8_t v___x_152_; 
v___x_152_ = 0;
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
lean_dec_ref(v___x_151_);
v___x_153_ = 1;
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(lean_object* v_e_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(v_e_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(lean_object* v_e_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
else
{
uint8_t v___x_160_; 
lean_dec_ref(v___x_158_);
v___x_160_ = 1;
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(lean_object* v_e_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(v_e_161_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(lean_object* v_e_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
else
{
uint8_t v___x_167_; 
lean_dec_ref(v___x_165_);
v___x_167_ = 1;
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(lean_object* v_e_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(v_e_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(lean_object* v_e_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
lean_dec_ref(v___x_172_);
v___x_174_ = 1;
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(lean_object* v_e_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(v_e_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(lean_object* v_e_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 0;
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
lean_dec_ref(v___x_179_);
v___x_181_ = 1;
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(lean_object* v_e_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(v_e_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(lean_object* v_e_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
uint8_t v___x_187_; 
v___x_187_ = 0;
return v___x_187_;
}
else
{
uint8_t v___x_188_; 
lean_dec_ref(v___x_186_);
v___x_188_ = 1;
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(lean_object* v_e_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(v_e_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(lean_object* v_e_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_192_);
if (lean_obj_tag(v___x_193_) == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
else
{
uint8_t v___x_195_; 
lean_dec_ref(v___x_193_);
v___x_195_ = 1;
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(lean_object* v_e_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(v_e_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(lean_object* v_e_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
else
{
uint8_t v___x_202_; 
lean_dec_ref(v___x_200_);
v___x_202_ = 1;
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(lean_object* v_e_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(v_e_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(lean_object* v_e_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
uint8_t v___x_208_; 
v___x_208_ = 0;
return v___x_208_;
}
else
{
uint8_t v___x_209_; 
lean_dec_ref(v___x_207_);
v___x_209_ = 1;
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value___boxed(lean_object* v_e_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(v_e_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object* v_e_213_, lean_object* v_x_214_){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_apply_1(v_x_214_, v_e_213_);
v___x_216_ = lean_unbox(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object* v_e_217_, lean_object* v_x_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(v_e_217_, v_x_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__1(lean_object* v___y_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_Sym_getNatValue_x3f(v___y_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
else
{
uint8_t v___x_224_; 
lean_dec_ref(v___x_222_);
v___x_224_ = 1;
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(lean_object* v___y_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(v___y_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__2(lean_object* v___y_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Sym_getStringValue_x3f(v___y_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
uint8_t v___x_230_; 
v___x_230_ = 0;
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
lean_dec_ref(v___x_229_);
v___x_231_ = 1;
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(lean_object* v___y_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(v___y_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__3(lean_object* v___y_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_Sym_getIntValue_x3f(v___y_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
else
{
uint8_t v___x_238_; 
lean_dec_ref(v___x_236_);
v___x_238_ = 1;
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(lean_object* v___y_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(v___y_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__4(lean_object* v___y_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v___y_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
else
{
uint8_t v___x_245_; 
lean_dec_ref(v___x_243_);
v___x_245_ = 1;
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(lean_object* v___y_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(v___y_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__5(lean_object* v___y_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Meta_Sym_getFinValue_x3f(v___y_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
else
{
uint8_t v___x_252_; 
lean_dec_ref(v___x_250_);
v___x_252_ = 1;
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(lean_object* v___y_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(v___y_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__6(lean_object* v___y_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Sym_getCharValue_x3f(v___y_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
lean_dec_ref(v___x_257_);
v___x_259_ = 1;
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(lean_object* v___y_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(v___y_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__7(lean_object* v___y_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v___y_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
uint8_t v___x_265_; 
v___x_265_ = 0;
return v___x_265_;
}
else
{
uint8_t v___x_266_; 
lean_dec_ref(v___x_264_);
v___x_266_ = 1;
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(lean_object* v___y_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(v___y_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__8(lean_object* v___y_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v___y_270_);
if (lean_obj_tag(v___x_271_) == 0)
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
lean_dec_ref(v___x_271_);
v___x_273_ = 1;
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(lean_object* v___y_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(v___y_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__9(lean_object* v___y_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v___y_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
uint8_t v___x_279_; 
v___x_279_ = 0;
return v___x_279_;
}
else
{
uint8_t v___x_280_; 
lean_dec_ref(v___x_278_);
v___x_280_ = 1;
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(lean_object* v___y_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(v___y_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__10(lean_object* v___y_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v___y_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
else
{
uint8_t v___x_287_; 
lean_dec_ref(v___x_285_);
v___x_287_ = 1;
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(lean_object* v___y_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(v___y_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__11(lean_object* v___y_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Meta_Sym_getInt8Value_x3f(v___y_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
uint8_t v___x_293_; 
v___x_293_ = 0;
return v___x_293_;
}
else
{
uint8_t v___x_294_; 
lean_dec_ref(v___x_292_);
v___x_294_ = 1;
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(lean_object* v___y_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(v___y_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__12(lean_object* v___y_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Sym_getInt16Value_x3f(v___y_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
else
{
uint8_t v___x_301_; 
lean_dec_ref(v___x_299_);
v___x_301_ = 1;
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(lean_object* v___y_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(v___y_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__13(lean_object* v___y_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Meta_Sym_getInt32Value_x3f(v___y_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
uint8_t v___x_307_; 
v___x_307_ = 0;
return v___x_307_;
}
else
{
uint8_t v___x_308_; 
lean_dec_ref(v___x_306_);
v___x_308_ = 1;
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed(lean_object* v___y_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__13(v___y_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__14(lean_object* v___y_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_Sym_getInt64Value_x3f(v___y_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
else
{
uint8_t v___x_315_; 
lean_dec_ref(v___x_313_);
v___x_315_ = 1;
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__14___boxed(lean_object* v___y_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__14(v___y_316_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal(lean_object* v_e_375_){
_start:
{
lean_object* v___f_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___f_376_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_376_, 0, v_e_375_);
v___x_377_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_isVal___closed__27));
v___x_378_ = l_List_any___redArg(v___x_377_, v___f_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___boxed(lean_object* v_e_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object* v_e_382_){
_start:
{
uint8_t v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_382_);
v___x_385_ = 0;
v___x_386_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_386_, 0, v___x_384_);
lean_ctor_set_uint8(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(lean_object* v_e_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue(lean_object* v_e_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_391_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(lean_object* v_e_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(v_e_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object* v_p_415_, lean_object* v_s_416_, lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; uint8_t v___x_429_; 
lean_inc_ref(v_e_417_);
v___x_428_ = lean_apply_1(v_p_415_, v_e_417_);
v___x_429_ = lean_unbox(v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v_e_417_);
lean_dec_ref(v_s_416_);
v___x_430_ = lean_alloc_ctor(0, 0, 2);
v___x_431_ = lean_unbox(v___x_428_);
lean_ctor_set_uint8(v___x_430_, 0, v___x_431_);
v___x_432_ = lean_unbox(v___x_428_);
lean_ctor_set_uint8(v___x_430_, 1, v___x_432_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_430_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; 
lean_inc(v_a_426_);
lean_inc_ref(v_a_425_);
lean_inc(v_a_424_);
lean_inc_ref(v_a_423_);
lean_inc(v_a_422_);
lean_inc_ref(v_a_421_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc(v_a_418_);
v___x_434_ = lean_apply_11(v_s_416_, v_e_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, lean_box(0));
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(lean_object* v_p_435_, lean_object* v_s_436_, lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v_p_435_, v_s_436_, v_e_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
return v_res_448_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(lean_object* v_x_449_){
_start:
{
switch(lean_obj_tag(v_x_449_))
{
case 0:
{
uint8_t v___x_450_; 
v___x_450_ = 1;
return v___x_450_;
}
case 2:
{
lean_object* v_a_451_; lean_object* v_a_452_; uint8_t v___x_453_; 
v_a_451_ = lean_ctor_get(v_x_449_, 0);
v_a_452_ = lean_ctor_get(v_x_449_, 1);
v___x_453_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_451_);
if (v___x_453_ == 0)
{
return v___x_453_;
}
else
{
v_x_449_ = v_a_452_;
goto _start;
}
}
case 3:
{
lean_object* v_a_455_; 
v_a_455_ = lean_ctor_get(v_x_449_, 1);
v_x_449_ = v_a_455_;
goto _start;
}
default: 
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(lean_object* v_x_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_x_458_);
lean_dec(v_x_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object* v_l_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; lean_object* v_mctx_465_; lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v_cache_470_; lean_object* v_zetaDeltaFVarIds_471_; lean_object* v_postponed_472_; lean_object* v_diag_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
v___x_464_ = lean_st_ref_get(v___y_462_);
v_mctx_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_ref(v_mctx_465_);
lean_dec(v___x_464_);
v___x_466_ = lean_instantiate_level_mvars(v_mctx_465_, v_l_461_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v___x_466_);
v___x_469_ = lean_st_ref_take(v___y_462_);
v_cache_470_ = lean_ctor_get(v___x_469_, 1);
v_zetaDeltaFVarIds_471_ = lean_ctor_get(v___x_469_, 2);
v_postponed_472_ = lean_ctor_get(v___x_469_, 3);
v_diag_473_ = lean_ctor_get(v___x_469_, 4);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_469_, 0);
lean_dec(v_unused_483_);
v___x_475_ = v___x_469_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_diag_473_);
lean_inc(v_postponed_472_);
lean_inc(v_zetaDeltaFVarIds_471_);
lean_inc(v_cache_470_);
lean_dec(v___x_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v_fst_467_);
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_fst_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_cache_470_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_zetaDeltaFVarIds_471_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_postponed_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_diag_473_);
v___x_478_ = v_reuseFailAlloc_481_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_st_ref_set(v___y_462_, v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v_snd_468_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object* v_l_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object* v_l_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_488_, v___y_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object* v_l_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(v_l_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object* v_e_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_514_; 
lean_inc_ref(v_e_506_);
v___x_514_ = l_Lean_Meta_isPropQuick(v_e_506_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_571_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_571_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_571_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_571_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint8_t v___x_519_; 
v___x_519_ = lean_unbox(v_a_515_);
lean_dec(v_a_515_);
switch(v___x_519_)
{
case 0:
{
uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec_ref(v_e_506_);
v___x_520_ = 0;
v___x_521_ = lean_box(v___x_520_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_521_);
v___x_523_ = v___x_517_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
case 1:
{
uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
lean_dec_ref(v_e_506_);
v___x_525_ = 1;
v___x_526_ = lean_box(v___x_525_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_526_);
v___x_528_ = v___x_517_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
default: 
{
lean_object* v___x_530_; 
lean_del_object(v___x_517_);
v___x_530_ = l_Lean_Meta_Sym_inferType___redArg(v_e_506_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref(v___x_530_);
v___x_532_ = l_Lean_Meta_whnfD(v_a_531_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_554_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_554_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_554_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_554_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
if (lean_obj_tag(v_a_533_) == 3)
{
lean_object* v_u_537_; lean_object* v___x_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
lean_del_object(v___x_535_);
v_u_537_ = lean_ctor_get(v_a_533_, 0);
lean_inc(v_u_537_);
lean_dec_ref(v_a_533_);
v___x_538_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_u_537_, v_a_510_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_539_);
lean_dec(v_a_539_);
v___x_544_ = lean_box(v___x_543_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
lean_dec(v_a_533_);
v___x_549_ = 0;
v___x_550_ = lean_box(v___x_549_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_550_);
v___x_552_ = v___x_535_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_532_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_532_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_530_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_530_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec_ref(v_e_506_);
v_a_572_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_514_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_514_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object* v_e_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_e_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_597_; 
lean_inc_ref(v_e_589_);
v___x_597_ = l_Lean_Meta_isProofQuick(v_e_589_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_624_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_624_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_624_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_624_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___x_602_; 
v___x_602_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
switch(v___x_602_)
{
case 0:
{
uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec_ref(v_e_589_);
v___x_603_ = 0;
v___x_604_ = lean_box(v___x_603_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_604_);
v___x_606_ = v___x_600_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
case 1:
{
uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec_ref(v_e_589_);
v___x_608_ = 1;
v___x_609_ = lean_box(v___x_608_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_609_);
v___x_611_ = v___x_600_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
default: 
{
lean_object* v___x_613_; 
lean_del_object(v___x_600_);
v___x_613_ = l_Lean_Meta_Sym_inferType___redArg(v_e_589_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_615_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref(v___x_613_);
v___x_615_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_a_614_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_616_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_613_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_613_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_e_589_);
v_a_625_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_597_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_597_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object* v_e_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_661_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_661_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
uint8_t v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_659_; 
v___x_655_ = 0;
v___x_656_ = lean_alloc_ctor(0, 0, 2);
v___x_657_ = lean_unbox(v_a_651_);
lean_dec(v_a_651_);
lean_ctor_set_uint8(v___x_656_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_656_, 1, v___x_655_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_656_);
v___x_659_ = v___x_653_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_656_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_650_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_650_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_679_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_Tactic_Cbv_isProofTerm(v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems(lean_object* v_e_712_, lean_object* v_acc_713_){
_start:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = l_Lean_Expr_cleanupAnnotations(v_e_712_);
v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v___x_714_);
lean_dec_ref(v_acc_713_);
v___x_716_ = lean_box(0);
return v___x_716_;
}
else
{
lean_object* v_arg_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_arg_717_ = lean_ctor_get(v___x_714_, 1);
lean_inc_ref(v_arg_717_);
v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2));
v___x_720_ = l_Lean_Expr_isConstOf(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec_ref(v___x_718_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_acc_713_);
v___x_722_ = lean_box(0);
return v___x_722_;
}
else
{
lean_object* v_arg_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_arg_723_ = lean_ctor_get(v___x_718_, 1);
lean_inc_ref(v_arg_723_);
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
v___x_725_ = l_Lean_Expr_isApp(v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_acc_713_);
v___x_726_ = lean_box(0);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_724_);
v___x_728_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4));
v___x_729_ = l_Lean_Expr_isConstOf(v___x_727_, v___x_728_);
lean_dec_ref(v___x_727_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec_ref(v_arg_723_);
lean_dec_ref(v_arg_717_);
lean_dec_ref(v_acc_713_);
v___x_730_ = lean_box(0);
return v___x_730_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = lean_array_push(v_acc_713_, v_arg_723_);
v_e_712_ = v_arg_717_;
v_acc_713_ = v___x_731_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec_ref(v___x_718_);
lean_dec_ref(v_arg_717_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v_acc_713_);
return v___x_733_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
}
#ifdef __cplusplus
}
#endif
