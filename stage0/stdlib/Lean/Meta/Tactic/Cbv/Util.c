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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(lean_object* v_e_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_1_);
if (lean_obj_tag(v___x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
lean_dec_ref(v___x_2_);
v___x_4_ = 1;
return v___x_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(lean_object* v_e_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(v_e_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(lean_object* v_e_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Sym_getStringValue_x3f(v_e_8_);
if (lean_obj_tag(v___x_9_) == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
lean_dec_ref(v___x_9_);
v___x_11_ = 1;
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(lean_object* v_e_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(v_e_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(lean_object* v_e_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_15_);
if (lean_obj_tag(v___x_16_) == 0)
{
uint8_t v___x_17_; 
v___x_17_ = 0;
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
lean_dec_ref(v___x_16_);
v___x_18_ = 1;
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(lean_object* v_e_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(v_e_19_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(lean_object* v_e_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_22_);
if (lean_obj_tag(v___x_23_) == 0)
{
uint8_t v___x_24_; 
v___x_24_ = 0;
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
lean_dec_ref(v___x_23_);
v___x_25_ = 1;
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(lean_object* v_e_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(v_e_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(lean_object* v_e_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_29_);
if (lean_obj_tag(v___x_30_) == 0)
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
else
{
uint8_t v___x_32_; 
lean_dec_ref(v___x_30_);
v___x_32_ = 1;
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(lean_object* v_e_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(v_e_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(lean_object* v_e_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_36_);
if (lean_obj_tag(v___x_37_) == 0)
{
uint8_t v___x_38_; 
v___x_38_ = 0;
return v___x_38_;
}
else
{
uint8_t v___x_39_; 
lean_dec_ref(v___x_37_);
v___x_39_ = 1;
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(lean_object* v_e_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(v_e_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(lean_object* v_e_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_Sym_getRatValue_x3f(v_e_43_);
if (lean_obj_tag(v___x_44_) == 0)
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
lean_dec_ref(v___x_44_);
v___x_46_ = 1;
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(lean_object* v_e_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(v_e_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(lean_object* v_e_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_50_);
if (lean_obj_tag(v___x_51_) == 0)
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
lean_dec_ref(v___x_51_);
v___x_53_ = 1;
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(lean_object* v_e_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(v_e_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(lean_object* v_e_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
else
{
uint8_t v___x_60_; 
lean_dec_ref(v___x_58_);
v___x_60_ = 1;
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(lean_object* v_e_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(v_e_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(lean_object* v_e_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_64_);
if (lean_obj_tag(v___x_65_) == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
else
{
uint8_t v___x_67_; 
lean_dec_ref(v___x_65_);
v___x_67_ = 1;
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(lean_object* v_e_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(v_e_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(lean_object* v_e_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_71_);
if (lean_obj_tag(v___x_72_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
else
{
uint8_t v___x_74_; 
lean_dec_ref(v___x_72_);
v___x_74_ = 1;
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(lean_object* v_e_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(v_e_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(lean_object* v_e_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_78_);
if (lean_obj_tag(v___x_79_) == 0)
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
else
{
uint8_t v___x_81_; 
lean_dec_ref(v___x_79_);
v___x_81_ = 1;
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(lean_object* v_e_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(v_e_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(lean_object* v_e_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_85_);
if (lean_obj_tag(v___x_86_) == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
lean_dec_ref(v___x_86_);
v___x_88_ = 1;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(lean_object* v_e_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(v_e_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(lean_object* v_e_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_92_);
if (lean_obj_tag(v___x_93_) == 0)
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
else
{
uint8_t v___x_95_; 
lean_dec_ref(v___x_93_);
v___x_95_ = 1;
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(lean_object* v_e_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(v_e_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(lean_object* v_e_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_99_);
if (lean_obj_tag(v___x_100_) == 0)
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
else
{
uint8_t v___x_102_; 
lean_dec_ref(v___x_100_);
v___x_102_ = 1;
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value___boxed(lean_object* v_e_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(v_e_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object* v_e_106_, lean_object* v_x_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_apply_1(v_x_107_, v_e_106_);
v___x_109_ = lean_unbox(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object* v_e_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(v_e_110_, v_x_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__1(lean_object* v___y_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Sym_getNatValue_x3f(v___y_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
lean_dec_ref(v___x_115_);
v___x_117_ = 1;
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(lean_object* v___y_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(v___y_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__2(lean_object* v___y_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Sym_getStringValue_x3f(v___y_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
lean_dec_ref(v___x_122_);
v___x_124_ = 1;
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(lean_object* v___y_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(v___y_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__3(lean_object* v___y_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Sym_getIntValue_x3f(v___y_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
lean_dec_ref(v___x_129_);
v___x_131_ = 1;
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(lean_object* v___y_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(v___y_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__4(lean_object* v___y_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v___y_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
lean_dec_ref(v___x_136_);
v___x_138_ = 1;
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(lean_object* v___y_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(v___y_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__5(lean_object* v___y_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Sym_getFinValue_x3f(v___y_142_);
if (lean_obj_tag(v___x_143_) == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
lean_dec_ref(v___x_143_);
v___x_145_ = 1;
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(lean_object* v___y_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(v___y_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__6(lean_object* v___y_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Sym_getCharValue_x3f(v___y_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
else
{
uint8_t v___x_152_; 
lean_dec_ref(v___x_150_);
v___x_152_ = 1;
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(lean_object* v___y_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(v___y_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__7(lean_object* v___y_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v___y_156_);
if (lean_obj_tag(v___x_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
else
{
uint8_t v___x_159_; 
lean_dec_ref(v___x_157_);
v___x_159_ = 1;
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(lean_object* v___y_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(v___y_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__8(lean_object* v___y_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v___y_163_);
if (lean_obj_tag(v___x_164_) == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
else
{
uint8_t v___x_166_; 
lean_dec_ref(v___x_164_);
v___x_166_ = 1;
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(lean_object* v___y_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(v___y_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__9(lean_object* v___y_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v___y_170_);
if (lean_obj_tag(v___x_171_) == 0)
{
uint8_t v___x_172_; 
v___x_172_ = 0;
return v___x_172_;
}
else
{
uint8_t v___x_173_; 
lean_dec_ref(v___x_171_);
v___x_173_ = 1;
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(lean_object* v___y_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(v___y_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__10(lean_object* v___y_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v___y_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
uint8_t v___x_179_; 
v___x_179_ = 0;
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
lean_dec_ref(v___x_178_);
v___x_180_ = 1;
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(lean_object* v___y_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(v___y_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__11(lean_object* v___y_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Sym_getInt8Value_x3f(v___y_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
lean_dec_ref(v___x_185_);
v___x_187_ = 1;
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(lean_object* v___y_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(v___y_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__12(lean_object* v___y_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Sym_getInt16Value_x3f(v___y_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
else
{
uint8_t v___x_194_; 
lean_dec_ref(v___x_192_);
v___x_194_ = 1;
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(lean_object* v___y_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(v___y_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__13(lean_object* v___y_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_Sym_getInt32Value_x3f(v___y_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
else
{
uint8_t v___x_201_; 
lean_dec_ref(v___x_199_);
v___x_201_ = 1;
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed(lean_object* v___y_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__13(v___y_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__14(lean_object* v___y_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_Sym_getInt64Value_x3f(v___y_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
uint8_t v___x_207_; 
v___x_207_ = 0;
return v___x_207_;
}
else
{
uint8_t v___x_208_; 
lean_dec_ref(v___x_206_);
v___x_208_ = 1;
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__14___boxed(lean_object* v___y_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__14(v___y_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal(lean_object* v_e_268_){
_start:
{
lean_object* v___f_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___f_269_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed), 2, 1);
lean_closure_set(v___f_269_, 0, v_e_268_);
v___x_270_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_isVal___closed__27));
v___x_271_ = l_List_any___redArg(v___x_270_, v___f_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___boxed(lean_object* v_e_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_272_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object* v_e_275_){
_start:
{
uint8_t v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_275_);
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_279_, 0, v___x_277_);
lean_ctor_set_uint8(v___x_279_, 1, v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(lean_object* v_e_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue(lean_object* v_e_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_284_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(lean_object* v_e_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(v_e_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object* v_p_308_, lean_object* v_s_309_, lean_object* v_e_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
lean_inc_ref(v_e_310_);
v___x_321_ = lean_apply_1(v_p_308_, v_e_310_);
v___x_322_ = lean_unbox(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v_e_310_);
lean_dec_ref(v_s_309_);
v___x_323_ = lean_alloc_ctor(0, 0, 2);
v___x_324_ = lean_unbox(v___x_321_);
lean_ctor_set_uint8(v___x_323_, 0, v___x_324_);
v___x_325_ = lean_unbox(v___x_321_);
lean_ctor_set_uint8(v___x_323_, 1, v___x_325_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_323_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; 
lean_inc(v_a_319_);
lean_inc_ref(v_a_318_);
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
lean_inc(v_a_311_);
v___x_327_ = lean_apply_11(v_s_309_, v_e_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, lean_box(0));
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(lean_object* v_p_328_, lean_object* v_s_329_, lean_object* v_e_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v_p_328_, v_s_329_, v_e_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(lean_object* v_x_342_){
_start:
{
switch(lean_obj_tag(v_x_342_))
{
case 0:
{
uint8_t v___x_343_; 
v___x_343_ = 1;
return v___x_343_;
}
case 2:
{
lean_object* v_a_344_; lean_object* v_a_345_; uint8_t v___x_346_; 
v_a_344_ = lean_ctor_get(v_x_342_, 0);
v_a_345_ = lean_ctor_get(v_x_342_, 1);
v___x_346_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_344_);
if (v___x_346_ == 0)
{
return v___x_346_;
}
else
{
v_x_342_ = v_a_345_;
goto _start;
}
}
case 3:
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v_x_342_, 1);
v_x_342_ = v_a_348_;
goto _start;
}
default: 
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(lean_object* v_x_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_x_351_);
lean_dec(v_x_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object* v_l_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; lean_object* v_mctx_358_; lean_object* v___x_359_; lean_object* v_fst_360_; lean_object* v_snd_361_; lean_object* v___x_362_; lean_object* v_cache_363_; lean_object* v_zetaDeltaFVarIds_364_; lean_object* v_postponed_365_; lean_object* v_diag_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_375_; 
v___x_357_ = lean_st_ref_get(v___y_355_);
v_mctx_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_mctx_358_);
lean_dec(v___x_357_);
v___x_359_ = lean_instantiate_level_mvars(v_mctx_358_, v_l_354_);
v_fst_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_fst_360_);
v_snd_361_ = lean_ctor_get(v___x_359_, 1);
lean_inc(v_snd_361_);
lean_dec_ref(v___x_359_);
v___x_362_ = lean_st_ref_take(v___y_355_);
v_cache_363_ = lean_ctor_get(v___x_362_, 1);
v_zetaDeltaFVarIds_364_ = lean_ctor_get(v___x_362_, 2);
v_postponed_365_ = lean_ctor_get(v___x_362_, 3);
v_diag_366_ = lean_ctor_get(v___x_362_, 4);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_376_);
v___x_368_ = v___x_362_;
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_diag_366_);
lean_inc(v_postponed_365_);
lean_inc(v_zetaDeltaFVarIds_364_);
lean_inc(v_cache_363_);
lean_dec(v___x_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_fst_360_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_fst_360_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_cache_363_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_zetaDeltaFVarIds_364_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_postponed_365_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_diag_366_);
v___x_371_ = v_reuseFailAlloc_374_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_st_ref_set(v___y_355_, v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v_snd_361_);
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object* v_l_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_377_, v___y_378_);
lean_dec(v___y_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object* v_l_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_381_, v___y_385_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object* v_l_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(v_l_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; 
lean_inc_ref(v_e_399_);
v___x_407_ = l_Lean_Meta_isPropQuick(v_e_399_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_464_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_464_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_464_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_464_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
uint8_t v___x_412_; 
v___x_412_ = lean_unbox(v_a_408_);
lean_dec(v_a_408_);
switch(v___x_412_)
{
case 0:
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec_ref(v_e_399_);
v___x_413_ = 0;
v___x_414_ = lean_box(v___x_413_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_414_);
v___x_416_ = v___x_410_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
case 1:
{
uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
lean_dec_ref(v_e_399_);
v___x_418_ = 1;
v___x_419_ = lean_box(v___x_418_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_419_);
v___x_421_ = v___x_410_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
default: 
{
lean_object* v___x_423_; 
lean_del_object(v___x_410_);
v___x_423_ = l_Lean_Meta_Sym_inferType___redArg(v_e_399_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v___x_423_);
v___x_425_ = l_Lean_Meta_whnfD(v_a_424_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_447_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_447_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_447_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_447_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
if (lean_obj_tag(v_a_426_) == 3)
{
lean_object* v_u_430_; lean_object* v___x_431_; lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
lean_del_object(v___x_428_);
v_u_430_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_u_430_);
lean_dec_ref(v_a_426_);
v___x_431_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_u_430_, v_a_403_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_441_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_432_);
lean_dec(v_a_432_);
v___x_437_ = lean_box(v___x_436_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec(v_a_426_);
v___x_442_ = 0;
v___x_443_ = lean_box(v___x_442_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_443_);
v___x_445_ = v___x_428_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_a_448_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_425_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_425_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_423_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_423_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_e_399_);
v_a_465_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_407_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_407_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_e_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
lean_inc_ref(v_e_482_);
v___x_490_ = l_Lean_Meta_isProofQuick(v_e_482_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_517_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_517_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; 
v___x_495_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
switch(v___x_495_)
{
case 0:
{
uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec_ref(v_e_482_);
v___x_496_ = 0;
v___x_497_ = lean_box(v___x_496_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
case 1:
{
uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec_ref(v_e_482_);
v___x_501_ = 1;
v___x_502_ = lean_box(v___x_501_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_502_);
v___x_504_ = v___x_493_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
default: 
{
lean_object* v___x_506_; 
lean_del_object(v___x_493_);
v___x_506_ = l_Lean_Meta_Sym_inferType___redArg(v_e_482_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_a_507_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_a_509_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_506_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_506_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_e_482_);
v_a_518_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_490_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_490_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object* v_e_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object* v_e_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_554_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_554_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
uint8_t v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_552_; 
v___x_548_ = 0;
v___x_549_ = lean_alloc_ctor(0, 0, 2);
v___x_550_ = lean_unbox(v_a_544_);
lean_dec(v_a_544_);
lean_ctor_set_uint8(v___x_549_, 0, v___x_550_);
lean_ctor_set_uint8(v___x_549_, 1, v___x_548_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_549_);
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_543_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_543_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_572_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object* v_e_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_Tactic_Cbv_isProofTerm(v_e_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems(lean_object* v_e_605_, lean_object* v_acc_606_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = l_Lean_Expr_cleanupAnnotations(v_e_605_);
v___x_608_ = l_Lean_Expr_isApp(v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v___x_607_);
lean_dec_ref(v_acc_606_);
v___x_609_ = lean_box(0);
return v___x_609_;
}
else
{
lean_object* v_arg_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_arg_610_ = lean_ctor_get(v___x_607_, 1);
lean_inc_ref(v_arg_610_);
v___x_611_ = l_Lean_Expr_appFnCleanup___redArg(v___x_607_);
v___x_612_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2));
v___x_613_ = l_Lean_Expr_isConstOf(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_Expr_isApp(v___x_611_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_arg_610_);
lean_dec_ref(v_acc_606_);
v___x_615_ = lean_box(0);
return v___x_615_;
}
else
{
lean_object* v_arg_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_arg_616_ = lean_ctor_get(v___x_611_, 1);
lean_inc_ref(v_arg_616_);
v___x_617_ = l_Lean_Expr_appFnCleanup___redArg(v___x_611_);
v___x_618_ = l_Lean_Expr_isApp(v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec_ref(v___x_617_);
lean_dec_ref(v_arg_616_);
lean_dec_ref(v_arg_610_);
lean_dec_ref(v_acc_606_);
v___x_619_ = lean_box(0);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_617_);
v___x_621_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4));
v___x_622_ = l_Lean_Expr_isConstOf(v___x_620_, v___x_621_);
lean_dec_ref(v___x_620_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v_arg_616_);
lean_dec_ref(v_arg_610_);
lean_dec_ref(v_acc_606_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_array_push(v_acc_606_, v_arg_616_);
v_e_605_ = v_arg_610_;
v_acc_606_ = v___x_624_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_626_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_arg_610_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_acc_606_);
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
uint8_t v_contextDependent_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_636_; 
v_contextDependent_628_ = lean_ctor_get_uint8(v_x_627_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_x_627_);
if (v_isSharedCheck_636_ == 0)
{
v___x_630_ = v_x_627_;
v_isShared_631_ = v_isSharedCheck_636_;
goto v_resetjp_629_;
}
else
{
lean_dec(v_x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_636_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v___x_632_; lean_object* v___x_634_; 
v___x_632_ = 1;
if (v_isShared_631_ == 0)
{
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_635_, 1, v_contextDependent_628_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_ctor_set_uint8(v___x_634_, 0, v___x_632_);
return v___x_634_;
}
}
}
else
{
return v_x_627_;
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
