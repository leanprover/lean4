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
lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object* v___y_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Meta_Sym_getNatValue_x3f(v___y_106_);
if (lean_obj_tag(v___x_107_) == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
else
{
uint8_t v___x_109_; 
lean_dec_ref(v___x_107_);
v___x_109_ = 1;
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object* v___y_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(v___y_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__1(lean_object* v___y_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Sym_getStringValue_x3f(v___y_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
lean_dec_ref(v___x_114_);
v___x_116_ = 1;
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(lean_object* v___y_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(v___y_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__2(lean_object* v___y_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Sym_getIntValue_x3f(v___y_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
lean_dec_ref(v___x_121_);
v___x_123_ = 1;
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(lean_object* v___y_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(v___y_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__3(lean_object* v___y_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v___y_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
lean_dec_ref(v___x_128_);
v___x_130_ = 1;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(lean_object* v___y_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(v___y_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__4(lean_object* v___y_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Sym_getFinValue_x3f(v___y_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
else
{
uint8_t v___x_137_; 
lean_dec_ref(v___x_135_);
v___x_137_ = 1;
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(lean_object* v___y_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(v___y_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__5(lean_object* v___y_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Sym_getCharValue_x3f(v___y_141_);
if (lean_obj_tag(v___x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
lean_dec_ref(v___x_142_);
v___x_144_ = 1;
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(lean_object* v___y_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(v___y_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__6(lean_object* v___y_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v___y_148_);
if (lean_obj_tag(v___x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
lean_dec_ref(v___x_149_);
v___x_151_ = 1;
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(lean_object* v___y_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(v___y_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__7(lean_object* v___y_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v___y_155_);
if (lean_obj_tag(v___x_156_) == 0)
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
lean_dec_ref(v___x_156_);
v___x_158_ = 1;
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(lean_object* v___y_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(v___y_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__8(lean_object* v___y_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v___y_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = 0;
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
lean_dec_ref(v___x_163_);
v___x_165_ = 1;
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(lean_object* v___y_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(v___y_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__9(lean_object* v___y_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v___y_169_);
if (lean_obj_tag(v___x_170_) == 0)
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
lean_dec_ref(v___x_170_);
v___x_172_ = 1;
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(lean_object* v___y_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(v___y_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__10(lean_object* v___y_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_Sym_getInt8Value_x3f(v___y_176_);
if (lean_obj_tag(v___x_177_) == 0)
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
else
{
uint8_t v___x_179_; 
lean_dec_ref(v___x_177_);
v___x_179_ = 1;
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(lean_object* v___y_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(v___y_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__11(lean_object* v___y_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Sym_getInt16Value_x3f(v___y_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
else
{
uint8_t v___x_186_; 
lean_dec_ref(v___x_184_);
v___x_186_ = 1;
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(lean_object* v___y_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(v___y_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__12(lean_object* v___y_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Sym_getInt32Value_x3f(v___y_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
uint8_t v___x_192_; 
v___x_192_ = 0;
return v___x_192_;
}
else
{
uint8_t v___x_193_; 
lean_dec_ref(v___x_191_);
v___x_193_ = 1;
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(lean_object* v___y_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(v___y_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__13(lean_object* v___y_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_Sym_getInt64Value_x3f(v___y_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
lean_dec_ref(v___x_198_);
v___x_200_ = 1;
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed(lean_object* v___y_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__13(v___y_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(lean_object* v_e_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
uint8_t v___x_206_; 
lean_dec_ref(v_e_204_);
v___x_206_ = 0;
return v___x_206_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_head_207_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_head_207_);
v_tail_208_ = lean_ctor_get(v_x_205_, 1);
lean_inc(v_tail_208_);
lean_dec_ref(v_x_205_);
lean_inc_ref(v_e_204_);
v___x_209_ = lean_apply_1(v_head_207_, v_e_204_);
v___x_210_ = lean_unbox(v___x_209_);
if (v___x_210_ == 0)
{
v_x_205_ = v_tail_208_;
goto _start;
}
else
{
uint8_t v___x_212_; 
lean_dec(v_tail_208_);
lean_dec_ref(v_e_204_);
v___x_212_ = lean_unbox(v___x_209_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0___boxed(lean_object* v_e_213_, lean_object* v_x_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_213_, v_x_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal(lean_object* v_e_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_isVal___closed__27));
v___x_275_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___boxed(lean_object* v_e_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object* v_e_279_){
_start:
{
uint8_t v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_279_);
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_283_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(lean_object* v_e_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_288_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(lean_object* v_e_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(v_e_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object* v_p_312_, lean_object* v_s_313_, lean_object* v_e_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; uint8_t v___x_326_; 
lean_inc_ref(v_e_314_);
v___x_325_ = lean_apply_1(v_p_312_, v_e_314_);
v___x_326_ = lean_unbox(v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_e_314_);
lean_dec_ref(v_s_313_);
v___x_327_ = lean_alloc_ctor(0, 0, 2);
v___x_328_ = lean_unbox(v___x_325_);
lean_ctor_set_uint8(v___x_327_, 0, v___x_328_);
v___x_329_ = lean_unbox(v___x_325_);
lean_ctor_set_uint8(v___x_327_, 1, v___x_329_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_327_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; 
lean_inc(v_a_323_);
lean_inc_ref(v_a_322_);
lean_inc(v_a_321_);
lean_inc_ref(v_a_320_);
lean_inc(v_a_319_);
lean_inc_ref(v_a_318_);
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc(v_a_315_);
v___x_331_ = lean_apply_11(v_s_313_, v_e_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, lean_box(0));
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(lean_object* v_p_332_, lean_object* v_s_333_, lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v_p_332_, v_s_333_, v_e_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
return v_res_345_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(lean_object* v_x_346_){
_start:
{
switch(lean_obj_tag(v_x_346_))
{
case 0:
{
uint8_t v___x_347_; 
v___x_347_ = 1;
return v___x_347_;
}
case 2:
{
lean_object* v_a_348_; lean_object* v_a_349_; uint8_t v___x_350_; 
v_a_348_ = lean_ctor_get(v_x_346_, 0);
v_a_349_ = lean_ctor_get(v_x_346_, 1);
v___x_350_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_348_);
if (v___x_350_ == 0)
{
return v___x_350_;
}
else
{
v_x_346_ = v_a_349_;
goto _start;
}
}
case 3:
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v_x_346_, 1);
v_x_346_ = v_a_352_;
goto _start;
}
default: 
{
uint8_t v___x_354_; 
v___x_354_ = 0;
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(lean_object* v_x_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_x_355_);
lean_dec(v_x_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object* v_l_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; lean_object* v_mctx_362_; lean_object* v___x_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_366_; lean_object* v_cache_367_; lean_object* v_zetaDeltaFVarIds_368_; lean_object* v_postponed_369_; lean_object* v_diag_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
v___x_361_ = lean_st_ref_get(v___y_359_);
v_mctx_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_mctx_362_);
lean_dec(v___x_361_);
v___x_363_ = lean_instantiate_level_mvars(v_mctx_362_, v_l_358_);
v_fst_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_fst_364_);
v_snd_365_ = lean_ctor_get(v___x_363_, 1);
lean_inc(v_snd_365_);
lean_dec_ref(v___x_363_);
v___x_366_ = lean_st_ref_take(v___y_359_);
v_cache_367_ = lean_ctor_get(v___x_366_, 1);
v_zetaDeltaFVarIds_368_ = lean_ctor_get(v___x_366_, 2);
v_postponed_369_ = lean_ctor_get(v___x_366_, 3);
v_diag_370_ = lean_ctor_get(v___x_366_, 4);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_366_, 0);
lean_dec(v_unused_380_);
v___x_372_ = v___x_366_;
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_diag_370_);
lean_inc(v_postponed_369_);
lean_inc(v_zetaDeltaFVarIds_368_);
lean_inc(v_cache_367_);
lean_dec(v___x_366_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v_fst_364_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_fst_364_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_cache_367_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_zetaDeltaFVarIds_368_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_postponed_369_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_diag_370_);
v___x_375_ = v_reuseFailAlloc_378_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_st_ref_set(v___y_359_, v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v_snd_365_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object* v_l_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_381_, v___y_382_);
lean_dec(v___y_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object* v_l_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_385_, v___y_389_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object* v_l_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(v_l_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object* v_e_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
lean_inc_ref(v_e_403_);
v___x_411_ = l_Lean_Meta_isPropQuick(v_e_403_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_468_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_468_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_468_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_468_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; 
v___x_416_ = lean_unbox(v_a_412_);
lean_dec(v_a_412_);
switch(v___x_416_)
{
case 0:
{
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec_ref(v_e_403_);
v___x_417_ = 0;
v___x_418_ = lean_box(v___x_417_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_418_);
v___x_420_ = v___x_414_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
case 1:
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_dec_ref(v_e_403_);
v___x_422_ = 1;
v___x_423_ = lean_box(v___x_422_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_423_);
v___x_425_ = v___x_414_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
default: 
{
lean_object* v___x_427_; 
lean_del_object(v___x_414_);
v___x_427_ = l_Lean_Meta_Sym_inferType___redArg(v_e_403_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref(v___x_427_);
v___x_429_ = l_Lean_Meta_whnfD(v_a_428_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_451_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_451_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_451_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_451_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
if (lean_obj_tag(v_a_430_) == 3)
{
lean_object* v_u_434_; lean_object* v___x_435_; lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_432_);
v_u_434_ = lean_ctor_get(v_a_430_, 0);
lean_inc(v_u_434_);
lean_dec_ref(v_a_430_);
v___x_435_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_u_434_, v_a_407_);
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_445_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_436_);
lean_dec(v_a_436_);
v___x_441_ = lean_box(v___x_440_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
lean_dec(v_a_430_);
v___x_446_ = 0;
v___x_447_ = lean_box(v___x_446_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_447_);
v___x_449_ = v___x_432_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_429_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_429_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_a_460_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_427_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_427_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref(v_e_403_);
v_a_469_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_411_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_411_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object* v_e_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_e_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object* v_e_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; 
lean_inc_ref(v_e_486_);
v___x_494_ = l_Lean_Meta_isProofQuick(v_e_486_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_521_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_521_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_521_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_521_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v___x_499_; 
v___x_499_ = lean_unbox(v_a_495_);
lean_dec(v_a_495_);
switch(v___x_499_)
{
case 0:
{
uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec_ref(v_e_486_);
v___x_500_ = 0;
v___x_501_ = lean_box(v___x_500_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_501_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
case 1:
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec_ref(v_e_486_);
v___x_505_ = 1;
v___x_506_ = lean_box(v___x_505_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_506_);
v___x_508_ = v___x_497_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
default: 
{
lean_object* v___x_510_; 
lean_del_object(v___x_497_);
v___x_510_ = l_Lean_Meta_Sym_inferType___redArg(v_e_486_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_a_511_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
return v___x_512_;
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_510_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v_e_486_);
v_a_522_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_494_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_494_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object* v_e_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object* v_e_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_558_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_558_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
uint8_t v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; lean_object* v___x_556_; 
v___x_552_ = 0;
v___x_553_ = lean_alloc_ctor(0, 0, 2);
v___x_554_ = lean_unbox(v_a_548_);
lean_dec(v_a_548_);
lean_ctor_set_uint8(v___x_553_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_553_, 1, v___x_552_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_553_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_553_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_a_559_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_547_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_547_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object* v_e_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object* v_e_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_576_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object* v_e_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_Tactic_Cbv_isProofTerm(v_e_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems(lean_object* v_e_609_, lean_object* v_acc_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = l_Lean_Expr_cleanupAnnotations(v_e_609_);
v___x_612_ = l_Lean_Expr_isApp(v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_acc_610_);
v___x_613_ = lean_box(0);
return v___x_613_;
}
else
{
lean_object* v_arg_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_arg_614_ = lean_ctor_get(v___x_611_, 1);
lean_inc_ref(v_arg_614_);
v___x_615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_611_);
v___x_616_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2));
v___x_617_ = l_Lean_Expr_isConstOf(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; 
v___x_618_ = l_Lean_Expr_isApp(v___x_615_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec_ref(v___x_615_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_acc_610_);
v___x_619_ = lean_box(0);
return v___x_619_;
}
else
{
lean_object* v_arg_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_arg_620_ = lean_ctor_get(v___x_615_, 1);
lean_inc_ref(v_arg_620_);
v___x_621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_615_);
v___x_622_ = l_Lean_Expr_isApp(v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v___x_621_);
lean_dec_ref(v_arg_620_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_acc_610_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_624_ = l_Lean_Expr_appFnCleanup___redArg(v___x_621_);
v___x_625_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4));
v___x_626_ = l_Lean_Expr_isConstOf(v___x_624_, v___x_625_);
lean_dec_ref(v___x_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v_arg_620_);
lean_dec_ref(v_arg_614_);
lean_dec_ref(v_acc_610_);
v___x_627_ = lean_box(0);
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = lean_array_push(v_acc_610_, v_arg_620_);
v_e_609_ = v_arg_614_;
v_acc_610_ = v___x_628_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_630_; 
lean_dec_ref(v___x_615_);
lean_dec_ref(v_arg_614_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_acc_610_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
uint8_t v_contextDependent_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
v_contextDependent_632_ = lean_ctor_get_uint8(v_x_631_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v_x_631_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_dec(v_x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; lean_object* v___x_638_; 
v___x_636_ = 1;
if (v_isShared_635_ == 0)
{
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_639_, 1, v_contextDependent_632_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_ctor_set_uint8(v___x_638_, 0, v___x_636_);
return v___x_638_;
}
}
}
else
{
return v_x_631_;
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
