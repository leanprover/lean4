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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(lean_object* v_e_1_){
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
lean_dec_ref_known(v___x_2_, 1);
v___x_4_ = 1;
return v___x_4_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
uint8_t v_res_5_;
v_res_5_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(v_e_1_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(lean_object* v_e_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(v_e_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(lean_object* v_e_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Meta_Sym_getStringValue_x3f(v_e_9_);
if (lean_obj_tag(v___x_10_) == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
lean_dec_ref_known(v___x_10_, 1);
v___x_12_ = 1;
return v___x_12_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_9_ = stack[0].m_obj;
uint8_t v_res_13_;
v_res_13_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(v_e_9_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(lean_object* v_e_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(v_e_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(lean_object* v_e_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_17_);
if (lean_obj_tag(v___x_18_) == 0)
{
uint8_t v___x_19_; 
v___x_19_ = 0;
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
lean_dec_ref_known(v___x_18_, 1);
v___x_20_ = 1;
return v___x_20_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_17_ = stack[0].m_obj;
uint8_t v_res_21_;
v_res_21_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(v_e_17_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(lean_object* v_e_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(v_e_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(lean_object* v_e_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_25_);
if (lean_obj_tag(v___x_26_) == 0)
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
lean_dec_ref_known(v___x_26_, 1);
v___x_28_ = 1;
return v___x_28_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_25_ = stack[0].m_obj;
uint8_t v_res_29_;
v_res_29_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(v_e_25_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(lean_object* v_e_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(v_e_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(lean_object* v_e_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_33_);
if (lean_obj_tag(v___x_34_) == 0)
{
uint8_t v___x_35_; 
v___x_35_ = 0;
return v___x_35_;
}
else
{
uint8_t v___x_36_; 
lean_dec_ref_known(v___x_34_, 1);
v___x_36_ = 1;
return v___x_36_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_33_ = stack[0].m_obj;
uint8_t v_res_37_;
v_res_37_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(v_e_33_);
stack->m_num = v_res_37_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(lean_object* v_e_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(v_e_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(lean_object* v_e_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_41_);
if (lean_obj_tag(v___x_42_) == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
lean_dec_ref_known(v___x_42_, 1);
v___x_44_ = 1;
return v___x_44_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_41_ = stack[0].m_obj;
uint8_t v_res_45_;
v_res_45_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(v_e_41_);
stack->m_num = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(lean_object* v_e_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(v_e_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(lean_object* v_e_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Sym_getRatValue_x3f(v_e_49_);
if (lean_obj_tag(v___x_50_) == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 0;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
lean_dec_ref_known(v___x_50_, 1);
v___x_52_ = 1;
return v___x_52_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_49_ = stack[0].m_obj;
uint8_t v_res_53_;
v_res_53_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(v_e_49_);
stack->m_num = v_res_53_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(lean_object* v_e_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(v_e_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(lean_object* v_e_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
else
{
uint8_t v___x_60_; 
lean_dec_ref_known(v___x_58_, 1);
v___x_60_ = 1;
return v___x_60_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_57_ = stack[0].m_obj;
uint8_t v_res_61_;
v_res_61_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(v_e_57_);
stack->m_num = v_res_61_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(lean_object* v_e_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(v_e_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(lean_object* v_e_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_65_);
if (lean_obj_tag(v___x_66_) == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = 1;
return v___x_68_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_65_ = stack[0].m_obj;
uint8_t v_res_69_;
v_res_69_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(v_e_65_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(lean_object* v_e_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(v_e_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(lean_object* v_e_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
else
{
uint8_t v___x_76_; 
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = 1;
return v___x_76_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_73_ = stack[0].m_obj;
uint8_t v_res_77_;
v_res_77_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(v_e_73_);
stack->m_num = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(lean_object* v_e_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(v_e_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(lean_object* v_e_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_81_);
if (lean_obj_tag(v___x_82_) == 0)
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
lean_dec_ref_known(v___x_82_, 1);
v___x_84_ = 1;
return v___x_84_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_81_ = stack[0].m_obj;
uint8_t v_res_85_;
v_res_85_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(v_e_81_);
stack->m_num = v_res_85_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(lean_object* v_e_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(v_e_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(lean_object* v_e_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_89_);
if (lean_obj_tag(v___x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = 1;
return v___x_92_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_89_ = stack[0].m_obj;
uint8_t v_res_93_;
v_res_93_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(v_e_89_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(lean_object* v_e_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(v_e_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(lean_object* v_e_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_97_);
if (lean_obj_tag(v___x_98_) == 0)
{
uint8_t v___x_99_; 
v___x_99_ = 0;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = 1;
return v___x_100_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_97_ = stack[0].m_obj;
uint8_t v_res_101_;
v_res_101_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(v_e_97_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(lean_object* v_e_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(v_e_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(lean_object* v_e_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_105_);
if (lean_obj_tag(v___x_106_) == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
lean_dec_ref_known(v___x_106_, 1);
v___x_108_ = 1;
return v___x_108_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_105_ = stack[0].m_obj;
uint8_t v_res_109_;
v_res_109_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(v_e_105_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(lean_object* v_e_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(v_e_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(lean_object* v_e_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
lean_dec_ref_known(v___x_114_, 1);
v___x_116_ = 1;
return v___x_116_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_113_ = stack[0].m_obj;
uint8_t v_res_117_;
v_res_117_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(v_e_113_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value___boxed(lean_object* v_e_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(v_e_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object* v___y_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Sym_getNatValue_x3f(v___y_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = 1;
return v___x_124_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_121_ = stack[0].m_obj;
uint8_t v_res_125_;
v_res_125_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(v___y_121_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object* v___y_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(v___y_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__1(lean_object* v___y_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Sym_getStringValue_x3f(v___y_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
lean_dec_ref_known(v___x_130_, 1);
v___x_132_ = 1;
return v___x_132_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_129_ = stack[0].m_obj;
uint8_t v_res_133_;
v_res_133_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(v___y_129_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(lean_object* v___y_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(v___y_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__2(lean_object* v___y_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Sym_getIntValue_x3f(v___y_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = 1;
return v___x_140_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_137_ = stack[0].m_obj;
uint8_t v_res_141_;
v_res_141_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(v___y_137_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(lean_object* v___y_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(v___y_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__3(lean_object* v___y_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v___y_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
else
{
uint8_t v___x_148_; 
lean_dec_ref_known(v___x_146_, 1);
v___x_148_ = 1;
return v___x_148_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_145_ = stack[0].m_obj;
uint8_t v_res_149_;
v_res_149_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(v___y_145_);
stack->m_num = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(lean_object* v___y_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(v___y_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__4(lean_object* v___y_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Sym_getFinValue_x3f(v___y_153_);
if (lean_obj_tag(v___x_154_) == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = 1;
return v___x_156_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_153_ = stack[0].m_obj;
uint8_t v_res_157_;
v_res_157_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(v___y_153_);
stack->m_num = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(lean_object* v___y_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(v___y_158_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__5(lean_object* v___y_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Meta_Sym_getCharValue_x3f(v___y_161_);
if (lean_obj_tag(v___x_162_) == 0)
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
else
{
uint8_t v___x_164_; 
lean_dec_ref_known(v___x_162_, 1);
v___x_164_ = 1;
return v___x_164_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_161_ = stack[0].m_obj;
uint8_t v_res_165_;
v_res_165_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(v___y_161_);
stack->m_num = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(lean_object* v___y_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(v___y_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__6(lean_object* v___y_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v___y_169_);
if (lean_obj_tag(v___x_170_) == 0)
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
lean_dec_ref_known(v___x_170_, 1);
v___x_172_ = 1;
return v___x_172_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_169_ = stack[0].m_obj;
uint8_t v_res_173_;
v_res_173_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(v___y_169_);
stack->m_num = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(lean_object* v___y_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(v___y_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__7(lean_object* v___y_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v___y_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
uint8_t v___x_179_; 
v___x_179_ = 0;
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = 1;
return v___x_180_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_177_ = stack[0].m_obj;
uint8_t v_res_181_;
v_res_181_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(v___y_177_);
stack->m_num = v_res_181_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(lean_object* v___y_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(v___y_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__8(lean_object* v___y_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v___y_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
uint8_t v___x_187_; 
v___x_187_ = 0;
return v___x_187_;
}
else
{
uint8_t v___x_188_; 
lean_dec_ref_known(v___x_186_, 1);
v___x_188_ = 1;
return v___x_188_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_185_ = stack[0].m_obj;
uint8_t v_res_189_;
v_res_189_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(v___y_185_);
stack->m_num = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(lean_object* v___y_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(v___y_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__9(lean_object* v___y_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v___y_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
uint8_t v___x_195_; 
v___x_195_ = 0;
return v___x_195_;
}
else
{
uint8_t v___x_196_; 
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = 1;
return v___x_196_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_193_ = stack[0].m_obj;
uint8_t v_res_197_;
v_res_197_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(v___y_193_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(lean_object* v___y_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(v___y_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__10(lean_object* v___y_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Meta_Sym_getInt8Value_x3f(v___y_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
else
{
uint8_t v___x_204_; 
lean_dec_ref_known(v___x_202_, 1);
v___x_204_ = 1;
return v___x_204_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_201_ = stack[0].m_obj;
uint8_t v_res_205_;
v_res_205_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(v___y_201_);
stack->m_num = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(lean_object* v___y_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(v___y_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__11(lean_object* v___y_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_Sym_getInt16Value_x3f(v___y_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
else
{
uint8_t v___x_212_; 
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = 1;
return v___x_212_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_209_ = stack[0].m_obj;
uint8_t v_res_213_;
v_res_213_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(v___y_209_);
stack->m_num = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(lean_object* v___y_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(v___y_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__12(lean_object* v___y_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Sym_getInt32Value_x3f(v___y_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
else
{
uint8_t v___x_220_; 
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = 1;
return v___x_220_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_217_ = stack[0].m_obj;
uint8_t v_res_221_;
v_res_221_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(v___y_217_);
stack->m_num = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(lean_object* v___y_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(v___y_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__13(lean_object* v___y_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_Sym_getInt64Value_x3f(v___y_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = 0;
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = 1;
return v___x_228_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_225_ = stack[0].m_obj;
uint8_t v_res_229_;
v_res_229_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__13(v___y_225_);
stack->m_num = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__13___boxed(lean_object* v___y_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__13(v___y_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
uint8_t l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(lean_object* v_e_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
uint8_t v___x_235_; 
lean_dec_ref(v_e_233_);
v___x_235_ = 0;
return v___x_235_;
}
else
{
lean_object* v_head_236_; lean_object* v_tail_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_head_236_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_head_236_);
v_tail_237_ = lean_ctor_get(v_x_234_, 1);
lean_inc(v_tail_237_);
lean_dec_ref_known(v_x_234_, 2);
lean_inc_ref(v_e_233_);
v___x_238_ = lean_apply_1(v_head_236_, v_e_233_);
v___x_239_ = lean_unbox(v___x_238_);
if (v___x_239_ == 0)
{
v_x_234_ = v_tail_237_;
goto _start;
}
else
{
uint8_t v___x_241_; 
lean_dec(v_tail_237_);
lean_dec_ref(v_e_233_);
v___x_241_ = lean_unbox(v___x_238_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_233_ = stack[0].m_obj;
lean_object* v_x_234_ = stack[1].m_obj;
uint8_t v_res_242_;
v_res_242_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_233_, v_x_234_);
stack->m_num = v_res_242_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0___boxed(lean_object* v_e_243_, lean_object* v_x_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_243_, v_x_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_isVal(lean_object* v_e_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_isVal___closed__27));
v___x_305_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_303_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isVal_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_303_ = stack[0].m_obj;
uint8_t v_res_306_;
v_res_306_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_303_);
stack->m_num = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___boxed(lean_object* v_e_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_307_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object* v_e_310_){
_start:
{
uint8_t v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_310_);
v___x_313_ = 0;
v___x_314_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_314_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_310_ = stack[0].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_310_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(lean_object* v_e_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_317_);
return v_res_319_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue(lean_object* v_e_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_320_);
return v___x_331_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isBuiltinValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_320_ = stack[0].m_obj;
lean_object* v_a_321_ = stack[1].m_obj;
lean_object* v_a_322_ = stack[2].m_obj;
lean_object* v_a_323_ = stack[3].m_obj;
lean_object* v_a_324_ = stack[4].m_obj;
lean_object* v_a_325_ = stack[5].m_obj;
lean_object* v_a_326_ = stack[6].m_obj;
lean_object* v_a_327_ = stack[7].m_obj;
lean_object* v_a_328_ = stack[8].m_obj;
lean_object* v_a_329_ = stack[9].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(v_e_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(lean_object* v_e_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(v_e_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
return v_res_344_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object* v_p_345_, lean_object* v_s_346_, lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
lean_inc_ref(v_e_347_);
v___x_358_ = lean_apply_1(v_p_345_, v_e_347_);
v___x_359_ = lean_unbox(v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; 
lean_dec_ref(v_e_347_);
lean_dec_ref(v_s_346_);
v___x_360_ = lean_alloc_ctor(0, 0, 2);
v___x_361_ = lean_unbox(v___x_358_);
lean_ctor_set_uint8(v___x_360_, 0, v___x_361_);
v___x_362_ = lean_unbox(v___x_358_);
lean_ctor_set_uint8(v___x_360_, 1, v___x_362_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_360_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_inc(v_a_356_);
lean_inc_ref(v_a_355_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
lean_inc(v_a_350_);
lean_inc_ref(v_a_349_);
lean_inc(v_a_348_);
v___x_364_ = lean_apply_11(v_s_346_, v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, lean_box(0));
return v___x_364_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_guardSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_345_ = stack[0].m_obj;
lean_object* v_s_346_ = stack[1].m_obj;
lean_object* v_e_347_ = stack[2].m_obj;
lean_object* v_a_348_ = stack[3].m_obj;
lean_object* v_a_349_ = stack[4].m_obj;
lean_object* v_a_350_ = stack[5].m_obj;
lean_object* v_a_351_ = stack[6].m_obj;
lean_object* v_a_352_ = stack[7].m_obj;
lean_object* v_a_353_ = stack[8].m_obj;
lean_object* v_a_354_ = stack[9].m_obj;
lean_object* v_a_355_ = stack[10].m_obj;
lean_object* v_a_356_ = stack[11].m_obj;
lean_object* v_res_365_;
v_res_365_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v_p_345_, v_s_346_, v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(lean_object* v_p_366_, lean_object* v_s_367_, lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v_p_366_, v_s_367_, v_e_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
return v_res_379_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(lean_object* v_x_380_){
_start:
{
switch(lean_obj_tag(v_x_380_))
{
case 0:
{
uint8_t v___x_381_; 
v___x_381_ = 1;
return v___x_381_;
}
case 2:
{
lean_object* v_a_382_; lean_object* v_a_383_; uint8_t v___x_384_; 
v_a_382_ = lean_ctor_get(v_x_380_, 0);
v_a_383_ = lean_ctor_get(v_x_380_, 1);
v___x_384_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_382_);
if (v___x_384_ == 0)
{
return v___x_384_;
}
else
{
v_x_380_ = v_a_383_;
goto _start;
}
}
case 3:
{
lean_object* v_a_386_; 
v_a_386_ = lean_ctor_get(v_x_380_, 1);
v_x_380_ = v_a_386_;
goto _start;
}
default: 
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_380_ = stack[0].m_obj;
uint8_t v_res_389_;
v_res_389_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_x_380_);
stack->m_num = v_res_389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(lean_object* v_x_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_x_390_);
lean_dec(v_x_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object* v_l_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; lean_object* v_mctx_397_; lean_object* v___x_398_; lean_object* v_fst_399_; lean_object* v_snd_400_; lean_object* v___x_401_; lean_object* v_cache_402_; lean_object* v_zetaDeltaFVarIds_403_; lean_object* v_postponed_404_; lean_object* v_diag_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_414_; 
v___x_396_ = lean_st_ref_get(v___y_394_);
v_mctx_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_mctx_397_);
lean_dec(v___x_396_);
v___x_398_ = lean_instantiate_level_mvars(v_mctx_397_, v_l_393_);
v_fst_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_fst_399_);
v_snd_400_ = lean_ctor_get(v___x_398_, 1);
lean_inc(v_snd_400_);
lean_dec_ref(v___x_398_);
v___x_401_ = lean_st_ref_take(v___y_394_);
v_cache_402_ = lean_ctor_get(v___x_401_, 1);
v_zetaDeltaFVarIds_403_ = lean_ctor_get(v___x_401_, 2);
v_postponed_404_ = lean_ctor_get(v___x_401_, 3);
v_diag_405_ = lean_ctor_get(v___x_401_, 4);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_401_, 0);
lean_dec(v_unused_415_);
v___x_407_ = v___x_401_;
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_diag_405_);
lean_inc(v_postponed_404_);
lean_inc(v_zetaDeltaFVarIds_403_);
lean_inc(v_cache_402_);
lean_dec(v___x_401_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v_fst_399_);
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_fst_399_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_cache_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_zetaDeltaFVarIds_403_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_postponed_404_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_diag_405_);
v___x_410_ = v_reuseFailAlloc_413_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_st_ref_put(v___y_394_, v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_snd_400_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_393_ = stack[0].m_obj;
lean_object* v___y_394_ = stack[1].m_obj;
lean_object* v_res_416_;
v_res_416_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_393_, v___y_394_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object* v_l_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_417_, v___y_418_);
lean_dec(v___y_418_);
return v_res_420_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object* v_l_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_421_, v___y_425_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_421_ = stack[0].m_obj;
lean_object* v___y_422_ = stack[1].m_obj;
lean_object* v___y_423_ = stack[2].m_obj;
lean_object* v___y_424_ = stack[3].m_obj;
lean_object* v___y_425_ = stack[4].m_obj;
lean_object* v___y_426_ = stack[5].m_obj;
lean_object* v___y_427_ = stack[6].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(v_l_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object* v_l_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(v_l_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_439_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object* v_e_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; 
lean_inc_ref(v_e_440_);
v___x_448_ = l_Lean_Meta_isPropQuick(v_e_440_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_505_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_505_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_505_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_505_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v___x_453_; 
v___x_453_ = lean_unbox(v_a_449_);
lean_dec(v_a_449_);
switch(v___x_453_)
{
case 0:
{
uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec_ref(v_e_440_);
v___x_454_ = 0;
v___x_455_ = lean_box(v___x_454_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_455_);
v___x_457_ = v___x_451_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
case 1:
{
uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec_ref(v_e_440_);
v___x_459_ = 1;
v___x_460_ = lean_box(v___x_459_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_460_);
v___x_462_ = v___x_451_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
default: 
{
lean_object* v___x_464_; 
lean_del_object(v___x_451_);
v___x_464_ = l_Lean_Meta_Sym_inferType(v_e_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_Meta_whnfD(v_a_465_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_488_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_488_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_488_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_488_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
if (lean_obj_tag(v_a_467_) == 3)
{
lean_object* v_u_471_; lean_object* v___x_472_; lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
lean_del_object(v___x_469_);
v_u_471_ = lean_ctor_get(v_a_467_, 0);
lean_inc(v_u_471_);
lean_dec_ref_known(v_a_467_, 1);
v___x_472_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_u_471_, v_a_444_);
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_482_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_477_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_473_);
lean_dec(v_a_473_);
v___x_478_ = lean_box(v___x_477_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_478_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec(v_a_467_);
v___x_483_ = 0;
v___x_484_ = lean_box(v___x_483_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_484_);
v___x_486_ = v___x_469_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_a_489_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_466_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_466_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_a_497_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_464_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_464_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_e_440_);
v_a_506_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_448_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_448_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_440_ = stack[0].m_obj;
lean_object* v_a_441_ = stack[1].m_obj;
lean_object* v_a_442_ = stack[2].m_obj;
lean_object* v_a_443_ = stack[3].m_obj;
lean_object* v_a_444_ = stack[4].m_obj;
lean_object* v_a_445_ = stack[5].m_obj;
lean_object* v_a_446_ = stack[6].m_obj;
lean_object* v_res_514_;
v_res_514_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_e_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object* v_e_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_e_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
return v_res_523_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object* v_e_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; 
lean_inc_ref(v_e_524_);
v___x_532_ = l_Lean_Meta_isProofQuick(v_e_524_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_559_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_559_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_559_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_559_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint8_t v___x_537_; 
v___x_537_ = lean_unbox(v_a_533_);
lean_dec(v_a_533_);
switch(v___x_537_)
{
case 0:
{
uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
lean_dec_ref(v_e_524_);
v___x_538_ = 0;
v___x_539_ = lean_box(v___x_538_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_539_);
v___x_541_ = v___x_535_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
case 1:
{
uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
lean_dec_ref(v_e_524_);
v___x_543_ = 1;
v___x_544_ = lean_box(v___x_543_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_544_);
v___x_546_ = v___x_535_;
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
default: 
{
lean_object* v___x_548_; 
lean_del_object(v___x_535_);
v___x_548_ = l_Lean_Meta_Sym_inferType(v_e_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_a_549_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_550_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_548_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_548_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v_e_524_);
v_a_560_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_532_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_532_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_524_ = stack[0].m_obj;
lean_object* v_a_525_ = stack[1].m_obj;
lean_object* v_a_526_ = stack[2].m_obj;
lean_object* v_a_527_ = stack[3].m_obj;
lean_object* v_a_528_ = stack[4].m_obj;
lean_object* v_a_529_ = stack[5].m_obj;
lean_object* v_a_530_ = stack[6].m_obj;
lean_object* v_res_568_;
v_res_568_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_577_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object* v_e_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_597_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_597_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
uint8_t v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___x_595_; 
v___x_591_ = 0;
v___x_592_ = lean_alloc_ctor(0, 0, 2);
v___x_593_ = lean_unbox(v_a_587_);
lean_dec(v_a_587_);
lean_ctor_set_uint8(v___x_592_, 0, v___x_593_);
lean_ctor_set_uint8(v___x_592_, 1, v___x_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_592_);
v___x_595_ = v___x_589_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_592_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_586_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_586_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_578_ = stack[0].m_obj;
lean_object* v_a_579_ = stack[1].m_obj;
lean_object* v_a_580_ = stack[2].m_obj;
lean_object* v_a_581_ = stack[3].m_obj;
lean_object* v_a_582_ = stack[4].m_obj;
lean_object* v_a_583_ = stack[5].m_obj;
lean_object* v_a_584_ = stack[6].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
stack->m_obj
 = v_res_606_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object* v_e_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_615_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object* v_e_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_616_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
return v___x_627_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isProofTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_616_ = stack[0].m_obj;
lean_object* v_a_617_ = stack[1].m_obj;
lean_object* v_a_618_ = stack[2].m_obj;
lean_object* v_a_619_ = stack[3].m_obj;
lean_object* v_a_620_ = stack[4].m_obj;
lean_object* v_a_621_ = stack[5].m_obj;
lean_object* v_a_622_ = stack[6].m_obj;
lean_object* v_a_623_ = stack[7].m_obj;
lean_object* v_a_624_ = stack[8].m_obj;
lean_object* v_a_625_ = stack[9].m_obj;
lean_object* v_res_628_;
v_res_628_ = l_Lean_Meta_Tactic_Cbv_isProofTerm(v_e_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
stack->m_obj
 = v_res_628_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object* v_e_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Meta_Tactic_Cbv_isProofTerm(v_e_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems(lean_object* v_e_650_, lean_object* v_acc_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = l_Lean_Expr_cleanupAnnotations(v_e_650_);
v___x_653_ = l_Lean_Expr_isApp(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v___x_652_);
lean_dec_ref(v_acc_651_);
v___x_654_ = lean_box(0);
return v___x_654_;
}
else
{
lean_object* v_arg_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_arg_655_ = lean_ctor_get(v___x_652_, 1);
lean_inc_ref(v_arg_655_);
v___x_656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_652_);
v___x_657_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2));
v___x_658_ = l_Lean_Expr_isConstOf(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = l_Lean_Expr_isApp(v___x_656_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v___x_656_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_acc_651_);
v___x_660_ = lean_box(0);
return v___x_660_;
}
else
{
lean_object* v_arg_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_arg_661_ = lean_ctor_get(v___x_656_, 1);
lean_inc_ref(v_arg_661_);
v___x_662_ = l_Lean_Expr_appFnCleanup___redArg(v___x_656_);
v___x_663_ = l_Lean_Expr_isApp(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec_ref(v___x_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_acc_651_);
v___x_664_ = lean_box(0);
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = l_Lean_Expr_appFnCleanup___redArg(v___x_662_);
v___x_666_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4));
v___x_667_ = l_Lean_Expr_isConstOf(v___x_665_, v___x_666_);
lean_dec_ref(v___x_665_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec_ref(v_arg_661_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_acc_651_);
v___x_668_ = lean_box(0);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_array_push(v_acc_651_, v_arg_661_);
v_e_650_ = v_arg_655_;
v_acc_651_ = v___x_669_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_671_; 
lean_dec_ref(v___x_656_);
lean_dec_ref(v_arg_655_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_acc_651_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_672_) == 0)
{
uint8_t v_contextDependent_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_contextDependent_673_ = lean_ctor_get_uint8(v_x_672_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_672_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v_x_672_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_dec(v_x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
uint8_t v___x_677_; lean_object* v___x_679_; 
v___x_677_ = 1;
if (v_isShared_676_ == 0)
{
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, 1, v_contextDependent_673_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_ctor_set_uint8(v___x_679_, 0, v___x_677_);
return v___x_679_;
}
}
}
else
{
return v_x_672_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
