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
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isNatValue___boxed(lean_object*);
uint8_t l_Lean_Meta_Sym_isNatValue(lean_object*);
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
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_isNatValue___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__7_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__8_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__9_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__10_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__11_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_isVal___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_isVal___closed__12_value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_isVal___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t v___x_2_; 
v___x_2_ = l_Lean_Meta_Sym_isNatValue(v_e_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue___boxed(lean_object* v_e_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isNatValue(v_e_3_);
lean_dec_ref(v_e_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(lean_object* v_e_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_Sym_getStringValue_x3f(v_e_6_);
if (lean_obj_tag(v___x_7_) == 0)
{
uint8_t v___x_8_; 
v___x_8_ = 0;
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
lean_dec_ref_known(v___x_7_, 1);
v___x_9_ = 1;
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue___boxed(lean_object* v_e_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isStringValue(v_e_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(lean_object* v_e_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_13_);
if (lean_obj_tag(v___x_14_) == 0)
{
uint8_t v___x_15_; 
v___x_15_ = 0;
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
lean_dec_ref_known(v___x_14_, 1);
v___x_16_ = 1;
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue___boxed(lean_object* v_e_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isIntValue(v_e_17_);
lean_dec_ref(v_e_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(lean_object* v_e_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_e_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
else
{
uint8_t v___x_23_; 
lean_dec_ref_known(v___x_21_, 1);
v___x_23_ = 1;
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue___boxed(lean_object* v_e_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isBitVecValue(v_e_24_);
lean_dec_ref(v_e_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(lean_object* v_e_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Sym_getFinValue_x3f(v_e_27_);
if (lean_obj_tag(v___x_28_) == 0)
{
uint8_t v___x_29_; 
v___x_29_ = 0;
return v___x_29_;
}
else
{
uint8_t v___x_30_; 
lean_dec_ref_known(v___x_28_, 1);
v___x_30_ = 1;
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue___boxed(lean_object* v_e_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isFinValue(v_e_31_);
lean_dec_ref(v_e_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(lean_object* v_e_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Sym_getCharValue_x3f(v_e_34_);
if (lean_obj_tag(v___x_35_) == 0)
{
uint8_t v___x_36_; 
v___x_36_ = 0;
return v___x_36_;
}
else
{
uint8_t v___x_37_; 
lean_dec_ref_known(v___x_35_, 1);
v___x_37_ = 1;
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue___boxed(lean_object* v_e_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isCharValue(v_e_38_);
lean_dec_ref(v_e_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(lean_object* v_e_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Sym_getRatValue_x3f(v_e_41_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue___boxed(lean_object* v_e_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isRatValue(v_e_45_);
lean_dec_ref(v_e_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(lean_object* v_e_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v_e_48_);
if (lean_obj_tag(v___x_49_) == 0)
{
uint8_t v___x_50_; 
v___x_50_ = 0;
return v___x_50_;
}
else
{
uint8_t v___x_51_; 
lean_dec_ref_known(v___x_49_, 1);
v___x_51_ = 1;
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value___boxed(lean_object* v_e_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt8Value(v_e_52_);
lean_dec_ref(v_e_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(lean_object* v_e_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v_e_55_);
if (lean_obj_tag(v___x_56_) == 0)
{
uint8_t v___x_57_; 
v___x_57_ = 0;
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
lean_dec_ref_known(v___x_56_, 1);
v___x_58_ = 1;
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value___boxed(lean_object* v_e_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt16Value(v_e_59_);
lean_dec_ref(v_e_59_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(lean_object* v_e_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v_e_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
uint8_t v___x_64_; 
v___x_64_ = 0;
return v___x_64_;
}
else
{
uint8_t v___x_65_; 
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = 1;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value___boxed(lean_object* v_e_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt32Value(v_e_66_);
lean_dec_ref(v_e_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(lean_object* v_e_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v_e_69_);
if (lean_obj_tag(v___x_70_) == 0)
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
else
{
uint8_t v___x_72_; 
lean_dec_ref_known(v___x_70_, 1);
v___x_72_ = 1;
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value___boxed(lean_object* v_e_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isUInt64Value(v_e_73_);
lean_dec_ref(v_e_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(lean_object* v_e_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Sym_getInt8Value_x3f(v_e_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
lean_dec_ref_known(v___x_77_, 1);
v___x_79_ = 1;
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value___boxed(lean_object* v_e_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt8Value(v_e_80_);
lean_dec_ref(v_e_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(lean_object* v_e_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_Sym_getInt16Value_x3f(v_e_83_);
if (lean_obj_tag(v___x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = 0;
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
lean_dec_ref_known(v___x_84_, 1);
v___x_86_ = 1;
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value___boxed(lean_object* v_e_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt16Value(v_e_87_);
lean_dec_ref(v_e_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(lean_object* v_e_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Meta_Sym_getInt32Value_x3f(v_e_90_);
if (lean_obj_tag(v___x_91_) == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
lean_dec_ref_known(v___x_91_, 1);
v___x_93_ = 1;
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value___boxed(lean_object* v_e_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt32Value(v_e_94_);
lean_dec_ref(v_e_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(lean_object* v_e_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Sym_getInt64Value_x3f(v_e_97_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value___boxed(lean_object* v_e_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isInt64Value(v_e_101_);
lean_dec_ref(v_e_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__0(lean_object* v___y_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Sym_getStringValue_x3f(v___y_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = 1;
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__0___boxed(lean_object* v___y_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__0(v___y_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__1(lean_object* v___y_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Sym_getIntValue_x3f(v___y_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
else
{
uint8_t v___x_114_; 
lean_dec_ref_known(v___x_112_, 1);
v___x_114_ = 1;
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__1___boxed(lean_object* v___y_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__1(v___y_115_);
lean_dec_ref(v___y_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__2(lean_object* v___y_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v___y_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
lean_dec_ref_known(v___x_119_, 1);
v___x_121_ = 1;
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__2___boxed(lean_object* v___y_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__2(v___y_122_);
lean_dec_ref(v___y_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__3(lean_object* v___y_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Sym_getFinValue_x3f(v___y_125_);
if (lean_obj_tag(v___x_126_) == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = 1;
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__3___boxed(lean_object* v___y_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__3(v___y_129_);
lean_dec_ref(v___y_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__4(lean_object* v___y_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Sym_getCharValue_x3f(v___y_132_);
if (lean_obj_tag(v___x_133_) == 0)
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
else
{
uint8_t v___x_135_; 
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = 1;
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__4___boxed(lean_object* v___y_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__4(v___y_136_);
lean_dec_ref(v___y_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__5(lean_object* v___y_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_Sym_getUInt8Value_x3f(v___y_139_);
if (lean_obj_tag(v___x_140_) == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = 1;
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__5___boxed(lean_object* v___y_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__5(v___y_143_);
lean_dec_ref(v___y_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__6(lean_object* v___y_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Sym_getUInt16Value_x3f(v___y_146_);
if (lean_obj_tag(v___x_147_) == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = 1;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__6___boxed(lean_object* v___y_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__6(v___y_150_);
lean_dec_ref(v___y_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__7(lean_object* v___y_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Sym_getUInt32Value_x3f(v___y_153_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__7___boxed(lean_object* v___y_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__7(v___y_157_);
lean_dec_ref(v___y_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__8(lean_object* v___y_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Sym_getUInt64Value_x3f(v___y_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
else
{
uint8_t v___x_163_; 
lean_dec_ref_known(v___x_161_, 1);
v___x_163_ = 1;
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__8___boxed(lean_object* v___y_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__8(v___y_164_);
lean_dec_ref(v___y_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__9(lean_object* v___y_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Sym_getInt8Value_x3f(v___y_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
lean_dec_ref_known(v___x_168_, 1);
v___x_170_ = 1;
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__9___boxed(lean_object* v___y_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__9(v___y_171_);
lean_dec_ref(v___y_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__10(lean_object* v___y_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_Sym_getInt16Value_x3f(v___y_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
else
{
uint8_t v___x_177_; 
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = 1;
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__10___boxed(lean_object* v___y_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__10(v___y_178_);
lean_dec_ref(v___y_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__11(lean_object* v___y_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_Sym_getInt32Value_x3f(v___y_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
lean_dec_ref_known(v___x_182_, 1);
v___x_184_ = 1;
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__11___boxed(lean_object* v___y_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__11(v___y_185_);
lean_dec_ref(v___y_185_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal___lam__12(lean_object* v___y_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Sym_getInt64Value_x3f(v___y_188_);
if (lean_obj_tag(v___x_189_) == 0)
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
lean_dec_ref_known(v___x_189_, 1);
v___x_191_ = 1;
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___lam__12___boxed(lean_object* v___y_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Lean_Meta_Tactic_Cbv_isVal___lam__12(v___y_192_);
lean_dec_ref(v___y_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(lean_object* v_e_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
uint8_t v___x_197_; 
lean_dec_ref(v_e_195_);
v___x_197_ = 0;
return v___x_197_;
}
else
{
lean_object* v_head_198_; lean_object* v_tail_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_head_198_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_head_198_);
v_tail_199_ = lean_ctor_get(v_x_196_, 1);
lean_inc(v_tail_199_);
lean_dec_ref_known(v_x_196_, 2);
lean_inc_ref(v_e_195_);
v___x_200_ = lean_apply_1(v_head_198_, v_e_195_);
v___x_201_ = lean_unbox(v___x_200_);
if (v___x_201_ == 0)
{
v_x_196_ = v_tail_199_;
goto _start;
}
else
{
uint8_t v___x_203_; 
lean_dec(v_tail_199_);
lean_dec_ref(v_e_195_);
v___x_203_ = lean_unbox(v___x_200_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0___boxed(lean_object* v_e_204_, lean_object* v_x_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_204_, v_x_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_isVal(lean_object* v_e_264_){
_start:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_isVal___closed__27));
v___x_266_ = l_List_any___at___00Lean_Meta_Tactic_Cbv_isVal_spec__0(v_e_264_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isVal___boxed(lean_object* v_e_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object* v_e_270_){
_start:
{
uint8_t v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = l_Lean_Meta_Tactic_Cbv_isVal(v_e_270_);
v___x_273_ = 0;
v___x_274_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_274_, 0, v___x_272_);
lean_ctor_set_uint8(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg___boxed(lean_object* v_e_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue(lean_object* v_e_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_e_279_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___boxed(lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue(v_e_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object* v_p_303_, lean_object* v_s_304_, lean_object* v_e_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; 
lean_inc_ref(v_e_305_);
v___x_316_ = lean_apply_1(v_p_303_, v_e_305_);
v___x_317_ = lean_unbox(v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; uint8_t v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; 
lean_dec_ref(v_e_305_);
lean_dec_ref(v_s_304_);
v___x_318_ = lean_alloc_ctor(0, 0, 2);
v___x_319_ = lean_unbox(v___x_316_);
lean_ctor_set_uint8(v___x_318_, 0, v___x_319_);
v___x_320_ = lean_unbox(v___x_316_);
lean_ctor_set_uint8(v___x_318_, 1, v___x_320_);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_318_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; 
lean_inc(v_a_314_);
lean_inc_ref(v_a_313_);
lean_inc(v_a_312_);
lean_inc_ref(v_a_311_);
lean_inc(v_a_310_);
lean_inc_ref(v_a_309_);
lean_inc(v_a_308_);
lean_inc_ref(v_a_307_);
lean_inc(v_a_306_);
v___x_322_ = lean_apply_11(v_s_304_, v_e_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, lean_box(0));
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc___boxed(lean_object* v_p_323_, lean_object* v_s_324_, lean_object* v_e_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v_p_323_, v_s_324_, v_e_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
return v_res_336_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(lean_object* v_x_337_){
_start:
{
switch(lean_obj_tag(v_x_337_))
{
case 0:
{
uint8_t v___x_338_; 
v___x_338_ = 1;
return v___x_338_;
}
case 2:
{
lean_object* v_a_339_; lean_object* v_a_340_; uint8_t v___x_341_; 
v_a_339_ = lean_ctor_get(v_x_337_, 0);
v_a_340_ = lean_ctor_get(v_x_337_, 1);
v___x_341_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_339_);
if (v___x_341_ == 0)
{
return v___x_341_;
}
else
{
v_x_337_ = v_a_340_;
goto _start;
}
}
case 3:
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v_x_337_, 1);
v_x_337_ = v_a_343_;
goto _start;
}
default: 
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero___boxed(lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_x_346_);
lean_dec(v_x_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(lean_object* v_l_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v_mctx_353_; lean_object* v___x_354_; lean_object* v_fst_355_; lean_object* v_snd_356_; lean_object* v___x_357_; lean_object* v_cache_358_; lean_object* v_zetaDeltaFVarIds_359_; lean_object* v_postponed_360_; lean_object* v_diag_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_370_; 
v___x_352_ = lean_st_ref_get(v___y_350_);
v_mctx_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_mctx_353_);
lean_dec(v___x_352_);
v___x_354_ = lean_instantiate_level_mvars(v_mctx_353_, v_l_349_);
v_fst_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_fst_355_);
v_snd_356_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_snd_356_);
lean_dec_ref(v___x_354_);
v___x_357_ = lean_st_ref_take(v___y_350_);
v_cache_358_ = lean_ctor_get(v___x_357_, 1);
v_zetaDeltaFVarIds_359_ = lean_ctor_get(v___x_357_, 2);
v_postponed_360_ = lean_ctor_get(v___x_357_, 3);
v_diag_361_ = lean_ctor_get(v___x_357_, 4);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_371_);
v___x_363_ = v___x_357_;
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_diag_361_);
lean_inc(v_postponed_360_);
lean_inc(v_zetaDeltaFVarIds_359_);
lean_inc(v_cache_358_);
lean_dec(v___x_357_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v_fst_355_);
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_fst_355_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_cache_358_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_zetaDeltaFVarIds_359_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_postponed_360_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_diag_361_);
v___x_366_ = v_reuseFailAlloc_369_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_st_ref_put(v___y_350_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v_snd_356_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg___boxed(lean_object* v_l_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_372_, v___y_373_);
lean_dec(v___y_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(lean_object* v_l_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_l_376_, v___y_380_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___boxed(lean_object* v_l_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0(v_l_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(lean_object* v_e_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
lean_inc_ref(v_e_394_);
v___x_402_ = l_Lean_Meta_isPropQuick(v_e_394_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_459_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_459_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_459_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_459_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
uint8_t v___x_407_; 
v___x_407_ = lean_unbox(v_a_403_);
lean_dec(v_a_403_);
switch(v___x_407_)
{
case 0:
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec_ref(v_e_394_);
v___x_408_ = 0;
v___x_409_ = lean_box(v___x_408_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_409_);
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
case 1:
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec_ref(v_e_394_);
v___x_413_ = 1;
v___x_414_ = lean_box(v___x_413_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_414_);
v___x_416_ = v___x_405_;
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
default: 
{
lean_object* v___x_418_; 
lean_del_object(v___x_405_);
v___x_418_ = l_Lean_Meta_Sym_inferType(v_e_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_Meta_whnfD(v_a_419_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_442_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_442_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_442_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_442_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
if (lean_obj_tag(v_a_421_) == 3)
{
lean_object* v_u_425_; lean_object* v___x_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
lean_del_object(v___x_423_);
v_u_425_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_u_425_);
lean_dec_ref_known(v_a_421_, 1);
v___x_426_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp_spec__0___redArg(v_u_425_, v_a_398_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_431_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isAlwaysZero(v_a_427_);
lean_dec(v_a_427_);
v___x_432_ = lean_box(v___x_431_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
lean_dec(v_a_421_);
v___x_437_ = 0;
v___x_438_ = lean_box(v___x_437_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_438_);
v___x_440_ = v___x_423_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_a_443_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_420_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_420_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_418_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_418_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v_e_394_);
v_a_460_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_402_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_402_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp___boxed(lean_object* v_e_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_e_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(lean_object* v_e_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
lean_inc_ref(v_e_477_);
v___x_485_ = l_Lean_Meta_isProofQuick(v_e_477_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_512_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_512_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_512_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_512_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint8_t v___x_490_; 
v___x_490_ = lean_unbox(v_a_486_);
lean_dec(v_a_486_);
switch(v___x_490_)
{
case 0:
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec_ref(v_e_477_);
v___x_491_ = 0;
v___x_492_ = lean_box(v___x_491_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_492_);
v___x_494_ = v___x_488_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
case 1:
{
uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec_ref(v_e_477_);
v___x_496_ = 1;
v___x_497_ = lean_box(v___x_496_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_497_);
v___x_499_ = v___x_488_;
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
default: 
{
lean_object* v___x_501_; 
lean_del_object(v___x_488_);
v___x_501_ = l_Lean_Meta_Sym_inferType(v_e_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProp(v_a_502_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_503_;
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_a_504_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_501_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v_e_477_);
v_a_513_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_485_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_485_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof___boxed(lean_object* v_e_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object* v_e_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Lean_Meta_Tactic_Cbv_Util_0__Lean_Meta_Tactic_Cbv_isProof(v_e_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_549_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_549_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_549_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_549_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
uint8_t v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_547_; 
v___x_543_ = 0;
v___x_544_ = lean_alloc_ctor(0, 0, 2);
v___x_545_ = lean_unbox(v_a_539_);
lean_dec(v_a_539_);
lean_ctor_set_uint8(v___x_544_, 0, v___x_545_);
lean_ctor_set_uint8(v___x_544_, 1, v___x_543_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_547_ = v___x_541_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_544_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_538_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_538_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg___boxed(lean_object* v_e_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm(lean_object* v_e_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_e_567_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___boxed(lean_object* v_e_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Meta_Tactic_Cbv_isProofTerm(v_e_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getListLitElems(lean_object* v_e_600_, lean_object* v_acc_601_){
_start:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = l_Lean_Expr_cleanupAnnotations(v_e_600_);
lean_dec_ref(v_e_600_);
v___x_603_ = l_Lean_Expr_isApp(v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_dec_ref(v___x_602_);
lean_dec_ref(v_acc_601_);
v___x_604_ = lean_box(0);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = l_Lean_Expr_appFnCleanup___redArg(v___x_602_);
v___x_606_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__2));
v___x_607_ = l_Lean_Expr_isConstOf(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_Expr_isApp(v___x_605_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v___x_605_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v_acc_601_);
v___x_609_ = lean_box(0);
return v___x_609_;
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_605_);
v___x_611_ = l_Lean_Expr_isApp(v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec_ref(v___x_610_);
lean_dec_ref(v___x_605_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v_acc_601_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = l_Lean_Expr_appFnCleanup___redArg(v___x_610_);
lean_dec_ref(v___x_610_);
v___x_614_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getListLitElems___closed__4));
v___x_615_ = l_Lean_Expr_isConstOf(v___x_613_, v___x_614_);
lean_dec_ref(v___x_613_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v___x_605_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v_acc_601_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v_arg_617_; lean_object* v_arg_618_; lean_object* v___x_619_; 
v_arg_617_ = lean_ctor_get(v___x_602_, 1);
lean_inc_ref(v_arg_617_);
lean_dec_ref(v___x_602_);
v_arg_618_ = lean_ctor_get(v___x_605_, 1);
lean_inc_ref(v_arg_618_);
lean_dec_ref(v___x_605_);
v___x_619_ = lean_array_push(v_acc_601_, v_arg_618_);
v_e_600_ = v_arg_617_;
v_acc_601_ = v___x_619_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref(v___x_605_);
lean_dec_ref(v___x_602_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v_acc_601_);
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
uint8_t v_contextDependent_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
v_contextDependent_623_ = lean_ctor_get_uint8(v_x_622_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v_x_622_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_dec(v_x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; lean_object* v___x_629_; 
v___x_627_ = 1;
if (v_isShared_626_ == 0)
{
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, 1, v_contextDependent_623_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_ctor_set_uint8(v___x_629_, 0, v___x_627_);
return v___x_629_;
}
}
}
else
{
return v_x_622_;
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
