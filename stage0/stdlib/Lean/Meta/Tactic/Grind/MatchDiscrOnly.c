// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MatchDiscrOnly
// Imports: public import Lean.Meta.Tactic.Simp.Simproc import Init.Grind.Util import Init.Simproc import Lean.Meta.Tactic.Simp.Rewrite
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "simpMatchDiscrsOnly"};
static const lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 129, 49, 184, 77, 13, 95, 2)}};
static const lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSimpMatchDiscrsOnly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "reduceSimpMatchDiscrsOnly"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(107, 135, 31, 2, 225, 129, 149, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_isSimpMatchDiscrsOnly___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_14_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_mk_empty_array_with_capacity(v___x_15_);
v___x_17_ = lean_array_push(v___x_16_, v_e_8_);
v___x_18_ = l_Lean_Meta_mkAppM(v___x_14_, v___x_17_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___boxed(lean_object* v_e_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(v_e_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_25_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(lean_object* v_e_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_27_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_28_ = lean_unsigned_to_nat(2u);
v___x_29_ = l_Lean_Expr_isAppOfArity(v_e_26_, v___x_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSimpMatchDiscrsOnly___boxed(lean_object* v_e_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(v_e_30_);
lean_dec_ref(v_e_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(lean_object* v_declName_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; lean_object* v_env_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_st_ref_get(v___y_34_);
v_env_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc_ref(v_env_37_);
lean_dec(v___x_36_);
v___x_38_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_37_, v_declName_33_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object* v_declName_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_40_, v___y_41_);
lean_dec(v___y_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(lean_object* v_declName_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_44_, v___y_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___boxed(lean_object* v_declName_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(v_declName_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(lean_object* v_e_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
lean_inc_ref(v_e_66_);
v___x_75_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_66_, v_a_71_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_173_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_173_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_173_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_173_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = l_Lean_Expr_cleanupAnnotations(v_a_76_);
v___x_86_ = l_Lean_Expr_isApp(v___x_85_);
if (v___x_86_ == 0)
{
lean_dec_ref(v___x_85_);
lean_dec_ref(v_e_66_);
goto v___jp_80_;
}
else
{
lean_object* v_arg_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_arg_87_ = lean_ctor_get(v___x_85_, 1);
lean_inc_ref(v_arg_87_);
v___x_88_ = l_Lean_Expr_appFnCleanup___redArg(v___x_85_);
v___x_89_ = l_Lean_Expr_isApp(v___x_88_);
if (v___x_89_ == 0)
{
lean_dec_ref(v___x_88_);
lean_dec_ref(v_arg_87_);
lean_dec_ref(v_e_66_);
goto v___jp_80_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_90_ = l_Lean_Expr_appFnCleanup___redArg(v___x_88_);
v___x_91_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_92_ = l_Lean_Expr_isConstOf(v___x_90_, v___x_91_);
lean_dec_ref(v___x_90_);
if (v___x_92_ == 0)
{
lean_dec_ref(v_arg_87_);
lean_dec_ref(v_e_66_);
goto v___jp_80_;
}
else
{
lean_object* v___x_93_; 
lean_del_object(v___x_78_);
v___x_93_ = l_Lean_Expr_getAppFn(v_arg_87_);
if (lean_obj_tag(v___x_93_) == 4)
{
lean_object* v_declName_94_; lean_object* v___x_95_; lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_168_; 
v_declName_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_declName_94_);
lean_dec_ref(v___x_93_);
v___x_95_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_94_, v_a_73_);
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_168_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_168_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_168_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
if (lean_obj_tag(v_a_96_) == 1)
{
lean_object* v_val_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_161_; 
lean_del_object(v___x_98_);
v_val_100_ = lean_ctor_get(v_a_96_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v_a_96_);
if (v_isSharedCheck_161_ == 0)
{
v___x_102_ = v_a_96_;
v_isShared_103_ = v_isSharedCheck_161_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_val_100_);
lean_dec(v_a_96_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_161_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_val_100_, v_arg_87_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_152_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_152_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_152_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_152_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
if (lean_obj_tag(v_a_105_) == 1)
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_143_; 
lean_del_object(v___x_107_);
lean_del_object(v___x_102_);
lean_dec_ref(v_e_66_);
v_val_109_ = lean_ctor_get(v_a_105_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v_a_105_);
if (v_isSharedCheck_143_ == 0)
{
v___x_111_ = v_a_105_;
v_isShared_112_ = v_isSharedCheck_143_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v_a_105_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_143_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_expr_113_; lean_object* v_proof_x3f_114_; uint8_t v_cache_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_142_; 
v_expr_113_ = lean_ctor_get(v_val_109_, 0);
v_proof_x3f_114_ = lean_ctor_get(v_val_109_, 1);
v_cache_115_ = lean_ctor_get_uint8(v_val_109_, sizeof(void*)*2);
v_isSharedCheck_142_ = !lean_is_exclusive(v_val_109_);
if (v_isSharedCheck_142_ == 0)
{
v___x_117_ = v_val_109_;
v_isShared_118_ = v_isSharedCheck_142_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_proof_x3f_114_);
lean_inc(v_expr_113_);
lean_dec(v_val_109_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_142_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(v_expr_113_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_133_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_133_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_133_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_133_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v_a_120_);
v___x_125_ = v___x_117_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_120_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_proof_x3f_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_132_, sizeof(void*)*2, v_cache_115_);
v___x_125_ = v_reuseFailAlloc_132_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set_tag(v___x_111_, 0);
lean_ctor_set(v___x_111_, 0, v___x_125_);
v___x_127_ = v___x_111_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_127_);
v___x_129_ = v___x_122_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_del_object(v___x_117_);
lean_dec(v_proof_x3f_114_);
lean_del_object(v___x_111_);
v_a_134_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_119_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_119_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
lean_dec(v_a_105_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_145_, 0, v_e_66_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*2, v___x_92_);
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 0);
lean_ctor_set(v___x_102_, 0, v___x_145_);
v___x_147_ = v___x_102_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_151_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_149_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_147_);
v___x_149_ = v___x_107_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_del_object(v___x_102_);
lean_dec_ref(v_e_66_);
v_a_153_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_104_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_104_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_a_96_);
lean_dec_ref(v_arg_87_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_163_, 0, v_e_66_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*2, v___x_92_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_164_);
v___x_166_ = v___x_98_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v___x_93_);
lean_dec_ref(v_arg_87_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_170_, 0, v_e_66_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*2, v___x_92_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
}
}
v___jp_80_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = ((lean_object*)(l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0));
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_81_);
v___x_83_ = v___x_78_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref(v_e_66_);
v_a_174_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_75_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_75_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed(lean_object* v_e_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(v_e_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_));
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_));
v___x_212_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed), 9, 0);
v___x_213_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_210_, v___x_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10____boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_();
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object* v_s_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_));
v___x_221_ = 0;
v___x_222_ = l_Lean_Meta_Simp_Simprocs_add(v_s_216_, v___x_220_, v___x_221_, v_a_217_, v_a_218_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly___boxed(lean_object* v_s_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(v_s_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(lean_object* v_e_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
lean_inc_ref(v_e_228_);
v___x_238_ = l_Lean_Expr_cleanupAnnotations(v_e_228_);
v___x_239_ = l_Lean_Expr_isApp(v___x_238_);
if (v___x_239_ == 0)
{
lean_dec_ref(v___x_238_);
goto v___jp_234_;
}
else
{
lean_object* v_arg_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_arg_240_ = lean_ctor_get(v___x_238_, 1);
lean_inc_ref(v_arg_240_);
v___x_241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_238_);
v___x_242_ = l_Lean_Expr_isApp(v___x_241_);
if (v___x_242_ == 0)
{
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_240_);
goto v___jp_234_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = l_Lean_Expr_appFnCleanup___redArg(v___x_241_);
v___x_244_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_245_ = l_Lean_Expr_isConstOf(v___x_243_, v___x_244_);
lean_dec_ref(v___x_243_);
if (v___x_245_ == 0)
{
lean_dec_ref(v_arg_240_);
goto v___jp_234_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_e_228_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_arg_240_);
v___x_247_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
v___jp_234_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_e_228_);
v___x_236_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0___boxed(lean_object* v_e_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(v_e_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(lean_object* v_e_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_e_256_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1___boxed(lean_object* v_e_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(v_e_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_object* v_00_u03b1_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_apply_1(v_x_272_, lean_box(0));
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0___boxed(lean_object* v_00_u03b1_280_, lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(v_00_u03b1_280_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_288_, lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_289_) == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_box(0);
return v___x_290_;
}
else
{
lean_object* v_key_291_; lean_object* v_value_292_; lean_object* v_tail_293_; uint8_t v___x_294_; 
v_key_291_ = lean_ctor_get(v_x_289_, 0);
v_value_292_ = lean_ctor_get(v_x_289_, 1);
v_tail_293_ = lean_ctor_get(v_x_289_, 2);
v___x_294_ = l_Lean_ExprStructEq_beq(v_key_291_, v_a_288_);
if (v___x_294_ == 0)
{
v_x_289_ = v_tail_293_;
goto _start;
}
else
{
lean_object* v___x_296_; 
lean_inc(v_value_292_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v_value_292_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_297_, lean_object* v_x_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_297_, v_x_298_);
lean_dec(v_x_298_);
lean_dec_ref(v_a_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(lean_object* v_m_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_buckets_302_; lean_object* v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v_fold_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_buckets_302_ = lean_ctor_get(v_m_300_, 1);
v___x_303_ = lean_array_get_size(v_buckets_302_);
v___x_304_ = l_Lean_ExprStructEq_hash(v_a_301_);
v___x_305_ = 32ULL;
v___x_306_ = lean_uint64_shift_right(v___x_304_, v___x_305_);
v_fold_307_ = lean_uint64_xor(v___x_304_, v___x_306_);
v___x_308_ = 16ULL;
v___x_309_ = lean_uint64_shift_right(v_fold_307_, v___x_308_);
v___x_310_ = lean_uint64_xor(v_fold_307_, v___x_309_);
v___x_311_ = lean_uint64_to_usize(v___x_310_);
v___x_312_ = lean_usize_of_nat(v___x_303_);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_sub(v___x_312_, v___x_313_);
v___x_315_ = lean_usize_land(v___x_311_, v___x_314_);
v___x_316_ = lean_array_uget_borrowed(v_buckets_302_, v___x_315_);
v___x_317_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_301_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_318_, v_a_319_);
lean_dec_ref(v_a_319_);
lean_dec_ref(v_m_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
return v_x_321_;
}
else
{
lean_object* v_key_323_; lean_object* v_value_324_; lean_object* v_tail_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_348_; 
v_key_323_ = lean_ctor_get(v_x_322_, 0);
v_value_324_ = lean_ctor_get(v_x_322_, 1);
v_tail_325_ = lean_ctor_get(v_x_322_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_322_);
if (v_isSharedCheck_348_ == 0)
{
v___x_327_ = v_x_322_;
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_tail_325_);
lean_inc(v_value_324_);
lean_inc(v_key_323_);
lean_dec(v_x_322_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v_fold_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_329_ = lean_array_get_size(v_x_321_);
v___x_330_ = l_Lean_ExprStructEq_hash(v_key_323_);
v___x_331_ = 32ULL;
v___x_332_ = lean_uint64_shift_right(v___x_330_, v___x_331_);
v_fold_333_ = lean_uint64_xor(v___x_330_, v___x_332_);
v___x_334_ = 16ULL;
v___x_335_ = lean_uint64_shift_right(v_fold_333_, v___x_334_);
v___x_336_ = lean_uint64_xor(v_fold_333_, v___x_335_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = lean_usize_of_nat(v___x_329_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v___x_338_, v___x_339_);
v___x_341_ = lean_usize_land(v___x_337_, v___x_340_);
v___x_342_ = lean_array_uget_borrowed(v_x_321_, v___x_341_);
lean_inc(v___x_342_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 2, v___x_342_);
v___x_344_ = v___x_327_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_key_323_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_value_324_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v___x_342_);
v___x_344_ = v_reuseFailAlloc_347_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; 
v___x_345_ = lean_array_uset(v_x_321_, v___x_341_, v___x_344_);
v_x_321_ = v___x_345_;
v_x_322_ = v_tail_325_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_349_, lean_object* v_source_350_, lean_object* v_target_351_){
_start:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = lean_array_get_size(v_source_350_);
v___x_353_ = lean_nat_dec_lt(v_i_349_, v___x_352_);
if (v___x_353_ == 0)
{
lean_dec_ref(v_source_350_);
lean_dec(v_i_349_);
return v_target_351_;
}
else
{
lean_object* v_es_354_; lean_object* v___x_355_; lean_object* v_source_356_; lean_object* v_target_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_es_354_ = lean_array_fget(v_source_350_, v_i_349_);
v___x_355_ = lean_box(0);
v_source_356_ = lean_array_fset(v_source_350_, v_i_349_, v___x_355_);
v_target_357_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_351_, v_es_354_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_i_349_, v___x_358_);
lean_dec(v_i_349_);
v_i_349_ = v___x_359_;
v_source_350_ = v_source_356_;
v_target_351_ = v_target_357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_nbuckets_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_362_ = lean_array_get_size(v_data_361_);
v___x_363_ = lean_unsigned_to_nat(2u);
v_nbuckets_364_ = lean_nat_mul(v___x_362_, v___x_363_);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_box(0);
v___x_367_ = lean_mk_array(v_nbuckets_364_, v___x_366_);
v___x_368_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_365_, v_data_361_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
else
{
lean_object* v_key_372_; lean_object* v_tail_373_; uint8_t v___x_374_; 
v_key_372_ = lean_ctor_get(v_x_370_, 0);
v_tail_373_ = lean_ctor_get(v_x_370_, 2);
v___x_374_ = l_Lean_ExprStructEq_beq(v_key_372_, v_a_369_);
if (v___x_374_ == 0)
{
v_x_370_ = v_tail_373_;
goto _start;
}
else
{
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___redArg(v_a_376_, v_x_377_);
lean_dec(v_x_377_);
lean_dec_ref(v_a_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_380_, lean_object* v_b_381_, lean_object* v_x_382_){
_start:
{
if (lean_obj_tag(v_x_382_) == 0)
{
lean_dec(v_b_381_);
lean_dec_ref(v_a_380_);
return v_x_382_;
}
else
{
lean_object* v_key_383_; lean_object* v_value_384_; lean_object* v_tail_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_397_; 
v_key_383_ = lean_ctor_get(v_x_382_, 0);
v_value_384_ = lean_ctor_get(v_x_382_, 1);
v_tail_385_ = lean_ctor_get(v_x_382_, 2);
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_382_);
if (v_isSharedCheck_397_ == 0)
{
v___x_387_ = v_x_382_;
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_tail_385_);
lean_inc(v_value_384_);
lean_inc(v_key_383_);
lean_dec(v_x_382_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
uint8_t v___x_389_; 
v___x_389_ = l_Lean_ExprStructEq_beq(v_key_383_, v_a_380_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_a_380_, v_b_381_, v_tail_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 2, v___x_390_);
v___x_392_ = v___x_387_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_key_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_value_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
else
{
lean_object* v___x_395_; 
lean_dec(v_value_384_);
lean_dec(v_key_383_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_b_381_);
lean_ctor_set(v___x_387_, 0, v_a_380_);
v___x_395_ = v___x_387_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_b_381_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_tail_385_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(lean_object* v_m_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v_size_401_; lean_object* v_buckets_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_445_; 
v_size_401_ = lean_ctor_get(v_m_398_, 0);
v_buckets_402_ = lean_ctor_get(v_m_398_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_m_398_);
if (v_isSharedCheck_445_ == 0)
{
v___x_404_ = v_m_398_;
v_isShared_405_ = v_isSharedCheck_445_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_buckets_402_);
lean_inc(v_size_401_);
lean_dec(v_m_398_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_445_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v_fold_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v_bkt_419_; uint8_t v___x_420_; 
v___x_406_ = lean_array_get_size(v_buckets_402_);
v___x_407_ = l_Lean_ExprStructEq_hash(v_a_399_);
v___x_408_ = 32ULL;
v___x_409_ = lean_uint64_shift_right(v___x_407_, v___x_408_);
v_fold_410_ = lean_uint64_xor(v___x_407_, v___x_409_);
v___x_411_ = 16ULL;
v___x_412_ = lean_uint64_shift_right(v_fold_410_, v___x_411_);
v___x_413_ = lean_uint64_xor(v_fold_410_, v___x_412_);
v___x_414_ = lean_uint64_to_usize(v___x_413_);
v___x_415_ = lean_usize_of_nat(v___x_406_);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_sub(v___x_415_, v___x_416_);
v___x_418_ = lean_usize_land(v___x_414_, v___x_417_);
v_bkt_419_ = lean_array_uget_borrowed(v_buckets_402_, v___x_418_);
v___x_420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___redArg(v_a_399_, v_bkt_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v_size_x27_422_; lean_object* v___x_423_; lean_object* v_buckets_x27_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v_size_x27_422_ = lean_nat_add(v_size_401_, v___x_421_);
lean_dec(v_size_401_);
lean_inc(v_bkt_419_);
v___x_423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_423_, 0, v_a_399_);
lean_ctor_set(v___x_423_, 1, v_b_400_);
lean_ctor_set(v___x_423_, 2, v_bkt_419_);
v_buckets_x27_424_ = lean_array_uset(v_buckets_402_, v___x_418_, v___x_423_);
v___x_425_ = lean_unsigned_to_nat(4u);
v___x_426_ = lean_nat_mul(v_size_x27_422_, v___x_425_);
v___x_427_ = lean_unsigned_to_nat(3u);
v___x_428_ = lean_nat_div(v___x_426_, v___x_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_array_get_size(v_buckets_x27_424_);
v___x_430_ = lean_nat_dec_le(v___x_428_, v___x_429_);
lean_dec(v___x_428_);
if (v___x_430_ == 0)
{
lean_object* v_val_431_; lean_object* v___x_433_; 
v_val_431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_424_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_val_431_);
lean_ctor_set(v___x_404_, 0, v_size_x27_422_);
v___x_433_ = v___x_404_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_val_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
lean_object* v___x_436_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_buckets_x27_424_);
lean_ctor_set(v___x_404_, 0, v_size_x27_422_);
v___x_436_ = v___x_404_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_size_x27_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_buckets_x27_424_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v___x_438_; lean_object* v_buckets_x27_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
lean_inc(v_bkt_419_);
v___x_438_ = lean_box(0);
v_buckets_x27_439_ = lean_array_uset(v_buckets_402_, v___x_418_, v___x_438_);
v___x_440_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_a_399_, v_b_400_, v_bkt_419_);
v___x_441_ = lean_array_uset(v_buckets_x27_439_, v___x_418_, v___x_440_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_441_);
v___x_443_ = v___x_404_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_size_401_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(lean_object* v_a_446_, lean_object* v_e_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = lean_st_ref_take(v_a_446_);
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v___x_450_, v_e_447_, v_a_448_);
v___x_452_ = lean_st_ref_set(v_a_446_, v___x_451_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed(lean_object* v_a_454_, lean_object* v_e_455_, lean_object* v_a_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(v_a_454_, v_e_455_, v_a_456_);
lean_dec(v_a_454_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_459_, lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_apply_1(v_x_460_, lean_box(0));
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_468_, lean_object* v_x_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(v_00_u03b1_468_, v_x_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_475_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = l_Lean_maxRecDepthErrorMessage;
v___x_482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_484_ = l_Lean_MessageData_ofFormat(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_486_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_487_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_488_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_ref_488_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___y_504_; lean_object* v_fileName_513_; lean_object* v_fileMap_514_; lean_object* v_options_515_; lean_object* v_currRecDepth_516_; lean_object* v_maxRecDepth_517_; lean_object* v_ref_518_; lean_object* v_currNamespace_519_; lean_object* v_openDecls_520_; lean_object* v_initHeartbeats_521_; lean_object* v_maxHeartbeats_522_; lean_object* v_quotContext_523_; lean_object* v_currMacroScope_524_; uint8_t v_diag_525_; lean_object* v_cancelTk_x3f_526_; uint8_t v_suppressElabErrors_527_; lean_object* v_inheritedTraceOptions_528_; uint8_t v___x_529_; 
v_fileName_513_ = lean_ctor_get(v___y_500_, 0);
lean_inc_ref(v_fileName_513_);
v_fileMap_514_ = lean_ctor_get(v___y_500_, 1);
lean_inc_ref(v_fileMap_514_);
v_options_515_ = lean_ctor_get(v___y_500_, 2);
lean_inc_ref(v_options_515_);
v_currRecDepth_516_ = lean_ctor_get(v___y_500_, 3);
lean_inc(v_currRecDepth_516_);
v_maxRecDepth_517_ = lean_ctor_get(v___y_500_, 4);
lean_inc(v_maxRecDepth_517_);
v_ref_518_ = lean_ctor_get(v___y_500_, 5);
lean_inc(v_ref_518_);
v_currNamespace_519_ = lean_ctor_get(v___y_500_, 6);
lean_inc(v_currNamespace_519_);
v_openDecls_520_ = lean_ctor_get(v___y_500_, 7);
lean_inc(v_openDecls_520_);
v_initHeartbeats_521_ = lean_ctor_get(v___y_500_, 8);
lean_inc(v_initHeartbeats_521_);
v_maxHeartbeats_522_ = lean_ctor_get(v___y_500_, 9);
lean_inc(v_maxHeartbeats_522_);
v_quotContext_523_ = lean_ctor_get(v___y_500_, 10);
lean_inc(v_quotContext_523_);
v_currMacroScope_524_ = lean_ctor_get(v___y_500_, 11);
lean_inc(v_currMacroScope_524_);
v_diag_525_ = lean_ctor_get_uint8(v___y_500_, sizeof(void*)*14);
v_cancelTk_x3f_526_ = lean_ctor_get(v___y_500_, 12);
lean_inc(v_cancelTk_x3f_526_);
v_suppressElabErrors_527_ = lean_ctor_get_uint8(v___y_500_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_528_ = lean_ctor_get(v___y_500_, 13);
lean_inc_ref(v_inheritedTraceOptions_528_);
lean_dec_ref(v___y_500_);
v___x_529_ = lean_nat_dec_eq(v_currRecDepth_516_, v_maxRecDepth_517_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_currRecDepth_516_, v___x_530_);
lean_dec(v_currRecDepth_516_);
v___x_532_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_532_, 0, v_fileName_513_);
lean_ctor_set(v___x_532_, 1, v_fileMap_514_);
lean_ctor_set(v___x_532_, 2, v_options_515_);
lean_ctor_set(v___x_532_, 3, v___x_531_);
lean_ctor_set(v___x_532_, 4, v_maxRecDepth_517_);
lean_ctor_set(v___x_532_, 5, v_ref_518_);
lean_ctor_set(v___x_532_, 6, v_currNamespace_519_);
lean_ctor_set(v___x_532_, 7, v_openDecls_520_);
lean_ctor_set(v___x_532_, 8, v_initHeartbeats_521_);
lean_ctor_set(v___x_532_, 9, v_maxHeartbeats_522_);
lean_ctor_set(v___x_532_, 10, v_quotContext_523_);
lean_ctor_set(v___x_532_, 11, v_currMacroScope_524_);
lean_ctor_set(v___x_532_, 12, v_cancelTk_x3f_526_);
lean_ctor_set(v___x_532_, 13, v_inheritedTraceOptions_528_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*14, v_diag_525_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*14 + 1, v_suppressElabErrors_527_);
lean_inc(v___y_501_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
v___x_533_ = lean_apply_6(v_x_496_, v___y_497_, v___y_498_, v___y_499_, v___x_532_, v___y_501_, lean_box(0));
v___y_504_ = v___x_533_;
goto v___jp_503_;
}
else
{
lean_object* v___x_534_; 
lean_dec_ref(v_inheritedTraceOptions_528_);
lean_dec(v_cancelTk_x3f_526_);
lean_dec(v_currMacroScope_524_);
lean_dec(v_quotContext_523_);
lean_dec(v_maxHeartbeats_522_);
lean_dec(v_initHeartbeats_521_);
lean_dec(v_openDecls_520_);
lean_dec(v_currNamespace_519_);
lean_dec(v_maxRecDepth_517_);
lean_dec(v_currRecDepth_516_);
lean_dec_ref(v_options_515_);
lean_dec_ref(v_fileMap_514_);
lean_dec_ref(v_fileName_513_);
lean_dec_ref(v_x_496_);
v___x_534_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_518_);
v___y_504_ = v___x_534_;
goto v___jp_503_;
}
v___jp_503_:
{
if (lean_obj_tag(v___y_504_) == 0)
{
return v___y_504_;
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___y_504_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___y_504_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___y_504_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___y_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
return v_res_542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_543_; lean_object* v_dummy_544_; 
v___x_543_ = lean_box(0);
v_dummy_544_ = l_Lean_Expr_sort___override(v___x_543_);
return v_dummy_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(lean_object* v_pre_545_, lean_object* v_post_546_, size_t v_sz_547_, size_t v_i_548_, lean_object* v_bs_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_lt(v_i_548_, v_sz_547_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
lean_dec_ref(v_post_546_);
lean_dec_ref(v_pre_545_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_bs_549_);
return v___x_557_;
}
else
{
lean_object* v_v_558_; lean_object* v___x_559_; 
v_v_558_ = lean_array_uget_borrowed(v_bs_549_, v_i_548_);
lean_inc(v_v_558_);
lean_inc_ref(v_post_546_);
lean_inc_ref(v_pre_545_);
v___x_559_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_545_, v_post_546_, v_v_558_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; lean_object* v_bs_x27_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v___x_559_);
v___x_561_ = lean_unsigned_to_nat(0u);
v_bs_x27_562_ = lean_array_uset(v_bs_549_, v_i_548_, v___x_561_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_548_, v___x_563_);
v___x_565_ = lean_array_uset(v_bs_x27_562_, v_i_548_, v_a_560_);
v_i_548_ = v___x_564_;
v_bs_549_ = v___x_565_;
goto _start;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_bs_549_);
lean_dec_ref(v_post_546_);
lean_dec_ref(v_pre_545_);
v_a_567_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_559_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_559_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(lean_object* v_pre_575_, lean_object* v_post_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
if (lean_obj_tag(v_x_577_) == 5)
{
lean_object* v_fn_586_; lean_object* v_arg_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_fn_586_ = lean_ctor_get(v_x_577_, 0);
lean_inc_ref(v_fn_586_);
v_arg_587_ = lean_ctor_get(v_x_577_, 1);
lean_inc_ref(v_arg_587_);
lean_dec_ref(v_x_577_);
v___x_588_ = lean_array_set(v_x_578_, v_x_579_, v_arg_587_);
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_sub(v_x_579_, v___x_589_);
lean_dec(v_x_579_);
v_x_577_ = v_fn_586_;
v_x_578_ = v___x_588_;
v_x_579_ = v___x_590_;
goto _start;
}
else
{
lean_object* v___x_592_; 
lean_dec(v_x_579_);
lean_inc_ref(v_post_576_);
lean_inc_ref(v_pre_575_);
v___x_592_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_575_, v_post_576_, v_x_577_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; size_t v_sz_594_; size_t v___x_595_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
v_sz_594_ = lean_array_size(v_x_578_);
v___x_595_ = ((size_t)0ULL);
lean_inc_ref(v_post_576_);
lean_inc_ref(v_pre_575_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_575_, v_post_576_, v_sz_594_, v___x_595_, v_x_578_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref(v___x_596_);
v___x_598_ = l_Lean_mkAppN(v_a_593_, v_a_597_);
lean_dec(v_a_597_);
v___x_599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_575_, v_post_576_, v___x_598_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_599_;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_a_593_);
lean_dec_ref(v_post_576_);
lean_dec_ref(v_pre_575_);
v_a_600_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_596_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_dec_ref(v_x_578_);
lean_dec_ref(v_post_576_);
lean_dec_ref(v_pre_575_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(lean_object* v_pre_608_, lean_object* v_e_609_, lean_object* v_post_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; uint8_t v___y_624_; uint8_t v___y_625_; lean_object* v___y_635_; uint8_t v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; lean_object* v___y_652_; uint8_t v___y_653_; lean_object* v___x_660_; 
lean_inc_ref(v_pre_608_);
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc(v___y_613_);
lean_inc_ref(v___y_612_);
lean_inc_ref(v_e_609_);
v___x_660_ = lean_apply_6(v_pre_608_, v_e_609_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, lean_box(0));
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_750_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_750_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_750_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_750_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___y_666_; 
switch(lean_obj_tag(v_a_661_))
{
case 0:
{
lean_object* v_e_740_; lean_object* v___x_742_; 
lean_dec_ref(v_post_610_);
lean_dec_ref(v_e_609_);
lean_dec_ref(v_pre_608_);
v_e_740_ = lean_ctor_get(v_a_661_, 0);
lean_inc_ref(v_e_740_);
lean_dec_ref(v_a_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v_e_740_);
v___x_742_ = v___x_663_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_e_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
case 1:
{
lean_object* v_e_744_; lean_object* v___x_745_; 
lean_del_object(v___x_663_);
lean_dec_ref(v_e_609_);
v_e_744_ = lean_ctor_get(v_a_661_, 0);
lean_inc_ref(v_e_744_);
lean_dec_ref(v_a_661_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_745_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_e_744_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref(v___x_745_);
v___x_747_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v_a_746_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_747_;
}
else
{
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_745_;
}
}
default: 
{
lean_object* v_e_x3f_748_; 
lean_del_object(v___x_663_);
v_e_x3f_748_ = lean_ctor_get(v_a_661_, 0);
lean_inc(v_e_x3f_748_);
lean_dec_ref(v_a_661_);
if (lean_obj_tag(v_e_x3f_748_) == 0)
{
v___y_666_ = v_e_609_;
goto v___jp_665_;
}
else
{
lean_object* v_val_749_; 
lean_dec_ref(v_e_609_);
v_val_749_ = lean_ctor_get(v_e_x3f_748_, 0);
lean_inc(v_val_749_);
lean_dec_ref(v_e_x3f_748_);
v___y_666_ = v_val_749_;
goto v___jp_665_;
}
}
}
v___jp_665_:
{
switch(lean_obj_tag(v___y_666_))
{
case 7:
{
lean_object* v_binderName_667_; lean_object* v_binderType_668_; lean_object* v_body_669_; uint8_t v_binderInfo_670_; lean_object* v___x_671_; 
v_binderName_667_ = lean_ctor_get(v___y_666_, 0);
lean_inc(v_binderName_667_);
v_binderType_668_ = lean_ctor_get(v___y_666_, 1);
v_body_669_ = lean_ctor_get(v___y_666_, 2);
v_binderInfo_670_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_668_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_binderType_668_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref(v___x_671_);
lean_inc_ref(v_body_669_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_673_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_body_669_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; size_t v___x_675_; size_t v___x_676_; uint8_t v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_673_);
v___x_675_ = lean_ptr_addr(v_binderType_668_);
v___x_676_ = lean_ptr_addr(v_a_672_);
v___x_677_ = lean_usize_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
v___y_648_ = v_a_674_;
v___y_649_ = v_a_672_;
v___y_650_ = v___y_666_;
v___y_651_ = v_binderInfo_670_;
v___y_652_ = v_binderName_667_;
v___y_653_ = v___x_677_;
goto v___jp_647_;
}
else
{
size_t v___x_678_; size_t v___x_679_; uint8_t v___x_680_; 
v___x_678_ = lean_ptr_addr(v_body_669_);
v___x_679_ = lean_ptr_addr(v_a_674_);
v___x_680_ = lean_usize_dec_eq(v___x_678_, v___x_679_);
v___y_648_ = v_a_674_;
v___y_649_ = v_a_672_;
v___y_650_ = v___y_666_;
v___y_651_ = v_binderInfo_670_;
v___y_652_ = v_binderName_667_;
v___y_653_ = v___x_680_;
goto v___jp_647_;
}
}
else
{
lean_dec(v_a_672_);
lean_dec_ref(v___y_666_);
lean_dec(v_binderName_667_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_673_;
}
}
else
{
lean_dec_ref(v___y_666_);
lean_dec(v_binderName_667_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_671_;
}
}
case 6:
{
lean_object* v_binderName_681_; lean_object* v_binderType_682_; lean_object* v_body_683_; uint8_t v_binderInfo_684_; lean_object* v___x_685_; 
v_binderName_681_ = lean_ctor_get(v___y_666_, 0);
lean_inc(v_binderName_681_);
v_binderType_682_ = lean_ctor_get(v___y_666_, 1);
v_body_683_ = lean_ctor_get(v___y_666_, 2);
v_binderInfo_684_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_682_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_685_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_binderType_682_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref(v___x_685_);
lean_inc_ref(v_body_683_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_body_683_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; size_t v___x_689_; size_t v___x_690_; uint8_t v___x_691_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref(v___x_687_);
v___x_689_ = lean_ptr_addr(v_binderType_682_);
v___x_690_ = lean_ptr_addr(v_a_686_);
v___x_691_ = lean_usize_dec_eq(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
v___y_635_ = v_a_686_;
v___y_636_ = v_binderInfo_684_;
v___y_637_ = v___y_666_;
v___y_638_ = v_a_688_;
v___y_639_ = v_binderName_681_;
v___y_640_ = v___x_691_;
goto v___jp_634_;
}
else
{
size_t v___x_692_; size_t v___x_693_; uint8_t v___x_694_; 
v___x_692_ = lean_ptr_addr(v_body_683_);
v___x_693_ = lean_ptr_addr(v_a_688_);
v___x_694_ = lean_usize_dec_eq(v___x_692_, v___x_693_);
v___y_635_ = v_a_686_;
v___y_636_ = v_binderInfo_684_;
v___y_637_ = v___y_666_;
v___y_638_ = v_a_688_;
v___y_639_ = v_binderName_681_;
v___y_640_ = v___x_694_;
goto v___jp_634_;
}
}
else
{
lean_dec(v_a_686_);
lean_dec_ref(v___y_666_);
lean_dec(v_binderName_681_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_687_;
}
}
else
{
lean_dec(v_binderName_681_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_685_;
}
}
case 8:
{
lean_object* v_declName_695_; lean_object* v_type_696_; lean_object* v_value_697_; lean_object* v_body_698_; uint8_t v_nondep_699_; lean_object* v___x_700_; 
v_declName_695_ = lean_ctor_get(v___y_666_, 0);
lean_inc(v_declName_695_);
v_type_696_ = lean_ctor_get(v___y_666_, 1);
v_value_697_ = lean_ctor_get(v___y_666_, 2);
v_body_698_ = lean_ctor_get(v___y_666_, 3);
lean_inc_ref(v_body_698_);
v_nondep_699_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_696_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_700_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_type_696_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v___x_700_);
lean_inc_ref(v_value_697_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_702_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_value_697_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
lean_inc_ref(v_body_698_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_body_698_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
v___x_706_ = lean_ptr_addr(v_type_696_);
v___x_707_ = lean_ptr_addr(v_a_701_);
v___x_708_ = lean_usize_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
v___y_618_ = v_a_701_;
v___y_619_ = v_body_698_;
v___y_620_ = v_a_703_;
v___y_621_ = v___y_666_;
v___y_622_ = v_declName_695_;
v___y_623_ = v_a_705_;
v___y_624_ = v_nondep_699_;
v___y_625_ = v___x_708_;
goto v___jp_617_;
}
else
{
size_t v___x_709_; size_t v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_ptr_addr(v_value_697_);
v___x_710_ = lean_ptr_addr(v_a_703_);
v___x_711_ = lean_usize_dec_eq(v___x_709_, v___x_710_);
v___y_618_ = v_a_701_;
v___y_619_ = v_body_698_;
v___y_620_ = v_a_703_;
v___y_621_ = v___y_666_;
v___y_622_ = v_declName_695_;
v___y_623_ = v_a_705_;
v___y_624_ = v_nondep_699_;
v___y_625_ = v___x_711_;
goto v___jp_617_;
}
}
else
{
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec_ref(v_body_698_);
lean_dec_ref(v___y_666_);
lean_dec(v_declName_695_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_704_;
}
}
else
{
lean_dec(v_a_701_);
lean_dec_ref(v_body_698_);
lean_dec(v_declName_695_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_702_;
}
}
else
{
lean_dec_ref(v_body_698_);
lean_dec_ref(v___y_666_);
lean_dec(v_declName_695_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_700_;
}
}
case 5:
{
lean_object* v_dummy_712_; lean_object* v_nargs_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_dummy_712_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0);
v_nargs_713_ = l_Lean_Expr_getAppNumArgs(v___y_666_);
lean_inc(v_nargs_713_);
v___x_714_ = lean_mk_array(v_nargs_713_, v_dummy_712_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = lean_nat_sub(v_nargs_713_, v___x_715_);
lean_dec(v_nargs_713_);
v___x_717_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_608_, v_post_610_, v___y_666_, v___x_714_, v___x_716_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_717_;
}
case 10:
{
lean_object* v_data_718_; lean_object* v_expr_719_; lean_object* v___x_720_; 
v_data_718_ = lean_ctor_get(v___y_666_, 0);
v_expr_719_ = lean_ctor_get(v___y_666_, 1);
lean_inc_ref(v_expr_719_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_720_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_expr_719_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; size_t v___x_722_; size_t v___x_723_; uint8_t v___x_724_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___x_720_);
v___x_722_ = lean_ptr_addr(v_expr_719_);
v___x_723_ = lean_ptr_addr(v_a_721_);
v___x_724_ = lean_usize_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc(v_data_718_);
lean_dec_ref(v___y_666_);
v___x_725_ = l_Lean_Expr_mdata___override(v_data_718_, v_a_721_);
v___x_726_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_725_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; 
lean_dec(v_a_721_);
v___x_727_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___y_666_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_727_;
}
}
else
{
lean_dec_ref(v___y_666_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_720_;
}
}
case 11:
{
lean_object* v_typeName_728_; lean_object* v_idx_729_; lean_object* v_struct_730_; lean_object* v___x_731_; 
v_typeName_728_ = lean_ctor_get(v___y_666_, 0);
v_idx_729_ = lean_ctor_get(v___y_666_, 1);
v_struct_730_ = lean_ctor_get(v___y_666_, 2);
lean_inc_ref(v_struct_730_);
lean_inc_ref(v_post_610_);
lean_inc_ref(v_pre_608_);
v___x_731_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_608_, v_post_610_, v_struct_730_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; size_t v___x_733_; size_t v___x_734_; uint8_t v___x_735_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = lean_ptr_addr(v_struct_730_);
v___x_734_ = lean_ptr_addr(v_a_732_);
v___x_735_ = lean_usize_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_inc(v_idx_729_);
lean_inc(v_typeName_728_);
lean_dec_ref(v___y_666_);
v___x_736_ = l_Lean_Expr_proj___override(v_typeName_728_, v_idx_729_, v_a_732_);
v___x_737_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_736_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; 
lean_dec(v_a_732_);
v___x_738_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___y_666_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_738_;
}
}
else
{
lean_dec_ref(v___y_666_);
lean_dec_ref(v_post_610_);
lean_dec_ref(v_pre_608_);
return v___x_731_;
}
}
default: 
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___y_666_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_739_;
}
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_post_610_);
lean_dec_ref(v_e_609_);
lean_dec_ref(v_pre_608_);
v_a_751_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_660_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_660_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
v___jp_617_:
{
if (v___y_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v___y_621_);
lean_dec_ref(v___y_619_);
v___x_626_ = l_Lean_Expr_letE___override(v___y_622_, v___y_618_, v___y_620_, v___y_623_, v___y_624_);
v___x_627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_626_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_627_;
}
else
{
size_t v___x_628_; size_t v___x_629_; uint8_t v___x_630_; 
v___x_628_ = lean_ptr_addr(v___y_619_);
lean_dec_ref(v___y_619_);
v___x_629_ = lean_ptr_addr(v___y_623_);
v___x_630_ = lean_usize_dec_eq(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref(v___y_621_);
v___x_631_ = l_Lean_Expr_letE___override(v___y_622_, v___y_618_, v___y_620_, v___y_623_, v___y_624_);
v___x_632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_631_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; 
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v___y_618_);
v___x_633_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___y_621_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_633_;
}
}
}
v___jp_634_:
{
if (v___y_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec_ref(v___y_637_);
v___x_641_ = l_Lean_Expr_lam___override(v___y_639_, v___y_635_, v___y_638_, v___y_636_);
v___x_642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_641_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_642_;
}
else
{
uint8_t v___x_643_; 
v___x_643_ = l_Lean_instBEqBinderInfo_beq(v___y_636_, v___y_636_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec_ref(v___y_637_);
v___x_644_ = l_Lean_Expr_lam___override(v___y_639_, v___y_635_, v___y_638_, v___y_636_);
v___x_645_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_644_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; 
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_635_);
v___x_646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___y_637_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_646_;
}
}
}
v___jp_647_:
{
if (v___y_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref(v___y_650_);
v___x_654_ = l_Lean_Expr_forallE___override(v___y_652_, v___y_649_, v___y_648_, v___y_651_);
v___x_655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_654_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = l_Lean_instBEqBinderInfo_beq(v___y_651_, v___y_651_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v___y_650_);
v___x_657_ = l_Lean_Expr_forallE___override(v___y_652_, v___y_649_, v___y_648_, v___y_651_);
v___x_658_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___x_657_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; 
lean_dec(v___y_652_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
v___x_659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_608_, v_post_610_, v___y_650_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_759_, lean_object* v_e_760_, lean_object* v_post_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(v_pre_759_, v_e_760_, v_post_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(lean_object* v_pre_769_, lean_object* v_post_770_, lean_object* v_e_771_, lean_object* v_a_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
lean_inc(v_a_772_);
v___x_778_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_778_, 0, lean_box(0));
lean_closure_set(v___x_778_, 1, lean_box(0));
lean_closure_set(v___x_778_, 2, v_a_772_);
v___x_779_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___x_778_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_810_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_810_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_810_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_a_780_, v_e_771_);
lean_dec(v_a_780_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___f_785_; lean_object* v___x_786_; 
lean_del_object(v___x_782_);
lean_inc_ref(v_e_771_);
v___f_785_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed), 9, 3);
lean_closure_set(v___f_785_, 0, v_pre_769_);
lean_closure_set(v___f_785_, 1, v_e_771_);
lean_closure_set(v___f_785_, 2, v_post_770_);
lean_inc_ref(v___y_775_);
v___x_786_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v___f_785_, v_a_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___f_788_; lean_object* v___x_789_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_786_);
lean_inc(v_a_787_);
lean_inc(v_a_772_);
v___f_788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_788_, 0, v_a_772_);
lean_closure_set(v___f_788_, 1, v_e_771_);
lean_closure_set(v___f_788_, 2, v_a_787_);
v___x_789_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___f_788_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_797_);
v___x_791_ = v___x_789_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_dec(v___x_789_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v_a_787_);
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_787_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_a_787_);
v_a_798_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_789_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_789_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_dec_ref(v_e_771_);
return v___x_786_;
}
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; 
lean_dec_ref(v_e_771_);
lean_dec_ref(v_post_770_);
lean_dec_ref(v_pre_769_);
v_val_806_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_val_806_);
lean_dec_ref(v___x_784_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v_val_806_);
v___x_808_ = v___x_782_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_e_771_);
lean_dec_ref(v_post_770_);
lean_dec_ref(v_pre_769_);
v_a_811_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_779_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_779_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(lean_object* v_pre_819_, lean_object* v_post_820_, lean_object* v_e_821_, lean_object* v_a_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
lean_inc_ref(v_post_820_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc_ref(v_e_821_);
v___x_828_ = lean_apply_6(v_post_820_, v_e_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, lean_box(0));
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_847_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_847_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_847_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_847_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
switch(lean_obj_tag(v_a_829_))
{
case 0:
{
lean_object* v_e_833_; lean_object* v___x_835_; 
lean_dec_ref(v_e_821_);
lean_dec_ref(v_post_820_);
lean_dec_ref(v_pre_819_);
v_e_833_ = lean_ctor_get(v_a_829_, 0);
lean_inc_ref(v_e_833_);
lean_dec_ref(v_a_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_e_833_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_e_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
case 1:
{
lean_object* v_e_837_; lean_object* v___x_838_; 
lean_del_object(v___x_831_);
lean_dec_ref(v_e_821_);
v_e_837_ = lean_ctor_get(v_a_829_, 0);
lean_inc_ref(v_e_837_);
lean_dec_ref(v_a_829_);
v___x_838_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_819_, v_post_820_, v_e_837_, v_a_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_838_;
}
default: 
{
lean_object* v_e_x3f_839_; 
lean_dec_ref(v_post_820_);
lean_dec_ref(v_pre_819_);
v_e_x3f_839_ = lean_ctor_get(v_a_829_, 0);
lean_inc(v_e_x3f_839_);
lean_dec_ref(v_a_829_);
if (lean_obj_tag(v_e_x3f_839_) == 0)
{
lean_object* v___x_841_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_e_821_);
v___x_841_ = v___x_831_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_e_821_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; 
lean_dec_ref(v_e_821_);
v_val_843_ = lean_ctor_get(v_e_x3f_839_, 0);
lean_inc(v_val_843_);
lean_dec_ref(v_e_x3f_839_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_val_843_);
v___x_845_ = v___x_831_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_val_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_e_821_);
lean_dec_ref(v_post_820_);
lean_dec_ref(v_pre_819_);
v_a_848_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_828_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_828_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_856_, lean_object* v_post_857_, lean_object* v_e_858_, lean_object* v_a_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_856_, v_post_857_, v_e_858_, v_a_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v_a_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_866_, lean_object* v_post_867_, lean_object* v_sz_868_, lean_object* v_i_869_, lean_object* v_bs_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
size_t v_sz_boxed_877_; size_t v_i_boxed_878_; lean_object* v_res_879_; 
v_sz_boxed_877_ = lean_unbox_usize(v_sz_868_);
lean_dec(v_sz_868_);
v_i_boxed_878_ = lean_unbox_usize(v_i_869_);
lean_dec(v_i_869_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_866_, v_post_867_, v_sz_boxed_877_, v_i_boxed_878_, v_bs_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_880_, lean_object* v_post_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_880_, v_post_881_, v_x_882_, v_x_883_, v_x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___boxed(lean_object* v_pre_892_, lean_object* v_post_893_, lean_object* v_e_894_, lean_object* v_a_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_892_, v_post_893_, v_e_894_, v_a_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v_a_895_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_box(0);
v___x_903_ = lean_unsigned_to_nat(16u);
v___x_904_ = lean_mk_array(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1);
v___x_909_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_909_, 0, lean_box(0));
lean_closure_set(v___x_909_, 1, lean_box(0));
lean_closure_set(v___x_909_, 2, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(lean_object* v_input_910_, lean_object* v_pre_911_, lean_object* v_post_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_921_; 
v___x_918_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2);
v___x_919_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_918_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
v___x_921_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_911_, v_post_912_, v_input_910_, v_a_920_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_923_, 0, lean_box(0));
lean_closure_set(v___x_923_, 1, lean_box(0));
lean_closure_set(v___x_923_, 2, v_a_920_);
v___x_924_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_923_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v___x_924_, 0);
lean_dec(v_unused_932_);
v___x_926_ = v___x_924_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_dec(v___x_924_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v_a_922_);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_922_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
else
{
lean_dec(v_a_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___boxed(lean_object* v_input_933_, lean_object* v_pre_934_, lean_object* v_post_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_input_933_, v_pre_934_, v_post_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object* v_e_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0));
v___x_952_ = lean_find_expr(v___x_951_, v_e_945_);
if (lean_obj_tag(v___x_952_) == 0)
{
uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_953_ = 1;
v___x_954_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_954_, 0, v_e_945_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*2, v___x_953_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
return v___x_955_;
}
else
{
lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1004_; 
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v___x_952_, 0);
lean_dec(v_unused_1005_);
v___x_957_ = v___x_952_;
v_isShared_958_ = v_isSharedCheck_1004_;
goto v_resetjp_956_;
}
else
{
lean_dec(v___x_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1004_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_pre_959_; lean_object* v___f_960_; lean_object* v___x_961_; 
v_pre_959_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1));
v___f_960_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2));
lean_inc_ref(v_e_945_);
v___x_961_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_e_945_, v_pre_959_, v___f_960_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
lean_inc(v_a_962_);
v___x_963_ = l_Lean_Meta_mkEqRefl(v_a_962_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref(v___x_963_);
lean_inc(v_a_962_);
v___x_965_ = l_Lean_Meta_mkEq(v_e_945_, v_a_962_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_979_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_979_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_979_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_979_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = 1;
v___x_971_ = l_Lean_Meta_mkExpectedPropHint(v_a_964_, v_a_966_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_971_);
v___x_973_ = v___x_957_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_978_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_974_, 0, v_a_962_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*2, v___x_970_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_974_);
v___x_976_ = v___x_968_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_a_964_);
lean_dec(v_a_962_);
lean_del_object(v___x_957_);
v_a_980_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_965_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_965_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_a_962_);
lean_del_object(v___x_957_);
lean_dec_ref(v_e_945_);
v_a_988_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_963_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_963_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_del_object(v___x_957_);
lean_dec_ref(v_e_945_);
v_a_996_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_961_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_961_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___boxed(lean_object* v_e_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_e_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1013_, lean_object* v_m_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_1014_, v_a_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1017_, lean_object* v_m_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(v_00_u03b2_1017_, v_m_1018_, v_a_1019_);
lean_dec_ref(v_a_1019_);
lean_dec_ref(v_m_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1021_, lean_object* v_ref_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_ref_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1027_, v_ref_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
lean_inc_ref(v___y_1038_);
v___x_1041_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(v_00_u03b1_1042_, v_x_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1051_, lean_object* v_m_1052_, lean_object* v_a_1053_, lean_object* v_b_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v_m_1052_, v_a_1053_, v_b_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1056_, lean_object* v_a_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1060_, v_a_1061_, v_x_1062_);
lean_dec(v_x_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_1064_, lean_object* v_a_1065_, lean_object* v_x_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1065_, v_x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_a_1069_, lean_object* v_x_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_1068_, v_a_1069_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec_ref(v_a_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1073_, lean_object* v_data_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_data_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1076_, lean_object* v_a_1077_, lean_object* v_b_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1077_, v_b_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_1081_, lean_object* v_i_1082_, lean_object* v_source_1083_, lean_object* v_target_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_1082_, v_source_1083_, v_target_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
}
#ifdef __cplusplus
}
#endif
