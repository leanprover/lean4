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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "reduceSimpMatchDiscrsOnly"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(107, 135, 31, 2, 225, 129, 149, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(lean_object* v_e_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_8_ = stack[0].m_obj;
lean_object* v_a_9_ = stack[1].m_obj;
lean_object* v_a_10_ = stack[2].m_obj;
lean_object* v_a_11_ = stack[3].m_obj;
lean_object* v_a_12_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(v_e_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___boxed(lean_object* v_e_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(v_e_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
return v_res_26_;
}
}
uint8_t l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(lean_object* v_e_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_28_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = l_Lean_Expr_isAppOfArity(v_e_27_, v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_isSimpMatchDiscrsOnly_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_27_ = stack[0].m_obj;
uint8_t v_res_31_;
v_res_31_ = l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(v_e_27_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isSimpMatchDiscrsOnly___boxed(lean_object* v_e_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Meta_Grind_isSimpMatchDiscrsOnly(v_e_32_);
lean_dec_ref(v_e_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(lean_object* v_declName_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; lean_object* v_env_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_38_ = lean_st_ref_get(v___y_36_);
v_env_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_env_39_);
lean_dec(v___x_38_);
v___x_40_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_39_, v_declName_35_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_35_ = stack[0].m_obj;
lean_object* v___y_36_ = stack[1].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_35_, v___y_36_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object* v_declName_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_43_, v___y_44_);
lean_dec(v___y_44_);
return v_res_46_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(lean_object* v_declName_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_47_, v___y_54_);
return v___x_56_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_47_ = stack[0].m_obj;
lean_object* v___y_48_ = stack[1].m_obj;
lean_object* v___y_49_ = stack[2].m_obj;
lean_object* v___y_50_ = stack[3].m_obj;
lean_object* v___y_51_ = stack[4].m_obj;
lean_object* v___y_52_ = stack[5].m_obj;
lean_object* v___y_53_ = stack[6].m_obj;
lean_object* v___y_54_ = stack[7].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(v_declName_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___boxed(lean_object* v_declName_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0(v_declName_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
return v_res_67_;
}
}
lean_object* l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(lean_object* v_e_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_82_; 
lean_inc_ref(v_e_70_);
v___x_82_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_70_, v_a_75_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_177_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_177_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_177_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_177_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = l_Lean_Expr_cleanupAnnotations(v_a_83_);
v___x_88_ = l_Lean_Expr_isApp(v___x_87_);
if (v___x_88_ == 0)
{
lean_dec_ref(v___x_87_);
lean_del_object(v___x_85_);
lean_dec_ref(v_e_70_);
goto v___jp_79_;
}
else
{
lean_object* v_arg_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_arg_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc_ref(v_arg_89_);
v___x_90_ = l_Lean_Expr_appFnCleanup___redArg(v___x_87_);
v___x_91_ = l_Lean_Expr_isApp(v___x_90_);
if (v___x_91_ == 0)
{
lean_dec_ref(v___x_90_);
lean_dec_ref(v_arg_89_);
lean_del_object(v___x_85_);
lean_dec_ref(v_e_70_);
goto v___jp_79_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_92_ = l_Lean_Expr_appFnCleanup___redArg(v___x_90_);
v___x_93_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_94_ = l_Lean_Expr_isConstOf(v___x_92_, v___x_93_);
lean_dec_ref(v___x_92_);
if (v___x_94_ == 0)
{
lean_dec_ref(v_arg_89_);
lean_del_object(v___x_85_);
lean_dec_ref(v_e_70_);
goto v___jp_79_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Expr_getAppFn(v_arg_89_);
if (lean_obj_tag(v___x_95_) == 4)
{
lean_object* v_declName_96_; lean_object* v___x_97_; lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_170_; 
lean_del_object(v___x_85_);
v_declName_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_declName_96_);
lean_dec_ref_known(v___x_95_, 2);
v___x_97_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_96_, v_a_77_);
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_170_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_170_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_170_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
if (lean_obj_tag(v_a_98_) == 1)
{
lean_object* v_val_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_163_; 
lean_del_object(v___x_100_);
v_val_102_ = lean_ctor_get(v_a_98_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_98_);
if (v_isSharedCheck_163_ == 0)
{
v___x_104_ = v_a_98_;
v_isShared_105_ = v_isSharedCheck_163_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_val_102_);
lean_dec(v_a_98_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_163_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_val_102_, v_arg_89_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_154_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_154_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_154_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_154_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
if (lean_obj_tag(v_a_107_) == 1)
{
lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_145_; 
lean_del_object(v___x_109_);
lean_del_object(v___x_104_);
lean_dec_ref(v_e_70_);
v_val_111_ = lean_ctor_get(v_a_107_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_145_ == 0)
{
v___x_113_ = v_a_107_;
v_isShared_114_ = v_isSharedCheck_145_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_dec(v_a_107_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_145_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_expr_115_; lean_object* v_proof_x3f_116_; uint8_t v_cache_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_144_; 
v_expr_115_ = lean_ctor_get(v_val_111_, 0);
v_proof_x3f_116_ = lean_ctor_get(v_val_111_, 1);
v_cache_117_ = lean_ctor_get_uint8(v_val_111_, sizeof(void*)*2);
v_isSharedCheck_144_ = !lean_is_exclusive(v_val_111_);
if (v_isSharedCheck_144_ == 0)
{
v___x_119_ = v_val_111_;
v_isShared_120_ = v_isSharedCheck_144_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_proof_x3f_116_);
lean_inc(v_expr_115_);
lean_dec(v_val_111_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_144_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(v_expr_115_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_135_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_135_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_135_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_135_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v_a_122_);
v___x_127_ = v___x_119_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_122_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_proof_x3f_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_134_, sizeof(void*)*2, v_cache_117_);
v___x_127_ = v_reuseFailAlloc_134_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 0);
lean_ctor_set(v___x_113_, 0, v___x_127_);
v___x_129_ = v___x_113_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_133_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_129_);
v___x_131_ = v___x_124_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_del_object(v___x_119_);
lean_dec(v_proof_x3f_116_);
lean_del_object(v___x_113_);
v_a_136_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_121_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_121_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_a_107_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_147_, 0, v_e_70_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*2, v___x_94_);
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 0);
lean_ctor_set(v___x_104_, 0, v___x_147_);
v___x_149_ = v___x_104_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_153_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_149_);
v___x_151_ = v___x_109_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_del_object(v___x_104_);
lean_dec_ref(v_e_70_);
v_a_155_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_106_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_106_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v_a_98_);
lean_dec_ref(v_arg_89_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_165_, 0, v_e_70_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*2, v___x_94_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_166_);
v___x_168_ = v___x_100_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
lean_dec_ref(v___x_95_);
lean_dec_ref(v_arg_89_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_172_, 0, v_e_70_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*2, v___x_94_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_173_);
v___x_175_ = v___x_85_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v_e_70_);
v_a_178_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_82_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_82_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
v___jp_79_:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0));
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_70_ = stack[0].m_obj;
lean_object* v_a_71_ = stack[1].m_obj;
lean_object* v_a_72_ = stack[2].m_obj;
lean_object* v_a_73_ = stack[3].m_obj;
lean_object* v_a_74_ = stack[4].m_obj;
lean_object* v_a_75_ = stack[5].m_obj;
lean_object* v_a_76_ = stack[6].m_obj;
lean_object* v_a_77_ = stack[7].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(v_e_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed(lean_object* v_e_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly(v_e_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
return v_res_196_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_));
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_));
v___x_217_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed), 9, 0);
v___x_218_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_215_, v___x_216_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_219_;
v_res_219_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_();
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11____boxed(lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_();
return v_res_221_;
}
}
lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object* v_s_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_));
v___x_227_ = 0;
v___x_228_ = l_Lean_Meta_Simp_Simprocs_add(v_s_222_, v___x_226_, v___x_227_, v_a_223_, v_a_224_);
return v___x_228_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addSimpMatchDiscrsOnly_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_222_ = stack[0].m_obj;
lean_object* v_a_223_ = stack[1].m_obj;
lean_object* v_a_224_ = stack[2].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(v_s_222_, v_a_223_, v_a_224_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly___boxed(lean_object* v_s_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(v_s_230_, v_a_231_, v_a_232_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
return v_res_234_;
}
}
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(lean_object* v_e_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
lean_inc_ref(v_e_235_);
v___x_245_ = l_Lean_Expr_cleanupAnnotations(v_e_235_);
v___x_246_ = l_Lean_Expr_isApp(v___x_245_);
if (v___x_246_ == 0)
{
lean_dec_ref(v___x_245_);
goto v___jp_241_;
}
else
{
lean_object* v_arg_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_arg_247_ = lean_ctor_get(v___x_245_, 1);
lean_inc_ref(v_arg_247_);
v___x_248_ = l_Lean_Expr_appFnCleanup___redArg(v___x_245_);
v___x_249_ = l_Lean_Expr_isApp(v___x_248_);
if (v___x_249_ == 0)
{
lean_dec_ref(v___x_248_);
lean_dec_ref(v_arg_247_);
goto v___jp_241_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_248_);
v___x_251_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_252_ = l_Lean_Expr_isConstOf(v___x_250_, v___x_251_);
lean_dec_ref(v___x_250_);
if (v___x_252_ == 0)
{
lean_dec_ref(v_arg_247_);
goto v___jp_241_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref(v_e_235_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_arg_247_);
v___x_254_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
v___jp_241_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_e_235_);
v___x_243_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_235_ = stack[0].m_obj;
lean_object* v___y_236_ = stack[1].m_obj;
lean_object* v___y_237_ = stack[2].m_obj;
lean_object* v___y_238_ = stack[3].m_obj;
lean_object* v___y_239_ = stack[4].m_obj;
lean_object* v_res_256_;
v_res_256_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(v_e_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0___boxed(lean_object* v_e_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__0(v_e_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_263_;
}
}
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(lean_object* v_e_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v_e_264_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_264_ = stack[0].m_obj;
lean_object* v___y_265_ = stack[1].m_obj;
lean_object* v___y_266_ = stack[2].m_obj;
lean_object* v___y_267_ = stack[3].m_obj;
lean_object* v___y_268_ = stack[4].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(v_e_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1___boxed(lean_object* v_e_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___lam__1(v_e_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_object* v_00_u03b1_280_, lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_apply_1(v_x_281_, lean_box(0));
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_281_ = stack[1].m_obj;
lean_object* v___y_282_ = stack[2].m_obj;
lean_object* v___y_283_ = stack[3].m_obj;
lean_object* v___y_284_ = stack[4].m_obj;
lean_object* v___y_285_ = stack[5].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0___boxed(lean_object* v_00_u03b1_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(v_00_u03b1_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_298_, lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v_key_301_; lean_object* v_value_302_; lean_object* v_tail_303_; uint8_t v___x_304_; 
v_key_301_ = lean_ctor_get(v_x_299_, 0);
v_value_302_ = lean_ctor_get(v_x_299_, 1);
v_tail_303_ = lean_ctor_get(v_x_299_, 2);
v___x_304_ = l_Lean_ExprStructEq_beq(v_key_301_, v_a_298_);
if (v___x_304_ == 0)
{
v_x_299_ = v_tail_303_;
goto _start;
}
else
{
lean_object* v___x_306_; 
lean_inc(v_value_302_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v_value_302_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_307_, lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_307_, v_x_308_);
lean_dec(v_x_308_);
lean_dec_ref(v_a_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(lean_object* v_m_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_buckets_312_; lean_object* v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v_fold_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_buckets_312_ = lean_ctor_get(v_m_310_, 1);
v___x_313_ = lean_array_get_size(v_buckets_312_);
v___x_314_ = l_Lean_ExprStructEq_hash(v_a_311_);
v___x_315_ = 32ULL;
v___x_316_ = lean_uint64_shift_right(v___x_314_, v___x_315_);
v_fold_317_ = lean_uint64_xor(v___x_314_, v___x_316_);
v___x_318_ = 16ULL;
v___x_319_ = lean_uint64_shift_right(v_fold_317_, v___x_318_);
v___x_320_ = lean_uint64_xor(v_fold_317_, v___x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = lean_usize_of_nat(v___x_313_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_sub(v___x_322_, v___x_323_);
v___x_325_ = lean_usize_land(v___x_321_, v___x_324_);
v___x_326_ = lean_array_uget_borrowed(v_buckets_312_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_311_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_328_, v_a_329_);
lean_dec_ref(v_a_329_);
lean_dec_ref(v_m_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_331_, lean_object* v_b_332_, lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_dec(v_b_332_);
lean_dec_ref(v_a_331_);
return v_x_333_;
}
else
{
lean_object* v_key_334_; lean_object* v_value_335_; lean_object* v_tail_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_348_; 
v_key_334_ = lean_ctor_get(v_x_333_, 0);
v_value_335_ = lean_ctor_get(v_x_333_, 1);
v_tail_336_ = lean_ctor_get(v_x_333_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_348_ == 0)
{
v___x_338_ = v_x_333_;
v_isShared_339_ = v_isSharedCheck_348_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_tail_336_);
lean_inc(v_value_335_);
lean_inc(v_key_334_);
lean_dec(v_x_333_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_348_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_ExprStructEq_beq(v_key_334_, v_a_331_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_331_, v_b_332_, v_tail_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 2, v___x_341_);
v___x_343_ = v___x_338_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_key_334_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_value_335_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec(v_value_335_);
lean_dec(v_key_334_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v_b_332_);
lean_ctor_set(v___x_338_, 0, v_a_331_);
v___x_346_ = v___x_338_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_331_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_b_332_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_tail_336_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
return v_x_349_;
}
else
{
lean_object* v_key_351_; lean_object* v_value_352_; lean_object* v_tail_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_376_; 
v_key_351_ = lean_ctor_get(v_x_350_, 0);
v_value_352_ = lean_ctor_get(v_x_350_, 1);
v_tail_353_ = lean_ctor_get(v_x_350_, 2);
v_isSharedCheck_376_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_376_ == 0)
{
v___x_355_ = v_x_350_;
v_isShared_356_ = v_isSharedCheck_376_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_tail_353_);
lean_inc(v_value_352_);
lean_inc(v_key_351_);
lean_dec(v_x_350_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_376_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v_fold_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_357_ = lean_array_get_size(v_x_349_);
v___x_358_ = l_Lean_ExprStructEq_hash(v_key_351_);
v___x_359_ = 32ULL;
v___x_360_ = lean_uint64_shift_right(v___x_358_, v___x_359_);
v_fold_361_ = lean_uint64_xor(v___x_358_, v___x_360_);
v___x_362_ = 16ULL;
v___x_363_ = lean_uint64_shift_right(v_fold_361_, v___x_362_);
v___x_364_ = lean_uint64_xor(v_fold_361_, v___x_363_);
v___x_365_ = lean_uint64_to_usize(v___x_364_);
v___x_366_ = lean_usize_of_nat(v___x_357_);
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_sub(v___x_366_, v___x_367_);
v___x_369_ = lean_usize_land(v___x_365_, v___x_368_);
v___x_370_ = lean_array_uget_borrowed(v_x_349_, v___x_369_);
lean_inc(v___x_370_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 2, v___x_370_);
v___x_372_ = v___x_355_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_key_351_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_value_352_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v___x_370_);
v___x_372_ = v_reuseFailAlloc_375_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; 
v___x_373_ = lean_array_uset(v_x_349_, v___x_369_, v___x_372_);
v_x_349_ = v___x_373_;
v_x_350_ = v_tail_353_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_377_, lean_object* v_source_378_, lean_object* v_target_379_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_array_get_size(v_source_378_);
v___x_381_ = lean_nat_dec_lt(v_i_377_, v___x_380_);
if (v___x_381_ == 0)
{
lean_dec_ref(v_source_378_);
lean_dec(v_i_377_);
return v_target_379_;
}
else
{
lean_object* v_es_382_; lean_object* v___x_383_; lean_object* v_source_384_; lean_object* v_target_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_es_382_ = lean_array_fget(v_source_378_, v_i_377_);
v___x_383_ = lean_box(0);
v_source_384_ = lean_array_fset(v_source_378_, v_i_377_, v___x_383_);
v_target_385_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_379_, v_es_382_);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_i_377_, v___x_386_);
lean_dec(v_i_377_);
v_i_377_ = v___x_387_;
v_source_378_ = v_source_384_;
v_target_379_ = v_target_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_nbuckets_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_390_ = lean_array_get_size(v_data_389_);
v___x_391_ = lean_unsigned_to_nat(2u);
v_nbuckets_392_ = lean_nat_mul(v___x_390_, v___x_391_);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_box(0);
v___x_395_ = lean_mk_array(v_nbuckets_392_, v___x_394_);
v___x_396_ = lean_array_propagate_mark(v_data_389_, v___x_395_);
v___x_397_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_393_, v_data_389_, v___x_396_);
return v___x_397_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
else
{
lean_object* v_key_401_; lean_object* v_tail_402_; uint8_t v___x_403_; 
v_key_401_ = lean_ctor_get(v_x_399_, 0);
v_tail_402_ = lean_ctor_get(v_x_399_, 2);
v___x_403_ = l_Lean_ExprStructEq_beq(v_key_401_, v_a_398_);
if (v___x_403_ == 0)
{
v_x_399_ = v_tail_402_;
goto _start;
}
else
{
return v___x_403_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_398_ = stack[0].m_obj;
lean_object* v_x_399_ = stack[1].m_obj;
uint8_t v_res_405_;
v_res_405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_398_, v_x_399_);
stack->m_num = v_res_405_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_406_, lean_object* v_x_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_406_, v_x_407_);
lean_dec(v_x_407_);
lean_dec_ref(v_a_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(lean_object* v_m_410_, lean_object* v_a_411_, lean_object* v_b_412_){
_start:
{
lean_object* v_size_413_; lean_object* v_buckets_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_457_; 
v_size_413_ = lean_ctor_get(v_m_410_, 0);
v_buckets_414_ = lean_ctor_get(v_m_410_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_m_410_);
if (v_isSharedCheck_457_ == 0)
{
v___x_416_ = v_m_410_;
v_isShared_417_ = v_isSharedCheck_457_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_buckets_414_);
lean_inc(v_size_413_);
lean_dec(v_m_410_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_457_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; uint64_t v_fold_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; lean_object* v_bkt_431_; uint8_t v___x_432_; 
v___x_418_ = lean_array_get_size(v_buckets_414_);
v___x_419_ = l_Lean_ExprStructEq_hash(v_a_411_);
v___x_420_ = 32ULL;
v___x_421_ = lean_uint64_shift_right(v___x_419_, v___x_420_);
v_fold_422_ = lean_uint64_xor(v___x_419_, v___x_421_);
v___x_423_ = 16ULL;
v___x_424_ = lean_uint64_shift_right(v_fold_422_, v___x_423_);
v___x_425_ = lean_uint64_xor(v_fold_422_, v___x_424_);
v___x_426_ = lean_uint64_to_usize(v___x_425_);
v___x_427_ = lean_usize_of_nat(v___x_418_);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_sub(v___x_427_, v___x_428_);
v___x_430_ = lean_usize_land(v___x_426_, v___x_429_);
v_bkt_431_ = lean_array_uget_borrowed(v_buckets_414_, v___x_430_);
v___x_432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_411_, v_bkt_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v_size_x27_434_; lean_object* v___x_435_; lean_object* v_buckets_x27_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v_size_x27_434_ = lean_nat_add(v_size_413_, v___x_433_);
lean_dec(v_size_413_);
lean_inc(v_bkt_431_);
v___x_435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_435_, 0, v_a_411_);
lean_ctor_set(v___x_435_, 1, v_b_412_);
lean_ctor_set(v___x_435_, 2, v_bkt_431_);
v_buckets_x27_436_ = lean_array_uset(v_buckets_414_, v___x_430_, v___x_435_);
v___x_437_ = lean_unsigned_to_nat(4u);
v___x_438_ = lean_nat_mul(v_size_x27_434_, v___x_437_);
v___x_439_ = lean_unsigned_to_nat(3u);
v___x_440_ = lean_nat_div(v___x_438_, v___x_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_array_get_size(v_buckets_x27_436_);
v___x_442_ = lean_nat_dec_le(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
if (v___x_442_ == 0)
{
lean_object* v_val_443_; lean_object* v___x_445_; 
v_val_443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_436_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_val_443_);
lean_ctor_set(v___x_416_, 0, v_size_x27_434_);
v___x_445_ = v___x_416_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_size_x27_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_val_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v___x_448_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_buckets_x27_436_);
lean_ctor_set(v___x_416_, 0, v_size_x27_434_);
v___x_448_ = v___x_416_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_size_x27_434_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_buckets_x27_436_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v___x_450_; lean_object* v_buckets_x27_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
lean_inc(v_bkt_431_);
v___x_450_ = lean_box(0);
v_buckets_x27_451_ = lean_array_uset(v_buckets_414_, v___x_430_, v___x_450_);
v___x_452_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_411_, v_b_412_, v_bkt_431_);
v___x_453_ = lean_array_uset(v_buckets_x27_451_, v___x_430_, v___x_452_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_453_);
v___x_455_ = v___x_416_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_size_413_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(lean_object* v_a_458_, lean_object* v_e_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_st_ref_take(v_a_458_);
v___x_463_ = lean_box(0);
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v___x_462_, v_e_459_, v_a_460_);
v___x_465_ = lean_st_ref_put(v_a_458_, v___x_464_);
return v___x_463_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_458_ = stack[0].m_obj;
lean_object* v_e_459_ = stack[1].m_obj;
lean_object* v_a_460_ = stack[2].m_obj;
lean_object* v_res_466_;
v_res_466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(v_a_458_, v_e_459_, v_a_460_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed(lean_object* v_a_467_, lean_object* v_e_468_, lean_object* v_a_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(v_a_467_, v_e_468_, v_a_469_);
lean_dec(v_a_467_);
return v_res_471_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_apply_1(v_x_473_, lean_box(0));
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_473_ = stack[1].m_obj;
lean_object* v___y_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v_res_481_;
v_res_481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v_x_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(v_00_u03b1_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_489_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_box(0);
v___x_491_ = l_Lean_interruptExceptionId;
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_490_);
return v___x_492_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_496_;
v_res_496_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_498_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = l_Lean_maxRecDepthErrorMessage;
v___x_505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_507_ = l_Lean_MessageData_ofFormat(v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_509_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_510_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
return v___x_510_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_511_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_ref_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_511_ = stack[0].m_obj;
lean_object* v_res_516_;
v_res_516_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_511_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_517_);
return v_res_519_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(lean_object* v_x_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___y_528_; uint8_t v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; uint16_t v___y_543_; lean_object* v_toCold_548_; lean_object* v_currRecDepth_549_; lean_object* v_ref_550_; uint16_t v_optionFlags_551_; uint8_t v_suppressElabErrors_552_; uint8_t v_isRecordingDeps_553_; lean_object* v_maxRecDepth_554_; lean_object* v_cancelTk_x3f_555_; 
v_toCold_548_ = lean_ctor_get(v___y_524_, 0);
v_currRecDepth_549_ = lean_ctor_get(v___y_524_, 1);
v_ref_550_ = lean_ctor_get(v___y_524_, 2);
v_optionFlags_551_ = lean_ctor_get_uint16(v___y_524_, sizeof(void*)*3);
v_suppressElabErrors_552_ = lean_ctor_get_uint8(v___y_524_, sizeof(void*)*3 + 2);
v_isRecordingDeps_553_ = lean_ctor_get_uint8(v___y_524_, sizeof(void*)*3 + 3);
v_maxRecDepth_554_ = lean_ctor_get(v_toCold_548_, 3);
v_cancelTk_x3f_555_ = lean_ctor_get(v_toCold_548_, 10);
if (lean_obj_tag(v_cancelTk_x3f_555_) == 1)
{
lean_object* v_val_561_; uint8_t v___x_562_; 
v_val_561_ = lean_ctor_get(v_cancelTk_x3f_555_, 0);
v___x_562_ = l_IO_CancelToken_isSet(v_val_561_);
if (v___x_562_ == 0)
{
goto v___jp_556_;
}
else
{
lean_object* v___x_563_; lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v_x_520_);
v___x_563_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
goto v___jp_556_;
}
v___jp_527_:
{
if (lean_obj_tag(v___y_528_) == 0)
{
return v___y_528_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___y_528_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___y_528_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___y_528_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___y_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v___jp_537_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_add(v___y_542_, v___x_544_);
lean_inc_ref(v___y_540_);
v___x_546_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_546_, 0, v___y_540_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
lean_ctor_set(v___x_546_, 2, v___y_539_);
lean_ctor_set_uint16(v___x_546_, sizeof(void*)*3, v___y_543_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*3 + 2, v___y_541_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*3 + 3, v___y_538_);
lean_inc(v___y_525_);
lean_inc(v___y_523_);
lean_inc_ref(v___y_522_);
lean_inc(v___y_521_);
v___x_547_ = lean_apply_6(v_x_520_, v___y_521_, v___y_522_, v___y_523_, v___x_546_, v___y_525_, lean_box(0));
v___y_528_ = v___x_547_;
goto v___jp_527_;
}
v___jp_556_:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_nat_dec_eq(v_maxRecDepth_554_, v___x_557_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_eq(v_currRecDepth_549_, v_maxRecDepth_554_);
if (v___x_559_ == 0)
{
lean_inc(v_ref_550_);
v___y_538_ = v_isRecordingDeps_553_;
v___y_539_ = v_ref_550_;
v___y_540_ = v_toCold_548_;
v___y_541_ = v_suppressElabErrors_552_;
v___y_542_ = v_currRecDepth_549_;
v___y_543_ = v_optionFlags_551_;
goto v___jp_537_;
}
else
{
lean_object* v___x_560_; 
lean_dec_ref(v_x_520_);
lean_inc(v_ref_550_);
v___x_560_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_550_);
v___y_528_ = v___x_560_;
goto v___jp_527_;
}
}
else
{
lean_inc(v_ref_550_);
v___y_538_ = v_isRecordingDeps_553_;
v___y_539_ = v_ref_550_;
v___y_540_ = v_toCold_548_;
v___y_541_ = v_suppressElabErrors_552_;
v___y_542_ = v_currRecDepth_549_;
v___y_543_ = v_optionFlags_551_;
goto v___jp_537_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_520_ = stack[0].m_obj;
lean_object* v___y_521_ = stack[1].m_obj;
lean_object* v___y_522_ = stack[2].m_obj;
lean_object* v___y_523_ = stack[3].m_obj;
lean_object* v___y_524_ = stack[4].m_obj;
lean_object* v___y_525_ = stack[5].m_obj;
lean_object* v_res_572_;
v_res_572_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
return v_res_580_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_582_; lean_object* v_dummy_583_; 
v___x_582_ = lean_box(0);
v_dummy_583_ = l_Lean_Expr_sort___override(v___x_582_);
return v_dummy_583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(lean_object* v_pre_584_, lean_object* v_post_585_, size_t v_sz_586_, size_t v_i_587_, lean_object* v_bs_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_lt(v_i_587_, v_sz_586_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v_post_585_);
lean_dec_ref(v_pre_584_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_bs_588_);
return v___x_596_;
}
else
{
lean_object* v_v_597_; lean_object* v___x_598_; lean_object* v_bs_x27_599_; lean_object* v___x_600_; 
v_v_597_ = lean_array_uget(v_bs_588_, v_i_587_);
v___x_598_ = lean_unsigned_to_nat(0u);
v_bs_x27_599_ = lean_array_uset(v_bs_588_, v_i_587_, v___x_598_);
lean_inc_ref(v_post_585_);
lean_inc_ref(v_pre_584_);
v___x_600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_584_, v_post_585_, v_v_597_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_587_, v___x_602_);
v___x_604_ = lean_array_uset(v_bs_x27_599_, v_i_587_, v_a_601_);
v_i_587_ = v___x_603_;
v_bs_588_ = v___x_604_;
goto _start;
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_bs_x27_599_);
lean_dec_ref(v_post_585_);
lean_dec_ref(v_pre_584_);
v_a_606_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_600_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_600_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_584_ = stack[0].m_obj;
lean_object* v_post_585_ = stack[1].m_obj;
size_t v_sz_586_ = stack[2].m_num;
size_t v_i_587_ = stack[3].m_num;
lean_object* v_bs_588_ = stack[4].m_obj;
lean_object* v___y_589_ = stack[5].m_obj;
lean_object* v___y_590_ = stack[6].m_obj;
lean_object* v___y_591_ = stack[7].m_obj;
lean_object* v___y_592_ = stack[8].m_obj;
lean_object* v___y_593_ = stack[9].m_obj;
lean_object* v_res_614_;
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_584_, v_post_585_, v_sz_586_, v_i_587_, v_bs_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
stack->m_obj
 = v_res_614_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(lean_object* v_pre_615_, lean_object* v_post_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
if (lean_obj_tag(v_x_617_) == 5)
{
lean_object* v_fn_626_; lean_object* v_arg_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_fn_626_ = lean_ctor_get(v_x_617_, 0);
lean_inc_ref(v_fn_626_);
v_arg_627_ = lean_ctor_get(v_x_617_, 1);
lean_inc_ref(v_arg_627_);
lean_dec_ref_known(v_x_617_, 2);
v___x_628_ = lean_array_set(v_x_618_, v_x_619_, v_arg_627_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_sub(v_x_619_, v___x_629_);
lean_dec(v_x_619_);
v_x_617_ = v_fn_626_;
v_x_618_ = v___x_628_;
v_x_619_ = v___x_630_;
goto _start;
}
else
{
lean_object* v___x_632_; 
lean_dec(v_x_619_);
lean_inc_ref(v_post_616_);
lean_inc_ref(v_pre_615_);
v___x_632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_615_, v_post_616_, v_x_617_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v_sz_634_ = lean_array_size(v_x_618_);
v___x_635_ = ((size_t)0ULL);
lean_inc_ref(v_post_616_);
lean_inc_ref(v_pre_615_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_615_, v_post_616_, v_sz_634_, v___x_635_, v_x_618_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_mkAppN(v_a_633_, v_a_637_);
lean_dec(v_a_637_);
v___x_639_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_615_, v_post_616_, v___x_638_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
return v___x_639_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_633_);
lean_dec_ref(v_post_616_);
lean_dec_ref(v_pre_615_);
v_a_640_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_636_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_636_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_dec_ref(v_x_618_);
lean_dec_ref(v_post_616_);
lean_dec_ref(v_pre_615_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_615_ = stack[0].m_obj;
lean_object* v_post_616_ = stack[1].m_obj;
lean_object* v_x_617_ = stack[2].m_obj;
lean_object* v_x_618_ = stack[3].m_obj;
lean_object* v_x_619_ = stack[4].m_obj;
lean_object* v___y_620_ = stack[5].m_obj;
lean_object* v___y_621_ = stack[6].m_obj;
lean_object* v___y_622_ = stack[7].m_obj;
lean_object* v___y_623_ = stack[8].m_obj;
lean_object* v___y_624_ = stack[9].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_615_, v_post_616_, v_x_617_, v_x_618_, v_x_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
stack->m_obj
 = v_res_648_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(lean_object* v___x_649_, lean_object* v_pre_650_, lean_object* v_e_651_, lean_object* v_post_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Core_checkSystem(v___x_649_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_660_; 
lean_dec_ref_known(v___x_659_, 1);
lean_inc_ref(v_pre_650_);
lean_inc(v___y_657_);
lean_inc_ref(v___y_656_);
lean_inc(v___y_655_);
lean_inc_ref(v___y_654_);
lean_inc_ref(v_e_651_);
v___x_660_ = lean_apply_6(v_pre_650_, v_e_651_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, lean_box(0));
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_776_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_776_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_776_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_776_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___y_666_; 
switch(lean_obj_tag(v_a_661_))
{
case 0:
{
lean_object* v_e_766_; lean_object* v___x_768_; 
lean_dec_ref(v_post_652_);
lean_dec_ref(v_e_651_);
lean_dec_ref(v_pre_650_);
v_e_766_ = lean_ctor_get(v_a_661_, 0);
lean_inc_ref(v_e_766_);
lean_dec_ref_known(v_a_661_, 1);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v_e_766_);
v___x_768_ = v___x_663_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_e_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
case 1:
{
lean_object* v_e_770_; lean_object* v___x_771_; 
lean_del_object(v___x_663_);
lean_dec_ref(v_e_651_);
v_e_770_ = lean_ctor_get(v_a_661_, 0);
lean_inc_ref(v_e_770_);
lean_dec_ref_known(v_a_661_, 1);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_771_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_e_770_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v_a_772_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_773_;
}
else
{
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_771_;
}
}
default: 
{
lean_object* v_e_x3f_774_; 
lean_del_object(v___x_663_);
v_e_x3f_774_ = lean_ctor_get(v_a_661_, 0);
lean_inc(v_e_x3f_774_);
lean_dec_ref_known(v_a_661_, 1);
if (lean_obj_tag(v_e_x3f_774_) == 0)
{
v___y_666_ = v_e_651_;
goto v___jp_665_;
}
else
{
lean_object* v_val_775_; 
lean_dec_ref(v_e_651_);
v_val_775_ = lean_ctor_get(v_e_x3f_774_, 0);
lean_inc(v_val_775_);
lean_dec_ref_known(v_e_x3f_774_, 1);
v___y_666_ = v_val_775_;
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
v_binderType_668_ = lean_ctor_get(v___y_666_, 1);
v_body_669_ = lean_ctor_get(v___y_666_, 2);
v_binderInfo_670_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_668_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_binderType_668_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
lean_inc_ref(v_body_669_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_673_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_body_669_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; size_t v___x_675_; size_t v___x_676_; uint8_t v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = lean_ptr_addr(v_binderType_668_);
v___x_676_ = lean_ptr_addr(v_a_672_);
v___x_677_ = lean_usize_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_inc(v_binderName_667_);
lean_dec_ref_known(v___y_666_, 3);
v___x_678_ = l_Lean_Expr_forallE___override(v_binderName_667_, v_a_672_, v_a_674_, v_binderInfo_670_);
v___x_679_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_678_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_679_;
}
else
{
size_t v___x_680_; size_t v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_ptr_addr(v_body_669_);
v___x_681_ = lean_ptr_addr(v_a_674_);
v___x_682_ = lean_usize_dec_eq(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc(v_binderName_667_);
lean_dec_ref_known(v___y_666_, 3);
v___x_683_ = l_Lean_Expr_forallE___override(v_binderName_667_, v_a_672_, v_a_674_, v_binderInfo_670_);
v___x_684_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_683_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_670_, v_binderInfo_670_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc(v_binderName_667_);
lean_dec_ref_known(v___y_666_, 3);
v___x_686_ = l_Lean_Expr_forallE___override(v_binderName_667_, v_a_672_, v_a_674_, v_binderInfo_670_);
v___x_687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_686_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; 
lean_dec(v_a_674_);
lean_dec(v_a_672_);
v___x_688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___y_666_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_688_;
}
}
}
}
else
{
lean_dec(v_a_672_);
lean_dec_ref_known(v___y_666_, 3);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_673_;
}
}
else
{
lean_dec_ref_known(v___y_666_, 3);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_671_;
}
}
case 6:
{
lean_object* v_binderName_689_; lean_object* v_binderType_690_; lean_object* v_body_691_; uint8_t v_binderInfo_692_; lean_object* v___x_693_; 
v_binderName_689_ = lean_ctor_get(v___y_666_, 0);
v_binderType_690_ = lean_ctor_get(v___y_666_, 1);
v_body_691_ = lean_ctor_get(v___y_666_, 2);
v_binderInfo_692_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_690_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_693_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_binderType_690_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
lean_inc_ref(v_body_691_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_695_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_body_691_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; size_t v___x_697_; size_t v___x_698_; uint8_t v___x_699_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = lean_ptr_addr(v_binderType_690_);
v___x_698_ = lean_ptr_addr(v_a_694_);
v___x_699_ = lean_usize_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_inc(v_binderName_689_);
lean_dec_ref_known(v___y_666_, 3);
v___x_700_ = l_Lean_Expr_lam___override(v_binderName_689_, v_a_694_, v_a_696_, v_binderInfo_692_);
v___x_701_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_700_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_701_;
}
else
{
size_t v___x_702_; size_t v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_ptr_addr(v_body_691_);
v___x_703_ = lean_ptr_addr(v_a_696_);
v___x_704_ = lean_usize_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_inc(v_binderName_689_);
lean_dec_ref_known(v___y_666_, 3);
v___x_705_ = l_Lean_Expr_lam___override(v_binderName_689_, v_a_694_, v_a_696_, v_binderInfo_692_);
v___x_706_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_705_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_706_;
}
else
{
uint8_t v___x_707_; 
v___x_707_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_692_, v_binderInfo_692_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc(v_binderName_689_);
lean_dec_ref_known(v___y_666_, 3);
v___x_708_ = l_Lean_Expr_lam___override(v_binderName_689_, v_a_694_, v_a_696_, v_binderInfo_692_);
v___x_709_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_708_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; 
lean_dec(v_a_696_);
lean_dec(v_a_694_);
v___x_710_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___y_666_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_710_;
}
}
}
}
else
{
lean_dec(v_a_694_);
lean_dec_ref_known(v___y_666_, 3);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_695_;
}
}
else
{
lean_dec_ref_known(v___y_666_, 3);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_693_;
}
}
case 8:
{
lean_object* v_declName_711_; lean_object* v_type_712_; lean_object* v_value_713_; lean_object* v_body_714_; uint8_t v_nondep_715_; lean_object* v___x_716_; 
v_declName_711_ = lean_ctor_get(v___y_666_, 0);
v_type_712_ = lean_ctor_get(v___y_666_, 1);
v_value_713_ = lean_ctor_get(v___y_666_, 2);
v_body_714_ = lean_ctor_get(v___y_666_, 3);
v_nondep_715_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_712_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_716_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_type_712_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
lean_inc_ref(v_value_713_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_718_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_value_713_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
lean_inc_ref(v_body_714_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_720_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_body_714_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; size_t v___x_722_; size_t v___x_723_; uint8_t v___x_724_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_ptr_addr(v_type_712_);
v___x_723_ = lean_ptr_addr(v_a_717_);
v___x_724_ = lean_usize_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc(v_declName_711_);
lean_dec_ref_known(v___y_666_, 4);
v___x_725_ = l_Lean_Expr_letE___override(v_declName_711_, v_a_717_, v_a_719_, v_a_721_, v_nondep_715_);
v___x_726_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_725_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_726_;
}
else
{
size_t v___x_727_; size_t v___x_728_; uint8_t v___x_729_; 
v___x_727_ = lean_ptr_addr(v_value_713_);
v___x_728_ = lean_ptr_addr(v_a_719_);
v___x_729_ = lean_usize_dec_eq(v___x_727_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_inc(v_declName_711_);
lean_dec_ref_known(v___y_666_, 4);
v___x_730_ = l_Lean_Expr_letE___override(v_declName_711_, v_a_717_, v_a_719_, v_a_721_, v_nondep_715_);
v___x_731_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_730_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_731_;
}
else
{
size_t v___x_732_; size_t v___x_733_; uint8_t v___x_734_; 
v___x_732_ = lean_ptr_addr(v_body_714_);
v___x_733_ = lean_ptr_addr(v_a_721_);
v___x_734_ = lean_usize_dec_eq(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc(v_declName_711_);
lean_dec_ref_known(v___y_666_, 4);
v___x_735_ = l_Lean_Expr_letE___override(v_declName_711_, v_a_717_, v_a_719_, v_a_721_, v_nondep_715_);
v___x_736_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_735_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
lean_dec(v_a_721_);
lean_dec(v_a_719_);
lean_dec(v_a_717_);
v___x_737_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___y_666_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_737_;
}
}
}
}
else
{
lean_dec(v_a_719_);
lean_dec(v_a_717_);
lean_dec_ref_known(v___y_666_, 4);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_720_;
}
}
else
{
lean_dec(v_a_717_);
lean_dec_ref_known(v___y_666_, 4);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_718_;
}
}
else
{
lean_dec_ref_known(v___y_666_, 4);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_716_;
}
}
case 5:
{
lean_object* v_dummy_738_; lean_object* v_nargs_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_dummy_738_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0);
v_nargs_739_ = l_Lean_Expr_getAppNumArgs(v___y_666_);
lean_inc(v_nargs_739_);
v___x_740_ = lean_mk_array(v_nargs_739_, v_dummy_738_);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_sub(v_nargs_739_, v___x_741_);
lean_dec(v_nargs_739_);
v___x_743_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_650_, v_post_652_, v___y_666_, v___x_740_, v___x_742_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_743_;
}
case 10:
{
lean_object* v_data_744_; lean_object* v_expr_745_; lean_object* v___x_746_; 
v_data_744_ = lean_ctor_get(v___y_666_, 0);
v_expr_745_ = lean_ctor_get(v___y_666_, 1);
lean_inc_ref(v_expr_745_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_746_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_expr_745_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; size_t v___x_748_; size_t v___x_749_; uint8_t v___x_750_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = lean_ptr_addr(v_expr_745_);
v___x_749_ = lean_ptr_addr(v_a_747_);
v___x_750_ = lean_usize_dec_eq(v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_inc(v_data_744_);
lean_dec_ref_known(v___y_666_, 2);
v___x_751_ = l_Lean_Expr_mdata___override(v_data_744_, v_a_747_);
v___x_752_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_751_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_752_;
}
else
{
lean_object* v___x_753_; 
lean_dec(v_a_747_);
v___x_753_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___y_666_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_753_;
}
}
else
{
lean_dec_ref_known(v___y_666_, 2);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_746_;
}
}
case 11:
{
lean_object* v_typeName_754_; lean_object* v_idx_755_; lean_object* v_struct_756_; lean_object* v___x_757_; 
v_typeName_754_ = lean_ctor_get(v___y_666_, 0);
v_idx_755_ = lean_ctor_get(v___y_666_, 1);
v_struct_756_ = lean_ctor_get(v___y_666_, 2);
lean_inc_ref(v_struct_756_);
lean_inc_ref(v_post_652_);
lean_inc_ref(v_pre_650_);
v___x_757_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_650_, v_post_652_, v_struct_756_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; size_t v___x_759_; size_t v___x_760_; uint8_t v___x_761_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = lean_ptr_addr(v_struct_756_);
v___x_760_ = lean_ptr_addr(v_a_758_);
v___x_761_ = lean_usize_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_inc(v_idx_755_);
lean_inc(v_typeName_754_);
lean_dec_ref_known(v___y_666_, 3);
v___x_762_ = l_Lean_Expr_proj___override(v_typeName_754_, v_idx_755_, v_a_758_);
v___x_763_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___x_762_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_763_;
}
else
{
lean_object* v___x_764_; 
lean_dec(v_a_758_);
v___x_764_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___y_666_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_764_;
}
}
else
{
lean_dec_ref_known(v___y_666_, 3);
lean_dec_ref(v_post_652_);
lean_dec_ref(v_pre_650_);
return v___x_757_;
}
}
default: 
{
lean_object* v___x_765_; 
v___x_765_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_650_, v_post_652_, v___y_666_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_765_;
}
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v_post_652_);
lean_dec_ref(v_e_651_);
lean_dec_ref(v_pre_650_);
v_a_777_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_660_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_660_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_post_652_);
lean_dec_ref(v_e_651_);
lean_dec_ref(v_pre_650_);
v_a_785_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_659_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_659_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_649_ = stack[0].m_obj;
lean_object* v_pre_650_ = stack[1].m_obj;
lean_object* v_e_651_ = stack[2].m_obj;
lean_object* v_post_652_ = stack[3].m_obj;
lean_object* v___y_653_ = stack[4].m_obj;
lean_object* v___y_654_ = stack[5].m_obj;
lean_object* v___y_655_ = stack[6].m_obj;
lean_object* v___y_656_ = stack[7].m_obj;
lean_object* v___y_657_ = stack[8].m_obj;
lean_object* v_res_793_;
v_res_793_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(v___x_649_, v_pre_650_, v_e_651_, v_post_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed(lean_object* v___x_794_, lean_object* v_pre_795_, lean_object* v_e_796_, lean_object* v_post_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(v___x_794_, v_pre_795_, v_e_796_, v_post_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
return v_res_804_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(lean_object* v_pre_805_, lean_object* v_post_806_, lean_object* v_e_807_, lean_object* v_a_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_inc(v_a_808_);
v___x_814_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_814_, 0, lean_box(0));
lean_closure_set(v___x_814_, 1, lean_box(0));
lean_closure_set(v___x_814_, 2, v_a_808_);
v___x_815_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___x_814_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_847_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_847_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_847_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_847_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_a_816_, v_e_807_);
lean_dec(v_a_816_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; 
lean_del_object(v___x_818_);
v___x_821_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_807_);
v___f_822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_822_, 0, v___x_821_);
lean_closure_set(v___f_822_, 1, v_pre_805_);
lean_closure_set(v___f_822_, 2, v_e_807_);
lean_closure_set(v___f_822_, 3, v_post_806_);
v___x_823_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v___f_822_, v_a_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___f_825_; lean_object* v___x_826_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc_n(v_a_824_, 2);
lean_dec_ref_known(v___x_823_, 1);
lean_inc(v_a_808_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_825_, 0, v_a_808_);
lean_closure_set(v___f_825_, 1, v_e_807_);
lean_closure_set(v___f_825_, 2, v_a_824_);
v___x_826_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___f_825_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_826_, 0);
lean_dec(v_unused_834_);
v___x_828_ = v___x_826_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_dec(v___x_826_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_a_824_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_824_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_a_824_);
v_a_835_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_826_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_826_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_dec_ref(v_e_807_);
return v___x_823_;
}
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; 
lean_dec_ref(v_e_807_);
lean_dec_ref(v_post_806_);
lean_dec_ref(v_pre_805_);
v_val_843_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v___x_820_, 1);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_val_843_);
v___x_845_ = v___x_818_;
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
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_e_807_);
lean_dec_ref(v_post_806_);
lean_dec_ref(v_pre_805_);
v_a_848_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_815_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_815_);
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_805_ = stack[0].m_obj;
lean_object* v_post_806_ = stack[1].m_obj;
lean_object* v_e_807_ = stack[2].m_obj;
lean_object* v_a_808_ = stack[3].m_obj;
lean_object* v___y_809_ = stack[4].m_obj;
lean_object* v___y_810_ = stack[5].m_obj;
lean_object* v___y_811_ = stack[6].m_obj;
lean_object* v___y_812_ = stack[7].m_obj;
lean_object* v_res_856_;
v_res_856_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_805_, v_post_806_, v_e_807_, v_a_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
stack->m_obj
 = v_res_856_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(lean_object* v_pre_857_, lean_object* v_post_858_, lean_object* v_e_859_, lean_object* v_a_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
lean_inc_ref(v_post_858_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc_ref(v_e_859_);
v___x_866_ = lean_apply_6(v_post_858_, v_e_859_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, lean_box(0));
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_885_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_885_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_885_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_885_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
switch(lean_obj_tag(v_a_867_))
{
case 0:
{
lean_object* v_e_871_; lean_object* v___x_873_; 
lean_dec_ref(v_e_859_);
lean_dec_ref(v_post_858_);
lean_dec_ref(v_pre_857_);
v_e_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc_ref(v_e_871_);
lean_dec_ref_known(v_a_867_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_e_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_e_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
case 1:
{
lean_object* v_e_875_; lean_object* v___x_876_; 
lean_del_object(v___x_869_);
lean_dec_ref(v_e_859_);
v_e_875_ = lean_ctor_get(v_a_867_, 0);
lean_inc_ref(v_e_875_);
lean_dec_ref_known(v_a_867_, 1);
v___x_876_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_857_, v_post_858_, v_e_875_, v_a_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
return v___x_876_;
}
default: 
{
lean_object* v_e_x3f_877_; 
lean_dec_ref(v_post_858_);
lean_dec_ref(v_pre_857_);
v_e_x3f_877_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_e_x3f_877_);
lean_dec_ref_known(v_a_867_, 1);
if (lean_obj_tag(v_e_x3f_877_) == 0)
{
lean_object* v___x_879_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_e_859_);
v___x_879_ = v___x_869_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_e_859_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_object* v_val_881_; lean_object* v___x_883_; 
lean_dec_ref(v_e_859_);
v_val_881_ = lean_ctor_get(v_e_x3f_877_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_e_x3f_877_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_val_881_);
v___x_883_ = v___x_869_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_val_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_e_859_);
lean_dec_ref(v_post_858_);
lean_dec_ref(v_pre_857_);
v_a_886_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_866_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_866_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_857_ = stack[0].m_obj;
lean_object* v_post_858_ = stack[1].m_obj;
lean_object* v_e_859_ = stack[2].m_obj;
lean_object* v_a_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v___y_862_ = stack[5].m_obj;
lean_object* v___y_863_ = stack[6].m_obj;
lean_object* v___y_864_ = stack[7].m_obj;
lean_object* v_res_894_;
v_res_894_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_857_, v_post_858_, v_e_859_, v_a_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_895_, lean_object* v_post_896_, lean_object* v_e_897_, lean_object* v_a_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_895_, v_post_896_, v_e_897_, v_a_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v_a_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_905_, lean_object* v_post_906_, lean_object* v_sz_907_, lean_object* v_i_908_, lean_object* v_bs_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
size_t v_sz_boxed_916_; size_t v_i_boxed_917_; lean_object* v_res_918_; 
v_sz_boxed_916_ = lean_unbox_usize(v_sz_907_);
lean_dec(v_sz_907_);
v_i_boxed_917_ = lean_unbox_usize(v_i_908_);
lean_dec(v_i_908_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_905_, v_post_906_, v_sz_boxed_916_, v_i_boxed_917_, v_bs_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_919_, lean_object* v_post_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_919_, v_post_920_, v_x_921_, v_x_922_, v_x_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___boxed(lean_object* v_pre_931_, lean_object* v_post_932_, lean_object* v_e_933_, lean_object* v_a_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_931_, v_post_932_, v_e_933_, v_a_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v_a_934_);
return v_res_940_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_box(0);
v___x_942_ = lean_unsigned_to_nat(16u);
v___x_943_ = lean_mk_array(v___x_942_, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0);
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1);
v___x_948_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_948_, 0, lean_box(0));
lean_closure_set(v___x_948_, 1, lean_box(0));
lean_closure_set(v___x_948_, 2, v___x_947_);
return v___x_948_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(lean_object* v_input_949_, lean_object* v_pre_950_, lean_object* v_post_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_960_; 
v___x_957_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2);
v___x_958_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_957_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v___x_960_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_950_, v_post_951_, v_input_949_, v_a_959_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_962_, 0, lean_box(0));
lean_closure_set(v___x_962_, 1, lean_box(0));
lean_closure_set(v___x_962_, 2, v_a_959_);
v___x_963_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_962_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_971_);
v___x_965_ = v___x_963_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_dec(v___x_963_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v_a_961_);
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_961_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
lean_dec(v_a_959_);
return v___x_960_;
}
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_949_ = stack[0].m_obj;
lean_object* v_pre_950_ = stack[1].m_obj;
lean_object* v_post_951_ = stack[2].m_obj;
lean_object* v___y_952_ = stack[3].m_obj;
lean_object* v___y_953_ = stack[4].m_obj;
lean_object* v___y_954_ = stack[5].m_obj;
lean_object* v___y_955_ = stack[6].m_obj;
lean_object* v_res_972_;
v_res_972_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_input_949_, v_pre_950_, v_post_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___boxed(lean_object* v_input_973_, lean_object* v_pre_974_, lean_object* v_post_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_input_973_, v_pre_974_, v_post_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_981_;
}
}
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object* v_e_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0));
v___x_992_ = lean_find_expr(v___x_991_, v_e_985_);
if (lean_obj_tag(v___x_992_) == 0)
{
uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = 1;
v___x_994_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_994_, 0, v_e_985_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*2, v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
else
{
lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1044_; 
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_992_, 0);
lean_dec(v_unused_1045_);
v___x_997_ = v___x_992_;
v_isShared_998_ = v_isSharedCheck_1044_;
goto v_resetjp_996_;
}
else
{
lean_dec(v___x_992_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1044_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_pre_999_; lean_object* v___f_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; 
v_pre_999_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1));
v___f_1000_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2));
v___x_1001_ = 1;
lean_inc_ref(v_e_985_);
v___x_1002_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_e_985_, v_pre_999_, v___f_1000_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc_n(v_a_1003_, 2);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l_Lean_Meta_mkEqRefl(v_a_1003_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
lean_inc(v_a_1003_);
v___x_1006_ = l_Lean_Meta_mkEq(v_e_985_, v_a_1003_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1019_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = l_Lean_Meta_mkExpectedPropHint(v_a_1005_, v_a_1007_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1011_);
v___x_1013_ = v___x_997_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1014_, 0, v_a_1003_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*2, v___x_1001_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1014_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_a_1005_);
lean_dec(v_a_1003_);
lean_del_object(v___x_997_);
v_a_1020_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1006_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1006_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_a_1003_);
lean_del_object(v___x_997_);
lean_dec_ref(v_e_985_);
v_a_1028_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1004_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1004_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_del_object(v___x_997_);
lean_dec_ref(v_e_985_);
v_a_1036_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1002_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1002_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_985_ = stack[0].m_obj;
lean_object* v_a_986_ = stack[1].m_obj;
lean_object* v_a_987_ = stack[2].m_obj;
lean_object* v_a_988_ = stack[3].m_obj;
lean_object* v_a_989_ = stack[4].m_obj;
lean_object* v_res_1046_;
v_res_1046_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_e_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
stack->m_obj
 = v_res_1046_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___boxed(lean_object* v_e_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_e_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1054_, lean_object* v_m_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_1055_, v_a_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1058_, lean_object* v_m_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(v_00_u03b2_1058_, v_m_1059_, v_a_1060_);
lean_dec_ref(v_a_1060_);
lean_dec_ref(v_m_1059_);
return v_res_1061_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1062_, lean_object* v_ref_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1063_);
return v___x_1067_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1063_ = stack[1].m_obj;
lean_object* v___y_1064_ = stack[2].m_obj;
lean_object* v___y_1065_ = stack[3].m_obj;
lean_object* v_res_1068_;
v_res_1068_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(lean_box(0), v_ref_1063_, v___y_1064_, v___y_1065_);
stack->m_obj
 = v_res_1068_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1069_, lean_object* v_ref_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1069_, v_ref_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1074_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1079_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1076_ = stack[1].m_obj;
lean_object* v___y_1077_ = stack[2].m_obj;
lean_object* v_res_1080_;
v_res_1080_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(lean_box(0), v___y_1076_, v___y_1077_);
stack->m_obj
 = v_res_1080_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1085_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1086_, lean_object* v_x_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1087_ = stack[1].m_obj;
lean_object* v___y_1088_ = stack[2].m_obj;
lean_object* v___y_1089_ = stack[3].m_obj;
lean_object* v___y_1090_ = stack[4].m_obj;
lean_object* v___y_1091_ = stack[5].m_obj;
lean_object* v___y_1092_ = stack[6].m_obj;
lean_object* v_res_1095_;
v_res_1095_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(lean_box(0), v_x_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
stack->m_obj
 = v_res_1095_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(v_00_u03b1_1096_, v_x_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1105_, lean_object* v_m_1106_, lean_object* v_a_1107_, lean_object* v_b_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v_m_1106_, v_a_1107_, v_b_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1114_, v_a_1115_, v_x_1116_);
lean_dec(v_x_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1117_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1118_, lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1119_, v_x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1119_ = stack[1].m_obj;
lean_object* v_x_1120_ = stack[2].m_obj;
uint8_t v_res_1122_;
v_res_1122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(lean_box(0), v_a_1119_, v_x_1120_);
stack->m_num = v_res_1122_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1123_, lean_object* v_a_1124_, lean_object* v_x_1125_){
_start:
{
uint8_t v_res_1126_; lean_object* v_r_1127_; 
v_res_1126_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1123_, v_a_1124_, v_x_1125_);
lean_dec(v_x_1125_);
lean_dec_ref(v_a_1124_);
v_r_1127_ = lean_box(v_res_1126_);
return v_r_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1128_, lean_object* v_data_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1131_, lean_object* v_a_1132_, lean_object* v_b_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1132_, v_b_1133_, v_x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1136_, lean_object* v_i_1137_, lean_object* v_source_1138_, lean_object* v_target_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1137_, v_source_1138_, v_target_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1142_, v_x_1143_);
return v___x_1144_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_();
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
