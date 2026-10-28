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
lean_object* v___x_78_; 
lean_inc_ref(v_e_66_);
v___x_78_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_66_, v_a_71_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_173_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_173_ == 0)
{
v___x_81_ = v___x_78_;
v_isShared_82_ = v_isSharedCheck_173_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_78_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_173_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = l_Lean_Expr_cleanupAnnotations(v_a_79_);
lean_dec(v_a_79_);
v___x_84_ = l_Lean_Expr_isApp(v___x_83_);
if (v___x_84_ == 0)
{
lean_dec_ref(v___x_83_);
lean_del_object(v___x_81_);
lean_dec_ref(v_e_66_);
goto v___jp_75_;
}
else
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = l_Lean_Expr_appFnCleanup___redArg(v___x_83_);
v___x_86_ = l_Lean_Expr_isApp(v___x_85_);
if (v___x_86_ == 0)
{
lean_dec_ref(v___x_85_);
lean_dec_ref(v___x_83_);
lean_del_object(v___x_81_);
lean_dec_ref(v_e_66_);
goto v___jp_75_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_87_ = l_Lean_Expr_appFnCleanup___redArg(v___x_85_);
lean_dec_ref(v___x_85_);
v___x_88_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_89_ = l_Lean_Expr_isConstOf(v___x_87_, v___x_88_);
lean_dec_ref(v___x_87_);
if (v___x_89_ == 0)
{
lean_dec_ref(v___x_83_);
lean_del_object(v___x_81_);
lean_dec_ref(v_e_66_);
goto v___jp_75_;
}
else
{
lean_object* v_arg_90_; lean_object* v___x_91_; 
v_arg_90_ = lean_ctor_get(v___x_83_, 1);
lean_inc_ref(v_arg_90_);
lean_dec_ref(v___x_83_);
v___x_91_ = l_Lean_Expr_getAppFn(v_arg_90_);
if (lean_obj_tag(v___x_91_) == 4)
{
lean_object* v_declName_92_; lean_object* v___x_93_; lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_166_; 
lean_del_object(v___x_81_);
v_declName_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_declName_92_);
lean_dec_ref_known(v___x_91_, 2);
v___x_93_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_spec__0___redArg(v_declName_92_, v_a_73_);
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_166_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_166_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_166_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
if (lean_obj_tag(v_a_94_) == 1)
{
lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_159_; 
lean_del_object(v___x_96_);
v_val_98_ = lean_ctor_get(v_a_94_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_a_94_);
if (v_isSharedCheck_159_ == 0)
{
v___x_100_ = v_a_94_;
v_isShared_101_ = v_isSharedCheck_159_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_dec(v_a_94_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_159_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_val_98_, v_arg_90_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_150_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_150_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_150_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_150_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
if (lean_obj_tag(v_a_103_) == 1)
{
lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_141_; 
lean_del_object(v___x_105_);
lean_del_object(v___x_100_);
lean_dec_ref(v_e_66_);
v_val_107_ = lean_ctor_get(v_a_103_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_a_103_);
if (v_isSharedCheck_141_ == 0)
{
v___x_109_ = v_a_103_;
v_isShared_110_ = v_isSharedCheck_141_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_dec(v_a_103_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_141_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_expr_111_; lean_object* v_proof_x3f_112_; uint8_t v_cache_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_140_; 
v_expr_111_ = lean_ctor_get(v_val_107_, 0);
v_proof_x3f_112_ = lean_ctor_get(v_val_107_, 1);
v_cache_113_ = lean_ctor_get_uint8(v_val_107_, sizeof(void*)*2);
v_isSharedCheck_140_ = !lean_is_exclusive(v_val_107_);
if (v_isSharedCheck_140_ == 0)
{
v___x_115_ = v_val_107_;
v_isShared_116_ = v_isSharedCheck_140_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_proof_x3f_112_);
lean_inc(v_expr_111_);
lean_dec(v_val_107_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_140_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly(v_expr_111_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_131_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_131_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_131_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_131_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v_a_118_);
v___x_123_ = v___x_115_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_118_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_proof_x3f_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*2, v_cache_113_);
v___x_123_ = v_reuseFailAlloc_130_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_123_);
v___x_125_ = v___x_109_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_125_);
v___x_127_ = v___x_120_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_del_object(v___x_115_);
lean_dec(v_proof_x3f_112_);
lean_del_object(v___x_109_);
v_a_132_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_117_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_117_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec(v_a_103_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_143_, 0, v_e_66_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*2, v___x_89_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 0);
lean_ctor_set(v___x_100_, 0, v___x_143_);
v___x_145_ = v___x_100_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_149_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_145_);
v___x_147_ = v___x_105_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_del_object(v___x_100_);
lean_dec_ref(v_e_66_);
v_a_151_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_102_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_102_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_dec(v_a_94_);
lean_dec_ref(v_arg_90_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_161_, 0, v_e_66_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*2, v___x_89_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_162_);
v___x_164_ = v___x_96_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_dec_ref(v___x_91_);
lean_dec_ref(v_arg_90_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_168_, 0, v_e_66_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*2, v___x_89_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_169_);
v___x_171_ = v___x_81_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref(v_e_66_);
v_a_174_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_78_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_78_);
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
v___jp_75_:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___closed__0));
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_));
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_));
v___x_212_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly___boxed), 9, 0);
v___x_213_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_210_, v___x_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11____boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_();
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(lean_object* v_s_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchDiscrOnly_0____regBuiltin_Lean_Meta_Grind_reduceSimpMatchDiscrsOnly_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_MatchDiscrOnly_1997758855____hygCtx___hyg_11_));
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
v___x_238_ = l_Lean_Expr_cleanupAnnotations(v_e_228_);
v___x_239_ = l_Lean_Expr_isApp(v___x_238_);
if (v___x_239_ == 0)
{
lean_dec_ref(v___x_238_);
goto v___jp_234_;
}
else
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = l_Lean_Expr_appFnCleanup___redArg(v___x_238_);
v___x_241_ = l_Lean_Expr_isApp(v___x_240_);
if (v___x_241_ == 0)
{
lean_dec_ref(v___x_240_);
lean_dec_ref(v___x_238_);
goto v___jp_234_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_240_);
lean_dec_ref(v___x_240_);
v___x_243_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_244_ = l_Lean_Expr_isConstOf(v___x_242_, v___x_243_);
lean_dec_ref(v___x_242_);
if (v___x_244_ == 0)
{
lean_dec_ref(v___x_238_);
goto v___jp_234_;
}
else
{
lean_object* v_arg_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_e_228_);
v_arg_245_ = lean_ctor_get(v___x_238_, 1);
lean_inc_ref(v_arg_245_);
lean_dec_ref(v___x_238_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_arg_245_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_321_, lean_object* v_b_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_dec(v_b_322_);
lean_dec_ref(v_a_321_);
return v_x_323_;
}
else
{
lean_object* v_key_324_; lean_object* v_value_325_; lean_object* v_tail_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_338_; 
v_key_324_ = lean_ctor_get(v_x_323_, 0);
v_value_325_ = lean_ctor_get(v_x_323_, 1);
v_tail_326_ = lean_ctor_get(v_x_323_, 2);
v_isSharedCheck_338_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_338_ == 0)
{
v___x_328_ = v_x_323_;
v_isShared_329_ = v_isSharedCheck_338_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_tail_326_);
lean_inc(v_value_325_);
lean_inc(v_key_324_);
lean_dec(v_x_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_338_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
uint8_t v___x_330_; 
v___x_330_ = l_Lean_ExprStructEq_beq(v_key_324_, v_a_321_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_321_, v_b_322_, v_tail_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 2, v___x_331_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_key_324_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_value_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
lean_object* v___x_336_; 
lean_dec(v_value_325_);
lean_dec(v_key_324_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_b_322_);
lean_ctor_set(v___x_328_, 0, v_a_321_);
v___x_336_ = v___x_328_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_321_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_b_322_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_tail_326_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
return v_x_339_;
}
else
{
lean_object* v_key_341_; lean_object* v_value_342_; lean_object* v_tail_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_366_; 
v_key_341_ = lean_ctor_get(v_x_340_, 0);
v_value_342_ = lean_ctor_get(v_x_340_, 1);
v_tail_343_ = lean_ctor_get(v_x_340_, 2);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_366_ == 0)
{
v___x_345_ = v_x_340_;
v_isShared_346_ = v_isSharedCheck_366_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_tail_343_);
lean_inc(v_value_342_);
lean_inc(v_key_341_);
lean_dec(v_x_340_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_366_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v_fold_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_347_ = lean_array_get_size(v_x_339_);
v___x_348_ = l_Lean_ExprStructEq_hash(v_key_341_);
v___x_349_ = 32ULL;
v___x_350_ = lean_uint64_shift_right(v___x_348_, v___x_349_);
v_fold_351_ = lean_uint64_xor(v___x_348_, v___x_350_);
v___x_352_ = 16ULL;
v___x_353_ = lean_uint64_shift_right(v_fold_351_, v___x_352_);
v___x_354_ = lean_uint64_xor(v_fold_351_, v___x_353_);
v___x_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = lean_usize_of_nat(v___x_347_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_sub(v___x_356_, v___x_357_);
v___x_359_ = lean_usize_land(v___x_355_, v___x_358_);
v___x_360_ = lean_array_uget_borrowed(v_x_339_, v___x_359_);
lean_inc(v___x_360_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 2, v___x_360_);
v___x_362_ = v___x_345_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_key_341_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_value_342_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v___x_360_);
v___x_362_ = v_reuseFailAlloc_365_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_array_uset(v_x_339_, v___x_359_, v___x_362_);
v_x_339_ = v___x_363_;
v_x_340_ = v_tail_343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_367_, lean_object* v_source_368_, lean_object* v_target_369_){
_start:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_array_get_size(v_source_368_);
v___x_371_ = lean_nat_dec_lt(v_i_367_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec_ref(v_source_368_);
lean_dec(v_i_367_);
return v_target_369_;
}
else
{
lean_object* v_es_372_; lean_object* v___x_373_; lean_object* v_source_374_; lean_object* v_target_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_es_372_ = lean_array_fget(v_source_368_, v_i_367_);
v___x_373_ = lean_box(0);
v_source_374_ = lean_array_fset(v_source_368_, v_i_367_, v___x_373_);
v_target_375_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_369_, v_es_372_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_i_367_, v___x_376_);
lean_dec(v_i_367_);
v_i_367_ = v___x_377_;
v_source_368_ = v_source_374_;
v_target_369_ = v_target_375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_nbuckets_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_380_ = lean_array_get_size(v_data_379_);
v___x_381_ = lean_unsigned_to_nat(2u);
v_nbuckets_382_ = lean_nat_mul(v___x_380_, v___x_381_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_box(0);
v___x_385_ = lean_mk_array(v_nbuckets_382_, v___x_384_);
v___x_386_ = lean_array_propagate_mark(v_data_379_, v___x_385_);
v___x_387_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_383_, v_data_379_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
else
{
lean_object* v_key_391_; lean_object* v_tail_392_; uint8_t v___x_393_; 
v_key_391_ = lean_ctor_get(v_x_389_, 0);
v_tail_392_ = lean_ctor_get(v_x_389_, 2);
v___x_393_ = l_Lean_ExprStructEq_beq(v_key_391_, v_a_388_);
if (v___x_393_ == 0)
{
v_x_389_ = v_tail_392_;
goto _start;
}
else
{
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_395_, lean_object* v_x_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_395_, v_x_396_);
lean_dec(v_x_396_);
lean_dec_ref(v_a_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(lean_object* v_m_399_, lean_object* v_a_400_, lean_object* v_b_401_){
_start:
{
lean_object* v_size_402_; lean_object* v_buckets_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_446_; 
v_size_402_ = lean_ctor_get(v_m_399_, 0);
v_buckets_403_ = lean_ctor_get(v_m_399_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_m_399_);
if (v_isSharedCheck_446_ == 0)
{
v___x_405_ = v_m_399_;
v_isShared_406_ = v_isSharedCheck_446_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_buckets_403_);
lean_inc(v_size_402_);
lean_dec(v_m_399_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_446_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v_fold_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v_bkt_420_; uint8_t v___x_421_; 
v___x_407_ = lean_array_get_size(v_buckets_403_);
v___x_408_ = l_Lean_ExprStructEq_hash(v_a_400_);
v___x_409_ = 32ULL;
v___x_410_ = lean_uint64_shift_right(v___x_408_, v___x_409_);
v_fold_411_ = lean_uint64_xor(v___x_408_, v___x_410_);
v___x_412_ = 16ULL;
v___x_413_ = lean_uint64_shift_right(v_fold_411_, v___x_412_);
v___x_414_ = lean_uint64_xor(v_fold_411_, v___x_413_);
v___x_415_ = lean_uint64_to_usize(v___x_414_);
v___x_416_ = lean_usize_of_nat(v___x_407_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_sub(v___x_416_, v___x_417_);
v___x_419_ = lean_usize_land(v___x_415_, v___x_418_);
v_bkt_420_ = lean_array_uget_borrowed(v_buckets_403_, v___x_419_);
v___x_421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_400_, v_bkt_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v_size_x27_423_; lean_object* v___x_424_; lean_object* v_buckets_x27_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v_size_x27_423_ = lean_nat_add(v_size_402_, v___x_422_);
lean_dec(v_size_402_);
lean_inc(v_bkt_420_);
v___x_424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_424_, 0, v_a_400_);
lean_ctor_set(v___x_424_, 1, v_b_401_);
lean_ctor_set(v___x_424_, 2, v_bkt_420_);
v_buckets_x27_425_ = lean_array_uset(v_buckets_403_, v___x_419_, v___x_424_);
v___x_426_ = lean_unsigned_to_nat(4u);
v___x_427_ = lean_nat_mul(v_size_x27_423_, v___x_426_);
v___x_428_ = lean_unsigned_to_nat(3u);
v___x_429_ = lean_nat_div(v___x_427_, v___x_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_array_get_size(v_buckets_x27_425_);
v___x_431_ = lean_nat_dec_le(v___x_429_, v___x_430_);
lean_dec(v___x_429_);
if (v___x_431_ == 0)
{
lean_object* v_val_432_; lean_object* v___x_434_; 
v_val_432_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_425_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_val_432_);
lean_ctor_set(v___x_405_, 0, v_size_x27_423_);
v___x_434_ = v___x_405_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_size_x27_423_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_val_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
else
{
lean_object* v___x_437_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_buckets_x27_425_);
lean_ctor_set(v___x_405_, 0, v_size_x27_423_);
v___x_437_ = v___x_405_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_size_x27_423_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_buckets_x27_425_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v___x_439_; lean_object* v_buckets_x27_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
lean_inc(v_bkt_420_);
v___x_439_ = lean_box(0);
v_buckets_x27_440_ = lean_array_uset(v_buckets_403_, v___x_419_, v___x_439_);
v___x_441_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_400_, v_b_401_, v_bkt_420_);
v___x_442_ = lean_array_uset(v_buckets_x27_440_, v___x_419_, v___x_441_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_442_);
v___x_444_ = v___x_405_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_size_402_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(lean_object* v_a_447_, lean_object* v_e_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = lean_st_ref_take(v_a_447_);
v___x_452_ = lean_box(0);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v___x_451_, v_e_448_, v_a_449_);
v___x_454_ = lean_st_ref_put(v_a_447_, v___x_453_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed(lean_object* v_a_455_, lean_object* v_e_456_, lean_object* v_a_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2(v_a_455_, v_e_456_, v_a_457_);
lean_dec(v_a_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_460_, lean_object* v_x_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_apply_1(v_x_461_, lean_box(0));
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_469_, lean_object* v_x_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(v_00_u03b1_469_, v_x_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_box(0);
v___x_478_ = l_Lean_interruptExceptionId;
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_484_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = l_Lean_maxRecDepthErrorMessage;
v___x_491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_493_ = l_Lean_MessageData_ofFormat(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_495_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_496_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_497_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_ref_497_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___y_513_; lean_object* v___y_523_; uint8_t v___y_524_; uint8_t v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; uint16_t v___y_529_; lean_object* v_toCold_534_; lean_object* v_currRecDepth_535_; lean_object* v_ref_536_; uint16_t v_optionFlags_537_; uint8_t v_suppressElabErrors_538_; uint8_t v_checkDeprecated_539_; uint8_t v_isRecordingDeps_540_; lean_object* v_maxRecDepth_541_; lean_object* v_cancelTk_x3f_542_; 
v_toCold_534_ = lean_ctor_get(v___y_509_, 0);
v_currRecDepth_535_ = lean_ctor_get(v___y_509_, 1);
v_ref_536_ = lean_ctor_get(v___y_509_, 2);
v_optionFlags_537_ = lean_ctor_get_uint16(v___y_509_, sizeof(void*)*3);
v_suppressElabErrors_538_ = lean_ctor_get_uint8(v___y_509_, sizeof(void*)*3 + 2);
v_checkDeprecated_539_ = lean_ctor_get_uint8(v___y_509_, sizeof(void*)*3 + 3);
v_isRecordingDeps_540_ = lean_ctor_get_uint8(v___y_509_, sizeof(void*)*3 + 4);
v_maxRecDepth_541_ = lean_ctor_get(v_toCold_534_, 3);
v_cancelTk_x3f_542_ = lean_ctor_get(v_toCold_534_, 10);
if (lean_obj_tag(v_cancelTk_x3f_542_) == 1)
{
lean_object* v_val_548_; uint8_t v___x_549_; 
v_val_548_ = lean_ctor_get(v_cancelTk_x3f_542_, 0);
v___x_549_ = l_IO_CancelToken_isSet(v_val_548_);
if (v___x_549_ == 0)
{
goto v___jp_543_;
}
else
{
lean_object* v___x_550_; lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec_ref(v_x_505_);
v___x_550_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
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
else
{
goto v___jp_543_;
}
v___jp_512_:
{
if (lean_obj_tag(v___y_513_) == 0)
{
return v___y_513_;
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v___y_513_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___y_513_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___y_513_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___y_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
v___jp_522_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v___y_528_, v___x_530_);
lean_inc_ref(v___y_523_);
v___x_532_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_532_, 0, v___y_523_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
lean_ctor_set(v___x_532_, 2, v___y_526_);
lean_ctor_set_uint16(v___x_532_, sizeof(void*)*3, v___y_529_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*3 + 2, v___y_525_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*3 + 3, v___y_527_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*3 + 4, v___y_524_);
lean_inc(v___y_510_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
lean_inc(v___y_506_);
v___x_533_ = lean_apply_6(v_x_505_, v___y_506_, v___y_507_, v___y_508_, v___x_532_, v___y_510_, lean_box(0));
v___y_513_ = v___x_533_;
goto v___jp_512_;
}
v___jp_543_:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_nat_dec_eq(v_maxRecDepth_541_, v___x_544_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; 
v___x_546_ = lean_nat_dec_eq(v_currRecDepth_535_, v_maxRecDepth_541_);
if (v___x_546_ == 0)
{
lean_inc(v_ref_536_);
v___y_523_ = v_toCold_534_;
v___y_524_ = v_isRecordingDeps_540_;
v___y_525_ = v_suppressElabErrors_538_;
v___y_526_ = v_ref_536_;
v___y_527_ = v_checkDeprecated_539_;
v___y_528_ = v_currRecDepth_535_;
v___y_529_ = v_optionFlags_537_;
goto v___jp_522_;
}
else
{
lean_object* v___x_547_; 
lean_dec_ref(v_x_505_);
lean_inc(v_ref_536_);
v___x_547_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_536_);
v___y_513_ = v___x_547_;
goto v___jp_512_;
}
}
else
{
lean_inc(v_ref_536_);
v___y_523_ = v_toCold_534_;
v___y_524_ = v_isRecordingDeps_540_;
v___y_525_ = v_suppressElabErrors_538_;
v___y_526_ = v_ref_536_;
v___y_527_ = v_checkDeprecated_539_;
v___y_528_ = v_currRecDepth_535_;
v___y_529_ = v_optionFlags_537_;
goto v___jp_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
return v_res_566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_568_; lean_object* v_dummy_569_; 
v___x_568_ = lean_box(0);
v_dummy_569_ = l_Lean_Expr_sort___override(v___x_568_);
return v_dummy_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(lean_object* v_pre_570_, lean_object* v_post_571_, size_t v_sz_572_, size_t v_i_573_, lean_object* v_bs_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
uint8_t v___x_581_; 
v___x_581_ = lean_usize_dec_lt(v_i_573_, v_sz_572_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v_post_571_);
lean_dec_ref(v_pre_570_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_bs_574_);
return v___x_582_;
}
else
{
lean_object* v_v_583_; lean_object* v___x_584_; lean_object* v_bs_x27_585_; lean_object* v___x_586_; 
v_v_583_ = lean_array_uget(v_bs_574_, v_i_573_);
v___x_584_ = lean_unsigned_to_nat(0u);
v_bs_x27_585_ = lean_array_uset(v_bs_574_, v_i_573_, v___x_584_);
lean_inc_ref(v_post_571_);
lean_inc_ref(v_pre_570_);
v___x_586_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_570_, v_post_571_, v_v_583_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_573_, v___x_588_);
v___x_590_ = lean_array_uset(v_bs_x27_585_, v_i_573_, v_a_587_);
v_i_573_ = v___x_589_;
v_bs_574_ = v___x_590_;
goto _start;
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_bs_x27_585_);
lean_dec_ref(v_post_571_);
lean_dec_ref(v_pre_570_);
v_a_592_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_586_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_586_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(lean_object* v_pre_600_, lean_object* v_post_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
if (lean_obj_tag(v_x_602_) == 5)
{
lean_object* v_fn_611_; lean_object* v_arg_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_fn_611_ = lean_ctor_get(v_x_602_, 0);
lean_inc_ref(v_fn_611_);
v_arg_612_ = lean_ctor_get(v_x_602_, 1);
lean_inc_ref(v_arg_612_);
lean_dec_ref_known(v_x_602_, 2);
v___x_613_ = lean_array_set(v_x_603_, v_x_604_, v_arg_612_);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_sub(v_x_604_, v___x_614_);
lean_dec(v_x_604_);
v_x_602_ = v_fn_611_;
v_x_603_ = v___x_613_;
v_x_604_ = v___x_615_;
goto _start;
}
else
{
lean_object* v___x_617_; 
lean_dec(v_x_604_);
lean_inc_ref(v_post_601_);
lean_inc_ref(v_pre_600_);
v___x_617_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_600_, v_post_601_, v_x_602_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; size_t v_sz_619_; size_t v___x_620_; lean_object* v___x_621_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v_sz_619_ = lean_array_size(v_x_603_);
v___x_620_ = ((size_t)0ULL);
lean_inc_ref(v_post_601_);
lean_inc_ref(v_pre_600_);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_600_, v_post_601_, v_sz_619_, v___x_620_, v_x_603_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = l_Lean_mkAppN(v_a_618_, v_a_622_);
lean_dec(v_a_622_);
v___x_624_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_600_, v_post_601_, v___x_623_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_618_);
lean_dec_ref(v_post_601_);
lean_dec_ref(v_pre_600_);
v_a_625_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_621_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_621_);
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
else
{
lean_dec_ref(v_x_603_);
lean_dec_ref(v_post_601_);
lean_dec_ref(v_pre_600_);
return v___x_617_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(lean_object* v___x_633_, lean_object* v_pre_634_, lean_object* v_e_635_, lean_object* v_post_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Core_checkSystem(v___x_633_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_644_; 
lean_dec_ref_known(v___x_643_, 1);
lean_inc_ref(v_pre_634_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc_ref(v_e_635_);
v___x_644_ = lean_apply_6(v_pre_634_, v_e_635_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, lean_box(0));
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_760_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_760_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_760_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_760_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___y_650_; 
switch(lean_obj_tag(v_a_645_))
{
case 0:
{
lean_object* v_e_750_; lean_object* v___x_752_; 
lean_dec_ref(v_post_636_);
lean_dec_ref(v_e_635_);
lean_dec_ref(v_pre_634_);
v_e_750_ = lean_ctor_get(v_a_645_, 0);
lean_inc_ref(v_e_750_);
lean_dec_ref_known(v_a_645_, 1);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v_e_750_);
v___x_752_ = v___x_647_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_e_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
case 1:
{
lean_object* v_e_754_; lean_object* v___x_755_; 
lean_del_object(v___x_647_);
lean_dec_ref(v_e_635_);
v_e_754_ = lean_ctor_get(v_a_645_, 0);
lean_inc_ref(v_e_754_);
lean_dec_ref_known(v_a_645_, 1);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_755_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_e_754_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v_a_756_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_757_;
}
else
{
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_755_;
}
}
default: 
{
lean_object* v_e_x3f_758_; 
lean_del_object(v___x_647_);
v_e_x3f_758_ = lean_ctor_get(v_a_645_, 0);
lean_inc(v_e_x3f_758_);
lean_dec_ref_known(v_a_645_, 1);
if (lean_obj_tag(v_e_x3f_758_) == 0)
{
v___y_650_ = v_e_635_;
goto v___jp_649_;
}
else
{
lean_object* v_val_759_; 
lean_dec_ref(v_e_635_);
v_val_759_ = lean_ctor_get(v_e_x3f_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v_e_x3f_758_, 1);
v___y_650_ = v_val_759_;
goto v___jp_649_;
}
}
}
v___jp_649_:
{
switch(lean_obj_tag(v___y_650_))
{
case 7:
{
lean_object* v_binderName_651_; lean_object* v_binderType_652_; lean_object* v_body_653_; uint8_t v_binderInfo_654_; lean_object* v___x_655_; 
v_binderName_651_ = lean_ctor_get(v___y_650_, 0);
v_binderType_652_ = lean_ctor_get(v___y_650_, 1);
v_body_653_ = lean_ctor_get(v___y_650_, 2);
v_binderInfo_654_ = lean_ctor_get_uint8(v___y_650_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_652_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_binderType_652_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
lean_inc_ref(v_body_653_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_body_653_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; size_t v___x_659_; size_t v___x_660_; uint8_t v___x_661_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_ptr_addr(v_binderType_652_);
v___x_660_ = lean_ptr_addr(v_a_656_);
v___x_661_ = lean_usize_dec_eq(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_inc(v_binderName_651_);
lean_dec_ref_known(v___y_650_, 3);
v___x_662_ = l_Lean_Expr_forallE___override(v_binderName_651_, v_a_656_, v_a_658_, v_binderInfo_654_);
v___x_663_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_662_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_663_;
}
else
{
size_t v___x_664_; size_t v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_ptr_addr(v_body_653_);
v___x_665_ = lean_ptr_addr(v_a_658_);
v___x_666_ = lean_usize_dec_eq(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_inc(v_binderName_651_);
lean_dec_ref_known(v___y_650_, 3);
v___x_667_ = l_Lean_Expr_forallE___override(v_binderName_651_, v_a_656_, v_a_658_, v_binderInfo_654_);
v___x_668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_667_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_654_, v_binderInfo_654_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_inc(v_binderName_651_);
lean_dec_ref_known(v___y_650_, 3);
v___x_670_ = l_Lean_Expr_forallE___override(v_binderName_651_, v_a_656_, v_a_658_, v_binderInfo_654_);
v___x_671_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_670_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; 
lean_dec(v_a_658_);
lean_dec(v_a_656_);
v___x_672_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___y_650_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_672_;
}
}
}
}
else
{
lean_dec(v_a_656_);
lean_dec_ref_known(v___y_650_, 3);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_657_;
}
}
else
{
lean_dec_ref_known(v___y_650_, 3);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_655_;
}
}
case 6:
{
lean_object* v_binderName_673_; lean_object* v_binderType_674_; lean_object* v_body_675_; uint8_t v_binderInfo_676_; lean_object* v___x_677_; 
v_binderName_673_ = lean_ctor_get(v___y_650_, 0);
v_binderType_674_ = lean_ctor_get(v___y_650_, 1);
v_body_675_ = lean_ctor_get(v___y_650_, 2);
v_binderInfo_676_ = lean_ctor_get_uint8(v___y_650_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_674_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_677_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_binderType_674_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
lean_inc_ref(v_body_675_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_679_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_body_675_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; size_t v___x_681_; size_t v___x_682_; uint8_t v___x_683_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = lean_ptr_addr(v_binderType_674_);
v___x_682_ = lean_ptr_addr(v_a_678_);
v___x_683_ = lean_usize_dec_eq(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_inc(v_binderName_673_);
lean_dec_ref_known(v___y_650_, 3);
v___x_684_ = l_Lean_Expr_lam___override(v_binderName_673_, v_a_678_, v_a_680_, v_binderInfo_676_);
v___x_685_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_684_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_685_;
}
else
{
size_t v___x_686_; size_t v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_ptr_addr(v_body_675_);
v___x_687_ = lean_ptr_addr(v_a_680_);
v___x_688_ = lean_usize_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_inc(v_binderName_673_);
lean_dec_ref_known(v___y_650_, 3);
v___x_689_ = l_Lean_Expr_lam___override(v_binderName_673_, v_a_678_, v_a_680_, v_binderInfo_676_);
v___x_690_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_689_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_676_, v_binderInfo_676_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_inc(v_binderName_673_);
lean_dec_ref_known(v___y_650_, 3);
v___x_692_ = l_Lean_Expr_lam___override(v_binderName_673_, v_a_678_, v_a_680_, v_binderInfo_676_);
v___x_693_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_692_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; 
lean_dec(v_a_680_);
lean_dec(v_a_678_);
v___x_694_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___y_650_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_694_;
}
}
}
}
else
{
lean_dec(v_a_678_);
lean_dec_ref_known(v___y_650_, 3);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_679_;
}
}
else
{
lean_dec_ref_known(v___y_650_, 3);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_677_;
}
}
case 8:
{
lean_object* v_declName_695_; lean_object* v_type_696_; lean_object* v_value_697_; lean_object* v_body_698_; uint8_t v_nondep_699_; lean_object* v___x_700_; 
v_declName_695_ = lean_ctor_get(v___y_650_, 0);
v_type_696_ = lean_ctor_get(v___y_650_, 1);
v_value_697_ = lean_ctor_get(v___y_650_, 2);
v_body_698_ = lean_ctor_get(v___y_650_, 3);
v_nondep_699_ = lean_ctor_get_uint8(v___y_650_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_696_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_700_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_type_696_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
lean_inc_ref(v_value_697_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_702_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_value_697_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
lean_inc_ref(v_body_698_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_body_698_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_ptr_addr(v_type_696_);
v___x_707_ = lean_ptr_addr(v_a_701_);
v___x_708_ = lean_usize_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_inc(v_declName_695_);
lean_dec_ref_known(v___y_650_, 4);
v___x_709_ = l_Lean_Expr_letE___override(v_declName_695_, v_a_701_, v_a_703_, v_a_705_, v_nondep_699_);
v___x_710_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_709_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_710_;
}
else
{
size_t v___x_711_; size_t v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_ptr_addr(v_value_697_);
v___x_712_ = lean_ptr_addr(v_a_703_);
v___x_713_ = lean_usize_dec_eq(v___x_711_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_inc(v_declName_695_);
lean_dec_ref_known(v___y_650_, 4);
v___x_714_ = l_Lean_Expr_letE___override(v_declName_695_, v_a_701_, v_a_703_, v_a_705_, v_nondep_699_);
v___x_715_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_714_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_715_;
}
else
{
size_t v___x_716_; size_t v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_ptr_addr(v_body_698_);
v___x_717_ = lean_ptr_addr(v_a_705_);
v___x_718_ = lean_usize_dec_eq(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_inc(v_declName_695_);
lean_dec_ref_known(v___y_650_, 4);
v___x_719_ = l_Lean_Expr_letE___override(v_declName_695_, v_a_701_, v_a_703_, v_a_705_, v_nondep_699_);
v___x_720_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_719_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; 
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
v___x_721_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___y_650_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_721_;
}
}
}
}
else
{
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec_ref_known(v___y_650_, 4);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_704_;
}
}
else
{
lean_dec(v_a_701_);
lean_dec_ref_known(v___y_650_, 4);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_702_;
}
}
else
{
lean_dec_ref_known(v___y_650_, 4);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_700_;
}
}
case 5:
{
lean_object* v_dummy_722_; lean_object* v_nargs_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_dummy_722_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0);
v_nargs_723_ = l_Lean_Expr_getAppNumArgs(v___y_650_);
lean_inc(v_nargs_723_);
v___x_724_ = lean_mk_array(v_nargs_723_, v_dummy_722_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_sub(v_nargs_723_, v___x_725_);
lean_dec(v_nargs_723_);
v___x_727_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_634_, v_post_636_, v___y_650_, v___x_724_, v___x_726_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_727_;
}
case 10:
{
lean_object* v_data_728_; lean_object* v_expr_729_; lean_object* v___x_730_; 
v_data_728_ = lean_ctor_get(v___y_650_, 0);
v_expr_729_ = lean_ctor_get(v___y_650_, 1);
lean_inc_ref(v_expr_729_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_730_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_expr_729_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; size_t v___x_732_; size_t v___x_733_; uint8_t v___x_734_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = lean_ptr_addr(v_expr_729_);
v___x_733_ = lean_ptr_addr(v_a_731_);
v___x_734_ = lean_usize_dec_eq(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc(v_data_728_);
lean_dec_ref_known(v___y_650_, 2);
v___x_735_ = l_Lean_Expr_mdata___override(v_data_728_, v_a_731_);
v___x_736_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_735_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; 
lean_dec(v_a_731_);
v___x_737_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___y_650_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_737_;
}
}
else
{
lean_dec_ref_known(v___y_650_, 2);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_730_;
}
}
case 11:
{
lean_object* v_typeName_738_; lean_object* v_idx_739_; lean_object* v_struct_740_; lean_object* v___x_741_; 
v_typeName_738_ = lean_ctor_get(v___y_650_, 0);
v_idx_739_ = lean_ctor_get(v___y_650_, 1);
v_struct_740_ = lean_ctor_get(v___y_650_, 2);
lean_inc_ref(v_struct_740_);
lean_inc_ref(v_post_636_);
lean_inc_ref(v_pre_634_);
v___x_741_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_634_, v_post_636_, v_struct_740_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; size_t v___x_743_; size_t v___x_744_; uint8_t v___x_745_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = lean_ptr_addr(v_struct_740_);
v___x_744_ = lean_ptr_addr(v_a_742_);
v___x_745_ = lean_usize_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_inc(v_idx_739_);
lean_inc(v_typeName_738_);
lean_dec_ref_known(v___y_650_, 3);
v___x_746_ = l_Lean_Expr_proj___override(v_typeName_738_, v_idx_739_, v_a_742_);
v___x_747_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___x_746_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; 
lean_dec(v_a_742_);
v___x_748_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___y_650_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_748_;
}
}
else
{
lean_dec_ref_known(v___y_650_, 3);
lean_dec_ref(v_post_636_);
lean_dec_ref(v_pre_634_);
return v___x_741_;
}
}
default: 
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_634_, v_post_636_, v___y_650_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_749_;
}
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v_post_636_);
lean_dec_ref(v_e_635_);
lean_dec_ref(v_pre_634_);
v_a_761_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_644_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_644_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_post_636_);
lean_dec_ref(v_e_635_);
lean_dec_ref(v_pre_634_);
v_a_769_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_643_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_643_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed(lean_object* v___x_777_, lean_object* v_pre_778_, lean_object* v_e_779_, lean_object* v_post_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(v___x_777_, v_pre_778_, v_e_779_, v_post_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(lean_object* v_pre_788_, lean_object* v_post_789_, lean_object* v_e_790_, lean_object* v_a_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc(v_a_791_);
v___x_797_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_797_, 0, lean_box(0));
lean_closure_set(v___x_797_, 1, lean_box(0));
lean_closure_set(v___x_797_, 2, v_a_791_);
v___x_798_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___x_797_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_830_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_830_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_830_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_830_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_a_799_, v_e_790_);
lean_dec(v_a_799_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___x_806_; 
lean_del_object(v___x_801_);
v___x_804_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_790_);
v___f_805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_805_, 0, v___x_804_);
lean_closure_set(v___f_805_, 1, v_pre_788_);
lean_closure_set(v___f_805_, 2, v_e_790_);
lean_closure_set(v___f_805_, 3, v_post_789_);
v___x_806_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v___f_805_, v_a_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___f_808_; lean_object* v___x_809_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_n(v_a_807_, 2);
lean_dec_ref_known(v___x_806_, 1);
lean_inc(v_a_791_);
v___f_808_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_808_, 0, v_a_791_);
lean_closure_set(v___f_808_, 1, v_e_790_);
lean_closure_set(v___f_808_, 2, v_a_807_);
v___x_809_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___f_808_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_809_, 0);
lean_dec(v_unused_817_);
v___x_811_ = v___x_809_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_dec(v___x_809_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_a_807_);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_807_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_a_807_);
v_a_818_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_809_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_809_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_dec_ref(v_e_790_);
return v___x_806_;
}
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; 
lean_dec_ref(v_e_790_);
lean_dec_ref(v_post_789_);
lean_dec_ref(v_pre_788_);
v_val_826_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_803_, 1);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v_val_826_);
v___x_828_ = v___x_801_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_val_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_e_790_);
lean_dec_ref(v_post_789_);
lean_dec_ref(v_pre_788_);
v_a_831_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_798_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_798_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(lean_object* v_pre_839_, lean_object* v_post_840_, lean_object* v_e_841_, lean_object* v_a_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
lean_inc_ref(v_post_840_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc_ref(v_e_841_);
v___x_848_ = lean_apply_6(v_post_840_, v_e_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_867_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_867_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
switch(lean_obj_tag(v_a_849_))
{
case 0:
{
lean_object* v_e_853_; lean_object* v___x_855_; 
lean_dec_ref(v_e_841_);
lean_dec_ref(v_post_840_);
lean_dec_ref(v_pre_839_);
v_e_853_ = lean_ctor_get(v_a_849_, 0);
lean_inc_ref(v_e_853_);
lean_dec_ref_known(v_a_849_, 1);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v_e_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_e_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
case 1:
{
lean_object* v_e_857_; lean_object* v___x_858_; 
lean_del_object(v___x_851_);
lean_dec_ref(v_e_841_);
v_e_857_ = lean_ctor_get(v_a_849_, 0);
lean_inc_ref(v_e_857_);
lean_dec_ref_known(v_a_849_, 1);
v___x_858_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_839_, v_post_840_, v_e_857_, v_a_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_858_;
}
default: 
{
lean_object* v_e_x3f_859_; 
lean_dec_ref(v_post_840_);
lean_dec_ref(v_pre_839_);
v_e_x3f_859_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_e_x3f_859_);
lean_dec_ref_known(v_a_849_, 1);
if (lean_obj_tag(v_e_x3f_859_) == 0)
{
lean_object* v___x_861_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v_e_841_);
v___x_861_ = v___x_851_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_e_841_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v_val_863_; lean_object* v___x_865_; 
lean_dec_ref(v_e_841_);
v_val_863_ = lean_ctor_get(v_e_x3f_859_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v_e_x3f_859_, 1);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v_val_863_);
v___x_865_ = v___x_851_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_val_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v_e_841_);
lean_dec_ref(v_post_840_);
lean_dec_ref(v_pre_839_);
v_a_868_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_848_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_848_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_876_, lean_object* v_post_877_, lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_876_, v_post_877_, v_e_878_, v_a_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v_a_879_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_886_, lean_object* v_post_887_, lean_object* v_sz_888_, lean_object* v_i_889_, lean_object* v_bs_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
size_t v_sz_boxed_897_; size_t v_i_boxed_898_; lean_object* v_res_899_; 
v_sz_boxed_897_ = lean_unbox_usize(v_sz_888_);
lean_dec(v_sz_888_);
v_i_boxed_898_ = lean_unbox_usize(v_i_889_);
lean_dec(v_i_889_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_886_, v_post_887_, v_sz_boxed_897_, v_i_boxed_898_, v_bs_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_900_, lean_object* v_post_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_900_, v_post_901_, v_x_902_, v_x_903_, v_x_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___boxed(lean_object* v_pre_912_, lean_object* v_post_913_, lean_object* v_e_914_, lean_object* v_a_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_912_, v_post_913_, v_e_914_, v_a_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v_a_915_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
v___x_923_ = lean_unsigned_to_nat(16u);
v___x_924_ = lean_mk_array(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1);
v___x_929_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_929_, 0, lean_box(0));
lean_closure_set(v___x_929_, 1, lean_box(0));
lean_closure_set(v___x_929_, 2, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(lean_object* v_input_930_, lean_object* v_pre_931_, lean_object* v_post_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_941_; 
v___x_938_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2);
v___x_939_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_938_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v___x_939_);
v___x_941_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_931_, v_post_932_, v_input_930_, v_a_940_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_943_, 0, lean_box(0));
lean_closure_set(v___x_943_, 1, lean_box(0));
lean_closure_set(v___x_943_, 2, v_a_940_);
v___x_944_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_943_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_944_, 0);
lean_dec(v_unused_952_);
v___x_946_ = v___x_944_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_dec(v___x_944_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_a_942_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_942_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_dec(v_a_940_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___boxed(lean_object* v_input_953_, lean_object* v_pre_954_, lean_object* v_post_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_input_953_, v_pre_954_, v_post_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object* v_e_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0));
v___x_972_ = lean_find_expr(v___x_971_, v_e_965_);
if (lean_obj_tag(v___x_972_) == 0)
{
uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = 1;
v___x_974_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_974_, 0, v_e_965_);
lean_ctor_set(v___x_974_, 1, v___x_972_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*2, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
else
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1024_; 
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_972_, 0);
lean_dec(v_unused_1025_);
v___x_977_ = v___x_972_;
v_isShared_978_ = v_isSharedCheck_1024_;
goto v_resetjp_976_;
}
else
{
lean_dec(v___x_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1024_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_pre_979_; lean_object* v___f_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v_pre_979_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1));
v___f_980_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2));
v___x_981_ = 1;
lean_inc_ref(v_e_965_);
v___x_982_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_e_965_, v_pre_979_, v___f_980_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_n(v_a_983_, 2);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = l_Lean_Meta_mkEqRefl(v_a_983_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_986_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
lean_inc(v_a_983_);
v___x_986_ = l_Lean_Meta_mkEq(v_e_965_, v_a_983_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_999_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_999_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_999_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_999_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_Meta_mkExpectedPropHint(v_a_985_, v_a_987_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_991_);
v___x_993_ = v___x_977_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_998_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_994_, 0, v_a_983_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*2, v___x_981_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_994_);
v___x_996_ = v___x_989_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec(v_a_985_);
lean_dec(v_a_983_);
lean_del_object(v___x_977_);
v_a_1000_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_986_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_986_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_a_983_);
lean_del_object(v___x_977_);
lean_dec_ref(v_e_965_);
v_a_1008_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_984_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_984_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_del_object(v___x_977_);
lean_dec_ref(v_e_965_);
v_a_1016_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_982_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_982_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___boxed(lean_object* v_e_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_e_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1033_, lean_object* v_m_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_1034_, v_a_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1037_, lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(v_00_u03b2_1037_, v_m_1038_, v_a_1039_);
lean_dec_ref(v_a_1039_);
lean_dec_ref(v_m_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1041_, lean_object* v_ref_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1042_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_ref_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1047_, v_ref_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1072_, lean_object* v_x_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(v_00_u03b1_1072_, v_x_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1081_, lean_object* v_m_1082_, lean_object* v_a_1083_, lean_object* v_b_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v_m_1082_, v_a_1083_, v_b_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1086_, lean_object* v_a_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1090_, lean_object* v_a_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1090_, v_a_1091_, v_x_1092_);
lean_dec(v_x_1092_);
lean_dec_ref(v_a_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1094_, lean_object* v_a_1095_, lean_object* v_x_1096_){
_start:
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1095_, v_x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1098_, lean_object* v_a_1099_, lean_object* v_x_1100_){
_start:
{
uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_res_1101_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1098_, v_a_1099_, v_x_1100_);
lean_dec(v_x_1100_);
lean_dec_ref(v_a_1099_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1103_, lean_object* v_data_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1106_, lean_object* v_a_1107_, lean_object* v_b_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1107_, v_b_1108_, v_x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1111_, lean_object* v_i_1112_, lean_object* v_source_1113_, lean_object* v_target_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1112_, v_source_1113_, v_target_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1117_, v_x_1118_);
return v___x_1119_;
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
