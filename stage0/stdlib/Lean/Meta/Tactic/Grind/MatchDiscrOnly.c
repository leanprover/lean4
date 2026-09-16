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
lean_object* v_arg_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_arg_85_ = lean_ctor_get(v___x_83_, 1);
lean_inc_ref(v_arg_85_);
v___x_86_ = l_Lean_Expr_appFnCleanup___redArg(v___x_83_);
v___x_87_ = l_Lean_Expr_isApp(v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v___x_86_);
lean_dec_ref(v_arg_85_);
lean_del_object(v___x_81_);
lean_dec_ref(v_e_66_);
goto v___jp_75_;
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_88_ = l_Lean_Expr_appFnCleanup___redArg(v___x_86_);
v___x_89_ = ((lean_object*)(l_Lean_Meta_Grind_markAsSimpMatchDiscrsOnly___closed__3));
v___x_90_ = l_Lean_Expr_isConstOf(v___x_88_, v___x_89_);
lean_dec_ref(v___x_88_);
if (v___x_90_ == 0)
{
lean_dec_ref(v_arg_85_);
lean_del_object(v___x_81_);
lean_dec_ref(v_e_66_);
goto v___jp_75_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Expr_getAppFn(v_arg_85_);
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
v___x_102_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_val_98_, v_arg_85_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
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
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*2, v___x_90_);
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
lean_dec_ref(v_arg_85_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_161_, 0, v_e_66_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*2, v___x_90_);
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
lean_dec_ref(v_arg_85_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_168_, 0, v_e_66_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*2, v___x_90_);
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
lean_object* v___y_513_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; uint8_t v___y_526_; lean_object* v___y_527_; lean_object* v_toCold_532_; lean_object* v_currRecDepth_533_; lean_object* v_ref_534_; uint8_t v_diag_535_; uint8_t v_suppressElabErrors_536_; lean_object* v_maxRecDepth_537_; lean_object* v_cancelTk_x3f_538_; 
v_toCold_532_ = lean_ctor_get(v___y_509_, 0);
v_currRecDepth_533_ = lean_ctor_get(v___y_509_, 1);
v_ref_534_ = lean_ctor_get(v___y_509_, 2);
v_diag_535_ = lean_ctor_get_uint8(v___y_509_, sizeof(void*)*3);
v_suppressElabErrors_536_ = lean_ctor_get_uint8(v___y_509_, sizeof(void*)*3 + 1);
v_maxRecDepth_537_ = lean_ctor_get(v_toCold_532_, 3);
v_cancelTk_x3f_538_ = lean_ctor_get(v_toCold_532_, 10);
if (lean_obj_tag(v_cancelTk_x3f_538_) == 1)
{
lean_object* v_val_544_; uint8_t v___x_545_; 
v_val_544_ = lean_ctor_get(v_cancelTk_x3f_538_, 0);
v___x_545_ = l_IO_CancelToken_isSet(v_val_544_);
if (v___x_545_ == 0)
{
goto v___jp_539_;
}
else
{
lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_x_505_);
v___x_546_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
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
goto v___jp_539_;
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
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v___y_527_, v___x_528_);
lean_inc_ref(v___y_525_);
v___x_530_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_530_, 0, v___y_525_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
lean_ctor_set(v___x_530_, 2, v___y_524_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*3, v___y_526_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*3 + 1, v___y_523_);
lean_inc(v___y_510_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
lean_inc(v___y_506_);
v___x_531_ = lean_apply_6(v_x_505_, v___y_506_, v___y_507_, v___y_508_, v___x_530_, v___y_510_, lean_box(0));
v___y_513_ = v___x_531_;
goto v___jp_512_;
}
v___jp_539_:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_nat_dec_eq(v_maxRecDepth_537_, v___x_540_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = lean_nat_dec_eq(v_currRecDepth_533_, v_maxRecDepth_537_);
if (v___x_542_ == 0)
{
lean_inc(v_ref_534_);
v___y_523_ = v_suppressElabErrors_536_;
v___y_524_ = v_ref_534_;
v___y_525_ = v_toCold_532_;
v___y_526_ = v_diag_535_;
v___y_527_ = v_currRecDepth_533_;
goto v___jp_522_;
}
else
{
lean_object* v___x_543_; 
lean_dec_ref(v_x_505_);
lean_inc(v_ref_534_);
v___x_543_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_534_);
v___y_513_ = v___x_543_;
goto v___jp_512_;
}
}
else
{
lean_inc(v_ref_534_);
v___y_523_ = v_suppressElabErrors_536_;
v___y_524_ = v_ref_534_;
v___y_525_ = v_toCold_532_;
v___y_526_ = v_diag_535_;
v___y_527_ = v_currRecDepth_533_;
goto v___jp_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
return v_res_562_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_564_; lean_object* v_dummy_565_; 
v___x_564_ = lean_box(0);
v_dummy_565_ = l_Lean_Expr_sort___override(v___x_564_);
return v_dummy_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(lean_object* v_pre_566_, lean_object* v_post_567_, size_t v_sz_568_, size_t v_i_569_, lean_object* v_bs_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_569_, v_sz_568_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec_ref(v_post_567_);
lean_dec_ref(v_pre_566_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_bs_570_);
return v___x_578_;
}
else
{
lean_object* v_v_579_; lean_object* v___x_580_; lean_object* v_bs_x27_581_; lean_object* v___x_582_; 
v_v_579_ = lean_array_uget(v_bs_570_, v_i_569_);
v___x_580_ = lean_unsigned_to_nat(0u);
v_bs_x27_581_ = lean_array_uset(v_bs_570_, v_i_569_, v___x_580_);
lean_inc_ref(v_post_567_);
lean_inc_ref(v_pre_566_);
v___x_582_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_566_, v_post_567_, v_v_579_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_add(v_i_569_, v___x_584_);
v___x_586_ = lean_array_uset(v_bs_x27_581_, v_i_569_, v_a_583_);
v_i_569_ = v___x_585_;
v_bs_570_ = v___x_586_;
goto _start;
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_bs_x27_581_);
lean_dec_ref(v_post_567_);
lean_dec_ref(v_pre_566_);
v_a_588_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_582_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_582_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(lean_object* v_pre_596_, lean_object* v_post_597_, lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
if (lean_obj_tag(v_x_598_) == 5)
{
lean_object* v_fn_607_; lean_object* v_arg_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_fn_607_ = lean_ctor_get(v_x_598_, 0);
lean_inc_ref(v_fn_607_);
v_arg_608_ = lean_ctor_get(v_x_598_, 1);
lean_inc_ref(v_arg_608_);
lean_dec_ref_known(v_x_598_, 2);
v___x_609_ = lean_array_set(v_x_599_, v_x_600_, v_arg_608_);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_sub(v_x_600_, v___x_610_);
lean_dec(v_x_600_);
v_x_598_ = v_fn_607_;
v_x_599_ = v___x_609_;
v_x_600_ = v___x_611_;
goto _start;
}
else
{
lean_object* v___x_613_; 
lean_dec(v_x_600_);
lean_inc_ref(v_post_597_);
lean_inc_ref(v_pre_596_);
v___x_613_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_596_, v_post_597_, v_x_598_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; size_t v_sz_615_; size_t v___x_616_; lean_object* v___x_617_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v_sz_615_ = lean_array_size(v_x_599_);
v___x_616_ = ((size_t)0ULL);
lean_inc_ref(v_post_597_);
lean_inc_ref(v_pre_596_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_596_, v_post_597_, v_sz_615_, v___x_616_, v_x_599_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = l_Lean_mkAppN(v_a_614_, v_a_618_);
lean_dec(v_a_618_);
v___x_620_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_596_, v_post_597_, v___x_619_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
return v___x_620_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_a_614_);
lean_dec_ref(v_post_597_);
lean_dec_ref(v_pre_596_);
v_a_621_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_617_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_617_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_dec_ref(v_x_599_);
lean_dec_ref(v_post_597_);
lean_dec_ref(v_pre_596_);
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(lean_object* v___x_629_, lean_object* v_pre_630_, lean_object* v_e_631_, lean_object* v_post_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Core_checkSystem(v___x_629_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_640_; 
lean_dec_ref_known(v___x_639_, 1);
lean_inc_ref(v_pre_630_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc_ref(v_e_631_);
v___x_640_ = lean_apply_6(v_pre_630_, v_e_631_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, lean_box(0));
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_756_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_756_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_756_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_756_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___y_646_; 
switch(lean_obj_tag(v_a_641_))
{
case 0:
{
lean_object* v_e_746_; lean_object* v___x_748_; 
lean_dec_ref(v_post_632_);
lean_dec_ref(v_e_631_);
lean_dec_ref(v_pre_630_);
v_e_746_ = lean_ctor_get(v_a_641_, 0);
lean_inc_ref(v_e_746_);
lean_dec_ref_known(v_a_641_, 1);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_e_746_);
v___x_748_ = v___x_643_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_e_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
case 1:
{
lean_object* v_e_750_; lean_object* v___x_751_; 
lean_del_object(v___x_643_);
lean_dec_ref(v_e_631_);
v_e_750_ = lean_ctor_get(v_a_641_, 0);
lean_inc_ref(v_e_750_);
lean_dec_ref_known(v_a_641_, 1);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_751_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_e_750_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v_a_752_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_753_;
}
else
{
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_751_;
}
}
default: 
{
lean_object* v_e_x3f_754_; 
lean_del_object(v___x_643_);
v_e_x3f_754_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_e_x3f_754_);
lean_dec_ref_known(v_a_641_, 1);
if (lean_obj_tag(v_e_x3f_754_) == 0)
{
v___y_646_ = v_e_631_;
goto v___jp_645_;
}
else
{
lean_object* v_val_755_; 
lean_dec_ref(v_e_631_);
v_val_755_ = lean_ctor_get(v_e_x3f_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v_e_x3f_754_, 1);
v___y_646_ = v_val_755_;
goto v___jp_645_;
}
}
}
v___jp_645_:
{
switch(lean_obj_tag(v___y_646_))
{
case 7:
{
lean_object* v_binderName_647_; lean_object* v_binderType_648_; lean_object* v_body_649_; uint8_t v_binderInfo_650_; lean_object* v___x_651_; 
v_binderName_647_ = lean_ctor_get(v___y_646_, 0);
v_binderType_648_ = lean_ctor_get(v___y_646_, 1);
v_body_649_ = lean_ctor_get(v___y_646_, 2);
v_binderInfo_650_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_648_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_651_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_binderType_648_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
lean_inc_ref(v_body_649_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_653_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_body_649_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; size_t v___x_655_; size_t v___x_656_; uint8_t v___x_657_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_ptr_addr(v_binderType_648_);
v___x_656_ = lean_ptr_addr(v_a_652_);
v___x_657_ = lean_usize_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_inc(v_binderName_647_);
lean_dec_ref_known(v___y_646_, 3);
v___x_658_ = l_Lean_Expr_forallE___override(v_binderName_647_, v_a_652_, v_a_654_, v_binderInfo_650_);
v___x_659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_658_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_659_;
}
else
{
size_t v___x_660_; size_t v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_ptr_addr(v_body_649_);
v___x_661_ = lean_ptr_addr(v_a_654_);
v___x_662_ = lean_usize_dec_eq(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_inc(v_binderName_647_);
lean_dec_ref_known(v___y_646_, 3);
v___x_663_ = l_Lean_Expr_forallE___override(v_binderName_647_, v_a_652_, v_a_654_, v_binderInfo_650_);
v___x_664_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_663_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_664_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_650_, v_binderInfo_650_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_inc(v_binderName_647_);
lean_dec_ref_known(v___y_646_, 3);
v___x_666_ = l_Lean_Expr_forallE___override(v_binderName_647_, v_a_652_, v_a_654_, v_binderInfo_650_);
v___x_667_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_666_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
lean_dec(v_a_654_);
lean_dec(v_a_652_);
v___x_668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___y_646_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_668_;
}
}
}
}
else
{
lean_dec(v_a_652_);
lean_dec_ref_known(v___y_646_, 3);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_653_;
}
}
else
{
lean_dec_ref_known(v___y_646_, 3);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_651_;
}
}
case 6:
{
lean_object* v_binderName_669_; lean_object* v_binderType_670_; lean_object* v_body_671_; uint8_t v_binderInfo_672_; lean_object* v___x_673_; 
v_binderName_669_ = lean_ctor_get(v___y_646_, 0);
v_binderType_670_ = lean_ctor_get(v___y_646_, 1);
v_body_671_ = lean_ctor_get(v___y_646_, 2);
v_binderInfo_672_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_670_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_673_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_binderType_670_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
lean_inc_ref(v_body_671_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_body_671_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; size_t v___x_677_; size_t v___x_678_; uint8_t v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = lean_ptr_addr(v_binderType_670_);
v___x_678_ = lean_ptr_addr(v_a_674_);
v___x_679_ = lean_usize_dec_eq(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc(v_binderName_669_);
lean_dec_ref_known(v___y_646_, 3);
v___x_680_ = l_Lean_Expr_lam___override(v_binderName_669_, v_a_674_, v_a_676_, v_binderInfo_672_);
v___x_681_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_680_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_681_;
}
else
{
size_t v___x_682_; size_t v___x_683_; uint8_t v___x_684_; 
v___x_682_ = lean_ptr_addr(v_body_671_);
v___x_683_ = lean_ptr_addr(v_a_676_);
v___x_684_ = lean_usize_dec_eq(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_inc(v_binderName_669_);
lean_dec_ref_known(v___y_646_, 3);
v___x_685_ = l_Lean_Expr_lam___override(v_binderName_669_, v_a_674_, v_a_676_, v_binderInfo_672_);
v___x_686_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_685_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_686_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_672_, v_binderInfo_672_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc(v_binderName_669_);
lean_dec_ref_known(v___y_646_, 3);
v___x_688_ = l_Lean_Expr_lam___override(v_binderName_669_, v_a_674_, v_a_676_, v_binderInfo_672_);
v___x_689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_688_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; 
lean_dec(v_a_676_);
lean_dec(v_a_674_);
v___x_690_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___y_646_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_690_;
}
}
}
}
else
{
lean_dec(v_a_674_);
lean_dec_ref_known(v___y_646_, 3);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_675_;
}
}
else
{
lean_dec_ref_known(v___y_646_, 3);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_673_;
}
}
case 8:
{
lean_object* v_declName_691_; lean_object* v_type_692_; lean_object* v_value_693_; lean_object* v_body_694_; uint8_t v_nondep_695_; lean_object* v___x_696_; 
v_declName_691_ = lean_ctor_get(v___y_646_, 0);
v_type_692_ = lean_ctor_get(v___y_646_, 1);
v_value_693_ = lean_ctor_get(v___y_646_, 2);
v_body_694_ = lean_ctor_get(v___y_646_, 3);
v_nondep_695_ = lean_ctor_get_uint8(v___y_646_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_692_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_696_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_type_692_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
lean_inc_ref(v_value_693_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_value_693_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
lean_inc_ref(v_body_694_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_700_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_body_694_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; size_t v___x_702_; size_t v___x_703_; uint8_t v___x_704_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_ptr_addr(v_type_692_);
v___x_703_ = lean_ptr_addr(v_a_697_);
v___x_704_ = lean_usize_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_inc(v_declName_691_);
lean_dec_ref_known(v___y_646_, 4);
v___x_705_ = l_Lean_Expr_letE___override(v_declName_691_, v_a_697_, v_a_699_, v_a_701_, v_nondep_695_);
v___x_706_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_705_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_706_;
}
else
{
size_t v___x_707_; size_t v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_ptr_addr(v_value_693_);
v___x_708_ = lean_ptr_addr(v_a_699_);
v___x_709_ = lean_usize_dec_eq(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_inc(v_declName_691_);
lean_dec_ref_known(v___y_646_, 4);
v___x_710_ = l_Lean_Expr_letE___override(v_declName_691_, v_a_697_, v_a_699_, v_a_701_, v_nondep_695_);
v___x_711_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_710_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_711_;
}
else
{
size_t v___x_712_; size_t v___x_713_; uint8_t v___x_714_; 
v___x_712_ = lean_ptr_addr(v_body_694_);
v___x_713_ = lean_ptr_addr(v_a_701_);
v___x_714_ = lean_usize_dec_eq(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc(v_declName_691_);
lean_dec_ref_known(v___y_646_, 4);
v___x_715_ = l_Lean_Expr_letE___override(v_declName_691_, v_a_697_, v_a_699_, v_a_701_, v_nondep_695_);
v___x_716_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_715_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; 
lean_dec(v_a_701_);
lean_dec(v_a_699_);
lean_dec(v_a_697_);
v___x_717_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___y_646_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_717_;
}
}
}
}
else
{
lean_dec(v_a_699_);
lean_dec(v_a_697_);
lean_dec_ref_known(v___y_646_, 4);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_700_;
}
}
else
{
lean_dec(v_a_697_);
lean_dec_ref_known(v___y_646_, 4);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_698_;
}
}
else
{
lean_dec_ref_known(v___y_646_, 4);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_696_;
}
}
case 5:
{
lean_object* v_dummy_718_; lean_object* v_nargs_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_dummy_718_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___closed__0);
v_nargs_719_ = l_Lean_Expr_getAppNumArgs(v___y_646_);
lean_inc(v_nargs_719_);
v___x_720_ = lean_mk_array(v_nargs_719_, v_dummy_718_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_sub(v_nargs_719_, v___x_721_);
lean_dec(v_nargs_719_);
v___x_723_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_630_, v_post_632_, v___y_646_, v___x_720_, v___x_722_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_723_;
}
case 10:
{
lean_object* v_data_724_; lean_object* v_expr_725_; lean_object* v___x_726_; 
v_data_724_ = lean_ctor_get(v___y_646_, 0);
v_expr_725_ = lean_ctor_get(v___y_646_, 1);
lean_inc_ref(v_expr_725_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_726_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_expr_725_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; size_t v___x_728_; size_t v___x_729_; uint8_t v___x_730_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = lean_ptr_addr(v_expr_725_);
v___x_729_ = lean_ptr_addr(v_a_727_);
v___x_730_ = lean_usize_dec_eq(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_inc(v_data_724_);
lean_dec_ref_known(v___y_646_, 2);
v___x_731_ = l_Lean_Expr_mdata___override(v_data_724_, v_a_727_);
v___x_732_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_731_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_732_;
}
else
{
lean_object* v___x_733_; 
lean_dec(v_a_727_);
v___x_733_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___y_646_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_733_;
}
}
else
{
lean_dec_ref_known(v___y_646_, 2);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_726_;
}
}
case 11:
{
lean_object* v_typeName_734_; lean_object* v_idx_735_; lean_object* v_struct_736_; lean_object* v___x_737_; 
v_typeName_734_ = lean_ctor_get(v___y_646_, 0);
v_idx_735_ = lean_ctor_get(v___y_646_, 1);
v_struct_736_ = lean_ctor_get(v___y_646_, 2);
lean_inc_ref(v_struct_736_);
lean_inc_ref(v_post_632_);
lean_inc_ref(v_pre_630_);
v___x_737_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_630_, v_post_632_, v_struct_736_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; size_t v___x_739_; size_t v___x_740_; uint8_t v___x_741_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = lean_ptr_addr(v_struct_736_);
v___x_740_ = lean_ptr_addr(v_a_738_);
v___x_741_ = lean_usize_dec_eq(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_inc(v_idx_735_);
lean_inc(v_typeName_734_);
lean_dec_ref_known(v___y_646_, 3);
v___x_742_ = l_Lean_Expr_proj___override(v_typeName_734_, v_idx_735_, v_a_738_);
v___x_743_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___x_742_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; 
lean_dec(v_a_738_);
v___x_744_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___y_646_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_744_;
}
}
else
{
lean_dec_ref_known(v___y_646_, 3);
lean_dec_ref(v_post_632_);
lean_dec_ref(v_pre_630_);
return v___x_737_;
}
}
default: 
{
lean_object* v___x_745_; 
v___x_745_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_630_, v_post_632_, v___y_646_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_post_632_);
lean_dec_ref(v_e_631_);
lean_dec_ref(v_pre_630_);
v_a_757_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_640_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_640_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_post_632_);
lean_dec_ref(v_e_631_);
lean_dec_ref(v_pre_630_);
v_a_765_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_639_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_639_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed(lean_object* v___x_773_, lean_object* v_pre_774_, lean_object* v_e_775_, lean_object* v_post_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1(v___x_773_, v_pre_774_, v_e_775_, v_post_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(lean_object* v_pre_784_, lean_object* v_post_785_, lean_object* v_e_786_, lean_object* v_a_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
lean_inc(v_a_787_);
v___x_793_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_793_, 0, lean_box(0));
lean_closure_set(v___x_793_, 1, lean_box(0));
lean_closure_set(v___x_793_, 2, v_a_787_);
v___x_794_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___x_793_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_826_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_826_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_826_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_826_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_a_795_, v_e_786_);
lean_dec(v_a_795_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; lean_object* v___f_801_; lean_object* v___x_802_; 
lean_del_object(v___x_797_);
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_786_);
v___f_801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_801_, 0, v___x_800_);
lean_closure_set(v___f_801_, 1, v_pre_784_);
lean_closure_set(v___f_801_, 2, v_e_786_);
lean_closure_set(v___f_801_, 3, v_post_785_);
v___x_802_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v___f_801_, v_a_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___f_804_; lean_object* v___x_805_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_n(v_a_803_, 2);
lean_dec_ref_known(v___x_802_, 1);
lean_inc(v_a_787_);
v___f_804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_804_, 0, v_a_787_);
lean_closure_set(v___f_804_, 1, v_e_786_);
lean_closure_set(v___f_804_, 2, v_a_803_);
v___x_805_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___lam__0(lean_box(0), v___f_804_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v___x_805_, 0);
lean_dec(v_unused_813_);
v___x_807_ = v___x_805_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_dec(v___x_805_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v_a_803_);
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_803_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_a_803_);
v_a_814_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_805_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_805_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_dec_ref(v_e_786_);
return v___x_802_;
}
}
else
{
lean_object* v_val_822_; lean_object* v___x_824_; 
lean_dec_ref(v_e_786_);
lean_dec_ref(v_post_785_);
lean_dec_ref(v_pre_784_);
v_val_822_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v___x_799_, 1);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_val_822_);
v___x_824_ = v___x_797_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_val_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v_e_786_);
lean_dec_ref(v_post_785_);
lean_dec_ref(v_pre_784_);
v_a_827_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_794_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_794_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(lean_object* v_pre_835_, lean_object* v_post_836_, lean_object* v_e_837_, lean_object* v_a_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
lean_inc_ref(v_post_836_);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc_ref(v_e_837_);
v___x_844_ = lean_apply_6(v_post_836_, v_e_837_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, lean_box(0));
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_863_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_863_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_863_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_863_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
switch(lean_obj_tag(v_a_845_))
{
case 0:
{
lean_object* v_e_849_; lean_object* v___x_851_; 
lean_dec_ref(v_e_837_);
lean_dec_ref(v_post_836_);
lean_dec_ref(v_pre_835_);
v_e_849_ = lean_ctor_get(v_a_845_, 0);
lean_inc_ref(v_e_849_);
lean_dec_ref_known(v_a_845_, 1);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v_e_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_e_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
case 1:
{
lean_object* v_e_853_; lean_object* v___x_854_; 
lean_del_object(v___x_847_);
lean_dec_ref(v_e_837_);
v_e_853_ = lean_ctor_get(v_a_845_, 0);
lean_inc_ref(v_e_853_);
lean_dec_ref_known(v_a_845_, 1);
v___x_854_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_835_, v_post_836_, v_e_853_, v_a_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_854_;
}
default: 
{
lean_object* v_e_x3f_855_; 
lean_dec_ref(v_post_836_);
lean_dec_ref(v_pre_835_);
v_e_x3f_855_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_e_x3f_855_);
lean_dec_ref_known(v_a_845_, 1);
if (lean_obj_tag(v_e_x3f_855_) == 0)
{
lean_object* v___x_857_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v_e_837_);
v___x_857_ = v___x_847_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_e_837_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v_val_859_; lean_object* v___x_861_; 
lean_dec_ref(v_e_837_);
v_val_859_ = lean_ctor_get(v_e_x3f_855_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v_e_x3f_855_, 1);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v_val_859_);
v___x_861_ = v___x_847_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_val_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec_ref(v_e_837_);
lean_dec_ref(v_post_836_);
lean_dec_ref(v_pre_835_);
v_a_864_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_844_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_844_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_872_, lean_object* v_post_873_, lean_object* v_e_874_, lean_object* v_a_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__2(v_pre_872_, v_post_873_, v_e_874_, v_a_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_a_875_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_882_, lean_object* v_post_883_, lean_object* v_sz_884_, lean_object* v_i_885_, lean_object* v_bs_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
size_t v_sz_boxed_893_; size_t v_i_boxed_894_; lean_object* v_res_895_; 
v_sz_boxed_893_ = lean_unbox_usize(v_sz_884_);
lean_dec(v_sz_884_);
v_i_boxed_894_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_res_895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__1(v_pre_882_, v_post_883_, v_sz_boxed_893_, v_i_boxed_894_, v_bs_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_896_, lean_object* v_post_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__4(v_pre_896_, v_post_897_, v_x_898_, v_x_899_, v_x_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0___boxed(lean_object* v_pre_908_, lean_object* v_post_909_, lean_object* v_e_910_, lean_object* v_a_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_908_, v_post_909_, v_e_910_, v_a_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v_a_911_);
return v_res_917_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_box(0);
v___x_919_ = lean_unsigned_to_nat(16u);
v___x_920_ = lean_mk_array(v___x_919_, v___x_918_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__0);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__1);
v___x_925_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_925_, 0, lean_box(0));
lean_closure_set(v___x_925_, 1, lean_box(0));
lean_closure_set(v___x_925_, 2, v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(lean_object* v_input_926_, lean_object* v_pre_927_, lean_object* v_post_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_a_936_; lean_object* v___x_937_; 
v___x_934_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___closed__2);
v___x_935_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_934_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref(v___x_935_);
v___x_937_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0(v_pre_927_, v_post_928_, v_input_926_, v_a_936_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v___x_939_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_939_, 0, lean_box(0));
lean_closure_set(v___x_939_, 1, lean_box(0));
lean_closure_set(v___x_939_, 2, v_a_936_);
v___x_940_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___lam__0(lean_box(0), v___x_939_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v___x_940_, 0);
lean_dec(v_unused_948_);
v___x_942_ = v___x_940_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_dec(v___x_940_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_a_938_);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_938_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
lean_dec(v_a_936_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0___boxed(lean_object* v_input_949_, lean_object* v_pre_950_, lean_object* v_post_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_input_949_, v_pre_950_, v_post_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object* v_e_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__0));
v___x_968_ = lean_find_expr(v___x_967_, v_e_961_);
if (lean_obj_tag(v___x_968_) == 0)
{
uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = 1;
v___x_970_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_970_, 0, v_e_961_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*2, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
else
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_968_, 0);
lean_dec(v_unused_1021_);
v___x_973_ = v___x_968_;
v_isShared_974_ = v_isSharedCheck_1020_;
goto v_resetjp_972_;
}
else
{
lean_dec(v___x_968_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1020_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_pre_975_; lean_object* v___f_976_; uint8_t v___x_977_; lean_object* v___x_978_; 
v_pre_975_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__1));
v___f_976_ = ((lean_object*)(l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___closed__2));
v___x_977_ = 1;
lean_inc_ref(v_e_961_);
v___x_978_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0(v_e_961_, v_pre_975_, v___f_976_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_n(v_a_979_, 2);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_Lean_Meta_mkEqRefl(v_a_979_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
lean_inc(v_a_979_);
v___x_982_ = l_Lean_Meta_mkEq(v_e_961_, v_a_979_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_995_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_995_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_995_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_995_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = l_Lean_Meta_mkExpectedPropHint(v_a_981_, v_a_983_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_987_);
v___x_989_ = v___x_973_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_994_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_990_, 0, v_a_979_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*2, v___x_977_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_990_);
v___x_992_ = v___x_985_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_981_);
lean_dec(v_a_979_);
lean_del_object(v___x_973_);
v_a_996_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_982_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_982_);
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
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_a_979_);
lean_del_object(v___x_973_);
lean_dec_ref(v_e_961_);
v_a_1004_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_980_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_980_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_973_);
lean_dec_ref(v_e_961_);
v_a_1012_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_978_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_978_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly___boxed(lean_object* v_e_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(v_e_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1029_, lean_object* v_m_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___redArg(v_m_1030_, v_a_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_m_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3(v_00_u03b2_1033_, v_m_1034_, v_a_1035_);
lean_dec_ref(v_a_1035_);
lean_dec_ref(v_m_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1037_, lean_object* v_ref_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1038_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_ref_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1043_, v_ref_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1059_, lean_object* v_x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___redArg(v_x_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_x_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__5(v_00_u03b1_1068_, v_x_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1077_, lean_object* v_m_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6___redArg(v_m_1078_, v_a_1079_, v_b_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1082_, lean_object* v_a_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1086_, lean_object* v_a_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1086_, v_a_1087_, v_x_1088_);
lean_dec(v_x_1088_);
lean_dec_ref(v_a_1087_);
return v_res_1089_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1090_, lean_object* v_a_1091_, lean_object* v_x_1092_){
_start:
{
uint8_t v___x_1093_; 
v___x_1093_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1091_, v_x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1094_, lean_object* v_a_1095_, lean_object* v_x_1096_){
_start:
{
uint8_t v_res_1097_; lean_object* v_r_1098_; 
v_res_1097_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1094_, v_a_1095_, v_x_1096_);
lean_dec(v_x_1096_);
lean_dec_ref(v_a_1095_);
v_r_1098_ = lean_box(v_res_1097_);
return v_r_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1099_, lean_object* v_data_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1102_, lean_object* v_a_1103_, lean_object* v_b_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1103_, v_b_1104_, v_x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1107_, lean_object* v_i_1108_, lean_object* v_source_1109_, lean_object* v_target_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1108_, v_source_1109_, v_target_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseSimpMatchDiscrsOnly_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1113_, v_x_1114_);
return v___x_1115_;
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
