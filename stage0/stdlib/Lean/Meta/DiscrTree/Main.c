// Lean compiler output
// Module: Lean.Meta.DiscrTree.Main
// Imports: public import Lean.Meta.Basic public import Lean.Meta.DiscrTree.Basic import Lean.Meta.WHNF
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
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isStrictImplicit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_isClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "_discr_tree_tmp"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 72, 223, 190, 190, 84, 146, 120)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value;
static const lean_string_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity;
static lean_once_cell_t l_Lean_Meta_DiscrTree_mkPath___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_DiscrTree_mkPath___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2_value;
static const lean_array_object l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4;
static const lean_closure_object l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5_value;
static const lean_array_object l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0_value;
static const lean_array_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 4:
{
lean_object* v_a_2_; 
v_a_2_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_2_);
return v_a_2_;
}
case 3:
{
lean_object* v_a_3_; 
v_a_3_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_3_);
return v_a_3_;
}
case 5:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(1u);
return v___x_4_;
}
case 6:
{
lean_object* v_a_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_a_5_ = lean_ctor_get(v_x_1_, 2);
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = lean_nat_add(v___x_6_, v_a_5_);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(0u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_arity___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_DiscrTree_Key_arity(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId));
v___x_16_ = l_Lean_mkMVar(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(lean_object* v_a_18_, lean_object* v_i_19_, lean_object* v_infos_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_39_ = lean_array_get_size(v_infos_20_);
v___x_40_ = lean_nat_dec_lt(v_i_19_, v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_isProof(v_a_18_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_41_;
}
else
{
lean_object* v_info_42_; uint8_t v_isInstance_43_; 
v_info_42_ = lean_array_fget_borrowed(v_infos_20_, v_i_19_);
v_isInstance_43_ = lean_ctor_get_uint8(v_info_42_, sizeof(void*)*1 + 4);
if (v_isInstance_43_ == 0)
{
uint8_t v___x_44_; 
v___x_44_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_42_);
if (v___x_44_ == 0)
{
uint8_t v___x_45_; 
v___x_45_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_42_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_isProof(v_a_18_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_46_;
}
else
{
goto v___jp_26_;
}
}
else
{
goto v___jp_26_;
}
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec_ref(v_a_18_);
v___x_47_ = lean_box(v_isInstance_43_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
v___jp_26_:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_isType(v_a_18_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_38_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_38_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_32_ = lean_unbox(v_a_28_);
lean_dec(v_a_28_);
v___x_33_ = lean_bool_not(v___x_32_);
v___x_34_ = lean_box(v___x_33_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_34_);
v___x_36_ = v___x_30_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object* v_a_49_, lean_object* v_i_50_, lean_object* v_infos_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_a_49_, v_i_50_, v_infos_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec_ref(v_infos_51_);
lean_dec(v_i_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object* v_infos_58_, lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
if (lean_obj_tag(v_x_60_) == 5)
{
lean_object* v_fn_67_; lean_object* v_arg_68_; lean_object* v___x_69_; 
v_fn_67_ = lean_ctor_get(v_x_60_, 0);
lean_inc_ref(v_fn_67_);
v_arg_68_ = lean_ctor_get(v_x_60_, 1);
lean_inc_ref_n(v_arg_68_, 2);
lean_dec_ref_known(v_x_60_, 2);
v___x_69_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_arg_68_, v_x_59_, v_infos_58_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; uint8_t v___x_71_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v___x_69_, 1);
v___x_71_ = lean_unbox(v_a_70_);
lean_dec(v_a_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_sub(v_x_59_, v___x_72_);
lean_dec(v_x_59_);
v___x_74_ = lean_array_push(v_x_61_, v_arg_68_);
v_x_59_ = v___x_73_;
v_x_60_ = v_fn_67_;
v_x_61_ = v___x_74_;
goto _start;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec_ref(v_arg_68_);
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_sub(v_x_59_, v___x_76_);
lean_dec(v_x_59_);
v___x_78_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
v___x_79_ = lean_array_push(v_x_61_, v___x_78_);
v_x_59_ = v___x_77_;
v_x_60_ = v_fn_67_;
v_x_61_ = v___x_79_;
goto _start;
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_fn_67_);
lean_dec_ref(v_x_61_);
lean_dec(v_x_59_);
v_a_81_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_69_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_69_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
else
{
lean_object* v___x_89_; 
lean_dec_ref(v_x_60_);
lean_dec(v_x_59_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v_x_61_);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object* v_infos_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_infos_90_, v_x_91_, v_x_92_, v_x_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec_ref(v_infos_90_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(lean_object* v_e_114_){
_start:
{
uint8_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = l_Lean_Expr_isRawNatLit(v_e_114_);
v___x_116_ = 1;
if (v___x_115_ == 0)
{
lean_object* v_f_117_; uint8_t v___x_118_; uint8_t v___x_119_; 
v_f_117_ = l_Lean_Expr_getAppFn(v_e_114_);
v___x_118_ = l_Lean_Expr_isConst(v_f_117_);
v___x_119_ = lean_bool_not(v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v_fName_120_; uint8_t v___y_122_; uint8_t v___y_135_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_fName_120_ = l_Lean_Expr_constName_x21(v_f_117_);
lean_dec_ref(v_f_117_);
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_144_ = lean_name_eq(v_fName_120_, v___x_143_);
if (v___x_144_ == 0)
{
v___y_135_ = v___x_144_;
goto v___jp_134_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_145_ = l_Lean_Expr_getAppNumArgs(v_e_114_);
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_dec_eq(v___x_145_, v___x_146_);
lean_dec(v___x_145_);
v___y_135_ = v___x_147_;
goto v___jp_134_;
}
v___jp_121_:
{
if (v___y_122_ == 0)
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2));
v___x_124_ = lean_name_eq(v_fName_120_, v___x_123_);
lean_dec(v_fName_120_);
if (v___x_124_ == 0)
{
lean_dec_ref(v_e_114_);
if (v___x_124_ == 0)
{
return v___x_124_;
}
else
{
return v___x_116_;
}
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = l_Lean_Expr_getAppNumArgs(v_e_114_);
lean_dec_ref(v_e_114_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_nat_dec_eq(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
return v___x_116_;
}
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_fName_120_);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = l_Lean_Expr_getAppNumArgs(v_e_114_);
v___x_130_ = lean_nat_sub(v___x_129_, v___x_128_);
lean_dec(v___x_129_);
v___x_131_ = lean_nat_sub(v___x_130_, v___x_128_);
lean_dec(v___x_130_);
v___x_132_ = l_Lean_Expr_getRevArg_x21(v_e_114_, v___x_131_);
lean_dec_ref(v_e_114_);
v_e_114_ = v___x_132_;
goto _start;
}
}
v___jp_134_:
{
if (v___y_135_ == 0)
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5));
v___x_137_ = lean_name_eq(v_fName_120_, v___x_136_);
if (v___x_137_ == 0)
{
v___y_122_ = v___x_137_;
goto v___jp_121_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_138_ = l_Lean_Expr_getAppNumArgs(v_e_114_);
v___x_139_ = lean_unsigned_to_nat(3u);
v___x_140_ = lean_nat_dec_eq(v___x_138_, v___x_139_);
lean_dec(v___x_138_);
v___y_122_ = v___x_140_;
goto v___jp_121_;
}
}
else
{
lean_object* v___x_141_; 
lean_dec(v_fName_120_);
v___x_141_ = l_Lean_Expr_appArg_x21(v_e_114_);
lean_dec_ref(v_e_114_);
v_e_114_ = v___x_141_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_f_117_);
lean_dec_ref(v_e_114_);
return v___x_115_;
}
}
else
{
lean_dec_ref(v_e_114_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object* v_e_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v_e_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(lean_object* v_e_153_){
_start:
{
uint8_t v___y_155_; lean_object* v_f_158_; 
v_f_158_ = l_Lean_Expr_getAppFn(v_e_153_);
switch(lean_obj_tag(v_f_158_))
{
case 9:
{
lean_object* v_a_159_; 
lean_dec_ref(v_e_153_);
v_a_159_ = lean_ctor_get(v_f_158_, 0);
lean_inc_ref(v_a_159_);
lean_dec_ref_known(v_f_158_, 1);
if (lean_obj_tag(v_a_159_) == 0)
{
lean_object* v_val_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_val_160_ = lean_ctor_get(v_a_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v_a_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_val_160_);
lean_dec(v_a_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set_tag(v___x_162_, 1);
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_val_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v___x_168_; 
lean_dec_ref(v_a_159_);
v___x_168_ = lean_box(0);
return v___x_168_;
}
}
case 4:
{
lean_object* v_declName_169_; uint8_t v___y_171_; uint8_t v___y_184_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_declName_169_ = lean_ctor_get(v_f_158_, 0);
lean_inc(v_declName_169_);
lean_dec_ref_known(v_f_158_, 2);
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_203_ = lean_name_eq(v_declName_169_, v___x_202_);
if (v___x_203_ == 0)
{
v___y_184_ = v___x_203_;
goto v___jp_183_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
lean_dec(v___x_204_);
v___y_184_ = v___x_206_;
goto v___jp_183_;
}
v___jp_170_:
{
if (v___y_171_ == 0)
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2));
v___x_173_ = lean_name_eq(v_declName_169_, v___x_172_);
lean_dec(v_declName_169_);
if (v___x_173_ == 0)
{
lean_dec_ref(v_e_153_);
v___y_155_ = v___x_173_;
goto v___jp_154_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
lean_dec_ref(v_e_153_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_nat_dec_eq(v___x_174_, v___x_175_);
lean_dec(v___x_174_);
v___y_155_ = v___x_176_;
goto v___jp_154_;
}
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_declName_169_);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
v___x_179_ = lean_nat_sub(v___x_178_, v___x_177_);
lean_dec(v___x_178_);
v___x_180_ = lean_nat_sub(v___x_179_, v___x_177_);
lean_dec(v___x_179_);
v___x_181_ = l_Lean_Expr_getRevArg_x21(v_e_153_, v___x_180_);
lean_dec_ref(v_e_153_);
v_e_153_ = v___x_181_;
goto _start;
}
}
v___jp_183_:
{
if (v___y_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5));
v___x_186_ = lean_name_eq(v_declName_169_, v___x_185_);
if (v___x_186_ == 0)
{
v___y_171_ = v___x_186_;
goto v___jp_170_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_187_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
v___x_188_ = lean_unsigned_to_nat(3u);
v___x_189_ = lean_nat_dec_eq(v___x_187_, v___x_188_);
lean_dec(v___x_187_);
v___y_171_ = v___x_189_;
goto v___jp_170_;
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec(v_declName_169_);
v___x_190_ = l_Lean_Expr_appArg_x21(v_e_153_);
lean_dec_ref(v_e_153_);
v___x_191_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v___x_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
return v___x_191_;
}
else
{
lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_201_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_201_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_val_192_, v___x_196_);
lean_dec(v_val_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_197_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_207_; 
lean_dec_ref(v_f_158_);
lean_dec_ref(v_e_153_);
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
v___jp_154_:
{
if (v___y_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0));
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(lean_object* v_e_208_){
_start:
{
uint8_t v___x_209_; 
lean_inc_ref(v_e_208_);
v___x_209_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v_e_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec_ref(v_e_208_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v_e_208_);
if (lean_obj_tag(v___x_211_) == 1)
{
lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_val_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v_val_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v___x_221_; 
lean_dec(v___x_211_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(lean_object* v_e_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_230_; 
lean_inc(v_a_228_);
lean_inc_ref(v_a_227_);
lean_inc(v_a_226_);
lean_inc_ref(v_a_225_);
v___x_230_ = lean_whnf(v_e_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_241_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_241_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_235_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0));
v___x_236_ = l_Lean_Expr_isConstOf(v_a_231_, v___x_235_);
lean_dec(v_a_231_);
v___x_237_ = lean_box(v___x_236_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_237_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_230_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_230_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___boxed(lean_object* v_e_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v_e_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(lean_object* v_fName_270_, lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
uint8_t v___y_278_; uint8_t v___y_308_; uint8_t v___y_333_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6));
v___x_344_ = lean_name_eq(v_fName_270_, v___x_343_);
if (v___x_344_ == 0)
{
v___y_333_ = v___x_344_;
goto v___jp_332_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = l_Lean_Expr_getAppNumArgs(v_e_271_);
v___x_346_ = lean_unsigned_to_nat(2u);
v___x_347_ = lean_nat_dec_eq(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
v___y_333_ = v___x_347_;
goto v___jp_332_;
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_280_ = lean_name_eq(v_fName_270_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_box(v___x_280_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = l_Lean_Expr_getAppNumArgs(v_e_271_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_dec_eq(v___x_283_, v___x_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = l_Lean_Expr_getAppNumArgs(v_e_271_);
v___x_290_ = lean_nat_sub(v___x_289_, v___x_288_);
lean_dec(v___x_289_);
v___x_291_ = lean_nat_sub(v___x_290_, v___x_288_);
lean_dec(v___x_290_);
v___x_292_ = l_Lean_Expr_getRevArg_x21(v_e_271_, v___x_291_);
v___x_293_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_292_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; uint8_t v___x_295_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
v___x_295_ = lean_unbox(v_a_294_);
lean_dec(v_a_294_);
if (v___x_295_ == 0)
{
return v___x_293_;
}
else
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_305_; 
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_293_, 0);
lean_dec(v_unused_306_);
v___x_297_ = v___x_293_;
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
else
{
lean_dec(v___x_293_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_299_ = l_Lean_Expr_appArg_x21(v_e_271_);
v___x_300_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_299_);
v___x_301_ = lean_box(v___x_300_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_301_);
v___x_303_ = v___x_297_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
return v___x_293_;
}
}
}
v___jp_307_:
{
if (v___y_308_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2));
v___x_310_ = lean_name_eq(v_fName_270_, v___x_309_);
if (v___x_310_ == 0)
{
v___y_278_ = v___x_310_;
goto v___jp_277_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_311_ = l_Lean_Expr_getAppNumArgs(v_e_271_);
v___x_312_ = lean_unsigned_to_nat(6u);
v___x_313_ = lean_nat_dec_eq(v___x_311_, v___x_312_);
lean_dec(v___x_311_);
v___y_278_ = v___x_313_;
goto v___jp_277_;
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_314_ = l_Lean_Expr_getAppNumArgs(v_e_271_);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_sub(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
v___x_317_ = l_Lean_Expr_getRevArg_x21(v_e_271_, v___x_316_);
v___x_318_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_317_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; uint8_t v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
v___x_320_ = lean_unbox(v_a_319_);
lean_dec(v_a_319_);
if (v___x_320_ == 0)
{
return v___x_318_;
}
else
{
lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_330_; 
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v___x_318_, 0);
lean_dec(v_unused_331_);
v___x_322_ = v___x_318_;
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
else
{
lean_dec(v___x_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_324_ = l_Lean_Expr_appArg_x21(v_e_271_);
v___x_325_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_324_);
v___x_326_ = lean_box(v___x_325_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_326_);
v___x_328_ = v___x_322_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
return v___x_318_;
}
}
}
v___jp_332_:
{
if (v___y_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5));
v___x_335_ = lean_name_eq(v_fName_270_, v___x_334_);
if (v___x_335_ == 0)
{
v___y_308_ = v___x_335_;
goto v___jp_307_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = l_Lean_Expr_getAppNumArgs(v_e_271_);
v___x_337_ = lean_unsigned_to_nat(4u);
v___x_338_ = lean_nat_dec_eq(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
v___y_308_ = v___x_338_;
goto v___jp_307_;
}
}
else
{
lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = l_Lean_Expr_appArg_x21(v_e_271_);
v___x_340_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_339_);
v___x_341_ = lean_box(v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object* v_fName_348_, lean_object* v_e_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_348_, v_e_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_e_349_);
lean_dec(v_fName_348_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object* v_fName_356_, lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_356_, v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object* v_fName_364_, lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(v_fName_364_, v_e_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec_ref(v_e_365_);
lean_dec(v_fName_364_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object* v_e_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_whnfCore(v_e_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; uint8_t v___x_380_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc_n(v_a_379_, 2);
lean_dec_ref_known(v___x_378_, 1);
v___x_380_ = 0;
v___x_381_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_379_, v___x_380_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_394_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_394_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_394_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
if (lean_obj_tag(v_a_382_) == 0)
{
lean_object* v___x_386_; 
lean_inc(v_a_379_);
v___x_386_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_379_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_388_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_a_379_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_379_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v_val_390_; 
lean_del_object(v___x_384_);
lean_dec(v_a_379_);
v_val_390_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___x_386_, 1);
v_e_372_ = v_val_390_;
goto _start;
}
}
else
{
lean_object* v_val_392_; 
lean_del_object(v___x_384_);
lean_dec(v_a_379_);
v_val_392_ = lean_ctor_get(v_a_382_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v_a_382_, 1);
v_e_372_ = v_val_392_;
goto _start;
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_a_379_);
v_a_395_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_381_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_381_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object* v_e_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_DiscrTree_reduce(v_e_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(lean_object* v_fn_410_){
_start:
{
switch(lean_obj_tag(v_fn_410_))
{
case 9:
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
case 4:
{
uint8_t v___x_412_; 
v___x_412_ = 0;
return v___x_412_;
}
case 1:
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
case 11:
{
uint8_t v___x_414_; 
v___x_414_ = 0;
return v___x_414_;
}
case 7:
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
default: 
{
uint8_t v___x_416_; 
v___x_416_ = 1;
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object* v_fn_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v_fn_417_);
lean_dec_ref(v_fn_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(lean_object* v_e_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_whnfCore(v_e_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; uint8_t v___x_428_; lean_object* v___x_429_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_n(v_a_427_, 2);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = 0;
v___x_429_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_427_, v___x_428_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_444_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_444_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_444_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_444_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
if (lean_obj_tag(v_a_430_) == 0)
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v_a_427_);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_427_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
else
{
lean_object* v_val_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_val_437_ = lean_ctor_get(v_a_430_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v_a_430_, 1);
v___x_438_ = l_Lean_Expr_getAppFn(v_val_437_);
v___x_439_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v___x_438_);
lean_dec_ref(v___x_438_);
if (v___x_439_ == 0)
{
lean_del_object(v___x_432_);
lean_dec(v_a_427_);
v_e_420_ = v_val_437_;
goto _start;
}
else
{
lean_object* v___x_442_; 
lean_dec(v_val_437_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v_a_427_);
v___x_442_ = v___x_432_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_427_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec(v_a_427_);
v_a_445_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_429_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_429_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object* v_e_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
v___x_468_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
return v___x_466_;
}
else
{
lean_object* v_val_469_; 
lean_dec_ref_known(v___x_466_, 1);
v_val_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_468_, 1);
v_e_460_ = v_val_469_;
goto _start;
}
}
else
{
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object* v_e_478_, uint8_t v_root_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
if (v_root_479_ == 0)
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Meta_DiscrTree_reduce(v_e_478_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
v___x_486_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_478_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT___boxed(lean_object* v_e_487_, lean_object* v_root_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
uint8_t v_root_boxed_494_; lean_object* v_res_495_; 
v_root_boxed_494_ = lean_unbox(v_root_488_);
v_res_495_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_487_, v_root_boxed_494_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(lean_object* v_n_496_, lean_object* v_todo_497_){
_start:
{
lean_object* v_zero_498_; uint8_t v_isZero_499_; 
v_zero_498_ = lean_unsigned_to_nat(0u);
v_isZero_499_ = lean_nat_dec_eq(v_n_496_, v_zero_498_);
if (v_isZero_499_ == 1)
{
lean_dec(v_n_496_);
return v_todo_497_;
}
else
{
lean_object* v_one_500_; lean_object* v_n_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_one_500_ = lean_unsigned_to_nat(1u);
v_n_501_ = lean_nat_sub(v_n_496_, v_one_500_);
lean_dec(v_n_496_);
v___x_502_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
v___x_503_ = lean_array_push(v_todo_497_, v___x_502_);
v_n_496_ = v_n_501_;
v_todo_497_ = v___x_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(uint8_t v_root_505_, lean_object* v_todo_506_, lean_object* v_e_507_, uint8_t v_noIndexAtArgs_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___y_515_; lean_object* v_todo_516_; uint8_t v___x_519_; 
v___x_519_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_507_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_507_, v_root_505_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_650_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_650_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_650_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_650_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_v_526_; lean_object* v___x_532_; lean_object* v_k_534_; lean_object* v_nargs_535_; lean_object* v_todo_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; 
v___x_532_ = l_Lean_Expr_getAppFn(v_a_521_);
switch(lean_obj_tag(v___x_532_))
{
case 9:
{
lean_object* v_a_565_; 
lean_dec(v_a_521_);
v_a_565_ = lean_ctor_get(v___x_532_, 0);
lean_inc_ref(v_a_565_);
lean_dec_ref_known(v___x_532_, 1);
v_v_526_ = v_a_565_;
goto v___jp_525_;
}
case 4:
{
lean_object* v_declName_566_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; 
v_declName_566_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_declName_566_);
if (v_root_505_ == 0)
{
lean_object* v___x_574_; 
lean_inc(v_a_521_);
v___x_574_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_521_);
if (lean_obj_tag(v___x_574_) == 1)
{
lean_object* v_val_575_; 
lean_dec(v_declName_566_);
lean_dec_ref_known(v___x_532_, 2);
lean_dec(v_a_521_);
v_val_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_val_575_);
lean_dec_ref_known(v___x_574_, 1);
v_v_526_ = v_val_575_;
goto v___jp_525_;
}
else
{
lean_object* v___x_576_; 
lean_dec(v___x_574_);
lean_del_object(v___x_523_);
v___x_576_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_declName_566_, v_a_521_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_587_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_587_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
uint8_t v___x_581_; 
v___x_581_ = lean_unbox(v_a_577_);
lean_dec(v_a_577_);
if (v___x_581_ == 0)
{
lean_del_object(v___x_579_);
v___y_568_ = v_a_509_;
v___y_569_ = v_a_510_;
v___y_570_ = v_a_511_;
v___y_571_ = v_a_512_;
goto v___jp_567_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
lean_dec(v_declName_566_);
lean_dec_ref_known(v___x_532_, 2);
lean_dec(v_a_521_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_todo_506_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_583_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_declName_566_);
lean_dec_ref_known(v___x_532_, 2);
lean_dec(v_a_521_);
lean_dec_ref(v_todo_506_);
v_a_588_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_576_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_576_);
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
else
{
lean_del_object(v___x_523_);
v___y_568_ = v_a_509_;
v___y_569_ = v_a_510_;
v___y_570_ = v_a_511_;
v___y_571_ = v_a_512_;
goto v___jp_567_;
}
v___jp_567_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_Lean_Expr_getAppNumArgs(v_a_521_);
lean_inc(v___x_572_);
v___x_573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_573_, 0, v_declName_566_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v_k_534_ = v___x_573_;
v_nargs_535_ = v___x_572_;
v_todo_536_ = v_todo_506_;
v___y_537_ = v___y_568_;
v___y_538_ = v___y_569_;
v___y_539_ = v___y_570_;
v___y_540_ = v___y_571_;
goto v___jp_533_;
}
}
case 11:
{
lean_object* v_typeName_596_; lean_object* v_idx_597_; lean_object* v_struct_598_; lean_object* v___x_599_; lean_object* v___y_601_; lean_object* v_env_605_; uint8_t v___x_606_; 
lean_del_object(v___x_523_);
v_typeName_596_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_typeName_596_);
v_idx_597_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_idx_597_);
v_struct_598_ = lean_ctor_get(v___x_532_, 2);
lean_inc_ref(v_struct_598_);
v___x_599_ = lean_st_ref_get(v_a_512_);
v_env_605_ = lean_ctor_get(v___x_599_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_599_);
v___x_606_ = l_Lean_isClass(v_env_605_, v_typeName_596_);
if (v___x_606_ == 0)
{
v___y_601_ = v_struct_598_;
goto v___jp_600_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_598_);
v___y_601_ = v___x_607_;
goto v___jp_600_;
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = l_Lean_Expr_getAppNumArgs(v_a_521_);
lean_inc(v___x_602_);
v___x_603_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_603_, 0, v_typeName_596_);
lean_ctor_set(v___x_603_, 1, v_idx_597_);
lean_ctor_set(v___x_603_, 2, v___x_602_);
v___x_604_ = lean_array_push(v_todo_506_, v___y_601_);
v_k_534_ = v___x_603_;
v_nargs_535_ = v___x_602_;
v_todo_536_ = v___x_604_;
v___y_537_ = v_a_509_;
v___y_538_ = v_a_510_;
v___y_539_ = v_a_511_;
v___y_540_ = v_a_512_;
goto v___jp_533_;
}
}
case 1:
{
lean_object* v_fvarId_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_del_object(v___x_523_);
v_fvarId_608_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_fvarId_608_);
v___x_609_ = l_Lean_Expr_getAppNumArgs(v_a_521_);
lean_inc(v___x_609_);
v___x_610_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_610_, 0, v_fvarId_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v_k_534_ = v___x_610_;
v_nargs_535_ = v___x_609_;
v_todo_536_ = v_todo_506_;
v___y_537_ = v_a_509_;
v___y_538_ = v_a_510_;
v___y_539_ = v_a_511_;
v___y_540_ = v_a_512_;
goto v___jp_533_;
}
case 2:
{
lean_object* v_mvarId_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
lean_del_object(v___x_523_);
lean_dec(v_a_521_);
v_mvarId_611_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_mvarId_611_);
lean_dec_ref_known(v___x_532_, 1);
v___x_612_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId));
v___x_613_ = l_Lean_instBEqMVarId_beq(v_mvarId_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_611_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_630_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_630_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_630_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_630_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; 
v___x_619_ = lean_unbox(v_a_615_);
lean_dec(v_a_615_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v_todo_506_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_621_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_625_ = lean_box(1);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_todo_506_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_626_);
v___x_628_ = v___x_617_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v_todo_506_);
v_a_631_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_614_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_614_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_mvarId_611_);
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_todo_506_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
case 7:
{
lean_object* v_binderType_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_del_object(v___x_523_);
lean_dec(v_a_521_);
v_binderType_642_ = lean_ctor_get(v___x_532_, 1);
lean_inc_ref(v_binderType_642_);
lean_dec_ref_known(v___x_532_, 3);
v___x_643_ = lean_box(5);
v___x_644_ = lean_array_push(v_todo_506_, v_binderType_642_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
default: 
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref(v___x_532_);
lean_del_object(v___x_523_);
lean_dec(v_a_521_);
v___x_647_ = lean_box(1);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v_todo_506_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_527_, 0, v_v_526_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_todo_506_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_528_);
v___x_530_ = v___x_523_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
v___jp_533_:
{
lean_object* v___x_541_; 
lean_inc(v_nargs_535_);
v___x_541_ = l_Lean_Meta_getFunInfoNArgs(v___x_532_, v_nargs_535_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
if (v_noIndexAtArgs_508_ == 0)
{
lean_object* v_a_542_; lean_object* v_paramInfo_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v_paramInfo_543_ = lean_ctor_get(v_a_542_, 0);
lean_inc_ref(v_paramInfo_543_);
lean_dec(v_a_542_);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_sub(v_nargs_535_, v___x_544_);
lean_dec(v_nargs_535_);
v___x_546_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_paramInfo_543_, v___x_545_, v_a_521_, v_todo_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec_ref(v_paramInfo_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___y_515_ = v_k_534_;
v_todo_516_ = v_a_547_;
goto v___jp_514_;
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_k_534_);
v_a_548_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_546_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v___x_556_; 
lean_dec_ref_known(v___x_541_, 1);
lean_dec(v_a_521_);
v___x_556_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(v_nargs_535_, v_todo_536_);
v___y_515_ = v_k_534_;
v_todo_516_ = v___x_556_;
goto v___jp_514_;
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v_todo_536_);
lean_dec(v_nargs_535_);
lean_dec(v_k_534_);
lean_dec(v_a_521_);
v_a_557_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_541_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_541_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_todo_506_);
v_a_651_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_520_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_520_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec_ref(v_e_507_);
v___x_659_ = lean_box(0);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_todo_506_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
v___jp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___y_515_);
lean_ctor_set(v___x_517_, 1, v_todo_516_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* v_root_662_, lean_object* v_todo_663_, lean_object* v_e_664_, lean_object* v_noIndexAtArgs_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
uint8_t v_root_boxed_671_; uint8_t v_noIndexAtArgs_boxed_672_; lean_object* v_res_673_; 
v_root_boxed_671_ = lean_unbox(v_root_662_);
v_noIndexAtArgs_boxed_672_ = lean_unbox(v_noIndexAtArgs_665_);
v_res_673_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_boxed_671_, v_todo_663_, v_e_664_, v_noIndexAtArgs_boxed_672_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t v_root_674_, lean_object* v_todo_675_, lean_object* v_keys_676_, uint8_t v_noIndexAtArgs_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_array_get_size(v_todo_675_);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_nat_dec_eq(v___x_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_e_689_; lean_object* v_todo_690_; lean_object* v___x_691_; 
v___x_686_ = l_Lean_instInhabitedExpr;
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_sub(v___x_683_, v___x_687_);
v_e_689_ = lean_array_get(v___x_686_, v_todo_675_, v___x_688_);
lean_dec(v___x_688_);
v_todo_690_ = lean_array_pop(v_todo_675_);
v___x_691_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_674_, v_todo_690_, v_e_689_, v_noIndexAtArgs_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_695_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v_fst_693_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_fst_693_);
v_snd_694_ = lean_ctor_get(v_a_692_, 1);
lean_inc(v_snd_694_);
lean_dec(v_a_692_);
v___x_695_ = lean_array_push(v_keys_676_, v_fst_693_);
v_root_674_ = v___x_685_;
v_todo_675_ = v_snd_694_;
v_keys_676_ = v___x_695_;
goto _start;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v_keys_676_);
v_a_697_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_691_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_691_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v___x_705_; 
lean_dec_ref(v_todo_675_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v_keys_676_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* v_root_706_, lean_object* v_todo_707_, lean_object* v_keys_708_, lean_object* v_noIndexAtArgs_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
uint8_t v_root_boxed_715_; uint8_t v_noIndexAtArgs_boxed_716_; lean_object* v_res_717_; 
v_root_boxed_715_ = lean_unbox(v_root_706_);
v_noIndexAtArgs_boxed_716_ = lean_unbox(v_noIndexAtArgs_709_);
v_res_717_ = l_Lean_Meta_DiscrTree_mkPathAux(v_root_boxed_715_, v_todo_707_, v_keys_708_, v_noIndexAtArgs_boxed_716_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_717_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_unsigned_to_nat(8u);
return v___x_718_;
}
}
static uint64_t _init_l_Lean_Meta_DiscrTree_mkPath___closed__0(void){
_start:
{
uint8_t v___x_719_; uint64_t v___x_720_; 
v___x_719_ = 2;
v___x_720_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* v_e_721_, uint8_t v_noIndexAtArgs_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_728_; uint8_t v_foApprox_729_; uint8_t v_ctxApprox_730_; uint8_t v_quasiPatternApprox_731_; uint8_t v_constApprox_732_; uint8_t v_isDefEqStuckEx_733_; uint8_t v_unificationHints_734_; uint8_t v_proofIrrelevance_735_; uint8_t v_assignSyntheticOpaque_736_; uint8_t v_offsetCnstrs_737_; uint8_t v_etaStruct_738_; uint8_t v_univApprox_739_; uint8_t v_iota_740_; uint8_t v_beta_741_; uint8_t v_proj_742_; uint8_t v_zeta_743_; uint8_t v_zetaDelta_744_; uint8_t v_zetaUnused_745_; uint8_t v_zetaHave_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_777_; 
v___x_728_ = l_Lean_Meta_Context_config(v_a_723_);
v_foApprox_729_ = lean_ctor_get_uint8(v___x_728_, 0);
v_ctxApprox_730_ = lean_ctor_get_uint8(v___x_728_, 1);
v_quasiPatternApprox_731_ = lean_ctor_get_uint8(v___x_728_, 2);
v_constApprox_732_ = lean_ctor_get_uint8(v___x_728_, 3);
v_isDefEqStuckEx_733_ = lean_ctor_get_uint8(v___x_728_, 4);
v_unificationHints_734_ = lean_ctor_get_uint8(v___x_728_, 5);
v_proofIrrelevance_735_ = lean_ctor_get_uint8(v___x_728_, 6);
v_assignSyntheticOpaque_736_ = lean_ctor_get_uint8(v___x_728_, 7);
v_offsetCnstrs_737_ = lean_ctor_get_uint8(v___x_728_, 8);
v_etaStruct_738_ = lean_ctor_get_uint8(v___x_728_, 10);
v_univApprox_739_ = lean_ctor_get_uint8(v___x_728_, 11);
v_iota_740_ = lean_ctor_get_uint8(v___x_728_, 12);
v_beta_741_ = lean_ctor_get_uint8(v___x_728_, 13);
v_proj_742_ = lean_ctor_get_uint8(v___x_728_, 14);
v_zeta_743_ = lean_ctor_get_uint8(v___x_728_, 15);
v_zetaDelta_744_ = lean_ctor_get_uint8(v___x_728_, 16);
v_zetaUnused_745_ = lean_ctor_get_uint8(v___x_728_, 17);
v_zetaHave_746_ = lean_ctor_get_uint8(v___x_728_, 18);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_777_ == 0)
{
v___x_748_ = v___x_728_;
v_isShared_749_ = v_isSharedCheck_777_;
goto v_resetjp_747_;
}
else
{
lean_dec(v___x_728_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_777_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v_trackZetaDelta_750_; lean_object* v_zetaDeltaSet_751_; lean_object* v_lctx_752_; lean_object* v_localInstances_753_; lean_object* v_defEqCtx_x3f_754_; lean_object* v_synthPendingDepth_755_; lean_object* v_canUnfold_x3f_756_; uint8_t v_univApprox_757_; uint8_t v_inTypeClassResolution_758_; uint8_t v_cacheInferType_759_; uint8_t v___x_760_; lean_object* v_config_762_; 
v_trackZetaDelta_750_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*7);
v_zetaDeltaSet_751_ = lean_ctor_get(v_a_723_, 1);
v_lctx_752_ = lean_ctor_get(v_a_723_, 2);
v_localInstances_753_ = lean_ctor_get(v_a_723_, 3);
v_defEqCtx_x3f_754_ = lean_ctor_get(v_a_723_, 4);
v_synthPendingDepth_755_ = lean_ctor_get(v_a_723_, 5);
v_canUnfold_x3f_756_ = lean_ctor_get(v_a_723_, 6);
v_univApprox_757_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_758_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*7 + 2);
v_cacheInferType_759_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*7 + 3);
v___x_760_ = 2;
if (v_isShared_749_ == 0)
{
v_config_762_ = v___x_748_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 0, v_foApprox_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 1, v_ctxApprox_730_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 2, v_quasiPatternApprox_731_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 3, v_constApprox_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 4, v_isDefEqStuckEx_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 5, v_unificationHints_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 6, v_proofIrrelevance_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 7, v_assignSyntheticOpaque_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 8, v_offsetCnstrs_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 10, v_etaStruct_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 11, v_univApprox_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 12, v_iota_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 13, v_beta_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 14, v_proj_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 15, v_zeta_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 16, v_zetaDelta_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 17, v_zetaUnused_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, 18, v_zetaHave_746_);
v_config_762_ = v_reuseFailAlloc_776_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
uint64_t v___x_763_; uint64_t v___x_764_; uint64_t v___x_765_; lean_object* v___x_766_; lean_object* v_todo_767_; uint8_t v___x_768_; lean_object* v___x_769_; uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v_key_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_ctor_set_uint8(v_config_762_, 9, v___x_760_);
v___x_763_ = l_Lean_Meta_Context_configKey(v_a_723_);
v___x_764_ = 3ULL;
v___x_765_ = lean_uint64_shift_right(v___x_763_, v___x_764_);
v___x_766_ = lean_unsigned_to_nat(8u);
v_todo_767_ = lean_mk_empty_array_with_capacity(v___x_766_);
v___x_768_ = 1;
lean_inc_ref(v_todo_767_);
v___x_769_ = lean_array_push(v_todo_767_, v_e_721_);
v___x_770_ = lean_uint64_shift_left(v___x_765_, v___x_764_);
v___x_771_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_772_ = lean_uint64_lor(v___x_770_, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_773_, 0, v_config_762_);
lean_ctor_set_uint64(v___x_773_, sizeof(void*)*1, v_key_772_);
lean_inc(v_canUnfold_x3f_756_);
lean_inc(v_synthPendingDepth_755_);
lean_inc(v_defEqCtx_x3f_754_);
lean_inc_ref(v_localInstances_753_);
lean_inc_ref(v_lctx_752_);
lean_inc(v_zetaDeltaSet_751_);
v___x_774_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v_zetaDeltaSet_751_);
lean_ctor_set(v___x_774_, 2, v_lctx_752_);
lean_ctor_set(v___x_774_, 3, v_localInstances_753_);
lean_ctor_set(v___x_774_, 4, v_defEqCtx_x3f_754_);
lean_ctor_set(v___x_774_, 5, v_synthPendingDepth_755_);
lean_ctor_set(v___x_774_, 6, v_canUnfold_x3f_756_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*7, v_trackZetaDelta_750_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*7 + 1, v_univApprox_757_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*7 + 2, v_inTypeClassResolution_758_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*7 + 3, v_cacheInferType_759_);
v___x_775_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_768_, v___x_769_, v_todo_767_, v_noIndexAtArgs_722_, v___x_774_, v_a_724_, v_a_725_, v_a_726_);
lean_dec_ref_known(v___x_774_, 7);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object* v_e_778_, lean_object* v_noIndexAtArgs_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_785_; lean_object* v_res_786_; 
v_noIndexAtArgs_boxed_785_ = lean_unbox(v_noIndexAtArgs_779_);
v_res_786_ = l_Lean_Meta_DiscrTree_mkPath(v_e_778_, v_noIndexAtArgs_boxed_785_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg(lean_object* v_inst_787_, lean_object* v_d_788_, lean_object* v_e_789_, lean_object* v_v_790_, uint8_t v_noIndexAtArgs_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_DiscrTree_mkPath(v_e_789_, v_noIndexAtArgs_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_787_, v_d_788_, v_a_798_, v_v_790_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_v_790_);
lean_dec_ref(v_d_788_);
lean_dec_ref(v_inst_787_);
v_a_807_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_797_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg___boxed(lean_object* v_inst_815_, lean_object* v_d_816_, lean_object* v_e_817_, lean_object* v_v_818_, lean_object* v_noIndexAtArgs_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_825_; lean_object* v_res_826_; 
v_noIndexAtArgs_boxed_825_ = lean_unbox(v_noIndexAtArgs_819_);
v_res_826_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_815_, v_d_816_, v_e_817_, v_v_818_, v_noIndexAtArgs_boxed_825_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* v_00_u03b1_827_, lean_object* v_inst_828_, lean_object* v_d_829_, lean_object* v_e_830_, lean_object* v_v_831_, uint8_t v_noIndexAtArgs_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_828_, v_d_829_, v_e_830_, v_v_831_, v_noIndexAtArgs_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___boxed(lean_object* v_00_u03b1_839_, lean_object* v_inst_840_, lean_object* v_d_841_, lean_object* v_e_842_, lean_object* v_v_843_, lean_object* v_noIndexAtArgs_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_850_; lean_object* v_res_851_; 
v_noIndexAtArgs_boxed_850_ = lean_unbox(v_noIndexAtArgs_844_);
v_res_851_ = l_Lean_Meta_DiscrTree_insert(v_00_u03b1_839_, v_inst_840_, v_d_841_, v_e_842_, v_v_843_, v_noIndexAtArgs_boxed_850_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_851_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_867_ = lean_array_get_size(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_874_ = lean_array_get_size(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(lean_object* v_inst_875_, lean_object* v_d_876_, lean_object* v_e_877_, lean_object* v_v_878_, uint8_t v_noIndexAtArgs_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_DiscrTree_mkPath(v_e_877_, v_noIndexAtArgs_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_910_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_910_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_910_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_910_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_903_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_904_ = lean_array_get_size(v_a_886_);
v___x_905_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7);
v___x_906_ = lean_nat_dec_eq(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
goto v___jp_895_;
}
else
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_908_ = l_Array_isEqvAux___redArg(v_a_886_, v___x_903_, v___x_907_, v___x_904_);
if (v___x_908_ == 0)
{
goto v___jp_895_;
}
else
{
lean_object* v___x_909_; 
lean_del_object(v___x_888_);
lean_dec(v_a_886_);
lean_dec(v_v_878_);
lean_dec_ref(v_inst_875_);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v_d_876_);
return v___x_909_;
}
}
v___jp_890_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_875_, v_d_876_, v_a_886_, v_v_878_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
v___jp_895_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_896_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_897_ = lean_array_get_size(v_a_886_);
v___x_898_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4);
v___x_899_ = lean_nat_dec_eq(v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
goto v___jp_890_;
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_901_ = l_Array_isEqvAux___redArg(v_a_886_, v___x_896_, v___x_900_, v___x_897_);
if (v___x_901_ == 0)
{
goto v___jp_890_;
}
else
{
lean_object* v___x_902_; 
lean_del_object(v___x_888_);
lean_dec(v_a_886_);
lean_dec(v_v_878_);
lean_dec_ref(v_inst_875_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v_d_876_);
return v___x_902_;
}
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_v_878_);
lean_dec_ref(v_d_876_);
lean_dec_ref(v_inst_875_);
v_a_911_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_885_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_885_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(lean_object* v_inst_919_, lean_object* v_d_920_, lean_object* v_e_921_, lean_object* v_v_922_, lean_object* v_noIndexAtArgs_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_929_; lean_object* v_res_930_; 
v_noIndexAtArgs_boxed_929_ = lean_unbox(v_noIndexAtArgs_923_);
v_res_930_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_919_, v_d_920_, v_e_921_, v_v_922_, v_noIndexAtArgs_boxed_929_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific(lean_object* v_00_u03b1_931_, lean_object* v_inst_932_, lean_object* v_d_933_, lean_object* v_e_934_, lean_object* v_v_935_, uint8_t v_noIndexAtArgs_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_932_, v_d_933_, v_e_934_, v_v_935_, v_noIndexAtArgs_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(lean_object* v_00_u03b1_943_, lean_object* v_inst_944_, lean_object* v_d_945_, lean_object* v_e_946_, lean_object* v_v_947_, lean_object* v_noIndexAtArgs_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_954_; lean_object* v_res_955_; 
v_noIndexAtArgs_boxed_954_ = lean_unbox(v_noIndexAtArgs_948_);
v_res_955_ = l_Lean_Meta_DiscrTree_insertIfSpecific(v_00_u03b1_943_, v_inst_944_, v_d_945_, v_e_946_, v_v_947_, v_noIndexAtArgs_boxed_954_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(lean_object* v_declName_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v_env_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_959_ = lean_st_ref_get(v___y_957_);
v_env_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_env_960_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_isRecCore(v_env_960_, v_declName_956_);
v___x_962_ = lean_box(v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_964_, v___y_965_);
lean_dec(v___y_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(lean_object* v_declName_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_968_, v___y_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(lean_object* v_declName_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(lean_object* v_a_982_, lean_object* v_b_983_){
_start:
{
lean_object* v_array_985_; lean_object* v_start_986_; lean_object* v_stop_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1004_; 
v_array_985_ = lean_ctor_get(v_a_982_, 0);
v_start_986_ = lean_ctor_get(v_a_982_, 1);
v_stop_987_ = lean_ctor_get(v_a_982_, 2);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_982_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_989_ = v_a_982_;
v_isShared_990_ = v_isSharedCheck_1004_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_stop_987_);
lean_inc(v_start_986_);
lean_inc(v_array_985_);
lean_dec(v_a_982_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1004_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
uint8_t v___x_991_; 
v___x_991_ = lean_nat_dec_lt(v_start_986_, v_stop_987_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
lean_del_object(v___x_989_);
lean_dec(v_stop_987_);
lean_dec(v_start_986_);
lean_dec_ref(v_array_985_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_983_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_993_ = lean_box(0);
v___x_994_ = lean_unsigned_to_nat(1u);
v___x_995_ = lean_nat_add(v_start_986_, v___x_994_);
lean_inc_ref(v_array_985_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___x_995_);
v___x_997_ = v___x_989_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_array_985_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_stop_987_);
v___x_997_ = v_reuseFailAlloc_1003_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_array_fget(v_array_985_, v_start_986_);
lean_dec(v_start_986_);
lean_dec_ref(v_array_985_);
v___x_999_ = l_Lean_Expr_hasExprMVar(v___x_998_);
lean_dec(v___x_998_);
if (v___x_999_ == 0)
{
v_a_982_ = v___x_997_;
v_b_983_ = v___x_993_;
goto _start;
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_dec_ref_known(v___x_1001_, 1);
v_a_982_ = v___x_997_;
v_b_983_ = v___x_993_;
goto _start;
}
else
{
lean_dec_ref(v___x_997_);
return v___x_1001_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1005_, lean_object* v_b_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1005_, v_b_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v_env_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1012_ = lean_st_ref_get(v___y_1010_);
v_env_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc_ref(v_env_1013_);
lean_dec(v___x_1012_);
v___x_1014_ = l_Lean_getReducibilityStatusCore(v_env_1013_, v_declName_1009_);
v___x_1015_ = lean_box(v___x_1014_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1017_, v___y_1018_);
lean_dec(v___y_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(lean_object* v_declName_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1043_; 
v___x_1027_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1021_, v___y_1025_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1043_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1043_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_unbox(v_a_1028_);
lean_dec(v_a_1028_);
if (v___x_1032_ == 0)
{
uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1033_ = 1;
v___x_1034_ = lean_box(v___x_1033_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1036_ = v___x_1030_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = 0;
v___x_1039_ = lean_box(v___x_1038_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1039_);
v___x_1041_ = v___x_1030_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0___boxed(lean_object* v_declName_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1(void){
_start:
{
lean_object* v___x_1053_; lean_object* v_dummy_1054_; 
v___x_1053_ = lean_box(0);
v_dummy_1054_ = l_Lean_Expr_sort___override(v___x_1053_);
return v_dummy_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* v_e_1061_, uint8_t v_isMatch_1062_, uint8_t v_root_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1061_, v_root_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1226_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1226_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1226_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___y_1075_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; 
if (v_root_1063_ == 0)
{
lean_object* v___x_1214_; 
lean_inc(v_a_1070_);
v___x_1214_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_1070_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 2);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_val_1215_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
else
{
lean_dec(v___x_1214_);
v___y_1085_ = v_a_1064_;
v___y_1086_ = v_a_1065_;
v___y_1087_ = v_a_1066_;
v___y_1088_ = v_a_1067_;
goto v___jp_1084_;
}
}
else
{
v___y_1085_ = v_a_1064_;
v___y_1086_ = v_a_1065_;
v___y_1087_ = v_a_1066_;
v___y_1088_ = v_a_1067_;
goto v___jp_1084_;
}
v___jp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1076_ = l_Lean_Expr_getAppNumArgs(v_a_1070_);
lean_inc(v___x_1076_);
v___x_1077_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___y_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_mk_empty_array_with_capacity(v___x_1076_);
lean_dec(v___x_1076_);
v___x_1079_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1070_, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1077_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1080_);
v___x_1082_ = v___x_1072_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
v___jp_1084_:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Expr_getAppFn(v_a_1070_);
switch(lean_obj_tag(v___x_1089_))
{
case 9:
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_a_1090_);
v___x_1092_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
case 4:
{
lean_object* v_declName_1095_; lean_object* v___x_1096_; uint8_t v_isDefEqStuckEx_1097_; 
v_declName_1095_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_declName_1095_);
lean_dec_ref_known(v___x_1089_, 2);
v___x_1096_ = l_Lean_Meta_Context_config(v___y_1085_);
v_isDefEqStuckEx_1097_ = lean_ctor_get_uint8(v___x_1096_, 4);
lean_dec_ref(v___x_1096_);
if (v_isDefEqStuckEx_1097_ == 0)
{
v___y_1075_ = v_declName_1095_;
goto v___jp_1074_;
}
else
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_Expr_hasExprMVar(v_a_1070_);
if (v___x_1098_ == 0)
{
v___y_1075_ = v_declName_1095_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1099_; 
lean_inc(v_declName_1095_);
v___x_1099_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1095_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; uint8_t v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = lean_unbox(v_a_1100_);
lean_dec(v_a_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_st_ref_get(v___y_1088_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1102_);
v___x_1104_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1103_, v_a_1070_);
if (lean_obj_tag(v___x_1104_) == 1)
{
lean_object* v_val_1105_; lean_object* v_numDiscrs_1106_; lean_object* v_nargs_1107_; lean_object* v_dummy_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_val_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v_numDiscrs_1106_ = lean_ctor_get(v_val_1105_, 1);
lean_inc(v_numDiscrs_1106_);
v_nargs_1107_ = l_Lean_Expr_getAppNumArgs(v_a_1070_);
v_dummy_1108_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
lean_inc(v_nargs_1107_);
v___x_1109_ = lean_mk_array(v_nargs_1107_, v_dummy_1108_);
v___x_1110_ = lean_unsigned_to_nat(1u);
v___x_1111_ = lean_nat_sub(v_nargs_1107_, v___x_1110_);
lean_dec(v_nargs_1107_);
lean_inc(v_a_1070_);
v___x_1112_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1070_, v___x_1109_, v___x_1111_);
v___x_1113_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1105_);
lean_dec(v_val_1105_);
v___x_1114_ = lean_nat_add(v___x_1113_, v_numDiscrs_1106_);
lean_dec(v_numDiscrs_1106_);
v___x_1115_ = l_Array_toSubarray___redArg(v___x_1112_, v___x_1113_, v___x_1114_);
v___x_1116_ = lean_box(0);
v___x_1117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_1115_, v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec_ref_known(v___x_1117_, 1);
v___y_1075_ = v_declName_1095_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_declName_1095_);
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v_a_1127_; uint8_t v___x_1128_; 
lean_dec(v___x_1104_);
lean_inc(v_declName_1095_);
v___x_1126_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_1095_, v___y_1088_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = lean_unbox(v_a_1127_);
lean_dec(v_a_1127_);
if (v___x_1128_ == 0)
{
v___y_1075_ = v_declName_1095_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_dec_ref_known(v___x_1129_, 1);
v___y_1075_ = v_declName_1095_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_declName_1095_);
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_dec_ref_known(v___x_1138_, 1);
v___y_1075_ = v_declName_1095_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_declName_1095_);
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_declName_1095_);
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v_a_1147_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1099_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1099_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_del_object(v___x_1072_);
v_fvarId_1155_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_fvarId_1155_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1156_ = l_Lean_Expr_getAppNumArgs(v_a_1070_);
lean_inc(v___x_1156_);
v___x_1157_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_fvarId_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1156_);
lean_dec(v___x_1156_);
v___x_1159_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1070_, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
case 2:
{
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
if (v_isMatch_1062_ == 0)
{
lean_object* v_mvarId_1162_; lean_object* v___x_1163_; uint8_t v_isDefEqStuckEx_1164_; 
v_mvarId_1162_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_mvarId_1162_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1163_ = l_Lean_Meta_Context_config(v___y_1085_);
v_isDefEqStuckEx_1164_ = lean_ctor_get_uint8(v___x_1163_, 4);
lean_dec_ref(v___x_1163_);
if (v_isDefEqStuckEx_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1162_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1179_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1179_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1179_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_unbox(v_a_1166_);
lean_dec(v_a_1166_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1171_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1175_);
v___x_1177_ = v___x_1168_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_a_1180_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1165_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1165_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v_mvarId_1162_);
v___x_1188_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref_known(v___x_1089_, 1);
v___x_1190_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
case 11:
{
lean_object* v_typeName_1192_; lean_object* v_idx_1193_; lean_object* v_struct_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_del_object(v___x_1072_);
v_typeName_1192_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_typeName_1192_);
v_idx_1193_ = lean_ctor_get(v___x_1089_, 1);
lean_inc(v_idx_1193_);
v_struct_1194_ = lean_ctor_get(v___x_1089_, 2);
lean_inc_ref(v_struct_1194_);
lean_dec_ref_known(v___x_1089_, 3);
v___x_1195_ = l_Lean_Expr_getAppNumArgs(v_a_1070_);
lean_inc(v___x_1195_);
v___x_1196_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1196_, 0, v_typeName_1192_);
lean_ctor_set(v___x_1196_, 1, v_idx_1193_);
lean_ctor_set(v___x_1196_, 2, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_mk_empty_array_with_capacity(v___x_1197_);
v___x_1199_ = lean_array_push(v___x_1198_, v_struct_1194_);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___x_1195_);
lean_dec(v___x_1195_);
v___x_1201_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1070_, v___x_1200_);
v___x_1202_ = l_Array_append___redArg(v___x_1199_, v___x_1201_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1196_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
case 7:
{
lean_object* v_binderType_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v_binderType_1205_ = lean_ctor_get(v___x_1089_, 1);
lean_inc_ref(v_binderType_1205_);
lean_dec_ref_known(v___x_1089_, 3);
v___x_1206_ = lean_box(5);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_mk_empty_array_with_capacity(v___x_1207_);
v___x_1209_ = lean_array_push(v___x_1208_, v_binderType_1205_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
default: 
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v___x_1089_);
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
v___x_1212_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1227_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1069_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1069_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* v_e_1235_, lean_object* v_isMatch_1236_, lean_object* v_root_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
uint8_t v_isMatch_boxed_1243_; uint8_t v_root_boxed_1244_; lean_object* v_res_1245_; 
v_isMatch_boxed_1243_ = lean_unbox(v_isMatch_1236_);
v_root_boxed_1244_ = lean_unbox(v_root_1237_);
v_res_1245_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1235_, v_isMatch_boxed_1243_, v_root_boxed_1244_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1246_, v___y_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object* v_inst_1260_, lean_object* v_R_1261_, lean_object* v_a_1262_, lean_object* v_b_1263_, lean_object* v_c_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1262_, v_b_1263_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object* v_inst_1271_, lean_object* v_R_1272_, lean_object* v_a_1273_, lean_object* v_b_1274_, lean_object* v_c_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_1271_, v_R_1272_, v_a_1273_, v_b_1274_, v_c_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* v_e_1282_, uint8_t v_root_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
uint8_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = 1;
v___x_1290_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1282_, v___x_1289_, v_root_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* v_e_1291_, lean_object* v_root_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
uint8_t v_root_boxed_1298_; lean_object* v_res_1299_; 
v_root_boxed_1298_ = lean_unbox(v_root_1292_);
v_res_1299_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1291_, v_root_boxed_1298_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* v_e_1300_, uint8_t v_root_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint8_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = 0;
v___x_1308_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1300_, v___x_1307_, v_root_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* v_e_1309_, lean_object* v_root_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
uint8_t v_root_boxed_1316_; lean_object* v_res_1317_; 
v_root_boxed_1316_ = lean_unbox(v_root_1310_);
v_res_1317_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1309_, v_root_boxed_1316_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1318_, lean_object* v_vals_1319_, lean_object* v_i_1320_, lean_object* v_k_1321_){
_start:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_array_get_size(v_keys_1318_);
v___x_1323_ = lean_nat_dec_lt(v_i_1320_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_i_1320_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
else
{
lean_object* v_k_x27_1325_; uint8_t v___x_1326_; 
v_k_x27_1325_ = lean_array_fget_borrowed(v_keys_1318_, v_i_1320_);
v___x_1326_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1321_, v_k_x27_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_nat_add(v_i_1320_, v___x_1327_);
lean_dec(v_i_1320_);
v_i_1320_ = v___x_1328_;
goto _start;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_array_fget_borrowed(v_vals_1319_, v_i_1320_);
lean_dec(v_i_1320_);
lean_inc(v___x_1330_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1332_, lean_object* v_vals_1333_, lean_object* v_i_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1332_, v_vals_1333_, v_i_1334_, v_k_1335_);
lean_dec(v_k_1335_);
lean_dec_ref(v_vals_1333_);
lean_dec_ref(v_keys_1332_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1337_, size_t v_x_1338_, lean_object* v_x_1339_){
_start:
{
if (lean_obj_tag(v_x_1337_) == 0)
{
lean_object* v_es_1340_; lean_object* v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v_j_1344_; lean_object* v___x_1345_; 
v_es_1340_ = lean_ctor_get(v_x_1337_, 0);
v___x_1341_ = lean_box(2);
v___x_1342_ = ((size_t)31ULL);
v___x_1343_ = lean_usize_land(v_x_1338_, v___x_1342_);
v_j_1344_ = lean_usize_to_nat(v___x_1343_);
v___x_1345_ = lean_array_get_borrowed(v___x_1341_, v_es_1340_, v_j_1344_);
lean_dec(v_j_1344_);
switch(lean_obj_tag(v___x_1345_))
{
case 0:
{
lean_object* v_key_1346_; lean_object* v_val_1347_; uint8_t v___x_1348_; 
v_key_1346_ = lean_ctor_get(v___x_1345_, 0);
v_val_1347_ = lean_ctor_get(v___x_1345_, 1);
v___x_1348_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1339_, v_key_1346_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_box(0);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; 
lean_inc(v_val_1347_);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_val_1347_);
return v___x_1350_;
}
}
case 1:
{
lean_object* v_node_1351_; size_t v___x_1352_; size_t v___x_1353_; 
v_node_1351_ = lean_ctor_get(v___x_1345_, 0);
v___x_1352_ = ((size_t)5ULL);
v___x_1353_ = lean_usize_shift_right(v_x_1338_, v___x_1352_);
v_x_1337_ = v_node_1351_;
v_x_1338_ = v___x_1353_;
goto _start;
}
default: 
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_box(0);
return v___x_1355_;
}
}
}
else
{
lean_object* v_ks_1356_; lean_object* v_vs_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_ks_1356_ = lean_ctor_get(v_x_1337_, 0);
v_vs_1357_ = lean_ctor_get(v_x_1337_, 1);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1356_, v_vs_1357_, v___x_1358_, v_x_1339_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
size_t v_x_165__boxed_1363_; lean_object* v_res_1364_; 
v_x_165__boxed_1363_ = lean_unbox_usize(v_x_1361_);
lean_dec(v_x_1361_);
v_res_1364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1360_, v_x_165__boxed_1363_, v_x_1362_);
lean_dec(v_x_1362_);
lean_dec_ref(v_x_1360_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1365_, lean_object* v_x_1366_){
_start:
{
uint64_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1366_);
v___x_1368_ = lean_uint64_to_usize(v___x_1367_);
v___x_1369_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1365_, v___x_1368_, v_x_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1370_, v_x_1371_);
lean_dec(v_x_1371_);
lean_dec_ref(v_x_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v_result_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_unsigned_to_nat(8u);
v_result_1375_ = lean_mk_empty_array_with_capacity(v___x_1374_);
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1373_, v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
return v_result_1375_;
}
else
{
lean_object* v_val_1378_; lean_object* v_vs_1379_; lean_object* v___x_1380_; 
v_val_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v_vs_1379_ = lean_ctor_get(v_val_1378_, 0);
lean_inc_ref(v_vs_1379_);
lean_dec(v_val_1378_);
v___x_1380_ = l_Array_append___redArg(v_result_1375_, v_vs_1379_);
lean_dec_ref(v_vs_1379_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___boxed(lean_object* v_d_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1381_);
lean_dec_ref(v_d_1381_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1383_, lean_object* v_d_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_d_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(v_00_u03b1_1386_, v_d_1387_);
lean_dec_ref(v_d_1387_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1390_, v_x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1393_, v_x_1394_, v_x_1395_);
lean_dec(v_x_1395_);
lean_dec_ref(v_x_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1397_, lean_object* v_x_1398_, size_t v_x_1399_, lean_object* v_x_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1398_, v_x_1399_, v_x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1402_, lean_object* v_x_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
size_t v_x_247__boxed_1406_; lean_object* v_res_1407_; 
v_x_247__boxed_1406_ = lean_unbox_usize(v_x_1404_);
lean_dec(v_x_1404_);
v_res_1407_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1402_, v_x_1403_, v_x_247__boxed_1406_, v_x_1405_);
lean_dec(v_x_1405_);
lean_dec_ref(v_x_1403_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1408_, lean_object* v_keys_1409_, lean_object* v_vals_1410_, lean_object* v_heq_1411_, lean_object* v_i_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1409_, v_vals_1410_, v_i_1412_, v_k_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1415_, lean_object* v_keys_1416_, lean_object* v_vals_1417_, lean_object* v_heq_1418_, lean_object* v_i_1419_, lean_object* v_k_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1415_, v_keys_1416_, v_vals_1417_, v_heq_1418_, v_i_1419_, v_k_1420_);
lean_dec(v_k_1420_);
lean_dec_ref(v_vals_1417_);
lean_dec_ref(v_keys_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object* v_a_1422_, lean_object* v_b_1423_){
_start:
{
lean_object* v_fst_1424_; lean_object* v_fst_1425_; uint8_t v___x_1426_; 
v_fst_1424_ = lean_ctor_get(v_a_1422_, 0);
v_fst_1425_ = lean_ctor_get(v_b_1423_, 0);
v___x_1426_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1424_, v_fst_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object* v_a_1427_, lean_object* v_b_1428_){
_start:
{
uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_res_1429_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1427_, v_b_1428_);
lean_dec_ref(v_b_1428_);
lean_dec_ref(v_a_1427_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1437_, lean_object* v_k_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_array_get_size(v_cs_1437_);
v___x_1441_ = lean_nat_dec_lt(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec(v_k_1438_);
v___x_1442_ = lean_box(0);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_sub(v___x_1440_, v___x_1443_);
v___x_1445_ = lean_nat_dec_le(v___x_1439_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_dec(v___x_1444_);
lean_dec(v_k_1438_);
v___x_1446_ = lean_box(0);
return v___x_1446_;
}
else
{
lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___f_1447_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1448_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_k_1438_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1451_ = l_Array_binSearchAux___redArg(v___f_1447_, v___x_1450_, v_cs_1437_, v___x_1449_, v___x_1439_, v___x_1444_);
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1452_, v_k_1453_);
lean_dec_ref(v_cs_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1455_, lean_object* v_cs_1456_, lean_object* v_k_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_array_get_size(v_cs_1456_);
v___x_1460_ = lean_nat_dec_lt(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; 
lean_dec(v_k_1457_);
v___x_1461_ = lean_box(0);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_sub(v___x_1459_, v___x_1462_);
v___x_1464_ = lean_nat_dec_le(v___x_1458_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
lean_dec(v___x_1463_);
lean_dec(v_k_1457_);
v___x_1465_ = lean_box(0);
return v___x_1465_;
}
else
{
lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___f_1466_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1467_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_k_1457_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1470_ = l_Array_binSearchAux___redArg(v___f_1466_, v___x_1469_, v_cs_1456_, v___x_1468_, v___x_1458_, v___x_1463_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1471_, lean_object* v_cs_1472_, lean_object* v_k_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1471_, v_cs_1472_, v_k_1473_);
lean_dec_ref(v_cs_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1475_, lean_object* v_k_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_m_1481_; lean_object* v_a_1482_; uint8_t v___x_1483_; 
v___x_1479_ = lean_nat_add(v_x_1477_, v_x_1478_);
v___x_1480_ = lean_unsigned_to_nat(1u);
v_m_1481_ = lean_nat_shiftr(v___x_1479_, v___x_1480_);
lean_dec(v___x_1479_);
v_a_1482_ = lean_array_fget_borrowed(v_as_1475_, v_m_1481_);
v___x_1483_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1482_, v_k_1476_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; 
lean_dec(v_x_1478_);
v___x_1484_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1476_, v_a_1482_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_dec(v_m_1481_);
lean_dec(v_x_1477_);
lean_inc(v_a_1482_);
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_a_1482_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_nat_dec_eq(v_m_1481_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_nat_sub(v_m_1481_, v___x_1480_);
lean_dec(v_m_1481_);
v___x_1489_ = lean_nat_dec_lt(v___x_1488_, v_x_1477_);
if (v___x_1489_ == 0)
{
v_x_1478_ = v___x_1488_;
goto _start;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v___x_1488_);
lean_dec(v_x_1477_);
v___x_1491_ = lean_box(0);
return v___x_1491_;
}
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_m_1481_);
lean_dec(v_x_1477_);
v___x_1492_ = lean_box(0);
return v___x_1492_;
}
}
}
else
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
lean_dec(v_x_1477_);
v___x_1493_ = lean_nat_add(v_m_1481_, v___x_1480_);
lean_dec(v_m_1481_);
v___x_1494_ = lean_nat_dec_le(v___x_1493_, v_x_1478_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v___x_1493_);
lean_dec(v_x_1478_);
v___x_1495_ = lean_box(0);
return v___x_1495_;
}
else
{
v_x_1477_ = v___x_1493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1497_, lean_object* v_k_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1497_, v_k_1498_, v_x_1499_, v_x_1500_);
lean_dec_ref(v_k_1498_);
lean_dec_ref(v_as_1497_);
return v_res_1501_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1506_, lean_object* v_c_1507_, lean_object* v_result_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_vs_1514_; lean_object* v_children_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_vs_1514_ = lean_ctor_get(v_c_1507_, 0);
lean_inc_ref(v_vs_1514_);
v_children_1515_ = lean_ctor_get(v_c_1507_, 1);
lean_inc_ref(v_children_1515_);
lean_dec_ref(v_c_1507_);
v___x_1516_ = lean_array_get_size(v_todo_1506_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_nat_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
lean_dec_ref(v_vs_1514_);
v___x_1519_ = lean_array_get_size(v_children_1515_);
v___x_1520_ = lean_nat_dec_eq(v___x_1519_, v___x_1517_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_e_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1521_ = l_Lean_instInhabitedExpr;
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_sub(v___x_1516_, v___x_1522_);
v_e_1524_ = lean_array_get_borrowed(v___x_1521_, v_todo_1506_, v___x_1523_);
lean_dec(v___x_1523_);
v___x_1525_ = 1;
lean_inc(v_e_1524_);
v___x_1526_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1524_, v___x_1525_, v___x_1520_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1564_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1564_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1564_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v_fst_1531_; lean_object* v_snd_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_first_1535_; lean_object* v_fst_1536_; lean_object* v_snd_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1563_; 
v_fst_1531_ = lean_ctor_get(v_a_1527_, 0);
lean_inc(v_fst_1531_);
v_snd_1532_ = lean_ctor_get(v_a_1527_, 1);
lean_inc(v_snd_1532_);
lean_dec(v_a_1527_);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v_first_1535_ = lean_array_get(v___x_1534_, v_children_1515_, v___x_1517_);
v_fst_1536_ = lean_ctor_get(v_first_1535_, 0);
v_snd_1537_ = lean_ctor_get(v_first_1535_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_first_1535_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1539_ = v_first_1535_;
v_isShared_1540_ = v_isSharedCheck_1563_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_snd_1537_);
lean_inc(v_fst_1536_);
lean_dec(v_first_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1563_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_todo_1541_; lean_object* v___y_1543_; lean_object* v_a_1544_; uint8_t v___x_1557_; 
v_todo_1541_ = lean_array_pop(v_todo_1506_);
v___x_1557_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1536_, v___x_1533_);
lean_dec(v_fst_1536_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1559_; 
lean_dec(v_snd_1537_);
lean_inc_ref(v_result_1508_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v_result_1508_);
v___x_1559_ = v___x_1529_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_result_1508_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
v___y_1543_ = v___x_1559_;
v_a_1544_ = v_result_1508_;
goto v___jp_1542_;
}
}
else
{
lean_object* v___x_1561_; 
lean_del_object(v___x_1529_);
lean_inc_ref(v_todo_1541_);
v___x_1561_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1541_, v_snd_1537_, v_result_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
v___y_1543_ = v___x_1561_;
v_a_1544_ = v_a_1562_;
goto v___jp_1542_;
}
else
{
lean_dec_ref(v_todo_1541_);
lean_del_object(v___x_1539_);
lean_dec(v_snd_1532_);
lean_dec(v_fst_1531_);
lean_dec_ref(v_children_1515_);
return v___x_1561_;
}
}
v___jp_1542_:
{
if (lean_obj_tag(v_fst_1531_) == 0)
{
lean_dec_ref(v_a_1544_);
lean_dec_ref(v_todo_1541_);
lean_del_object(v___x_1539_);
lean_dec(v_snd_1532_);
lean_dec_ref(v_children_1515_);
return v___y_1543_;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_nat_dec_lt(v___x_1517_, v___x_1519_);
if (v___x_1545_ == 0)
{
lean_dec_ref(v_a_1544_);
lean_dec_ref(v_todo_1541_);
lean_del_object(v___x_1539_);
lean_dec(v_snd_1532_);
lean_dec(v_fst_1531_);
lean_dec_ref(v_children_1515_);
return v___y_1543_;
}
else
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = lean_nat_sub(v___x_1519_, v___x_1522_);
v___x_1547_ = lean_nat_dec_le(v___x_1517_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_dec(v___x_1546_);
lean_dec_ref(v_a_1544_);
lean_dec_ref(v_todo_1541_);
lean_del_object(v___x_1539_);
lean_dec(v_snd_1532_);
lean_dec(v_fst_1531_);
lean_dec_ref(v_children_1515_);
return v___y_1543_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 1, v___x_1548_);
lean_ctor_set(v___x_1539_, 0, v_fst_1531_);
v___x_1550_ = v___x_1539_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_fst_1531_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1515_, v___x_1550_, v___x_1517_, v___x_1546_);
lean_dec_ref(v___x_1550_);
lean_dec_ref(v_children_1515_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_dec_ref(v_a_1544_);
lean_dec_ref(v_todo_1541_);
lean_dec(v_snd_1532_);
return v___y_1543_;
}
else
{
lean_object* v_val_1552_; lean_object* v_snd_1553_; lean_object* v___x_1554_; 
lean_dec_ref(v___y_1543_);
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v_snd_1553_ = lean_ctor_get(v_val_1552_, 1);
lean_inc(v_snd_1553_);
lean_dec(v_val_1552_);
v___x_1554_ = l_Array_append___redArg(v_todo_1541_, v_snd_1532_);
lean_dec(v_snd_1532_);
v_todo_1506_ = v___x_1554_;
v_c_1507_ = v_snd_1553_;
v_result_1508_ = v_a_1544_;
goto _start;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v_children_1515_);
lean_dec_ref(v_result_1508_);
lean_dec_ref(v_todo_1506_);
v_a_1565_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1526_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1526_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v___x_1573_; 
lean_dec_ref(v_children_1515_);
lean_dec_ref(v_todo_1506_);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_result_1508_);
return v___x_1573_;
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec_ref(v_children_1515_);
lean_dec_ref(v_todo_1506_);
v___x_1574_ = l_Array_append___redArg(v_result_1508_, v_vs_1514_);
lean_dec_ref(v_vs_1514_);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1576_, lean_object* v_c_1577_, lean_object* v_result_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1576_, v_c_1577_, v_result_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1585_, lean_object* v_todo_1586_, lean_object* v_c_1587_, lean_object* v_result_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1586_, v_c_1587_, v_result_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_todo_1596_, lean_object* v_c_1597_, lean_object* v_result_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1595_, v_todo_1596_, v_c_1597_, v_result_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1605_, lean_object* v_as_1606_, lean_object* v_k_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1606_, v_k_1607_, v_x_1608_, v_x_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_as_1613_, lean_object* v_k_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1612_, v_as_1613_, v_k_1614_, v_x_1615_, v_x_1616_, v_x_1617_);
lean_dec_ref(v_k_1614_);
lean_dec_ref(v_as_1613_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1619_, lean_object* v_k_1620_, lean_object* v_args_1621_, lean_object* v_result_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1619_, v_k_1620_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v___x_1629_; 
lean_dec_ref(v_args_1621_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_result_1622_);
return v___x_1629_;
}
else
{
lean_object* v_val_1630_; lean_object* v___x_1631_; 
v_val_1630_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1631_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1621_, v_val_1630_, v_result_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1632_, lean_object* v_k_1633_, lean_object* v_args_1634_, lean_object* v_result_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1632_, v_k_1633_, v_args_1634_, v_result_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_k_1633_);
lean_dec_ref(v_d_1632_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1642_, lean_object* v_d_1643_, lean_object* v_k_1644_, lean_object* v_args_1645_, lean_object* v_result_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1643_, v_k_1644_, v_args_1645_, v_result_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_d_1654_, lean_object* v_k_1655_, lean_object* v_args_1656_, lean_object* v_result_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1653_, v_d_1654_, v_k_1655_, v_args_1656_, v_result_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_k_1655_);
lean_dec_ref(v_d_1654_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1664_, lean_object* v_e_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___x_1671_; uint8_t v_foApprox_1672_; uint8_t v_ctxApprox_1673_; uint8_t v_quasiPatternApprox_1674_; uint8_t v_constApprox_1675_; uint8_t v_isDefEqStuckEx_1676_; uint8_t v_unificationHints_1677_; uint8_t v_proofIrrelevance_1678_; uint8_t v_assignSyntheticOpaque_1679_; uint8_t v_offsetCnstrs_1680_; uint8_t v_etaStruct_1681_; uint8_t v_univApprox_1682_; uint8_t v_iota_1683_; uint8_t v_beta_1684_; uint8_t v_proj_1685_; uint8_t v_zeta_1686_; uint8_t v_zetaDelta_1687_; uint8_t v_zetaUnused_1688_; uint8_t v_zetaHave_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1763_; 
v___x_1671_ = l_Lean_Meta_Context_config(v_a_1666_);
v_foApprox_1672_ = lean_ctor_get_uint8(v___x_1671_, 0);
v_ctxApprox_1673_ = lean_ctor_get_uint8(v___x_1671_, 1);
v_quasiPatternApprox_1674_ = lean_ctor_get_uint8(v___x_1671_, 2);
v_constApprox_1675_ = lean_ctor_get_uint8(v___x_1671_, 3);
v_isDefEqStuckEx_1676_ = lean_ctor_get_uint8(v___x_1671_, 4);
v_unificationHints_1677_ = lean_ctor_get_uint8(v___x_1671_, 5);
v_proofIrrelevance_1678_ = lean_ctor_get_uint8(v___x_1671_, 6);
v_assignSyntheticOpaque_1679_ = lean_ctor_get_uint8(v___x_1671_, 7);
v_offsetCnstrs_1680_ = lean_ctor_get_uint8(v___x_1671_, 8);
v_etaStruct_1681_ = lean_ctor_get_uint8(v___x_1671_, 10);
v_univApprox_1682_ = lean_ctor_get_uint8(v___x_1671_, 11);
v_iota_1683_ = lean_ctor_get_uint8(v___x_1671_, 12);
v_beta_1684_ = lean_ctor_get_uint8(v___x_1671_, 13);
v_proj_1685_ = lean_ctor_get_uint8(v___x_1671_, 14);
v_zeta_1686_ = lean_ctor_get_uint8(v___x_1671_, 15);
v_zetaDelta_1687_ = lean_ctor_get_uint8(v___x_1671_, 16);
v_zetaUnused_1688_ = lean_ctor_get_uint8(v___x_1671_, 17);
v_zetaHave_1689_ = lean_ctor_get_uint8(v___x_1671_, 18);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1691_ = v___x_1671_;
v_isShared_1692_ = v_isSharedCheck_1763_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v___x_1671_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1763_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
uint8_t v_trackZetaDelta_1693_; lean_object* v_zetaDeltaSet_1694_; lean_object* v_lctx_1695_; lean_object* v_localInstances_1696_; lean_object* v_defEqCtx_x3f_1697_; lean_object* v_synthPendingDepth_1698_; lean_object* v_canUnfold_x3f_1699_; uint8_t v_univApprox_1700_; uint8_t v_inTypeClassResolution_1701_; uint8_t v_cacheInferType_1702_; uint8_t v___x_1703_; lean_object* v_config_1705_; 
v_trackZetaDelta_1693_ = lean_ctor_get_uint8(v_a_1666_, sizeof(void*)*7);
v_zetaDeltaSet_1694_ = lean_ctor_get(v_a_1666_, 1);
v_lctx_1695_ = lean_ctor_get(v_a_1666_, 2);
v_localInstances_1696_ = lean_ctor_get(v_a_1666_, 3);
v_defEqCtx_x3f_1697_ = lean_ctor_get(v_a_1666_, 4);
v_synthPendingDepth_1698_ = lean_ctor_get(v_a_1666_, 5);
v_canUnfold_x3f_1699_ = lean_ctor_get(v_a_1666_, 6);
v_univApprox_1700_ = lean_ctor_get_uint8(v_a_1666_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1701_ = lean_ctor_get_uint8(v_a_1666_, sizeof(void*)*7 + 2);
v_cacheInferType_1702_ = lean_ctor_get_uint8(v_a_1666_, sizeof(void*)*7 + 3);
v___x_1703_ = 2;
if (v_isShared_1692_ == 0)
{
v_config_1705_ = v___x_1691_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 0, v_foApprox_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 1, v_ctxApprox_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 2, v_quasiPatternApprox_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 3, v_constApprox_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 4, v_isDefEqStuckEx_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 5, v_unificationHints_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 6, v_proofIrrelevance_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 7, v_assignSyntheticOpaque_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 8, v_offsetCnstrs_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 10, v_etaStruct_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 11, v_univApprox_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 12, v_iota_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 13, v_beta_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 14, v_proj_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 15, v_zeta_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 16, v_zetaDelta_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 17, v_zetaUnused_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, 18, v_zetaHave_1689_);
v_config_1705_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
uint64_t v___x_1706_; uint64_t v___x_1707_; uint64_t v___x_1708_; uint8_t v___x_1709_; uint64_t v___x_1710_; uint64_t v___x_1711_; uint64_t v_key_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_ctor_set_uint8(v_config_1705_, 9, v___x_1703_);
v___x_1706_ = l_Lean_Meta_Context_configKey(v_a_1666_);
v___x_1707_ = 3ULL;
v___x_1708_ = lean_uint64_shift_right(v___x_1706_, v___x_1707_);
v___x_1709_ = 1;
v___x_1710_ = lean_uint64_shift_left(v___x_1708_, v___x_1707_);
v___x_1711_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_1712_ = lean_uint64_lor(v___x_1710_, v___x_1711_);
v___x_1713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1713_, 0, v_config_1705_);
lean_ctor_set_uint64(v___x_1713_, sizeof(void*)*1, v_key_1712_);
lean_inc(v_canUnfold_x3f_1699_);
lean_inc(v_synthPendingDepth_1698_);
lean_inc(v_defEqCtx_x3f_1697_);
lean_inc_ref(v_localInstances_1696_);
lean_inc_ref(v_lctx_1695_);
lean_inc(v_zetaDeltaSet_1694_);
v___x_1714_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v_zetaDeltaSet_1694_);
lean_ctor_set(v___x_1714_, 2, v_lctx_1695_);
lean_ctor_set(v___x_1714_, 3, v_localInstances_1696_);
lean_ctor_set(v___x_1714_, 4, v_defEqCtx_x3f_1697_);
lean_ctor_set(v___x_1714_, 5, v_synthPendingDepth_1698_);
lean_ctor_set(v___x_1714_, 6, v_canUnfold_x3f_1699_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*7, v_trackZetaDelta_1693_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*7 + 1, v_univApprox_1700_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1701_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*7 + 3, v_cacheInferType_1702_);
v___x_1715_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1665_, v___x_1709_, v___x_1709_, v___x_1714_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1753_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1753_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1753_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v_fst_1720_; lean_object* v_snd_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1752_; 
v_fst_1720_ = lean_ctor_get(v_a_1716_, 0);
v_snd_1721_ = lean_ctor_get(v_a_1716_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_a_1716_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1723_ = v_a_1716_;
v_isShared_1724_ = v_isSharedCheck_1752_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_snd_1721_);
lean_inc(v_fst_1720_);
lean_dec(v_a_1716_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1752_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_result_1725_; 
v_result_1725_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1664_);
if (lean_obj_tag(v_fst_1720_) == 0)
{
lean_object* v___x_1727_; 
lean_dec(v_snd_1721_);
lean_dec_ref_known(v___x_1714_, 7);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v_result_1725_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_fst_1720_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_result_1725_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1727_);
v___x_1729_ = v___x_1718_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
else
{
lean_object* v___x_1732_; 
lean_del_object(v___x_1718_);
v___x_1732_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1664_, v_fst_1720_, v_snd_1721_, v_result_1725_, v___x_1714_, v_a_1667_, v_a_1668_, v_a_1669_);
lean_dec_ref_known(v___x_1714_, 7);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1743_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1743_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1743_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v_a_1733_);
v___x_1738_ = v___x_1723_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_fst_1720_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1738_);
v___x_1740_ = v___x_1735_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_del_object(v___x_1723_);
lean_dec(v_fst_1720_);
v_a_1744_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1732_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1732_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref_known(v___x_1714_, 7);
v_a_1754_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1715_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1715_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1764_, lean_object* v_e_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1764_, v_e_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec_ref(v_d_1764_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1772_, lean_object* v_d_1773_, lean_object* v_e_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1773_, v_e_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1781_, lean_object* v_d_1782_, lean_object* v_e_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1781_, v_d_1782_, v_e_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec_ref(v_d_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1790_, lean_object* v_e_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1790_, v_e_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_snd_1802_; lean_object* v___x_1804_; 
v_snd_1802_ = lean_ctor_get(v_a_1798_, 1);
lean_inc(v_snd_1802_);
lean_dec(v_a_1798_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v_snd_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_snd_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
v_a_1807_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1797_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1797_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1815_, lean_object* v_e_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1815_, v_e_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec_ref(v_d_1815_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1823_, lean_object* v_d_1824_, lean_object* v_e_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1824_, v_e_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1832_, lean_object* v_d_1833_, lean_object* v_e_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1832_, v_d_1833_, v_e_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec_ref(v_d_1833_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1841_, lean_object* v_k_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_k_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; 
switch(lean_obj_tag(v_k_1842_))
{
case 4:
{
lean_object* v_a_1870_; lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1882_; 
v_a_1870_ = lean_ctor_get(v_k_1842_, 0);
v_a_1871_ = lean_ctor_get(v_k_1842_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_k_1842_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1873_ = v_k_1842_;
v_isShared_1874_ = v_isSharedCheck_1882_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_inc(v_a_1870_);
lean_dec(v_k_1842_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1882_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v_zero_1875_; uint8_t v_isZero_1876_; 
v_zero_1875_ = lean_unsigned_to_nat(0u);
v_isZero_1876_ = lean_nat_dec_eq(v_a_1871_, v_zero_1875_);
if (v_isZero_1876_ == 0)
{
lean_object* v_one_1877_; lean_object* v_n_1878_; lean_object* v___x_1880_; 
v_one_1877_ = lean_unsigned_to_nat(1u);
v_n_1878_ = lean_nat_sub(v_a_1871_, v_one_1877_);
lean_dec(v_a_1871_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v_n_1878_);
v___x_1880_ = v___x_1873_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1870_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_n_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
v_k_1853_ = v___x_1880_;
v___y_1854_ = v_a_1843_;
v___y_1855_ = v_a_1844_;
v___y_1856_ = v_a_1845_;
v___y_1857_ = v_a_1846_;
goto v___jp_1852_;
}
}
else
{
lean_del_object(v___x_1873_);
lean_dec(v_a_1871_);
lean_dec(v_a_1870_);
goto v___jp_1848_;
}
}
}
case 3:
{
lean_object* v_a_1883_; lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1895_; 
v_a_1883_ = lean_ctor_get(v_k_1842_, 0);
v_a_1884_ = lean_ctor_get(v_k_1842_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_k_1842_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1886_ = v_k_1842_;
v_isShared_1887_ = v_isSharedCheck_1895_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_inc(v_a_1883_);
lean_dec(v_k_1842_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1895_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_zero_1888_; uint8_t v_isZero_1889_; 
v_zero_1888_ = lean_unsigned_to_nat(0u);
v_isZero_1889_ = lean_nat_dec_eq(v_a_1884_, v_zero_1888_);
if (v_isZero_1889_ == 0)
{
lean_object* v_one_1890_; lean_object* v_n_1891_; lean_object* v___x_1893_; 
v_one_1890_ = lean_unsigned_to_nat(1u);
v_n_1891_ = lean_nat_sub(v_a_1884_, v_one_1890_);
lean_dec(v_a_1884_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v_n_1891_);
v___x_1893_ = v___x_1886_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1883_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_n_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
v_k_1853_ = v___x_1893_;
v___y_1854_ = v_a_1843_;
v___y_1855_ = v_a_1844_;
v___y_1856_ = v_a_1845_;
v___y_1857_ = v_a_1846_;
goto v___jp_1852_;
}
}
else
{
lean_del_object(v___x_1886_);
lean_dec(v_a_1884_);
lean_dec(v_a_1883_);
goto v___jp_1848_;
}
}
}
case 6:
{
lean_object* v_a_1896_; lean_object* v_a_1897_; lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1909_; 
v_a_1896_ = lean_ctor_get(v_k_1842_, 0);
v_a_1897_ = lean_ctor_get(v_k_1842_, 1);
v_a_1898_ = lean_ctor_get(v_k_1842_, 2);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_k_1842_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1900_ = v_k_1842_;
v_isShared_1901_ = v_isSharedCheck_1909_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_inc(v_a_1897_);
lean_inc(v_a_1896_);
lean_dec(v_k_1842_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1909_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_zero_1902_; uint8_t v_isZero_1903_; 
v_zero_1902_ = lean_unsigned_to_nat(0u);
v_isZero_1903_ = lean_nat_dec_eq(v_a_1898_, v_zero_1902_);
if (v_isZero_1903_ == 0)
{
lean_object* v_one_1904_; lean_object* v_n_1905_; lean_object* v___x_1907_; 
v_one_1904_ = lean_unsigned_to_nat(1u);
v_n_1905_ = lean_nat_sub(v_a_1898_, v_one_1904_);
lean_dec(v_a_1898_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 2, v_n_1905_);
v___x_1907_ = v___x_1900_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1896_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1897_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_n_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v_k_1853_ = v___x_1907_;
v___y_1854_ = v_a_1843_;
v___y_1855_ = v_a_1844_;
v___y_1856_ = v_a_1845_;
v___y_1857_ = v_a_1846_;
goto v___jp_1852_;
}
}
else
{
lean_del_object(v___x_1900_);
lean_dec(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec(v_a_1896_);
goto v___jp_1848_;
}
}
}
default: 
{
lean_dec(v_k_1842_);
goto v___jp_1848_;
}
}
v___jp_1848_:
{
uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = 0;
v___x_1850_ = lean_box(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
v___jp_1852_:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1841_, v_k_1853_);
if (lean_obj_tag(v___x_1858_) == 0)
{
v_k_1842_ = v_k_1853_;
v_a_1843_ = v___y_1854_;
v_a_1844_ = v___y_1855_;
v_a_1845_ = v___y_1856_;
v_a_1846_ = v___y_1857_;
goto _start;
}
else
{
lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_k_1853_);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v___x_1858_, 0);
lean_dec(v_unused_1869_);
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = 1;
v___x_1864_ = lean_box(v___x_1863_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_1910_, lean_object* v_k_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1910_, v_k_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec_ref(v_d_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_1918_, lean_object* v_d_1919_, lean_object* v_k_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1919_, v_k_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_d_1928_, lean_object* v_k_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_1927_, v_d_1928_, v_k_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec_ref(v_d_1928_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_1936_, size_t v_sz_1937_, size_t v_i_1938_, lean_object* v_bs_1939_){
_start:
{
uint8_t v___x_1940_; 
v___x_1940_ = lean_usize_dec_lt(v_i_1938_, v_sz_1937_);
if (v___x_1940_ == 0)
{
lean_dec(v_numExtra_1936_);
return v_bs_1939_;
}
else
{
lean_object* v_v_1941_; lean_object* v___x_1942_; lean_object* v_bs_x27_1943_; lean_object* v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v_v_1941_ = lean_array_uget(v_bs_1939_, v_i_1938_);
v___x_1942_ = lean_unsigned_to_nat(0u);
v_bs_x27_1943_ = lean_array_uset(v_bs_1939_, v_i_1938_, v___x_1942_);
lean_inc(v_numExtra_1936_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_v_1941_);
lean_ctor_set(v___x_1944_, 1, v_numExtra_1936_);
v___x_1945_ = ((size_t)1ULL);
v___x_1946_ = lean_usize_add(v_i_1938_, v___x_1945_);
v___x_1947_ = lean_array_uset(v_bs_x27_1943_, v_i_1938_, v___x_1944_);
v_i_1938_ = v___x_1946_;
v_bs_1939_ = v___x_1947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_1949_, lean_object* v_sz_1950_, lean_object* v_i_1951_, lean_object* v_bs_1952_){
_start:
{
size_t v_sz_boxed_1953_; size_t v_i_boxed_1954_; lean_object* v_res_1955_; 
v_sz_boxed_1953_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1954_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1949_, v_sz_boxed_1953_, v_i_boxed_1954_, v_bs_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_1956_, lean_object* v_e_1957_, lean_object* v_numExtra_1958_, lean_object* v_result_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; 
lean_inc_ref(v_e_1957_);
v___x_1965_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1956_, v_e_1957_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1983_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_snd_1970_; size_t v_sz_1971_; size_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_snd_1970_ = lean_ctor_get(v_a_1966_, 1);
lean_inc(v_snd_1970_);
lean_dec(v_a_1966_);
v_sz_1971_ = lean_array_size(v_snd_1970_);
v___x_1972_ = ((size_t)0ULL);
lean_inc(v_numExtra_1958_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1958_, v_sz_1971_, v___x_1972_, v_snd_1970_);
v___x_1974_ = l_Array_append___redArg(v_result_1959_, v___x_1973_);
lean_dec_ref(v___x_1973_);
v___x_1975_ = l_Lean_Expr_isApp(v_e_1957_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1977_; 
lean_dec(v_numExtra_1958_);
lean_dec_ref(v_e_1957_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1974_);
v___x_1977_ = v___x_1968_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1974_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_del_object(v___x_1968_);
v___x_1979_ = l_Lean_Expr_appFn_x21(v_e_1957_);
lean_dec_ref(v_e_1957_);
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_nat_add(v_numExtra_1958_, v___x_1980_);
lean_dec(v_numExtra_1958_);
v_e_1957_ = v___x_1979_;
v_numExtra_1958_ = v___x_1981_;
v_result_1959_ = v___x_1974_;
goto _start;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_result_1959_);
lean_dec(v_numExtra_1958_);
lean_dec_ref(v_e_1957_);
v_a_1984_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1965_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1965_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_1992_, lean_object* v_e_1993_, lean_object* v_numExtra_1994_, lean_object* v_result_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_1992_, v_e_1993_, v_numExtra_1994_, v_result_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec_ref(v_d_1992_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2002_, lean_object* v_d_2003_, lean_object* v_e_2004_, lean_object* v_numExtra_2005_, lean_object* v_result_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2003_, v_e_2004_, v_numExtra_2005_, v_result_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2013_, lean_object* v_d_2014_, lean_object* v_e_2015_, lean_object* v_numExtra_2016_, lean_object* v_result_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2013_, v_d_2014_, v_e_2015_, v_numExtra_2016_, v_result_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec_ref(v_d_2014_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2024_, lean_object* v_numExtra_2025_, size_t v_sz_2026_, size_t v_i_2027_, lean_object* v_bs_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2025_, v_sz_2026_, v_i_2027_, v_bs_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_numExtra_2031_, lean_object* v_sz_2032_, lean_object* v_i_2033_, lean_object* v_bs_2034_){
_start:
{
size_t v_sz_boxed_2035_; size_t v_i_boxed_2036_; lean_object* v_res_2037_; 
v_sz_boxed_2035_ = lean_unbox_usize(v_sz_2032_);
lean_dec(v_sz_2032_);
v_i_boxed_2036_ = lean_unbox_usize(v_i_2033_);
lean_dec(v_i_2033_);
v_res_2037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2030_, v_numExtra_2031_, v_sz_boxed_2035_, v_i_boxed_2036_, v_bs_2034_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2038_, size_t v_i_2039_, lean_object* v_bs_2040_){
_start:
{
uint8_t v___x_2041_; 
v___x_2041_ = lean_usize_dec_lt(v_i_2039_, v_sz_2038_);
if (v___x_2041_ == 0)
{
return v_bs_2040_;
}
else
{
lean_object* v_v_2042_; lean_object* v___x_2043_; lean_object* v_bs_x27_2044_; lean_object* v___x_2045_; size_t v___x_2046_; size_t v___x_2047_; lean_object* v___x_2048_; 
v_v_2042_ = lean_array_uget(v_bs_2040_, v_i_2039_);
v___x_2043_ = lean_unsigned_to_nat(0u);
v_bs_x27_2044_ = lean_array_uset(v_bs_2040_, v_i_2039_, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_v_2042_);
lean_ctor_set(v___x_2045_, 1, v___x_2043_);
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2039_, v___x_2046_);
v___x_2048_ = lean_array_uset(v_bs_x27_2044_, v_i_2039_, v___x_2045_);
v_i_2039_ = v___x_2047_;
v_bs_2040_ = v___x_2048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2050_, lean_object* v_i_2051_, lean_object* v_bs_2052_){
_start:
{
size_t v_sz_boxed_2053_; size_t v_i_boxed_2054_; lean_object* v_res_2055_; 
v_sz_boxed_2053_ = lean_unbox_usize(v_sz_2050_);
lean_dec(v_sz_2050_);
v_i_boxed_2054_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_res_2055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2053_, v_i_boxed_2054_, v_bs_2052_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2056_, lean_object* v_e_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v___x_2063_; 
lean_inc_ref(v_e_2057_);
v___x_2063_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2056_, v_e_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2100_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2100_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2100_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_fst_2068_; lean_object* v_snd_2069_; size_t v_sz_2070_; size_t v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; uint8_t v___x_2074_; 
v_fst_2068_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_fst_2068_);
v_snd_2069_ = lean_ctor_get(v_a_2064_, 1);
lean_inc(v_snd_2069_);
lean_dec(v_a_2064_);
v_sz_2070_ = lean_array_size(v_snd_2069_);
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2070_, v___x_2071_, v_snd_2069_);
v___x_2073_ = l_Lean_Expr_isApp(v_e_2057_);
v___x_2074_ = lean_bool_not(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
lean_del_object(v___x_2066_);
v___x_2075_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2056_, v_fst_2068_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2088_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2088_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2088_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
uint8_t v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = lean_unbox(v_a_2076_);
lean_dec(v_a_2076_);
v___x_2081_ = lean_bool_not(v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_del_object(v___x_2078_);
v___x_2082_ = l_Lean_Expr_appFn_x21(v_e_2057_);
lean_dec_ref(v_e_2057_);
v___x_2083_ = lean_unsigned_to_nat(1u);
v___x_2084_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2056_, v___x_2082_, v___x_2083_, v___x_2072_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
return v___x_2084_;
}
else
{
lean_object* v___x_2086_; 
lean_dec_ref(v_e_2057_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2072_);
v___x_2086_ = v___x_2078_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2072_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v_e_2057_);
v_a_2089_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2075_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2075_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_fst_2068_);
lean_dec_ref(v_e_2057_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2072_);
v___x_2098_ = v___x_2066_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2072_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_e_2057_);
v_a_2101_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2063_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2063_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2109_, lean_object* v_e_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2109_, v_e_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec_ref(v_d_2109_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2117_, lean_object* v_d_2118_, lean_object* v_e_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2118_, v_e_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2126_, lean_object* v_d_2127_, lean_object* v_e_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2126_, v_d_2127_, v_e_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec_ref(v_d_2127_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2135_, size_t v_sz_2136_, size_t v_i_2137_, lean_object* v_bs_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2136_, v_i_2137_, v_bs_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2140_, lean_object* v_sz_2141_, lean_object* v_i_2142_, lean_object* v_bs_2143_){
_start:
{
size_t v_sz_boxed_2144_; size_t v_i_boxed_2145_; lean_object* v_res_2146_; 
v_sz_boxed_2144_ = lean_unbox_usize(v_sz_2141_);
lean_dec(v_sz_2141_);
v_i_boxed_2145_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2140_, v_sz_boxed_2144_, v_i_boxed_2145_, v_bs_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
uint8_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = 1;
v___x_2154_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2147_, v___x_2153_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2179_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2179_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2179_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___y_2161_; lean_object* v___x_2166_; 
v___x_2159_ = l_Lean_Expr_getAppNumArgs(v_a_2155_);
v___x_2166_ = l_Lean_Expr_getAppFn(v_a_2155_);
lean_dec(v_a_2155_);
switch(lean_obj_tag(v___x_2166_))
{
case 9:
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc_ref(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_a_2167_);
v___y_2161_ = v___x_2168_;
goto v___jp_2160_;
}
case 1:
{
lean_object* v_fvarId_2169_; lean_object* v___x_2170_; 
v_fvarId_2169_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_fvarId_2169_);
lean_dec_ref_known(v___x_2166_, 1);
lean_inc(v___x_2159_);
v___x_2170_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_fvarId_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2159_);
v___y_2161_ = v___x_2170_;
goto v___jp_2160_;
}
case 2:
{
lean_object* v___x_2171_; 
lean_dec_ref_known(v___x_2166_, 1);
v___x_2171_ = lean_box(1);
v___y_2161_ = v___x_2171_;
goto v___jp_2160_;
}
case 11:
{
lean_object* v_typeName_2172_; lean_object* v_idx_2173_; lean_object* v___x_2174_; 
v_typeName_2172_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_typeName_2172_);
v_idx_2173_ = lean_ctor_get(v___x_2166_, 1);
lean_inc(v_idx_2173_);
lean_dec_ref_known(v___x_2166_, 3);
lean_inc(v___x_2159_);
v___x_2174_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2174_, 0, v_typeName_2172_);
lean_ctor_set(v___x_2174_, 1, v_idx_2173_);
lean_ctor_set(v___x_2174_, 2, v___x_2159_);
v___y_2161_ = v___x_2174_;
goto v___jp_2160_;
}
case 7:
{
lean_object* v___x_2175_; 
lean_dec_ref_known(v___x_2166_, 3);
v___x_2175_ = lean_box(5);
v___y_2161_ = v___x_2175_;
goto v___jp_2160_;
}
case 4:
{
lean_object* v_declName_2176_; lean_object* v___x_2177_; 
v_declName_2176_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_declName_2176_);
lean_dec_ref_known(v___x_2166_, 2);
lean_inc(v___x_2159_);
v___x_2177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_declName_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2159_);
v___y_2161_ = v___x_2177_;
goto v___jp_2160_;
}
default: 
{
lean_object* v___x_2178_; 
lean_dec_ref(v___x_2166_);
v___x_2178_ = lean_box(1);
v___y_2161_ = v___x_2178_;
goto v___jp_2160_;
}
}
v___jp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___y_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2159_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2162_);
v___x_2164_ = v___x_2157_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2154_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2154_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2195_, size_t v_sz_2196_, size_t v_i_2197_, lean_object* v_b_2198_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_usize_dec_lt(v_i_2197_, v_sz_2196_);
if (v___x_2199_ == 0)
{
return v_b_2198_;
}
else
{
lean_object* v_a_2200_; lean_object* v_snd_2201_; lean_object* v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; 
v_a_2200_ = lean_array_uget_borrowed(v_as_2195_, v_i_2197_);
v_snd_2201_ = lean_ctor_get(v_a_2200_, 1);
v___x_2202_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2201_, v_b_2198_);
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = lean_usize_add(v_i_2197_, v___x_2203_);
v_i_2197_ = v___x_2204_;
v_b_2198_ = v___x_2202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2206_, lean_object* v_result_2207_){
_start:
{
lean_object* v_vs_2208_; lean_object* v_children_2209_; lean_object* v_result_2210_; size_t v_sz_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v_vs_2208_ = lean_ctor_get(v_trie_2206_, 0);
v_children_2209_ = lean_ctor_get(v_trie_2206_, 1);
v_result_2210_ = l_Array_append___redArg(v_result_2207_, v_vs_2208_);
v_sz_2211_ = lean_array_size(v_children_2209_);
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2209_, v_sz_2211_, v___x_2212_, v_result_2210_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2214_, lean_object* v_result_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2214_, v_result_2215_);
lean_dec_ref(v_trie_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2217_, lean_object* v_sz_2218_, lean_object* v_i_2219_, lean_object* v_b_2220_){
_start:
{
size_t v_sz_boxed_2221_; size_t v_i_boxed_2222_; lean_object* v_res_2223_; 
v_sz_boxed_2221_ = lean_unbox_usize(v_sz_2218_);
lean_dec(v_sz_2218_);
v_i_boxed_2222_ = lean_unbox_usize(v_i_2219_);
lean_dec(v_i_2219_);
v_res_2223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2217_, v_sz_boxed_2221_, v_i_boxed_2222_, v_b_2220_);
lean_dec_ref(v_as_2217_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2224_, lean_object* v_trie_2225_, lean_object* v_result_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2225_, v_result_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2228_, lean_object* v_trie_2229_, lean_object* v_result_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2228_, v_trie_2229_, v_result_2230_);
lean_dec_ref(v_trie_2229_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2232_, lean_object* v_as_2233_, size_t v_sz_2234_, size_t v_i_2235_, lean_object* v_b_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2233_, v_sz_2234_, v_i_2235_, v_b_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2238_, lean_object* v_as_2239_, lean_object* v_sz_2240_, lean_object* v_i_2241_, lean_object* v_b_2242_){
_start:
{
size_t v_sz_boxed_2243_; size_t v_i_boxed_2244_; lean_object* v_res_2245_; 
v_sz_boxed_2243_ = lean_unbox_usize(v_sz_2240_);
lean_dec(v_sz_2240_);
v_i_boxed_2244_ = lean_unbox_usize(v_i_2241_);
lean_dec(v_i_2241_);
v_res_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2238_, v_as_2239_, v_sz_boxed_2243_, v_i_boxed_2244_, v_b_2242_);
lean_dec_ref(v_as_2239_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2246_, lean_object* v_k_2247_, lean_object* v_result_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2246_, v_k_2247_);
if (lean_obj_tag(v___x_2249_) == 0)
{
return v_result_2248_;
}
else
{
lean_object* v_val_2250_; lean_object* v___x_2251_; 
v_val_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_val_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2250_, v_result_2248_);
lean_dec(v_val_2250_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2252_, lean_object* v_k_2253_, lean_object* v_result_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2252_, v_k_2253_, v_result_2254_);
lean_dec(v_k_2253_);
lean_dec_ref(v_d_2252_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2256_, lean_object* v_d_2257_, lean_object* v_k_2258_, lean_object* v_result_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2257_, v_k_2258_, v_result_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2261_, lean_object* v_d_2262_, lean_object* v_k_2263_, lean_object* v_result_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2261_, v_d_2262_, v_k_2263_, v_result_2264_);
lean_dec(v_k_2263_);
lean_dec_ref(v_d_2262_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2266_, lean_object* v_e_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___x_2273_; uint8_t v_foApprox_2274_; uint8_t v_ctxApprox_2275_; uint8_t v_quasiPatternApprox_2276_; uint8_t v_constApprox_2277_; uint8_t v_isDefEqStuckEx_2278_; uint8_t v_unificationHints_2279_; uint8_t v_proofIrrelevance_2280_; uint8_t v_assignSyntheticOpaque_2281_; uint8_t v_offsetCnstrs_2282_; uint8_t v_etaStruct_2283_; uint8_t v_univApprox_2284_; uint8_t v_iota_2285_; uint8_t v_beta_2286_; uint8_t v_proj_2287_; uint8_t v_zeta_2288_; uint8_t v_zetaDelta_2289_; uint8_t v_zetaUnused_2290_; uint8_t v_zetaHave_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2345_; 
v___x_2273_ = l_Lean_Meta_Context_config(v_a_2268_);
v_foApprox_2274_ = lean_ctor_get_uint8(v___x_2273_, 0);
v_ctxApprox_2275_ = lean_ctor_get_uint8(v___x_2273_, 1);
v_quasiPatternApprox_2276_ = lean_ctor_get_uint8(v___x_2273_, 2);
v_constApprox_2277_ = lean_ctor_get_uint8(v___x_2273_, 3);
v_isDefEqStuckEx_2278_ = lean_ctor_get_uint8(v___x_2273_, 4);
v_unificationHints_2279_ = lean_ctor_get_uint8(v___x_2273_, 5);
v_proofIrrelevance_2280_ = lean_ctor_get_uint8(v___x_2273_, 6);
v_assignSyntheticOpaque_2281_ = lean_ctor_get_uint8(v___x_2273_, 7);
v_offsetCnstrs_2282_ = lean_ctor_get_uint8(v___x_2273_, 8);
v_etaStruct_2283_ = lean_ctor_get_uint8(v___x_2273_, 10);
v_univApprox_2284_ = lean_ctor_get_uint8(v___x_2273_, 11);
v_iota_2285_ = lean_ctor_get_uint8(v___x_2273_, 12);
v_beta_2286_ = lean_ctor_get_uint8(v___x_2273_, 13);
v_proj_2287_ = lean_ctor_get_uint8(v___x_2273_, 14);
v_zeta_2288_ = lean_ctor_get_uint8(v___x_2273_, 15);
v_zetaDelta_2289_ = lean_ctor_get_uint8(v___x_2273_, 16);
v_zetaUnused_2290_ = lean_ctor_get_uint8(v___x_2273_, 17);
v_zetaHave_2291_ = lean_ctor_get_uint8(v___x_2273_, 18);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2293_ = v___x_2273_;
v_isShared_2294_ = v_isSharedCheck_2345_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v___x_2273_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2345_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
uint8_t v_trackZetaDelta_2295_; lean_object* v_zetaDeltaSet_2296_; lean_object* v_lctx_2297_; lean_object* v_localInstances_2298_; lean_object* v_defEqCtx_x3f_2299_; lean_object* v_synthPendingDepth_2300_; lean_object* v_canUnfold_x3f_2301_; uint8_t v_univApprox_2302_; uint8_t v_inTypeClassResolution_2303_; uint8_t v_cacheInferType_2304_; uint8_t v___x_2305_; lean_object* v_config_2307_; 
v_trackZetaDelta_2295_ = lean_ctor_get_uint8(v_a_2268_, sizeof(void*)*7);
v_zetaDeltaSet_2296_ = lean_ctor_get(v_a_2268_, 1);
v_lctx_2297_ = lean_ctor_get(v_a_2268_, 2);
v_localInstances_2298_ = lean_ctor_get(v_a_2268_, 3);
v_defEqCtx_x3f_2299_ = lean_ctor_get(v_a_2268_, 4);
v_synthPendingDepth_2300_ = lean_ctor_get(v_a_2268_, 5);
v_canUnfold_x3f_2301_ = lean_ctor_get(v_a_2268_, 6);
v_univApprox_2302_ = lean_ctor_get_uint8(v_a_2268_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2303_ = lean_ctor_get_uint8(v_a_2268_, sizeof(void*)*7 + 2);
v_cacheInferType_2304_ = lean_ctor_get_uint8(v_a_2268_, sizeof(void*)*7 + 3);
v___x_2305_ = 2;
if (v_isShared_2294_ == 0)
{
v_config_2307_ = v___x_2293_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 0, v_foApprox_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 1, v_ctxApprox_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 2, v_quasiPatternApprox_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 3, v_constApprox_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 4, v_isDefEqStuckEx_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 5, v_unificationHints_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 6, v_proofIrrelevance_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 7, v_assignSyntheticOpaque_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 8, v_offsetCnstrs_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 10, v_etaStruct_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 11, v_univApprox_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 12, v_iota_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 13, v_beta_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 14, v_proj_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 15, v_zeta_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 16, v_zetaDelta_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 17, v_zetaUnused_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2344_, 18, v_zetaHave_2291_);
v_config_2307_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
uint64_t v___x_2308_; uint64_t v___x_2309_; uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v___x_2312_; uint64_t v_key_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_ctor_set_uint8(v_config_2307_, 9, v___x_2305_);
v___x_2308_ = l_Lean_Meta_Context_configKey(v_a_2268_);
v___x_2309_ = 3ULL;
v___x_2310_ = lean_uint64_shift_right(v___x_2308_, v___x_2309_);
v___x_2311_ = lean_uint64_shift_left(v___x_2310_, v___x_2309_);
v___x_2312_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2313_ = lean_uint64_lor(v___x_2311_, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2314_, 0, v_config_2307_);
lean_ctor_set_uint64(v___x_2314_, sizeof(void*)*1, v_key_2313_);
lean_inc(v_canUnfold_x3f_2301_);
lean_inc(v_synthPendingDepth_2300_);
lean_inc(v_defEqCtx_x3f_2299_);
lean_inc_ref(v_localInstances_2298_);
lean_inc_ref(v_lctx_2297_);
lean_inc(v_zetaDeltaSet_2296_);
v___x_2315_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v_zetaDeltaSet_2296_);
lean_ctor_set(v___x_2315_, 2, v_lctx_2297_);
lean_ctor_set(v___x_2315_, 3, v_localInstances_2298_);
lean_ctor_set(v___x_2315_, 4, v_defEqCtx_x3f_2299_);
lean_ctor_set(v___x_2315_, 5, v_synthPendingDepth_2300_);
lean_ctor_set(v___x_2315_, 6, v_canUnfold_x3f_2301_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*7, v_trackZetaDelta_2295_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*7 + 1, v_univApprox_2302_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2303_);
lean_ctor_set_uint8(v___x_2315_, sizeof(void*)*7 + 3, v_cacheInferType_2304_);
v___x_2316_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2267_, v___x_2315_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec_ref_known(v___x_2315_, 7);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2335_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2335_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2335_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_fst_2321_; lean_object* v_snd_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2334_; 
v_fst_2321_ = lean_ctor_get(v_a_2317_, 0);
v_snd_2322_ = lean_ctor_get(v_a_2317_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2317_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2324_ = v_a_2317_;
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snd_2322_);
lean_inc(v_fst_2321_);
lean_dec(v_a_2317_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_result_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v_result_2326_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2266_);
v___x_2327_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2266_, v_fst_2321_, v_result_2326_);
lean_dec(v_fst_2321_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2327_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_snd_2322_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2329_);
v___x_2331_ = v___x_2319_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
v_a_2336_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2316_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2316_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2346_, lean_object* v_e_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2346_, v_e_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec_ref(v_d_2346_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2354_, lean_object* v_d_2355_, lean_object* v_e_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2355_, v_e_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2363_, lean_object* v_d_2364_, lean_object* v_e_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2363_, v_d_2364_, v_e_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec_ref(v_d_2364_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2372_, lean_object* v_todo_2373_, lean_object* v_as_2374_, size_t v_i_2375_, size_t v_stop_2376_, lean_object* v_b_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_usize_dec_eq(v_i_2375_, v_stop_2376_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; lean_object* v_fst_2385_; lean_object* v_snd_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2384_ = lean_array_uget_borrowed(v_as_2374_, v_i_2375_);
v_fst_2385_ = lean_ctor_get(v___x_2384_, 0);
v_snd_2386_ = lean_ctor_get(v___x_2384_, 1);
v___x_2387_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2385_);
v___x_2388_ = lean_nat_add(v_n_2372_, v___x_2387_);
lean_dec(v___x_2387_);
lean_inc(v_snd_2386_);
lean_inc_ref(v_todo_2373_);
v___x_2389_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2388_, v_todo_2373_, v_snd_2386_, v_b_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; size_t v___x_2391_; size_t v___x_2392_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = ((size_t)1ULL);
v___x_2392_ = lean_usize_add(v_i_2375_, v___x_2391_);
v_i_2375_ = v___x_2392_;
v_b_2377_ = v_a_2390_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2373_);
return v___x_2389_;
}
}
else
{
lean_object* v___x_2394_; 
lean_dec_ref(v_todo_2373_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_b_2377_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2395_, lean_object* v_todo_2396_, lean_object* v_c_2397_, lean_object* v_result_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_zero_2404_; uint8_t v_isZero_2405_; 
v_zero_2404_ = lean_unsigned_to_nat(0u);
v_isZero_2405_ = lean_nat_dec_eq(v_skip_2395_, v_zero_2404_);
if (v_isZero_2405_ == 1)
{
lean_object* v_vs_2406_; lean_object* v_children_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
lean_dec(v_skip_2395_);
v_vs_2406_ = lean_ctor_get(v_c_2397_, 0);
lean_inc_ref(v_vs_2406_);
v_children_2407_ = lean_ctor_get(v_c_2397_, 1);
lean_inc_ref(v_children_2407_);
lean_dec_ref(v_c_2397_);
v___x_2408_ = lean_array_get_size(v_todo_2396_);
v___x_2409_ = lean_nat_dec_eq(v___x_2408_, v_zero_2404_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
lean_dec_ref(v_vs_2406_);
v___x_2410_ = lean_array_get_size(v_children_2407_);
v___x_2411_ = lean_nat_dec_eq(v___x_2410_, v_zero_2404_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v_e_2415_; lean_object* v___x_2416_; 
v___x_2412_ = l_Lean_instInhabitedExpr;
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_sub(v___x_2408_, v___x_2413_);
v_e_2415_ = lean_array_get_borrowed(v___x_2412_, v_todo_2396_, v___x_2414_);
lean_dec(v___x_2414_);
lean_inc(v_e_2415_);
v___x_2416_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2415_, v___x_2411_, v___x_2411_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2468_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2468_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2468_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_fst_2421_; lean_object* v_snd_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2467_; 
v_fst_2421_ = lean_ctor_get(v_a_2417_, 0);
v_snd_2422_ = lean_ctor_get(v_a_2417_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_a_2417_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2424_ = v_a_2417_;
v_isShared_2425_ = v_isSharedCheck_2467_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_snd_2422_);
lean_inc(v_fst_2421_);
lean_dec(v_a_2417_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2467_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_todo_2426_; lean_object* v___y_2428_; lean_object* v_a_2429_; 
v_todo_2426_ = lean_array_pop(v_todo_2396_);
if (lean_obj_tag(v_fst_2421_) == 0)
{
uint8_t v___x_2442_; 
lean_del_object(v___x_2424_);
lean_dec(v_snd_2422_);
v___x_2442_ = lean_nat_dec_lt(v_zero_2404_, v___x_2410_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2444_; 
lean_dec_ref(v_todo_2426_);
lean_dec_ref(v_children_2407_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_result_2398_);
v___x_2444_ = v___x_2419_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_result_2398_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
else
{
uint8_t v___x_2446_; 
v___x_2446_ = lean_nat_dec_le(v___x_2410_, v___x_2410_);
if (v___x_2446_ == 0)
{
if (v___x_2442_ == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref(v_todo_2426_);
lean_dec_ref(v_children_2407_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_result_2398_);
v___x_2448_ = v___x_2419_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_result_2398_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
else
{
size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
lean_del_object(v___x_2419_);
v___x_2450_ = ((size_t)0ULL);
v___x_2451_ = lean_usize_of_nat(v___x_2410_);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2426_, v_children_2407_, v___x_2450_, v___x_2451_, v_result_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec_ref(v_children_2407_);
return v___x_2452_;
}
}
else
{
size_t v___x_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
lean_del_object(v___x_2419_);
v___x_2453_ = ((size_t)0ULL);
v___x_2454_ = lean_usize_of_nat(v___x_2410_);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2426_, v_children_2407_, v___x_2453_, v___x_2454_, v_result_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec_ref(v_children_2407_);
return v___x_2455_;
}
}
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_fst_2459_; lean_object* v_snd_2460_; uint8_t v___x_2461_; 
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_2458_ = lean_array_get_borrowed(v___x_2457_, v_children_2407_, v_zero_2404_);
v_fst_2459_ = lean_ctor_get(v___x_2458_, 0);
v_snd_2460_ = lean_ctor_get(v___x_2458_, 1);
v___x_2461_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2459_, v___x_2456_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2463_; 
lean_inc_ref(v_result_2398_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_result_2398_);
v___x_2463_ = v___x_2419_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_result_2398_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
v___y_2428_ = v___x_2463_;
v_a_2429_ = v_result_2398_;
goto v___jp_2427_;
}
}
else
{
lean_object* v___x_2465_; 
lean_del_object(v___x_2419_);
lean_inc(v_snd_2460_);
lean_inc_ref(v_todo_2426_);
v___x_2465_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2404_, v_todo_2426_, v_snd_2460_, v_result_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
v___y_2428_ = v___x_2465_;
v_a_2429_ = v_a_2466_;
goto v___jp_2427_;
}
else
{
lean_dec_ref(v_todo_2426_);
lean_del_object(v___x_2424_);
lean_dec(v_snd_2422_);
lean_dec(v_fst_2421_);
lean_dec_ref(v_children_2407_);
return v___x_2465_;
}
}
}
v___jp_2427_:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_nat_dec_lt(v_zero_2404_, v___x_2410_);
if (v___x_2430_ == 0)
{
lean_dec_ref(v_a_2429_);
lean_dec_ref(v_todo_2426_);
lean_del_object(v___x_2424_);
lean_dec(v_snd_2422_);
lean_dec(v_fst_2421_);
lean_dec_ref(v_children_2407_);
return v___y_2428_;
}
else
{
lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = lean_nat_sub(v___x_2410_, v___x_2413_);
v___x_2432_ = lean_nat_dec_le(v_zero_2404_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_dec(v___x_2431_);
lean_dec_ref(v_a_2429_);
lean_dec_ref(v_todo_2426_);
lean_del_object(v___x_2424_);
lean_dec(v_snd_2422_);
lean_dec(v_fst_2421_);
lean_dec_ref(v_children_2407_);
return v___y_2428_;
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2433_);
v___x_2435_ = v___x_2424_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_fst_2421_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_2407_, v___x_2435_, v_zero_2404_, v___x_2431_);
lean_dec_ref(v___x_2435_);
lean_dec_ref(v_children_2407_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_dec_ref(v_a_2429_);
lean_dec_ref(v_todo_2426_);
lean_dec(v_snd_2422_);
return v___y_2428_;
}
else
{
lean_object* v_val_2437_; lean_object* v_snd_2438_; lean_object* v___x_2439_; 
lean_dec_ref(v___y_2428_);
v_val_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_val_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v_snd_2438_ = lean_ctor_get(v_val_2437_, 1);
lean_inc(v_snd_2438_);
lean_dec(v_val_2437_);
v___x_2439_ = l_Array_append___redArg(v_todo_2426_, v_snd_2422_);
lean_dec(v_snd_2422_);
v_skip_2395_ = v_zero_2404_;
v_todo_2396_ = v___x_2439_;
v_c_2397_ = v_snd_2438_;
v_result_2398_ = v_a_2429_;
goto _start;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_children_2407_);
lean_dec_ref(v_result_2398_);
lean_dec_ref(v_todo_2396_);
v_a_2469_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2416_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2416_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v___x_2477_; 
lean_dec_ref(v_children_2407_);
lean_dec_ref(v_todo_2396_);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_result_2398_);
return v___x_2477_;
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec_ref(v_children_2407_);
lean_dec_ref(v_todo_2396_);
v___x_2478_ = l_Array_append___redArg(v_result_2398_, v_vs_2406_);
lean_dec_ref(v_vs_2406_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
}
else
{
lean_object* v_children_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_children_2480_ = lean_ctor_get(v_c_2397_, 1);
lean_inc_ref(v_children_2480_);
lean_dec_ref(v_c_2397_);
v___x_2481_ = lean_array_get_size(v_children_2480_);
v___x_2482_ = lean_nat_dec_eq(v___x_2481_, v_zero_2404_);
if (v___x_2482_ == 0)
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_nat_dec_lt(v_zero_2404_, v___x_2481_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
lean_dec_ref(v_children_2480_);
lean_dec_ref(v_todo_2396_);
lean_dec(v_skip_2395_);
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_result_2398_);
return v___x_2484_;
}
else
{
lean_object* v_one_2485_; lean_object* v_n_2486_; uint8_t v___x_2487_; 
v_one_2485_ = lean_unsigned_to_nat(1u);
v_n_2486_ = lean_nat_sub(v_skip_2395_, v_one_2485_);
lean_dec(v_skip_2395_);
v___x_2487_ = lean_nat_dec_le(v___x_2481_, v___x_2481_);
if (v___x_2487_ == 0)
{
if (v___x_2483_ == 0)
{
lean_object* v___x_2488_; 
lean_dec(v_n_2486_);
lean_dec_ref(v_children_2480_);
lean_dec_ref(v_todo_2396_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_result_2398_);
return v___x_2488_;
}
else
{
size_t v___x_2489_; size_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = ((size_t)0ULL);
v___x_2490_ = lean_usize_of_nat(v___x_2481_);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2486_, v_todo_2396_, v_children_2480_, v___x_2489_, v___x_2490_, v_result_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec_ref(v_children_2480_);
lean_dec(v_n_2486_);
return v___x_2491_;
}
}
else
{
size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = lean_usize_of_nat(v___x_2481_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2486_, v_todo_2396_, v_children_2480_, v___x_2492_, v___x_2493_, v_result_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec_ref(v_children_2480_);
lean_dec(v_n_2486_);
return v___x_2494_;
}
}
}
else
{
lean_object* v___x_2495_; 
lean_dec_ref(v_children_2480_);
lean_dec_ref(v_todo_2396_);
lean_dec(v_skip_2395_);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_result_2398_);
return v___x_2495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2496_, lean_object* v_as_2497_, size_t v_i_2498_, size_t v_stop_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_usize_dec_eq(v_i_2498_, v_stop_2499_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; lean_object* v_fst_2508_; lean_object* v_snd_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2507_ = lean_array_uget_borrowed(v_as_2497_, v_i_2498_);
v_fst_2508_ = lean_ctor_get(v___x_2507_, 0);
v_snd_2509_ = lean_ctor_get(v___x_2507_, 1);
v___x_2510_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2508_);
lean_inc(v_snd_2509_);
lean_inc_ref(v_todo_2496_);
v___x_2511_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2510_, v_todo_2496_, v_snd_2509_, v_b_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; size_t v___x_2513_; size_t v___x_2514_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2498_, v___x_2513_);
v_i_2498_ = v___x_2514_;
v_b_2500_ = v_a_2512_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2496_);
return v___x_2511_;
}
}
else
{
lean_object* v___x_2516_; 
lean_dec_ref(v_todo_2496_);
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_b_2500_);
return v___x_2516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2517_, lean_object* v_as_2518_, lean_object* v_i_2519_, lean_object* v_stop_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
size_t v_i_boxed_2527_; size_t v_stop_boxed_2528_; lean_object* v_res_2529_; 
v_i_boxed_2527_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_stop_boxed_2528_ = lean_unbox_usize(v_stop_2520_);
lean_dec(v_stop_2520_);
v_res_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2517_, v_as_2518_, v_i_boxed_2527_, v_stop_boxed_2528_, v_b_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec_ref(v_as_2518_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2530_, lean_object* v_todo_2531_, lean_object* v_as_2532_, lean_object* v_i_2533_, lean_object* v_stop_2534_, lean_object* v_b_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
size_t v_i_boxed_2541_; size_t v_stop_boxed_2542_; lean_object* v_res_2543_; 
v_i_boxed_2541_ = lean_unbox_usize(v_i_2533_);
lean_dec(v_i_2533_);
v_stop_boxed_2542_ = lean_unbox_usize(v_stop_2534_);
lean_dec(v_stop_2534_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2530_, v_todo_2531_, v_as_2532_, v_i_boxed_2541_, v_stop_boxed_2542_, v_b_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v_as_2532_);
lean_dec(v_n_2530_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2544_, lean_object* v_todo_2545_, lean_object* v_c_2546_, lean_object* v_result_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2544_, v_todo_2545_, v_c_2546_, v_result_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2554_, lean_object* v_skip_2555_, lean_object* v_todo_2556_, lean_object* v_c_2557_, lean_object* v_result_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2555_, v_todo_2556_, v_c_2557_, v_result_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2565_, lean_object* v_skip_2566_, lean_object* v_todo_2567_, lean_object* v_c_2568_, lean_object* v_result_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2565_, v_skip_2566_, v_todo_2567_, v_c_2568_, v_result_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2576_, lean_object* v_todo_2577_, lean_object* v_as_2578_, size_t v_i_2579_, size_t v_stop_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2577_, v_as_2578_, v_i_2579_, v_stop_2580_, v_b_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2588_, lean_object* v_todo_2589_, lean_object* v_as_2590_, lean_object* v_i_2591_, lean_object* v_stop_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
size_t v_i_boxed_2599_; size_t v_stop_boxed_2600_; lean_object* v_res_2601_; 
v_i_boxed_2599_ = lean_unbox_usize(v_i_2591_);
lean_dec(v_i_2591_);
v_stop_boxed_2600_ = lean_unbox_usize(v_stop_2592_);
lean_dec(v_stop_2592_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2588_, v_todo_2589_, v_as_2590_, v_i_boxed_2599_, v_stop_boxed_2600_, v_b_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v_as_2590_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2602_, lean_object* v_n_2603_, lean_object* v_todo_2604_, lean_object* v_as_2605_, size_t v_i_2606_, size_t v_stop_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2603_, v_todo_2604_, v_as_2605_, v_i_2606_, v_stop_2607_, v_b_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2615_, lean_object* v_n_2616_, lean_object* v_todo_2617_, lean_object* v_as_2618_, lean_object* v_i_2619_, lean_object* v_stop_2620_, lean_object* v_b_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
size_t v_i_boxed_2627_; size_t v_stop_boxed_2628_; lean_object* v_res_2629_; 
v_i_boxed_2627_ = lean_unbox_usize(v_i_2619_);
lean_dec(v_i_2619_);
v_stop_boxed_2628_ = lean_unbox_usize(v_stop_2620_);
lean_dec(v_stop_2620_);
v_res_2629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2615_, v_n_2616_, v_todo_2617_, v_as_2618_, v_i_boxed_2627_, v_stop_boxed_2628_, v_b_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec_ref(v_as_2618_);
lean_dec(v_n_2616_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2630_, lean_object* v_k_2631_, lean_object* v_c_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2631_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2640_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2638_, v___x_2639_, v_c_2632_, v_result_2630_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2641_, lean_object* v_k_2642_, lean_object* v_c_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2641_, v_k_2642_, v_c_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v_k_2642_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2650_, lean_object* v_keys_2651_, lean_object* v_vals_2652_, lean_object* v_i_2653_, lean_object* v_acc_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = lean_array_get_size(v_keys_2651_);
v___x_2661_ = lean_nat_dec_lt(v_i_2653_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec(v_i_2653_);
lean_dec_ref(v_f_2650_);
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_acc_2654_);
return v___x_2662_;
}
else
{
lean_object* v_k_2663_; lean_object* v_v_2664_; lean_object* v___x_2665_; 
v_k_2663_ = lean_array_fget_borrowed(v_keys_2651_, v_i_2653_);
v_v_2664_ = lean_array_fget_borrowed(v_vals_2652_, v_i_2653_);
lean_inc_ref(v_f_2650_);
lean_inc(v___y_2658_);
lean_inc_ref(v___y_2657_);
lean_inc(v___y_2656_);
lean_inc_ref(v___y_2655_);
lean_inc(v_v_2664_);
lean_inc(v_k_2663_);
v___x_2665_ = lean_apply_8(v_f_2650_, v_acc_2654_, v_k_2663_, v_v_2664_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, lean_box(0));
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = lean_nat_add(v_i_2653_, v___x_2667_);
lean_dec(v_i_2653_);
v_i_2653_ = v___x_2668_;
v_acc_2654_ = v_a_2666_;
goto _start;
}
else
{
lean_dec(v_i_2653_);
lean_dec_ref(v_f_2650_);
return v___x_2665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2670_, lean_object* v_keys_2671_, lean_object* v_vals_2672_, lean_object* v_i_2673_, lean_object* v_acc_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2670_, v_keys_2671_, v_vals_2672_, v_i_2673_, v_acc_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v_vals_2672_);
lean_dec_ref(v_keys_2671_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
if (lean_obj_tag(v_x_2682_) == 0)
{
lean_object* v_es_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2709_; 
v_es_2689_ = lean_ctor_get(v_x_2682_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_x_2682_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2691_ = v_x_2682_;
v_isShared_2692_ = v_isSharedCheck_2709_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_es_2689_);
lean_dec(v_x_2682_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2709_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = lean_array_get_size(v_es_2689_);
v___x_2695_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2697_; 
lean_dec_ref(v_es_2689_);
lean_dec_ref(v_f_2681_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v_x_2683_);
v___x_2697_ = v___x_2691_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_x_2683_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
else
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_nat_dec_le(v___x_2694_, v___x_2694_);
if (v___x_2699_ == 0)
{
if (v___x_2695_ == 0)
{
lean_object* v___x_2701_; 
lean_dec_ref(v_es_2689_);
lean_dec_ref(v_f_2681_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v_x_2683_);
v___x_2701_ = v___x_2691_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_x_2683_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
else
{
size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
lean_del_object(v___x_2691_);
v___x_2703_ = ((size_t)0ULL);
v___x_2704_ = lean_usize_of_nat(v___x_2694_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2681_, v_es_2689_, v___x_2703_, v___x_2704_, v_x_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec_ref(v_es_2689_);
return v___x_2705_;
}
}
else
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
lean_del_object(v___x_2691_);
v___x_2706_ = ((size_t)0ULL);
v___x_2707_ = lean_usize_of_nat(v___x_2694_);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2681_, v_es_2689_, v___x_2706_, v___x_2707_, v_x_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec_ref(v_es_2689_);
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_ks_2710_; lean_object* v_vs_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_ks_2710_ = lean_ctor_get(v_x_2682_, 0);
lean_inc_ref(v_ks_2710_);
v_vs_2711_ = lean_ctor_get(v_x_2682_, 1);
lean_inc_ref(v_vs_2711_);
lean_dec_ref_known(v_x_2682_, 2);
v___x_2712_ = lean_unsigned_to_nat(0u);
v___x_2713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2681_, v_ks_2710_, v_vs_2711_, v___x_2712_, v_x_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec_ref(v_vs_2711_);
lean_dec_ref(v_ks_2710_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2714_, lean_object* v_as_2715_, size_t v_i_2716_, size_t v_stop_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_a_2725_; lean_object* v___y_2730_; uint8_t v___x_2732_; 
v___x_2732_ = lean_usize_dec_eq(v_i_2716_, v_stop_2717_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_array_uget_borrowed(v_as_2715_, v_i_2716_);
switch(lean_obj_tag(v___x_2733_))
{
case 0:
{
lean_object* v_key_2734_; lean_object* v_val_2735_; lean_object* v___x_2736_; 
v_key_2734_ = lean_ctor_get(v___x_2733_, 0);
v_val_2735_ = lean_ctor_get(v___x_2733_, 1);
lean_inc_ref(v_f_2714_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v_val_2735_);
lean_inc(v_key_2734_);
v___x_2736_ = lean_apply_8(v_f_2714_, v_b_2718_, v_key_2734_, v_val_2735_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
v___y_2730_ = v___x_2736_;
goto v___jp_2729_;
}
case 1:
{
lean_object* v_node_2737_; lean_object* v___x_2738_; 
v_node_2737_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_node_2737_);
lean_inc_ref(v_f_2714_);
v___x_2738_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2714_, v_node_2737_, v_b_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v___y_2730_ = v___x_2738_;
goto v___jp_2729_;
}
default: 
{
v_a_2725_ = v_b_2718_;
goto v___jp_2724_;
}
}
}
else
{
lean_object* v___x_2739_; 
lean_dec_ref(v_f_2714_);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_b_2718_);
return v___x_2739_;
}
v___jp_2724_:
{
size_t v___x_2726_; size_t v___x_2727_; 
v___x_2726_ = ((size_t)1ULL);
v___x_2727_ = lean_usize_add(v_i_2716_, v___x_2726_);
v_i_2716_ = v___x_2727_;
v_b_2718_ = v_a_2725_;
goto _start;
}
v___jp_2729_:
{
if (lean_obj_tag(v___y_2730_) == 0)
{
lean_object* v_a_2731_; 
v_a_2731_ = lean_ctor_get(v___y_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___y_2730_, 1);
v_a_2725_ = v_a_2731_;
goto v___jp_2724_;
}
else
{
lean_dec_ref(v_f_2714_);
return v___y_2730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2740_, lean_object* v_as_2741_, lean_object* v_i_2742_, lean_object* v_stop_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
size_t v_i_boxed_2750_; size_t v_stop_boxed_2751_; lean_object* v_res_2752_; 
v_i_boxed_2750_ = lean_unbox_usize(v_i_2742_);
lean_dec(v_i_2742_);
v_stop_boxed_2751_ = lean_unbox_usize(v_stop_2743_);
lean_dec(v_stop_2743_);
v_res_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2740_, v_as_2741_, v_i_boxed_2750_, v_stop_boxed_2751_, v_b_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v_as_2741_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2753_, v_x_2754_, v_x_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2763_, lean_object* v_e_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; uint8_t v_foApprox_2771_; uint8_t v_ctxApprox_2772_; uint8_t v_quasiPatternApprox_2773_; uint8_t v_constApprox_2774_; uint8_t v_isDefEqStuckEx_2775_; uint8_t v_unificationHints_2776_; uint8_t v_proofIrrelevance_2777_; uint8_t v_assignSyntheticOpaque_2778_; uint8_t v_offsetCnstrs_2779_; uint8_t v_etaStruct_2780_; uint8_t v_univApprox_2781_; uint8_t v_iota_2782_; uint8_t v_beta_2783_; uint8_t v_proj_2784_; uint8_t v_zeta_2785_; uint8_t v_zetaDelta_2786_; uint8_t v_zetaUnused_2787_; uint8_t v_zetaHave_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2843_; 
v___x_2770_ = l_Lean_Meta_Context_config(v_a_2765_);
v_foApprox_2771_ = lean_ctor_get_uint8(v___x_2770_, 0);
v_ctxApprox_2772_ = lean_ctor_get_uint8(v___x_2770_, 1);
v_quasiPatternApprox_2773_ = lean_ctor_get_uint8(v___x_2770_, 2);
v_constApprox_2774_ = lean_ctor_get_uint8(v___x_2770_, 3);
v_isDefEqStuckEx_2775_ = lean_ctor_get_uint8(v___x_2770_, 4);
v_unificationHints_2776_ = lean_ctor_get_uint8(v___x_2770_, 5);
v_proofIrrelevance_2777_ = lean_ctor_get_uint8(v___x_2770_, 6);
v_assignSyntheticOpaque_2778_ = lean_ctor_get_uint8(v___x_2770_, 7);
v_offsetCnstrs_2779_ = lean_ctor_get_uint8(v___x_2770_, 8);
v_etaStruct_2780_ = lean_ctor_get_uint8(v___x_2770_, 10);
v_univApprox_2781_ = lean_ctor_get_uint8(v___x_2770_, 11);
v_iota_2782_ = lean_ctor_get_uint8(v___x_2770_, 12);
v_beta_2783_ = lean_ctor_get_uint8(v___x_2770_, 13);
v_proj_2784_ = lean_ctor_get_uint8(v___x_2770_, 14);
v_zeta_2785_ = lean_ctor_get_uint8(v___x_2770_, 15);
v_zetaDelta_2786_ = lean_ctor_get_uint8(v___x_2770_, 16);
v_zetaUnused_2787_ = lean_ctor_get_uint8(v___x_2770_, 17);
v_zetaHave_2788_ = lean_ctor_get_uint8(v___x_2770_, 18);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2790_ = v___x_2770_;
v_isShared_2791_ = v_isSharedCheck_2843_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v___x_2770_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2843_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
uint8_t v_trackZetaDelta_2792_; lean_object* v_zetaDeltaSet_2793_; lean_object* v_lctx_2794_; lean_object* v_localInstances_2795_; lean_object* v_defEqCtx_x3f_2796_; lean_object* v_synthPendingDepth_2797_; lean_object* v_canUnfold_x3f_2798_; uint8_t v_univApprox_2799_; uint8_t v_inTypeClassResolution_2800_; uint8_t v_cacheInferType_2801_; uint8_t v___x_2802_; lean_object* v_config_2804_; 
v_trackZetaDelta_2792_ = lean_ctor_get_uint8(v_a_2765_, sizeof(void*)*7);
v_zetaDeltaSet_2793_ = lean_ctor_get(v_a_2765_, 1);
v_lctx_2794_ = lean_ctor_get(v_a_2765_, 2);
v_localInstances_2795_ = lean_ctor_get(v_a_2765_, 3);
v_defEqCtx_x3f_2796_ = lean_ctor_get(v_a_2765_, 4);
v_synthPendingDepth_2797_ = lean_ctor_get(v_a_2765_, 5);
v_canUnfold_x3f_2798_ = lean_ctor_get(v_a_2765_, 6);
v_univApprox_2799_ = lean_ctor_get_uint8(v_a_2765_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2800_ = lean_ctor_get_uint8(v_a_2765_, sizeof(void*)*7 + 2);
v_cacheInferType_2801_ = lean_ctor_get_uint8(v_a_2765_, sizeof(void*)*7 + 3);
v___x_2802_ = 2;
if (v_isShared_2791_ == 0)
{
v_config_2804_ = v___x_2790_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 0, v_foApprox_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 1, v_ctxApprox_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 2, v_quasiPatternApprox_2773_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 3, v_constApprox_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 4, v_isDefEqStuckEx_2775_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 5, v_unificationHints_2776_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 6, v_proofIrrelevance_2777_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 7, v_assignSyntheticOpaque_2778_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 8, v_offsetCnstrs_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 10, v_etaStruct_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 11, v_univApprox_2781_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 12, v_iota_2782_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 13, v_beta_2783_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 14, v_proj_2784_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 15, v_zeta_2785_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 16, v_zetaDelta_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 17, v_zetaUnused_2787_);
lean_ctor_set_uint8(v_reuseFailAlloc_2842_, 18, v_zetaHave_2788_);
v_config_2804_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
uint64_t v___x_2805_; uint64_t v___x_2806_; uint64_t v___x_2807_; uint8_t v___x_2808_; uint64_t v___x_2809_; uint64_t v___x_2810_; uint64_t v_key_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; lean_object* v___x_2815_; 
lean_ctor_set_uint8(v_config_2804_, 9, v___x_2802_);
v___x_2805_ = l_Lean_Meta_Context_configKey(v_a_2765_);
v___x_2806_ = 3ULL;
v___x_2807_ = lean_uint64_shift_right(v___x_2805_, v___x_2806_);
v___x_2808_ = 1;
v___x_2809_ = lean_uint64_shift_left(v___x_2807_, v___x_2806_);
v___x_2810_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2811_ = lean_uint64_lor(v___x_2809_, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2812_, 0, v_config_2804_);
lean_ctor_set_uint64(v___x_2812_, sizeof(void*)*1, v_key_2811_);
lean_inc(v_canUnfold_x3f_2798_);
lean_inc(v_synthPendingDepth_2797_);
lean_inc(v_defEqCtx_x3f_2796_);
lean_inc_ref(v_localInstances_2795_);
lean_inc_ref(v_lctx_2794_);
lean_inc(v_zetaDeltaSet_2793_);
v___x_2813_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v_zetaDeltaSet_2793_);
lean_ctor_set(v___x_2813_, 2, v_lctx_2794_);
lean_ctor_set(v___x_2813_, 3, v_localInstances_2795_);
lean_ctor_set(v___x_2813_, 4, v_defEqCtx_x3f_2796_);
lean_ctor_set(v___x_2813_, 5, v_synthPendingDepth_2797_);
lean_ctor_set(v___x_2813_, 6, v_canUnfold_x3f_2798_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*7, v_trackZetaDelta_2792_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*7 + 1, v_univApprox_2799_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2800_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*7 + 3, v_cacheInferType_2801_);
v___x_2814_ = 0;
v___x_2815_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2764_, v___x_2814_, v___x_2808_, v___x_2813_, v_a_2766_, v_a_2767_, v_a_2768_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2833_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2833_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2833_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_fst_2820_; 
v_fst_2820_ = lean_ctor_get(v_a_2816_, 0);
lean_inc(v_fst_2820_);
if (lean_obj_tag(v_fst_2820_) == 0)
{
lean_object* v___f_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
lean_del_object(v___x_2818_);
lean_dec(v_a_2816_);
v___f_2821_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_2823_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2821_, v_d_2763_, v___x_2822_, v___x_2813_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec_ref_known(v___x_2813_, 7);
return v___x_2823_;
}
else
{
lean_object* v_snd_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_snd_2824_ = lean_ctor_get(v_a_2816_, 1);
lean_inc(v_snd_2824_);
lean_dec(v_a_2816_);
v___x_2825_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2763_);
v___x_2826_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2763_, v_fst_2820_);
lean_dec(v_fst_2820_);
lean_dec_ref(v_d_2763_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v___x_2828_; 
lean_dec(v_snd_2824_);
lean_dec_ref_known(v___x_2813_, 7);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2825_);
v___x_2828_ = v___x_2818_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2825_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
else
{
lean_object* v_val_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_del_object(v___x_2818_);
v_val_2830_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2831_, v_snd_2824_, v_val_2830_, v___x_2825_, v___x_2813_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec_ref_known(v___x_2813_, 7);
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec_ref_known(v___x_2813_, 7);
lean_dec_ref(v_d_2763_);
v_a_2834_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2815_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2815_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_2844_, lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2844_, v_e_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_2852_, lean_object* v_d_2853_, lean_object* v_e_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2853_, v_e_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_2861_, lean_object* v_d_2862_, lean_object* v_e_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_2861_, v_d_2862_, v_e_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_2870_, lean_object* v_f_2871_, lean_object* v_init_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2871_, v_map_2870_, v_init_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_2879_, lean_object* v_f_2880_, lean_object* v_init_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_2879_, v_f_2880_, v_init_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_2888_, lean_object* v_00_u03b2_2889_, lean_object* v_map_2890_, lean_object* v_f_2891_, lean_object* v_init_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2891_, v_map_2890_, v_init_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_2899_, lean_object* v_00_u03b2_2900_, lean_object* v_map_2901_, lean_object* v_f_2902_, lean_object* v_init_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_2899_, v_00_u03b2_2900_, v_map_2901_, v_f_2902_, v_init_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_2910_, lean_object* v_00_u03b1_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_f_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2913_, v_x_2914_, v_x_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2922_, lean_object* v_00_u03b1_2923_, lean_object* v_00_u03b2_2924_, lean_object* v_f_2925_, lean_object* v_x_2926_, lean_object* v_x_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_2922_, v_00_u03b1_2923_, v_00_u03b2_2924_, v_f_2925_, v_x_2926_, v_x_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2934_, lean_object* v_00_u03b2_2935_, lean_object* v_00_u03c3_2936_, lean_object* v_f_2937_, lean_object* v_as_2938_, size_t v_i_2939_, size_t v_stop_2940_, lean_object* v_b_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2937_, v_as_2938_, v_i_2939_, v_stop_2940_, v_b_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2948_, lean_object* v_00_u03b2_2949_, lean_object* v_00_u03c3_2950_, lean_object* v_f_2951_, lean_object* v_as_2952_, lean_object* v_i_2953_, lean_object* v_stop_2954_, lean_object* v_b_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
size_t v_i_boxed_2961_; size_t v_stop_boxed_2962_; lean_object* v_res_2963_; 
v_i_boxed_2961_ = lean_unbox_usize(v_i_2953_);
lean_dec(v_i_2953_);
v_stop_boxed_2962_ = lean_unbox_usize(v_stop_2954_);
lean_dec(v_stop_2954_);
v_res_2963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_2948_, v_00_u03b2_2949_, v_00_u03c3_2950_, v_f_2951_, v_as_2952_, v_i_boxed_2961_, v_stop_boxed_2962_, v_b_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v_as_2952_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2964_, lean_object* v_00_u03b1_2965_, lean_object* v_00_u03b2_2966_, lean_object* v_f_2967_, lean_object* v_keys_2968_, lean_object* v_vals_2969_, lean_object* v_heq_2970_, lean_object* v_i_2971_, lean_object* v_acc_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2967_, v_keys_2968_, v_vals_2969_, v_i_2971_, v_acc_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2979_, lean_object* v_00_u03b1_2980_, lean_object* v_00_u03b2_2981_, lean_object* v_f_2982_, lean_object* v_keys_2983_, lean_object* v_vals_2984_, lean_object* v_heq_2985_, lean_object* v_i_2986_, lean_object* v_acc_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_2979_, v_00_u03b1_2980_, v_00_u03b2_2981_, v_f_2982_, v_keys_2983_, v_vals_2984_, v_heq_2985_, v_i_2986_, v_acc_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_vals_2984_);
lean_dec_ref(v_keys_2983_);
return v_res_2993_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar = _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar);
l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity = _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_DiscrTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_DiscrTree_Main(builtin);
}
#ifdef __cplusplus
}
#endif
