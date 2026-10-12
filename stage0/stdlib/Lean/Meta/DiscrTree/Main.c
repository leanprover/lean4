// Lean compiler output
// Module: Lean.Meta.DiscrTree.Main
// Imports: public import Lean.Meta.Basic public import Lean.Meta.DiscrTree.Util import Lean.Meta.WHNF
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
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg();
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1;
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
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(lean_object* v_a_18_, lean_object* v_i_19_, lean_object* v_infos_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = lean_array_get_size(v_infos_20_);
v___x_27_ = lean_nat_dec_lt(v_i_19_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_isProof(v_a_18_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_28_;
}
else
{
lean_object* v_info_29_; uint8_t v_isInstance_30_; uint8_t v___y_32_; 
v_info_29_ = lean_array_fget_borrowed(v_infos_20_, v_i_19_);
v_isInstance_30_ = lean_ctor_get_uint8(v_info_29_, sizeof(void*)*1 + 4);
if (v_isInstance_30_ == 0)
{
uint8_t v___x_48_; 
v___x_48_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_29_);
if (v___x_48_ == 0)
{
uint8_t v___x_49_; 
v___x_49_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_29_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_isProof(v_a_18_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_50_;
}
else
{
v___y_32_ = v___x_49_;
goto v___jp_31_;
}
}
else
{
v___y_32_ = v___x_27_;
goto v___jp_31_;
}
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec_ref(v_a_18_);
v___x_51_ = lean_box(v___x_27_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
v___jp_31_:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_isType(v_a_18_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_47_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_47_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_47_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_47_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
uint8_t v___x_38_; 
v___x_38_ = lean_unbox(v_a_34_);
lean_dec(v_a_34_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_39_ = lean_box(v___y_32_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_39_);
v___x_41_ = v___x_36_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
else
{
lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_43_ = lean_box(v_isInstance_30_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_43_);
v___x_45_ = v___x_36_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
else
{
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_18_ = stack[0].m_obj;
lean_object* v_i_19_ = stack[1].m_obj;
lean_object* v_infos_20_ = stack[2].m_obj;
lean_object* v_a_21_ = stack[3].m_obj;
lean_object* v_a_22_ = stack[4].m_obj;
lean_object* v_a_23_ = stack[5].m_obj;
lean_object* v_a_24_ = stack[6].m_obj;
lean_object* v_res_53_;
v_res_53_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_a_18_, v_i_19_, v_infos_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object* v_a_54_, lean_object* v_i_55_, lean_object* v_infos_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_a_54_, v_i_55_, v_infos_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec_ref(v_infos_56_);
lean_dec(v_i_55_);
return v_res_62_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object* v_infos_63_, lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
if (lean_obj_tag(v_x_65_) == 5)
{
lean_object* v_fn_72_; lean_object* v_arg_73_; lean_object* v___x_74_; 
v_fn_72_ = lean_ctor_get(v_x_65_, 0);
lean_inc_ref(v_fn_72_);
v_arg_73_ = lean_ctor_get(v_x_65_, 1);
lean_inc_ref_n(v_arg_73_, 2);
lean_dec_ref_known(v_x_65_, 2);
v___x_74_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_arg_73_, v_x_64_, v_infos_63_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; uint8_t v___x_76_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = lean_unbox(v_a_75_);
lean_dec(v_a_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_sub(v_x_64_, v___x_77_);
lean_dec(v_x_64_);
v___x_79_ = lean_array_push(v_x_66_, v_arg_73_);
v_x_64_ = v___x_78_;
v_x_65_ = v_fn_72_;
v_x_66_ = v___x_79_;
goto _start;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v_arg_73_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_sub(v_x_64_, v___x_81_);
lean_dec(v_x_64_);
v___x_83_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
v___x_84_ = lean_array_push(v_x_66_, v___x_83_);
v_x_64_ = v___x_82_;
v_x_65_ = v_fn_72_;
v_x_66_ = v___x_84_;
goto _start;
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_fn_72_);
lean_dec_ref(v_x_66_);
lean_dec(v_x_64_);
v_a_86_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_74_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_74_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v___x_94_; 
lean_dec_ref(v_x_65_);
lean_dec(v_x_64_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_x_66_);
return v___x_94_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_63_ = stack[0].m_obj;
lean_object* v_x_64_ = stack[1].m_obj;
lean_object* v_x_65_ = stack[2].m_obj;
lean_object* v_x_66_ = stack[3].m_obj;
lean_object* v_a_67_ = stack[4].m_obj;
lean_object* v_a_68_ = stack[5].m_obj;
lean_object* v_a_69_ = stack[6].m_obj;
lean_object* v_a_70_ = stack[7].m_obj;
lean_object* v_res_95_;
v_res_95_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_infos_63_, v_x_64_, v_x_65_, v_x_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object* v_infos_96_, lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_infos_96_, v_x_97_, v_x_98_, v_x_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec_ref(v_infos_96_);
return v_res_105_;
}
}
uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(lean_object* v_e_120_){
_start:
{
uint8_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = l_Lean_Expr_isRawNatLit(v_e_120_);
v___x_122_ = 1;
if (v___x_121_ == 0)
{
lean_object* v_f_123_; uint8_t v___x_124_; 
v_f_123_ = l_Lean_Expr_getAppFn(v_e_120_);
v___x_124_ = l_Lean_Expr_isConst(v_f_123_);
if (v___x_124_ == 0)
{
lean_dec_ref(v_f_123_);
lean_dec_ref(v_e_120_);
return v___x_121_;
}
else
{
if (v___x_121_ == 0)
{
lean_object* v_fName_125_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_fName_125_ = l_Lean_Expr_constName_x21(v_f_123_);
lean_dec_ref(v_f_123_);
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_144_ = lean_name_eq(v_fName_125_, v___x_143_);
if (v___x_144_ == 0)
{
goto v___jp_132_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_145_ = l_Lean_Expr_getAppNumArgs(v_e_120_);
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_dec_eq(v___x_145_, v___x_146_);
lean_dec(v___x_145_);
if (v___x_147_ == 0)
{
goto v___jp_132_;
}
else
{
lean_object* v___x_148_; 
lean_dec(v_fName_125_);
v___x_148_ = l_Lean_Expr_appArg_x21(v_e_120_);
lean_dec_ref(v_e_120_);
v_e_120_ = v___x_148_;
goto _start;
}
}
v___jp_126_:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2));
v___x_128_ = lean_name_eq(v_fName_125_, v___x_127_);
lean_dec(v_fName_125_);
if (v___x_128_ == 0)
{
lean_dec_ref(v_e_120_);
return v___x_121_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = l_Lean_Expr_getAppNumArgs(v_e_120_);
lean_dec_ref(v_e_120_);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_nat_dec_eq(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
return v___x_122_;
}
}
}
v___jp_132_:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5));
v___x_134_ = lean_name_eq(v_fName_125_, v___x_133_);
if (v___x_134_ == 0)
{
goto v___jp_126_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = l_Lean_Expr_getAppNumArgs(v_e_120_);
v___x_136_ = lean_unsigned_to_nat(3u);
v___x_137_ = lean_nat_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec(v___x_135_);
goto v___jp_126_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v_fName_125_);
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_sub(v___x_135_, v___x_138_);
lean_dec(v___x_135_);
v___x_140_ = lean_nat_sub(v___x_139_, v___x_138_);
lean_dec(v___x_139_);
v___x_141_ = l_Lean_Expr_getRevArg_x21(v_e_120_, v___x_140_);
lean_dec_ref(v_e_120_);
v_e_120_ = v___x_141_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v_f_123_);
lean_dec_ref(v_e_120_);
return v___x_121_;
}
}
}
else
{
lean_dec_ref(v_e_120_);
return v___x_122_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_120_ = stack[0].m_obj;
uint8_t v_res_150_;
v_res_150_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v_e_120_);
stack->m_num = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___boxed(lean_object* v_e_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v_e_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(lean_object* v_e_156_){
_start:
{
uint8_t v___y_158_; lean_object* v_f_161_; 
v_f_161_ = l_Lean_Expr_getAppFn(v_e_156_);
switch(lean_obj_tag(v_f_161_))
{
case 9:
{
lean_object* v_a_162_; 
lean_dec_ref(v_e_156_);
v_a_162_ = lean_ctor_get(v_f_161_, 0);
lean_inc_ref(v_a_162_);
lean_dec_ref_known(v_f_161_, 1);
if (lean_obj_tag(v_a_162_) == 0)
{
lean_object* v_val_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
v_val_163_ = lean_ctor_get(v_a_162_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_a_162_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v_a_162_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_val_163_);
lean_dec(v_a_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 1);
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_val_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v___x_171_; 
lean_dec_ref(v_a_162_);
v___x_171_ = lean_box(0);
return v___x_171_;
}
}
case 4:
{
lean_object* v_declName_172_; uint8_t v___y_174_; uint8_t v___y_187_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_declName_172_ = lean_ctor_get(v_f_161_, 0);
lean_inc(v_declName_172_);
lean_dec_ref_known(v_f_161_, 2);
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_206_ = lean_name_eq(v_declName_172_, v___x_205_);
if (v___x_206_ == 0)
{
v___y_187_ = v___x_206_;
goto v___jp_186_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_207_ = l_Lean_Expr_getAppNumArgs(v_e_156_);
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
lean_dec(v___x_207_);
v___y_187_ = v___x_209_;
goto v___jp_186_;
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2));
v___x_176_ = lean_name_eq(v_declName_172_, v___x_175_);
lean_dec(v_declName_172_);
if (v___x_176_ == 0)
{
lean_dec_ref(v_e_156_);
v___y_158_ = v___x_176_;
goto v___jp_157_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_177_ = l_Lean_Expr_getAppNumArgs(v_e_156_);
lean_dec_ref(v_e_156_);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_nat_dec_eq(v___x_177_, v___x_178_);
lean_dec(v___x_177_);
v___y_158_ = v___x_179_;
goto v___jp_157_;
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_declName_172_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = l_Lean_Expr_getAppNumArgs(v_e_156_);
v___x_182_ = lean_nat_sub(v___x_181_, v___x_180_);
lean_dec(v___x_181_);
v___x_183_ = lean_nat_sub(v___x_182_, v___x_180_);
lean_dec(v___x_182_);
v___x_184_ = l_Lean_Expr_getRevArg_x21(v_e_156_, v___x_183_);
lean_dec_ref(v_e_156_);
v_e_156_ = v___x_184_;
goto _start;
}
}
v___jp_186_:
{
if (v___y_187_ == 0)
{
lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5));
v___x_189_ = lean_name_eq(v_declName_172_, v___x_188_);
if (v___x_189_ == 0)
{
v___y_174_ = v___x_189_;
goto v___jp_173_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_190_ = l_Lean_Expr_getAppNumArgs(v_e_156_);
v___x_191_ = lean_unsigned_to_nat(3u);
v___x_192_ = lean_nat_dec_eq(v___x_190_, v___x_191_);
lean_dec(v___x_190_);
v___y_174_ = v___x_192_;
goto v___jp_173_;
}
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_declName_172_);
v___x_193_ = l_Lean_Expr_appArg_x21(v_e_156_);
lean_dec_ref(v_e_156_);
v___x_194_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v___x_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
return v___x_194_;
}
else
{
lean_object* v_val_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_204_; 
v_val_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_val_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_add(v_val_195_, v___x_199_);
lean_dec(v_val_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_200_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_210_; 
lean_dec_ref(v_f_161_);
lean_dec_ref(v_e_156_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
v___jp_157_:
{
if (v___y_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0));
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(lean_object* v_e_211_){
_start:
{
uint8_t v___x_212_; 
lean_inc_ref(v_e_211_);
v___x_212_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v_e_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
lean_dec_ref(v_e_211_);
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v_e_211_);
if (lean_obj_tag(v___x_214_) == 1)
{
lean_object* v_val_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_val_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_val_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v_val_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v___x_214_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(lean_object* v_e_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; 
lean_inc(v_a_231_);
lean_inc_ref(v_a_230_);
lean_inc(v_a_229_);
lean_inc_ref(v_a_228_);
v___x_233_ = lean_whnf(v_e_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0));
v___x_239_ = l_Lean_Expr_isConstOf(v_a_234_, v___x_238_);
lean_dec(v_a_234_);
v___x_240_ = lean_box(v___x_239_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_240_);
v___x_242_ = v___x_236_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_233_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_233_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_227_ = stack[0].m_obj;
lean_object* v_a_228_ = stack[1].m_obj;
lean_object* v_a_229_ = stack[2].m_obj;
lean_object* v_a_230_ = stack[3].m_obj;
lean_object* v_a_231_ = stack[4].m_obj;
lean_object* v_res_253_;
v_res_253_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v_e_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___boxed(lean_object* v_e_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v_e_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_260_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(lean_object* v_fName_274_, lean_object* v_e_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
uint8_t v___y_282_; uint8_t v___y_312_; uint8_t v___y_337_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6));
v___x_348_ = lean_name_eq(v_fName_274_, v___x_347_);
if (v___x_348_ == 0)
{
v___y_337_ = v___x_348_;
goto v___jp_336_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = l_Lean_Expr_getAppNumArgs(v_e_275_);
v___x_350_ = lean_unsigned_to_nat(2u);
v___x_351_ = lean_nat_dec_eq(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
v___y_337_ = v___x_351_;
goto v___jp_336_;
}
v___jp_281_:
{
if (v___y_282_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_284_ = lean_name_eq(v_fName_274_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_box(v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_287_ = l_Lean_Expr_getAppNumArgs(v_e_275_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_dec_eq(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = l_Lean_Expr_getAppNumArgs(v_e_275_);
v___x_294_ = lean_nat_sub(v___x_293_, v___x_292_);
lean_dec(v___x_293_);
v___x_295_ = lean_nat_sub(v___x_294_, v___x_292_);
lean_dec(v___x_294_);
v___x_296_ = l_Lean_Expr_getRevArg_x21(v_e_275_, v___x_295_);
v___x_297_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_296_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; uint8_t v___x_299_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v___x_299_ = lean_unbox(v_a_298_);
if (v___x_299_ == 0)
{
return v___x_297_;
}
else
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_309_; 
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v___x_297_, 0);
lean_dec(v_unused_310_);
v___x_301_ = v___x_297_;
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
else
{
lean_dec(v___x_297_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_303_ = l_Lean_Expr_appArg_x21(v_e_275_);
v___x_304_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_303_);
v___x_305_ = lean_box(v___x_304_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_305_);
v___x_307_ = v___x_301_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
return v___x_297_;
}
}
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2));
v___x_314_ = lean_name_eq(v_fName_274_, v___x_313_);
if (v___x_314_ == 0)
{
v___y_282_ = v___x_314_;
goto v___jp_281_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = l_Lean_Expr_getAppNumArgs(v_e_275_);
v___x_316_ = lean_unsigned_to_nat(6u);
v___x_317_ = lean_nat_dec_eq(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
v___y_282_ = v___x_317_;
goto v___jp_281_;
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_318_ = l_Lean_Expr_getAppNumArgs(v_e_275_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_sub(v___x_318_, v___x_319_);
lean_dec(v___x_318_);
v___x_321_ = l_Lean_Expr_getRevArg_x21(v_e_275_, v___x_320_);
v___x_322_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_321_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; uint8_t v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v___x_324_ = lean_unbox(v_a_323_);
if (v___x_324_ == 0)
{
return v___x_322_;
}
else
{
lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_334_; 
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v___x_322_, 0);
lean_dec(v_unused_335_);
v___x_326_ = v___x_322_;
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
else
{
lean_dec(v___x_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_328_ = l_Lean_Expr_appArg_x21(v_e_275_);
v___x_329_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_328_);
v___x_330_ = lean_box(v___x_329_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_330_);
v___x_332_ = v___x_326_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
return v___x_322_;
}
}
}
v___jp_336_:
{
if (v___y_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5));
v___x_339_ = lean_name_eq(v_fName_274_, v___x_338_);
if (v___x_339_ == 0)
{
v___y_312_ = v___x_339_;
goto v___jp_311_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = l_Lean_Expr_getAppNumArgs(v_e_275_);
v___x_341_ = lean_unsigned_to_nat(4u);
v___x_342_ = lean_nat_dec_eq(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
v___y_312_ = v___x_342_;
goto v___jp_311_;
}
}
else
{
lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = l_Lean_Expr_appArg_x21(v_e_275_);
v___x_344_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_343_);
v___x_345_ = lean_box(v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_fName_274_ = stack[0].m_obj;
lean_object* v_e_275_ = stack[1].m_obj;
lean_object* v_a_276_ = stack[2].m_obj;
lean_object* v_a_277_ = stack[3].m_obj;
lean_object* v_a_278_ = stack[4].m_obj;
lean_object* v_a_279_ = stack[5].m_obj;
lean_object* v_res_352_;
v_res_352_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_274_, v_e_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object* v_fName_353_, lean_object* v_e_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_353_, v_e_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_e_354_);
lean_dec(v_fName_353_);
return v_res_360_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object* v_fName_361_, lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_361_, v_e_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_368_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fName_361_ = stack[0].m_obj;
lean_object* v_e_362_ = stack[1].m_obj;
lean_object* v_a_363_ = stack[2].m_obj;
lean_object* v_a_364_ = stack[3].m_obj;
lean_object* v_a_365_ = stack[4].m_obj;
lean_object* v_a_366_ = stack[5].m_obj;
lean_object* v_res_369_;
v_res_369_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(v_fName_361_, v_e_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object* v_fName_370_, lean_object* v_e_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(v_fName_370_, v_e_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_e_371_);
lean_dec(v_fName_370_);
return v_res_377_;
}
}
lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object* v_e_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_whnfCore(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; uint8_t v___x_386_; lean_object* v___x_387_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc_n(v_a_385_, 2);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = 0;
v___x_387_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_385_, v___x_386_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_400_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_400_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
if (lean_obj_tag(v_a_388_) == 0)
{
lean_object* v___x_392_; 
lean_inc(v_a_385_);
v___x_392_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_385_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_394_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v_a_385_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_385_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
else
{
lean_object* v_val_396_; 
lean_del_object(v___x_390_);
lean_dec(v_a_385_);
v_val_396_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_392_, 1);
v_e_378_ = v_val_396_;
goto _start;
}
}
else
{
lean_object* v_val_398_; 
lean_del_object(v___x_390_);
lean_dec(v_a_385_);
v_val_398_ = lean_ctor_get(v_a_388_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v_a_388_, 1);
v_e_378_ = v_val_398_;
goto _start;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_a_385_);
v_a_401_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_387_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_387_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
return v___x_384_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_reduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_378_ = stack[0].m_obj;
lean_object* v_a_379_ = stack[1].m_obj;
lean_object* v_a_380_ = stack[2].m_obj;
lean_object* v_a_381_ = stack[3].m_obj;
lean_object* v_a_382_ = stack[4].m_obj;
lean_object* v_res_409_;
v_res_409_ = l_Lean_Meta_DiscrTree_reduce(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_DiscrTree_reduce(v_e_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_416_;
}
}
uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(lean_object* v_fn_417_){
_start:
{
switch(lean_obj_tag(v_fn_417_))
{
case 9:
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
case 4:
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
case 1:
{
uint8_t v___x_420_; 
v___x_420_ = 0;
return v___x_420_;
}
case 11:
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
case 7:
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
default: 
{
uint8_t v___x_423_; 
v___x_423_ = 1;
return v___x_423_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_417_ = stack[0].m_obj;
uint8_t v_res_424_;
v_res_424_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v_fn_417_);
stack->m_num = v_res_424_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object* v_fn_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v_fn_425_);
lean_dec_ref(v_fn_425_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_whnfCore(v_e_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_n(v_a_435_, 2);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = 0;
v___x_437_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_435_, v___x_436_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_452_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_452_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_452_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_452_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
if (lean_obj_tag(v_a_438_) == 0)
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_a_435_);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_435_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
else
{
lean_object* v_val_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_val_445_ = lean_ctor_get(v_a_438_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v_a_438_, 1);
v___x_446_ = l_Lean_Expr_getAppFn(v_val_445_);
v___x_447_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v___x_446_);
lean_dec_ref(v___x_446_);
if (v___x_447_ == 0)
{
lean_del_object(v___x_440_);
lean_dec(v_a_435_);
v_e_428_ = v_val_445_;
goto _start;
}
else
{
lean_object* v___x_450_; 
lean_dec(v_val_445_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_a_435_);
v___x_450_ = v___x_440_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_435_);
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
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_a_435_);
v_a_453_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_437_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_437_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
return v___x_434_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_428_ = stack[0].m_obj;
lean_object* v_a_429_ = stack[1].m_obj;
lean_object* v_a_430_ = stack[2].m_obj;
lean_object* v_a_431_ = stack[3].m_obj;
lean_object* v_a_432_ = stack[4].m_obj;
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object* v_e_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_468_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object* v_e_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
v___x_477_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
return v___x_475_;
}
else
{
lean_object* v_val_478_; 
lean_dec_ref_known(v___x_475_, 1);
v_val_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_478_);
lean_dec_ref_known(v___x_477_, 1);
v_e_469_ = v_val_478_;
goto _start;
}
}
else
{
return v___x_475_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_469_ = stack[0].m_obj;
lean_object* v_a_470_ = stack[1].m_obj;
lean_object* v_a_471_ = stack[2].m_obj;
lean_object* v_a_472_ = stack[3].m_obj;
lean_object* v_a_473_ = stack[4].m_obj;
lean_object* v_res_480_;
v_res_480_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object* v_e_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
return v_res_487_;
}
}
lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object* v_e_488_, uint8_t v_root_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
if (v_root_489_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_DiscrTree_reduce(v_e_488_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_488_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_496_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_reduceDT_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_488_ = stack[0].m_obj;
uint8_t v_root_489_ = stack[1].m_num;
lean_object* v_a_490_ = stack[2].m_obj;
lean_object* v_a_491_ = stack[3].m_obj;
lean_object* v_a_492_ = stack[4].m_obj;
lean_object* v_a_493_ = stack[5].m_obj;
lean_object* v_res_497_;
v_res_497_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_488_, v_root_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT___boxed(lean_object* v_e_498_, lean_object* v_root_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
uint8_t v_root_boxed_505_; lean_object* v_res_506_; 
v_root_boxed_505_ = lean_unbox(v_root_499_);
v_res_506_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_498_, v_root_boxed_505_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(lean_object* v_n_507_, lean_object* v_todo_508_){
_start:
{
lean_object* v_zero_509_; uint8_t v_isZero_510_; 
v_zero_509_ = lean_unsigned_to_nat(0u);
v_isZero_510_ = lean_nat_dec_eq(v_n_507_, v_zero_509_);
if (v_isZero_510_ == 1)
{
lean_dec(v_n_507_);
return v_todo_508_;
}
else
{
lean_object* v_one_511_; lean_object* v_n_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_one_511_ = lean_unsigned_to_nat(1u);
v_n_512_ = lean_nat_sub(v_n_507_, v_one_511_);
lean_dec(v_n_507_);
v___x_513_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
v___x_514_ = lean_array_push(v_todo_508_, v___x_513_);
v_n_507_ = v_n_512_;
v_todo_508_ = v___x_514_;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(uint8_t v_root_516_, lean_object* v_todo_517_, lean_object* v_e_518_, uint8_t v_noIndexAtArgs_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_v_526_; lean_object* v___y_531_; lean_object* v_todo_532_; uint8_t v___x_535_; 
v___x_535_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_518_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_518_, v_root_516_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_665_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_665_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_665_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_665_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v_k_543_; lean_object* v_nargs_544_; lean_object* v_todo_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; 
v___x_541_ = l_Lean_Expr_getAppFn(v_a_537_);
switch(lean_obj_tag(v___x_541_))
{
case 9:
{
lean_object* v_a_574_; 
lean_del_object(v___x_539_);
lean_dec(v_a_537_);
v_a_574_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_a_574_);
lean_dec_ref_known(v___x_541_, 1);
v_v_526_ = v_a_574_;
goto v___jp_525_;
}
case 4:
{
lean_object* v_declName_575_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; 
lean_del_object(v___x_539_);
v_declName_575_ = lean_ctor_get(v___x_541_, 0);
if (v_root_516_ == 0)
{
lean_object* v___x_583_; 
lean_inc(v_a_537_);
v___x_583_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_537_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v_val_584_; 
lean_dec_ref_known(v___x_541_, 2);
lean_dec(v_a_537_);
v_val_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v___x_583_, 1);
v_v_526_ = v_val_584_;
goto v___jp_525_;
}
else
{
lean_object* v___x_585_; 
lean_dec(v___x_583_);
v___x_585_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_declName_575_, v_a_537_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_596_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_596_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_596_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_596_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
uint8_t v___x_590_; 
v___x_590_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_590_ == 0)
{
lean_del_object(v___x_588_);
v___y_577_ = v_a_520_;
v___y_578_ = v_a_521_;
v___y_579_ = v_a_522_;
v___y_580_ = v_a_523_;
goto v___jp_576_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
lean_dec_ref_known(v___x_541_, 2);
lean_dec(v_a_537_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v_todo_517_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_592_);
v___x_594_ = v___x_588_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref_known(v___x_541_, 2);
lean_dec(v_a_537_);
lean_dec_ref(v_todo_517_);
v_a_597_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_585_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_585_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
else
{
v___y_577_ = v_a_520_;
v___y_578_ = v_a_521_;
v___y_579_ = v_a_522_;
v___y_580_ = v_a_523_;
goto v___jp_576_;
}
v___jp_576_:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = l_Lean_Expr_getAppNumArgs(v_a_537_);
lean_inc(v___x_581_);
lean_inc(v_declName_575_);
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v_declName_575_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v_k_543_ = v___x_582_;
v_nargs_544_ = v___x_581_;
v_todo_545_ = v_todo_517_;
v___y_546_ = v___y_577_;
v___y_547_ = v___y_578_;
v___y_548_ = v___y_579_;
v___y_549_ = v___y_580_;
goto v___jp_542_;
}
}
case 11:
{
lean_object* v_typeName_605_; lean_object* v_idx_606_; lean_object* v_struct_607_; lean_object* v___x_608_; lean_object* v___y_610_; lean_object* v_env_614_; uint8_t v___x_615_; 
lean_del_object(v___x_539_);
v_typeName_605_ = lean_ctor_get(v___x_541_, 0);
v_idx_606_ = lean_ctor_get(v___x_541_, 1);
v_struct_607_ = lean_ctor_get(v___x_541_, 2);
v___x_608_ = lean_st_ref_get(v_a_523_);
v_env_614_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_608_);
v___x_615_ = l_Lean_isClass(v_env_614_, v_typeName_605_);
if (v___x_615_ == 0)
{
lean_inc_ref(v_struct_607_);
v___y_610_ = v_struct_607_;
goto v___jp_609_;
}
else
{
lean_object* v___x_616_; 
lean_inc_ref(v_struct_607_);
v___x_616_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_607_);
v___y_610_ = v___x_616_;
goto v___jp_609_;
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = l_Lean_Expr_getAppNumArgs(v_a_537_);
lean_inc(v___x_611_);
lean_inc(v_idx_606_);
lean_inc(v_typeName_605_);
v___x_612_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_612_, 0, v_typeName_605_);
lean_ctor_set(v___x_612_, 1, v_idx_606_);
lean_ctor_set(v___x_612_, 2, v___x_611_);
v___x_613_ = lean_array_push(v_todo_517_, v___y_610_);
v_k_543_ = v___x_612_;
v_nargs_544_ = v___x_611_;
v_todo_545_ = v___x_613_;
v___y_546_ = v_a_520_;
v___y_547_ = v_a_521_;
v___y_548_ = v_a_522_;
v___y_549_ = v_a_523_;
goto v___jp_542_;
}
}
case 1:
{
lean_object* v_fvarId_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_del_object(v___x_539_);
v_fvarId_617_ = lean_ctor_get(v___x_541_, 0);
v___x_618_ = l_Lean_Expr_getAppNumArgs(v_a_537_);
lean_inc(v___x_618_);
lean_inc(v_fvarId_617_);
v___x_619_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_619_, 0, v_fvarId_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v_k_543_ = v___x_619_;
v_nargs_544_ = v___x_618_;
v_todo_545_ = v_todo_517_;
v___y_546_ = v_a_520_;
v___y_547_ = v_a_521_;
v___y_548_ = v_a_522_;
v___y_549_ = v_a_523_;
goto v___jp_542_;
}
case 2:
{
lean_object* v_mvarId_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
lean_dec(v_a_537_);
v_mvarId_620_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_mvarId_620_);
lean_dec_ref_known(v___x_541_, 1);
v___x_621_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId));
v___x_622_ = l_Lean_instBEqMVarId_beq(v_mvarId_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_del_object(v___x_539_);
v___x_623_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_620_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_639_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_639_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_639_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_639_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint8_t v___x_628_; 
v___x_628_ = lean_unbox(v_a_624_);
lean_dec(v_a_624_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_todo_517_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_630_);
v___x_632_ = v___x_626_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = lean_box(1);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_todo_517_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_635_);
v___x_637_ = v___x_626_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_todo_517_);
v_a_640_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_623_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_623_);
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
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec(v_mvarId_620_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_todo_517_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_649_);
v___x_651_ = v___x_539_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
case 7:
{
lean_object* v_binderType_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
lean_dec(v_a_537_);
v_binderType_653_ = lean_ctor_get(v___x_541_, 1);
lean_inc_ref(v_binderType_653_);
lean_dec_ref_known(v___x_541_, 3);
v___x_654_ = lean_box(5);
v___x_655_ = lean_array_push(v_todo_517_, v_binderType_653_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_656_);
v___x_658_ = v___x_539_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
default: 
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec_ref(v___x_541_);
lean_dec(v_a_537_);
v___x_660_ = lean_box(1);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_todo_517_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_661_);
v___x_663_ = v___x_539_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
v___jp_542_:
{
lean_object* v___x_550_; 
lean_inc(v_nargs_544_);
v___x_550_ = l_Lean_Meta_getFunInfoNArgs(v___x_541_, v_nargs_544_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
if (v_noIndexAtArgs_519_ == 0)
{
lean_object* v_a_551_; lean_object* v_paramInfo_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v_paramInfo_552_ = lean_ctor_get(v_a_551_, 0);
lean_inc_ref(v_paramInfo_552_);
lean_dec(v_a_551_);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_sub(v_nargs_544_, v___x_553_);
lean_dec(v_nargs_544_);
v___x_555_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_paramInfo_552_, v___x_554_, v_a_537_, v_todo_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec_ref(v_paramInfo_552_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v___y_531_ = v_k_543_;
v_todo_532_ = v_a_556_;
goto v___jp_530_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_k_543_);
v_a_557_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_555_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_555_);
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
else
{
lean_object* v___x_565_; 
lean_dec_ref_known(v___x_550_, 1);
lean_dec(v_a_537_);
v___x_565_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(v_nargs_544_, v_todo_545_);
v___y_531_ = v_k_543_;
v_todo_532_ = v___x_565_;
goto v___jp_530_;
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec_ref(v_todo_545_);
lean_dec(v_nargs_544_);
lean_dec(v_k_543_);
lean_dec(v_a_537_);
v_a_566_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_550_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_550_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_todo_517_);
v_a_666_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_536_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_536_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_e_518_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v_todo_517_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_527_, 0, v_v_526_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_todo_517_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
v___jp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_531_);
lean_ctor_set(v___x_533_, 1, v_todo_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_root_516_ = stack[0].m_num;
lean_object* v_todo_517_ = stack[1].m_obj;
lean_object* v_e_518_ = stack[2].m_obj;
uint8_t v_noIndexAtArgs_519_ = stack[3].m_num;
lean_object* v_a_520_ = stack[4].m_obj;
lean_object* v_a_521_ = stack[5].m_obj;
lean_object* v_a_522_ = stack[6].m_obj;
lean_object* v_a_523_ = stack[7].m_obj;
lean_object* v_res_677_;
v_res_677_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_516_, v_todo_517_, v_e_518_, v_noIndexAtArgs_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* v_root_678_, lean_object* v_todo_679_, lean_object* v_e_680_, lean_object* v_noIndexAtArgs_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
uint8_t v_root_boxed_687_; uint8_t v_noIndexAtArgs_boxed_688_; lean_object* v_res_689_; 
v_root_boxed_687_ = lean_unbox(v_root_678_);
v_noIndexAtArgs_boxed_688_ = lean_unbox(v_noIndexAtArgs_681_);
v_res_689_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_boxed_687_, v_todo_679_, v_e_680_, v_noIndexAtArgs_boxed_688_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
return v_res_689_;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t v_root_690_, lean_object* v_todo_691_, lean_object* v_keys_692_, uint8_t v_noIndexAtArgs_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_array_get_size(v_todo_691_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_eq(v___x_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_e_705_; lean_object* v_todo_706_; lean_object* v___x_707_; 
v___x_702_ = l_Lean_instInhabitedExpr;
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_sub(v___x_699_, v___x_703_);
v_e_705_ = lean_array_get(v___x_702_, v_todo_691_, v___x_704_);
lean_dec(v___x_704_);
v_todo_706_ = lean_array_pop(v_todo_691_);
v___x_707_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_690_, v_todo_706_, v_e_705_, v_noIndexAtArgs_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_711_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v_fst_709_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_fst_709_);
v_snd_710_ = lean_ctor_get(v_a_708_, 1);
lean_inc(v_snd_710_);
lean_dec(v_a_708_);
v___x_711_ = lean_array_push(v_keys_692_, v_fst_709_);
v_root_690_ = v___x_701_;
v_todo_691_ = v_snd_710_;
v_keys_692_ = v___x_711_;
goto _start;
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v_keys_692_);
v_a_713_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_707_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_707_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v___x_721_; 
lean_dec_ref(v_todo_691_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_keys_692_);
return v___x_721_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_mkPathAux_0interp(lean_interpreter_value* stack)
{
uint8_t v_root_690_ = stack[0].m_num;
lean_object* v_todo_691_ = stack[1].m_obj;
lean_object* v_keys_692_ = stack[2].m_obj;
uint8_t v_noIndexAtArgs_693_ = stack[3].m_num;
lean_object* v_a_694_ = stack[4].m_obj;
lean_object* v_a_695_ = stack[5].m_obj;
lean_object* v_a_696_ = stack[6].m_obj;
lean_object* v_a_697_ = stack[7].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_Lean_Meta_DiscrTree_mkPathAux(v_root_690_, v_todo_691_, v_keys_692_, v_noIndexAtArgs_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* v_root_723_, lean_object* v_todo_724_, lean_object* v_keys_725_, lean_object* v_noIndexAtArgs_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
uint8_t v_root_boxed_732_; uint8_t v_noIndexAtArgs_boxed_733_; lean_object* v_res_734_; 
v_root_boxed_732_ = lean_unbox(v_root_723_);
v_noIndexAtArgs_boxed_733_ = lean_unbox(v_noIndexAtArgs_726_);
v_res_734_ = l_Lean_Meta_DiscrTree_mkPathAux(v_root_boxed_732_, v_todo_724_, v_keys_725_, v_noIndexAtArgs_boxed_733_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
return v_res_734_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_unsigned_to_nat(8u);
return v___x_735_;
}
}
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* v_e_736_, uint8_t v_noIndexAtArgs_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___y_744_; lean_object* v___x_761_; uint8_t v_transparency_762_; lean_object* v___x_763_; lean_object* v_todo_764_; uint8_t v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; uint8_t v___x_768_; 
v___x_761_ = l_Lean_Meta_Context_config(v_a_738_);
v_transparency_762_ = lean_ctor_get_uint8(v___x_761_, 9);
lean_dec_ref(v___x_761_);
v___x_763_ = lean_unsigned_to_nat(8u);
v_todo_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
v___x_765_ = 1;
lean_inc_ref(v_todo_764_);
v___x_766_ = lean_array_push(v_todo_764_, v_e_736_);
v___x_767_ = 2;
v___x_768_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_762_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v_keyedConfig_769_; uint8_t v_trackZetaDelta_770_; lean_object* v_zetaDeltaSet_771_; lean_object* v_lctx_772_; lean_object* v_localInstances_773_; lean_object* v_defEqCtx_x3f_774_; lean_object* v_synthPendingDepth_775_; lean_object* v_customCanUnfoldPredicate_x3f_776_; uint8_t v_univApprox_777_; uint8_t v_inTypeClassResolution_778_; uint8_t v_cacheInferType_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_keyedConfig_769_ = lean_ctor_get(v_a_738_, 0);
v_trackZetaDelta_770_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*7);
v_zetaDeltaSet_771_ = lean_ctor_get(v_a_738_, 1);
v_lctx_772_ = lean_ctor_get(v_a_738_, 2);
v_localInstances_773_ = lean_ctor_get(v_a_738_, 3);
v_defEqCtx_x3f_774_ = lean_ctor_get(v_a_738_, 4);
v_synthPendingDepth_775_ = lean_ctor_get(v_a_738_, 5);
v_customCanUnfoldPredicate_x3f_776_ = lean_ctor_get(v_a_738_, 6);
v_univApprox_777_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_778_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*7 + 2);
v_cacheInferType_779_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_769_);
v___x_780_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_767_, v_keyedConfig_769_);
lean_inc(v_customCanUnfoldPredicate_x3f_776_);
lean_inc(v_synthPendingDepth_775_);
lean_inc(v_defEqCtx_x3f_774_);
lean_inc_ref(v_localInstances_773_);
lean_inc_ref(v_lctx_772_);
lean_inc(v_zetaDeltaSet_771_);
v___x_781_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_zetaDeltaSet_771_);
lean_ctor_set(v___x_781_, 2, v_lctx_772_);
lean_ctor_set(v___x_781_, 3, v_localInstances_773_);
lean_ctor_set(v___x_781_, 4, v_defEqCtx_x3f_774_);
lean_ctor_set(v___x_781_, 5, v_synthPendingDepth_775_);
lean_ctor_set(v___x_781_, 6, v_customCanUnfoldPredicate_x3f_776_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7, v_trackZetaDelta_770_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7 + 1, v_univApprox_777_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7 + 2, v_inTypeClassResolution_778_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*7 + 3, v_cacheInferType_779_);
v___x_782_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_765_, v___x_766_, v_todo_764_, v_noIndexAtArgs_737_, v___x_781_, v_a_739_, v_a_740_, v_a_741_);
lean_dec_ref_known(v___x_781_, 7);
v___y_744_ = v___x_782_;
goto v___jp_743_;
}
else
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_765_, v___x_766_, v_todo_764_, v_noIndexAtArgs_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
v___y_744_ = v___x_783_;
goto v___jp_743_;
}
v___jp_743_:
{
if (lean_obj_tag(v___y_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v___y_744_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___y_744_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___y_744_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___y_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_753_ = lean_ctor_get(v___y_744_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___y_744_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___y_744_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___y_744_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_mkPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_736_ = stack[0].m_obj;
uint8_t v_noIndexAtArgs_737_ = stack[1].m_num;
lean_object* v_a_738_ = stack[2].m_obj;
lean_object* v_a_739_ = stack[3].m_obj;
lean_object* v_a_740_ = stack[4].m_obj;
lean_object* v_a_741_ = stack[5].m_obj;
lean_object* v_res_784_;
v_res_784_ = l_Lean_Meta_DiscrTree_mkPath(v_e_736_, v_noIndexAtArgs_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object* v_e_785_, lean_object* v_noIndexAtArgs_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_792_; lean_object* v_res_793_; 
v_noIndexAtArgs_boxed_792_ = lean_unbox(v_noIndexAtArgs_786_);
v_res_793_ = l_Lean_Meta_DiscrTree_mkPath(v_e_785_, v_noIndexAtArgs_boxed_792_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
return v_res_793_;
}
}
lean_object* l_Lean_Meta_DiscrTree_insert___redArg(lean_object* v_inst_794_, lean_object* v_d_795_, lean_object* v_e_796_, lean_object* v_v_797_, uint8_t v_noIndexAtArgs_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Meta_DiscrTree_mkPath(v_e_796_, v_noIndexAtArgs_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_794_, v_d_795_, v_a_805_, v_v_797_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_v_797_);
lean_dec_ref(v_d_795_);
lean_dec_ref(v_inst_794_);
v_a_814_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_804_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_804_);
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
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_insert___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_794_ = stack[0].m_obj;
lean_object* v_d_795_ = stack[1].m_obj;
lean_object* v_e_796_ = stack[2].m_obj;
lean_object* v_v_797_ = stack[3].m_obj;
uint8_t v_noIndexAtArgs_798_ = stack[4].m_num;
lean_object* v_a_799_ = stack[5].m_obj;
lean_object* v_a_800_ = stack[6].m_obj;
lean_object* v_a_801_ = stack[7].m_obj;
lean_object* v_a_802_ = stack[8].m_obj;
lean_object* v_res_822_;
v_res_822_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_794_, v_d_795_, v_e_796_, v_v_797_, v_noIndexAtArgs_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
stack->m_obj
 = v_res_822_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg___boxed(lean_object* v_inst_823_, lean_object* v_d_824_, lean_object* v_e_825_, lean_object* v_v_826_, lean_object* v_noIndexAtArgs_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_833_; lean_object* v_res_834_; 
v_noIndexAtArgs_boxed_833_ = lean_unbox(v_noIndexAtArgs_827_);
v_res_834_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_823_, v_d_824_, v_e_825_, v_v_826_, v_noIndexAtArgs_boxed_833_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_834_;
}
}
lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* v_00_u03b1_835_, lean_object* v_inst_836_, lean_object* v_d_837_, lean_object* v_e_838_, lean_object* v_v_839_, uint8_t v_noIndexAtArgs_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_836_, v_d_837_, v_e_838_, v_v_839_, v_noIndexAtArgs_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
return v___x_846_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_insert_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_836_ = stack[1].m_obj;
lean_object* v_d_837_ = stack[2].m_obj;
lean_object* v_e_838_ = stack[3].m_obj;
lean_object* v_v_839_ = stack[4].m_obj;
uint8_t v_noIndexAtArgs_840_ = stack[5].m_num;
lean_object* v_a_841_ = stack[6].m_obj;
lean_object* v_a_842_ = stack[7].m_obj;
lean_object* v_a_843_ = stack[8].m_obj;
lean_object* v_a_844_ = stack[9].m_obj;
lean_object* v_res_847_;
v_res_847_ = l_Lean_Meta_DiscrTree_insert(lean_box(0), v_inst_836_, v_d_837_, v_e_838_, v_v_839_, v_noIndexAtArgs_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___boxed(lean_object* v_00_u03b1_848_, lean_object* v_inst_849_, lean_object* v_d_850_, lean_object* v_e_851_, lean_object* v_v_852_, lean_object* v_noIndexAtArgs_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_859_; lean_object* v_res_860_; 
v_noIndexAtArgs_boxed_859_ = lean_unbox(v_noIndexAtArgs_853_);
v_res_860_ = l_Lean_Meta_DiscrTree_insert(v_00_u03b1_848_, v_inst_849_, v_d_850_, v_e_851_, v_v_852_, v_noIndexAtArgs_boxed_859_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
return v_res_860_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_876_ = lean_array_get_size(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_883_ = lean_array_get_size(v___x_882_);
return v___x_883_;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(lean_object* v_inst_884_, lean_object* v_d_885_, lean_object* v_e_886_, lean_object* v_v_887_, uint8_t v_noIndexAtArgs_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_DiscrTree_mkPath(v_e_886_, v_noIndexAtArgs_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_919_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_919_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_919_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_919_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_912_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_913_ = lean_array_get_size(v_a_895_);
v___x_914_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7);
v___x_915_ = lean_nat_dec_eq(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
goto v___jp_904_;
}
else
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_917_ = l_Array_isEqvAux___redArg(v_a_895_, v___x_912_, v___x_916_, v___x_913_);
if (v___x_917_ == 0)
{
goto v___jp_904_;
}
else
{
lean_object* v___x_918_; 
lean_del_object(v___x_897_);
lean_dec(v_a_895_);
lean_dec(v_v_887_);
lean_dec_ref(v_inst_884_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v_d_885_);
return v___x_918_;
}
}
v___jp_899_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_884_, v_d_885_, v_a_895_, v_v_887_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_900_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
v___jp_904_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_905_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_906_ = lean_array_get_size(v_a_895_);
v___x_907_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4);
v___x_908_ = lean_nat_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
goto v___jp_899_;
}
else
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_910_ = l_Array_isEqvAux___redArg(v_a_895_, v___x_905_, v___x_909_, v___x_906_);
if (v___x_910_ == 0)
{
goto v___jp_899_;
}
else
{
lean_object* v___x_911_; 
lean_del_object(v___x_897_);
lean_dec(v_a_895_);
lean_dec(v_v_887_);
lean_dec_ref(v_inst_884_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v_d_885_);
return v___x_911_;
}
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_v_887_);
lean_dec_ref(v_d_885_);
lean_dec_ref(v_inst_884_);
v_a_920_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_894_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_894_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_insertIfSpecific___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_884_ = stack[0].m_obj;
lean_object* v_d_885_ = stack[1].m_obj;
lean_object* v_e_886_ = stack[2].m_obj;
lean_object* v_v_887_ = stack[3].m_obj;
uint8_t v_noIndexAtArgs_888_ = stack[4].m_num;
lean_object* v_a_889_ = stack[5].m_obj;
lean_object* v_a_890_ = stack[6].m_obj;
lean_object* v_a_891_ = stack[7].m_obj;
lean_object* v_a_892_ = stack[8].m_obj;
lean_object* v_res_928_;
v_res_928_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_884_, v_d_885_, v_e_886_, v_v_887_, v_noIndexAtArgs_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(lean_object* v_inst_929_, lean_object* v_d_930_, lean_object* v_e_931_, lean_object* v_v_932_, lean_object* v_noIndexAtArgs_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_939_; lean_object* v_res_940_; 
v_noIndexAtArgs_boxed_939_ = lean_unbox(v_noIndexAtArgs_933_);
v_res_940_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_929_, v_d_930_, v_e_931_, v_v_932_, v_noIndexAtArgs_boxed_939_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
return v_res_940_;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific(lean_object* v_00_u03b1_941_, lean_object* v_inst_942_, lean_object* v_d_943_, lean_object* v_e_944_, lean_object* v_v_945_, uint8_t v_noIndexAtArgs_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_942_, v_d_943_, v_e_944_, v_v_945_, v_noIndexAtArgs_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_952_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_insertIfSpecific_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_942_ = stack[1].m_obj;
lean_object* v_d_943_ = stack[2].m_obj;
lean_object* v_e_944_ = stack[3].m_obj;
lean_object* v_v_945_ = stack[4].m_obj;
uint8_t v_noIndexAtArgs_946_ = stack[5].m_num;
lean_object* v_a_947_ = stack[6].m_obj;
lean_object* v_a_948_ = stack[7].m_obj;
lean_object* v_a_949_ = stack[8].m_obj;
lean_object* v_a_950_ = stack[9].m_obj;
lean_object* v_res_953_;
v_res_953_ = l_Lean_Meta_DiscrTree_insertIfSpecific(lean_box(0), v_inst_942_, v_d_943_, v_e_944_, v_v_945_, v_noIndexAtArgs_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(lean_object* v_00_u03b1_954_, lean_object* v_inst_955_, lean_object* v_d_956_, lean_object* v_e_957_, lean_object* v_v_958_, lean_object* v_noIndexAtArgs_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_965_; lean_object* v_res_966_; 
v_noIndexAtArgs_boxed_965_ = lean_unbox(v_noIndexAtArgs_959_);
v_res_966_ = l_Lean_Meta_DiscrTree_insertIfSpecific(v_00_u03b1_954_, v_inst_955_, v_d_956_, v_e_957_, v_v_958_, v_noIndexAtArgs_boxed_965_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_966_;
}
}
lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(lean_object* v_declName_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_env_971_; uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_970_ = lean_st_ref_get(v___y_968_);
v_env_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_971_);
lean_dec(v___x_970_);
v___x_972_ = l_Lean_isRecCore(v_env_971_, v_declName_967_);
v___x_973_ = lean_box(v___x_972_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT void l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_967_ = stack[0].m_obj;
lean_object* v___y_968_ = stack[1].m_obj;
lean_object* v_res_975_;
v_res_975_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_967_, v___y_968_);
stack->m_obj
 = v_res_975_;
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_976_, v___y_977_);
lean_dec(v___y_977_);
return v_res_979_;
}
}
lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(lean_object* v_declName_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_980_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT void l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_980_ = stack[0].m_obj;
lean_object* v___y_981_ = stack[1].m_obj;
lean_object* v___y_982_ = stack[2].m_obj;
lean_object* v___y_983_ = stack[3].m_obj;
lean_object* v___y_984_ = stack[4].m_obj;
lean_object* v_res_987_;
v_res_987_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
stack->m_obj
 = v_res_987_;
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(lean_object* v_declName_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_994_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(lean_object* v_a_995_, lean_object* v_b_996_){
_start:
{
lean_object* v_array_998_; lean_object* v_start_999_; lean_object* v_stop_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1017_; 
v_array_998_ = lean_ctor_get(v_a_995_, 0);
v_start_999_ = lean_ctor_get(v_a_995_, 1);
v_stop_1000_ = lean_ctor_get(v_a_995_, 2);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1002_ = v_a_995_;
v_isShared_1003_ = v_isSharedCheck_1017_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_stop_1000_);
lean_inc(v_start_999_);
lean_inc(v_array_998_);
lean_dec(v_a_995_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1017_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_nat_dec_lt(v_start_999_, v_stop_1000_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_del_object(v___x_1002_);
lean_dec(v_stop_1000_);
lean_dec(v_start_999_);
lean_dec_ref(v_array_998_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_b_996_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_nat_add(v_start_999_, v___x_1007_);
lean_inc_ref(v_array_998_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v___x_1008_);
v___x_1010_ = v___x_1002_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_array_998_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_stop_1000_);
v___x_1010_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = lean_array_fget(v_array_998_, v_start_999_);
lean_dec(v_start_999_);
lean_dec_ref(v_array_998_);
v___x_1012_ = l_Lean_Expr_hasExprMVar(v___x_1011_);
lean_dec(v___x_1011_);
if (v___x_1012_ == 0)
{
v_a_995_ = v___x_1010_;
v_b_996_ = v___x_1006_;
goto _start;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref_known(v___x_1014_, 1);
v_a_995_ = v___x_1010_;
v_b_996_ = v___x_1006_;
goto _start;
}
else
{
lean_dec_ref(v___x_1010_);
return v___x_1014_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_995_ = stack[0].m_obj;
lean_object* v_b_996_ = stack[1].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_995_, v_b_996_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1019_, lean_object* v_b_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1019_, v_b_1020_);
return v_res_1022_;
}
}
lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v_env_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1026_ = lean_st_ref_get(v___y_1024_);
v_env_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc_ref(v_env_1027_);
lean_dec(v___x_1026_);
v___x_1028_ = l_Lean_getReducibilityStatusCore(v_env_1027_, v_declName_1023_);
v___x_1029_ = lean_box(v___x_1028_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1023_ = stack[0].m_obj;
lean_object* v___y_1024_ = stack[1].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1023_, v___y_1024_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1032_, v___y_1033_);
lean_dec(v___y_1033_);
return v_res_1035_;
}
}
lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(lean_object* v_declName_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1058_; 
v___x_1042_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1036_, v___y_1040_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1058_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1058_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_unbox(v_a_1043_);
lean_dec(v_a_1043_);
if (v___x_1047_ == 0)
{
uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1048_ = 1;
v___x_1049_ = lean_box(v___x_1048_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = 0;
v___x_1054_ = lean_box(v___x_1053_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1054_);
v___x_1056_ = v___x_1045_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1036_ = stack[0].m_obj;
lean_object* v___y_1037_ = stack[1].m_obj;
lean_object* v___y_1038_ = stack[2].m_obj;
lean_object* v___y_1039_ = stack[3].m_obj;
lean_object* v___y_1040_ = stack[4].m_obj;
lean_object* v_res_1059_;
v_res_1059_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
stack->m_obj
 = v_res_1059_;
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0___boxed(lean_object* v_declName_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1066_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1(void){
_start:
{
lean_object* v___x_1069_; lean_object* v_dummy_1070_; 
v___x_1069_ = lean_box(0);
v_dummy_1070_ = l_Lean_Expr_sort___override(v___x_1069_);
return v_dummy_1070_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* v_e_1077_, uint8_t v_isMatch_1078_, uint8_t v_root_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1077_, v_root_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1242_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1242_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1242_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___y_1091_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; 
if (v_root_1079_ == 0)
{
lean_object* v___x_1230_; 
lean_inc(v_a_1086_);
v___x_1230_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_1086_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1241_; 
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_val_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 2);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_val_1231_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
return v___x_1239_;
}
}
}
else
{
lean_dec(v___x_1230_);
v___y_1101_ = v_a_1080_;
v___y_1102_ = v_a_1081_;
v___y_1103_ = v_a_1082_;
v___y_1104_ = v_a_1083_;
goto v___jp_1100_;
}
}
else
{
v___y_1101_ = v_a_1080_;
v___y_1102_ = v_a_1081_;
v___y_1103_ = v_a_1082_;
v___y_1104_ = v_a_1083_;
goto v___jp_1100_;
}
v___jp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1092_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
lean_inc(v___x_1092_);
v___x_1093_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___y_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_mk_empty_array_with_capacity(v___x_1092_);
lean_dec(v___x_1092_);
v___x_1095_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1086_, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1093_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1096_);
v___x_1098_ = v___x_1088_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
v___jp_1100_:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Expr_getAppFn(v_a_1086_);
switch(lean_obj_tag(v___x_1105_))
{
case 9:
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_a_1106_);
v___x_1108_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
case 4:
{
lean_object* v_declName_1111_; lean_object* v___x_1112_; uint8_t v_isDefEqStuckEx_1113_; 
v_declName_1111_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_declName_1111_);
lean_dec_ref_known(v___x_1105_, 2);
v___x_1112_ = l_Lean_Meta_Context_config(v___y_1101_);
v_isDefEqStuckEx_1113_ = lean_ctor_get_uint8(v___x_1112_, 4);
lean_dec_ref(v___x_1112_);
if (v_isDefEqStuckEx_1113_ == 0)
{
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Lean_Expr_hasExprMVar(v_a_1086_);
if (v___x_1114_ == 0)
{
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1115_; 
lean_inc(v_declName_1111_);
v___x_1115_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1111_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; uint8_t v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_unbox(v_a_1116_);
lean_dec(v_a_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v_env_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_st_ref_get(v___y_1104_);
v_env_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_env_1119_);
lean_dec(v___x_1118_);
v___x_1120_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1119_, v_a_1086_);
if (lean_obj_tag(v___x_1120_) == 1)
{
lean_object* v_val_1121_; lean_object* v_numDiscrs_1122_; lean_object* v_nargs_1123_; lean_object* v_dummy_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_val_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_val_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v_numDiscrs_1122_ = lean_ctor_get(v_val_1121_, 1);
lean_inc(v_numDiscrs_1122_);
v_nargs_1123_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
v_dummy_1124_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
lean_inc(v_nargs_1123_);
v___x_1125_ = lean_mk_array(v_nargs_1123_, v_dummy_1124_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_sub(v_nargs_1123_, v___x_1126_);
lean_dec(v_nargs_1123_);
lean_inc(v_a_1086_);
v___x_1128_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1086_, v___x_1125_, v___x_1127_);
v___x_1129_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1121_);
lean_dec(v_val_1121_);
v___x_1130_ = lean_nat_add(v___x_1129_, v_numDiscrs_1122_);
lean_dec(v_numDiscrs_1122_);
v___x_1131_ = l_Array_toSubarray___redArg(v___x_1128_, v___x_1129_, v___x_1130_);
v___x_1132_ = lean_box(0);
v___x_1133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_1131_, v___x_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref_known(v___x_1133_, 1);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_declName_1111_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v___x_1142_; lean_object* v_a_1143_; uint8_t v___x_1144_; 
lean_dec(v___x_1120_);
lean_inc(v_declName_1111_);
v___x_1142_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_1111_, v___y_1104_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = lean_unbox(v_a_1143_);
lean_dec(v_a_1143_);
if (v___x_1144_ == 0)
{
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_dec_ref_known(v___x_1145_, 1);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_declName_1111_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_dec_ref_known(v___x_1154_, 1);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_declName_1111_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_declName_1111_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1163_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1115_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1115_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_del_object(v___x_1088_);
v_fvarId_1171_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_fvarId_1171_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1172_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
lean_inc(v___x_1172_);
v___x_1173_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_fvarId_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_mk_empty_array_with_capacity(v___x_1172_);
lean_dec(v___x_1172_);
v___x_1175_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1086_, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
case 2:
{
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
if (v_isMatch_1078_ == 0)
{
lean_object* v_mvarId_1178_; lean_object* v___x_1179_; uint8_t v_isDefEqStuckEx_1180_; 
v_mvarId_1178_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_mvarId_1178_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1179_ = l_Lean_Meta_Context_config(v___y_1101_);
v_isDefEqStuckEx_1180_ = lean_ctor_get_uint8(v___x_1179_, 4);
lean_dec_ref(v___x_1179_);
if (v_isDefEqStuckEx_1180_ == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1178_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1195_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_unbox(v_a_1182_);
lean_dec(v_a_1182_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1191_);
v___x_1193_ = v___x_1184_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_a_1196_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1181_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1181_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_mvarId_1178_);
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec_ref_known(v___x_1105_, 1);
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
case 11:
{
lean_object* v_typeName_1208_; lean_object* v_idx_1209_; lean_object* v_struct_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_del_object(v___x_1088_);
v_typeName_1208_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_typeName_1208_);
v_idx_1209_ = lean_ctor_get(v___x_1105_, 1);
lean_inc(v_idx_1209_);
v_struct_1210_ = lean_ctor_get(v___x_1105_, 2);
lean_inc_ref(v_struct_1210_);
lean_dec_ref_known(v___x_1105_, 3);
v___x_1211_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
lean_inc(v___x_1211_);
v___x_1212_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1212_, 0, v_typeName_1208_);
lean_ctor_set(v___x_1212_, 1, v_idx_1209_);
lean_ctor_set(v___x_1212_, 2, v___x_1211_);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = lean_mk_empty_array_with_capacity(v___x_1213_);
v___x_1215_ = lean_array_push(v___x_1214_, v_struct_1210_);
v___x_1216_ = lean_mk_empty_array_with_capacity(v___x_1211_);
lean_dec(v___x_1211_);
v___x_1217_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1086_, v___x_1216_);
v___x_1218_ = l_Array_append___redArg(v___x_1215_, v___x_1217_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1212_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
case 7:
{
lean_object* v_binderType_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_binderType_1221_ = lean_ctor_get(v___x_1105_, 1);
lean_inc_ref(v_binderType_1221_);
lean_dec_ref_known(v___x_1105_, 3);
v___x_1222_ = lean_box(5);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_mk_empty_array_with_capacity(v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1224_, v_binderType_1221_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1222_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
default: 
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v___x_1105_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v___x_1228_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_a_1243_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1085_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1085_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1077_ = stack[0].m_obj;
uint8_t v_isMatch_1078_ = stack[1].m_num;
uint8_t v_root_1079_ = stack[2].m_num;
lean_object* v_a_1080_ = stack[3].m_obj;
lean_object* v_a_1081_ = stack[4].m_obj;
lean_object* v_a_1082_ = stack[5].m_obj;
lean_object* v_a_1083_ = stack[6].m_obj;
lean_object* v_res_1251_;
v_res_1251_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1077_, v_isMatch_1078_, v_root_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
stack->m_obj
 = v_res_1251_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* v_e_1252_, lean_object* v_isMatch_1253_, lean_object* v_root_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
uint8_t v_isMatch_boxed_1260_; uint8_t v_root_boxed_1261_; lean_object* v_res_1262_; 
v_isMatch_boxed_1260_ = lean_unbox(v_isMatch_1253_);
v_root_boxed_1261_ = lean_unbox(v_root_1254_);
v_res_1262_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1252_, v_isMatch_boxed_1260_, v_root_boxed_1261_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
return v_res_1262_;
}
}
lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1263_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1263_ = stack[0].m_obj;
lean_object* v___y_1264_ = stack[1].m_obj;
lean_object* v___y_1265_ = stack[2].m_obj;
lean_object* v___y_1266_ = stack[3].m_obj;
lean_object* v___y_1267_ = stack[4].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1277_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object* v_inst_1278_, lean_object* v_R_1279_, lean_object* v_a_1280_, lean_object* v_b_1281_, lean_object* v_c_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1280_, v_b_1281_);
return v___x_1288_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1280_ = stack[2].m_obj;
lean_object* v_b_1281_ = stack[3].m_obj;
lean_object* v___y_1283_ = stack[5].m_obj;
lean_object* v___y_1284_ = stack[6].m_obj;
lean_object* v___y_1285_ = stack[7].m_obj;
lean_object* v___y_1286_ = stack[8].m_obj;
lean_object* v_res_1289_;
v_res_1289_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_box(0), lean_box(0), v_a_1280_, v_b_1281_, lean_box(0), v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
stack->m_obj
 = v_res_1289_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object* v_inst_1290_, lean_object* v_R_1291_, lean_object* v_a_1292_, lean_object* v_b_1293_, lean_object* v_c_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_1290_, v_R_1291_, v_a_1292_, v_b_1293_, v_c_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* v_e_1301_, uint8_t v_root_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
uint8_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = 1;
v___x_1309_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1301_, v___x_1308_, v_root_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1309_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1301_ = stack[0].m_obj;
uint8_t v_root_1302_ = stack[1].m_num;
lean_object* v_a_1303_ = stack[2].m_obj;
lean_object* v_a_1304_ = stack[3].m_obj;
lean_object* v_a_1305_ = stack[4].m_obj;
lean_object* v_a_1306_ = stack[5].m_obj;
lean_object* v_res_1310_;
v_res_1310_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1301_, v_root_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
stack->m_obj
 = v_res_1310_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* v_e_1311_, lean_object* v_root_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
uint8_t v_root_boxed_1318_; lean_object* v_res_1319_; 
v_root_boxed_1318_ = lean_unbox(v_root_1312_);
v_res_1319_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1311_, v_root_boxed_1318_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1319_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* v_e_1320_, uint8_t v_root_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
uint8_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = 0;
v___x_1328_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1320_, v___x_1327_, v_root_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v___x_1328_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1320_ = stack[0].m_obj;
uint8_t v_root_1321_ = stack[1].m_num;
lean_object* v_a_1322_ = stack[2].m_obj;
lean_object* v_a_1323_ = stack[3].m_obj;
lean_object* v_a_1324_ = stack[4].m_obj;
lean_object* v_a_1325_ = stack[5].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1320_, v_root_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* v_e_1330_, lean_object* v_root_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
uint8_t v_root_boxed_1337_; lean_object* v_res_1338_; 
v_root_boxed_1337_ = lean_unbox(v_root_1331_);
v_res_1338_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1330_, v_root_boxed_1337_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1339_, lean_object* v_vals_1340_, lean_object* v_i_1341_, lean_object* v_k_1342_){
_start:
{
lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1343_ = lean_array_get_size(v_keys_1339_);
v___x_1344_ = lean_nat_dec_lt(v_i_1341_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_dec(v_i_1341_);
v___x_1345_ = lean_box(0);
return v___x_1345_;
}
else
{
lean_object* v_k_x27_1346_; uint8_t v___x_1347_; 
v_k_x27_1346_ = lean_array_fget_borrowed(v_keys_1339_, v_i_1341_);
v___x_1347_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1342_, v_k_x27_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_add(v_i_1341_, v___x_1348_);
lean_dec(v_i_1341_);
v_i_1341_ = v___x_1349_;
goto _start;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_array_fget_borrowed(v_vals_1340_, v_i_1341_);
lean_dec(v_i_1341_);
lean_inc(v___x_1351_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1353_, lean_object* v_vals_1354_, lean_object* v_i_1355_, lean_object* v_k_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1353_, v_vals_1354_, v_i_1355_, v_k_1356_);
lean_dec(v_k_1356_);
lean_dec_ref(v_vals_1354_);
lean_dec_ref(v_keys_1353_);
return v_res_1357_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1358_, size_t v_x_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v_es_1361_; lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v_j_1365_; lean_object* v___x_1366_; 
v_es_1361_ = lean_ctor_get(v_x_1358_, 0);
v___x_1362_ = lean_box(2);
v___x_1363_ = ((size_t)31ULL);
v___x_1364_ = lean_usize_land(v_x_1359_, v___x_1363_);
v_j_1365_ = lean_usize_to_nat(v___x_1364_);
v___x_1366_ = lean_array_get_borrowed(v___x_1362_, v_es_1361_, v_j_1365_);
lean_dec(v_j_1365_);
switch(lean_obj_tag(v___x_1366_))
{
case 0:
{
lean_object* v_key_1367_; lean_object* v_val_1368_; uint8_t v___x_1369_; 
v_key_1367_ = lean_ctor_get(v___x_1366_, 0);
v_val_1368_ = lean_ctor_get(v___x_1366_, 1);
v___x_1369_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1360_, v_key_1367_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_box(0);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; 
lean_inc(v_val_1368_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_val_1368_);
return v___x_1371_;
}
}
case 1:
{
lean_object* v_node_1372_; size_t v___x_1373_; size_t v___x_1374_; 
v_node_1372_ = lean_ctor_get(v___x_1366_, 0);
v___x_1373_ = ((size_t)5ULL);
v___x_1374_ = lean_usize_shift_right(v_x_1359_, v___x_1373_);
v_x_1358_ = v_node_1372_;
v_x_1359_ = v___x_1374_;
goto _start;
}
default: 
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
}
}
else
{
lean_object* v_ks_1377_; lean_object* v_vs_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_ks_1377_ = lean_ctor_get(v_x_1358_, 0);
v_vs_1378_ = lean_ctor_get(v_x_1358_, 1);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1377_, v_vs_1378_, v___x_1379_, v_x_1360_);
return v___x_1380_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1358_ = stack[0].m_obj;
size_t v_x_1359_ = stack[1].m_num;
lean_object* v_x_1360_ = stack[2].m_obj;
lean_object* v_res_1381_;
v_res_1381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1358_, v_x_1359_, v_x_1360_);
stack->m_obj
 = v_res_1381_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
size_t v_x_193__boxed_1385_; lean_object* v_res_1386_; 
v_x_193__boxed_1385_ = lean_unbox_usize(v_x_1383_);
lean_dec(v_x_1383_);
v_res_1386_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1382_, v_x_193__boxed_1385_, v_x_1384_);
lean_dec(v_x_1384_);
lean_dec_ref(v_x_1382_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
uint64_t v___x_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1388_);
v___x_1390_ = lean_uint64_to_usize(v___x_1389_);
v___x_1391_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1387_, v___x_1390_, v_x_1388_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1392_, v_x_1393_);
lean_dec(v_x_1393_);
lean_dec_ref(v_x_1392_);
return v_res_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_result_1399_; lean_object* v___x_1400_; 
v___x_1397_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_1398_ = lean_unsigned_to_nat(8u);
v_result_1399_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1400_ = l_Array_append___redArg(v_result_1399_, v___x_1397_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v_result_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = lean_unsigned_to_nat(8u);
v_result_1403_ = lean_mk_empty_array_with_capacity(v___x_1402_);
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1401_, v___x_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
return v_result_1403_;
}
else
{
lean_object* v_val_1406_; 
v_val_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v___x_1405_, 1);
if (lean_obj_tag(v_val_1406_) == 0)
{
lean_object* v___x_1407_; 
lean_dec_ref_known(v_val_1406_, 2);
lean_dec_ref(v_result_1403_);
v___x_1407_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1);
return v___x_1407_;
}
else
{
lean_object* v_vs_1408_; lean_object* v___x_1409_; 
v_vs_1408_ = lean_ctor_get(v_val_1406_, 0);
lean_inc_ref(v_vs_1408_);
lean_dec_ref_known(v_val_1406_, 2);
v___x_1409_ = l_Array_append___redArg(v_result_1403_, v_vs_1408_);
lean_dec_ref(v_vs_1408_);
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___boxed(lean_object* v_d_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1410_);
lean_dec_ref(v_d_1410_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1412_, lean_object* v_d_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_d_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(v_00_u03b1_1415_, v_d_1416_);
lean_dec_ref(v_d_1416_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1419_, v_x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1422_, v_x_1423_, v_x_1424_);
lean_dec(v_x_1424_);
lean_dec_ref(v_x_1423_);
return v_res_1425_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, size_t v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1427_, v_x_1428_, v_x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1427_ = stack[1].m_obj;
size_t v_x_1428_ = stack[2].m_num;
lean_object* v_x_1429_ = stack[3].m_obj;
lean_object* v_res_1431_;
v_res_1431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_box(0), v_x_1427_, v_x_1428_, v_x_1429_);
stack->m_obj
 = v_res_1431_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
size_t v_x_344__boxed_1436_; lean_object* v_res_1437_; 
v_x_344__boxed_1436_ = lean_unbox_usize(v_x_1434_);
lean_dec(v_x_1434_);
v_res_1437_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1432_, v_x_1433_, v_x_344__boxed_1436_, v_x_1435_);
lean_dec(v_x_1435_);
lean_dec_ref(v_x_1433_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1438_, lean_object* v_keys_1439_, lean_object* v_vals_1440_, lean_object* v_heq_1441_, lean_object* v_i_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1439_, v_vals_1440_, v_i_1442_, v_k_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1445_, lean_object* v_keys_1446_, lean_object* v_vals_1447_, lean_object* v_heq_1448_, lean_object* v_i_1449_, lean_object* v_k_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1445_, v_keys_1446_, v_vals_1447_, v_heq_1448_, v_i_1449_, v_k_1450_);
lean_dec(v_k_1450_);
lean_dec_ref(v_vals_1447_);
lean_dec_ref(v_keys_1446_);
return v_res_1451_;
}
}
uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object* v_a_1452_, lean_object* v_b_1453_){
_start:
{
lean_object* v_fst_1454_; lean_object* v_fst_1455_; uint8_t v___x_1456_; 
v_fst_1454_ = lean_ctor_get(v_a_1452_, 0);
v_fst_1455_ = lean_ctor_get(v_b_1453_, 0);
v___x_1456_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1454_, v_fst_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1452_ = stack[0].m_obj;
lean_object* v_b_1453_ = stack[1].m_obj;
uint8_t v_res_1457_;
v_res_1457_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1452_, v_b_1453_);
stack->m_num = v_res_1457_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object* v_a_1458_, lean_object* v_b_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1458_, v_b_1459_);
lean_dec_ref(v_b_1459_);
lean_dec_ref(v_a_1458_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1466_, lean_object* v_k_1467_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_array_get_size(v_cs_1466_);
v___x_1470_ = lean_nat_dec_lt(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; 
lean_dec(v_k_1467_);
v___x_1471_ = lean_box(0);
return v___x_1471_;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_sub(v___x_1469_, v___x_1472_);
v___x_1474_ = lean_nat_dec_le(v___x_1468_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec(v___x_1473_);
lean_dec(v_k_1467_);
v___x_1475_ = lean_box(0);
return v___x_1475_;
}
else
{
lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___f_1476_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1477_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_k_1467_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1480_ = l_Array_binSearchAux___redArg(v___f_1476_, v___x_1479_, v_cs_1466_, v___x_1478_, v___x_1468_, v___x_1473_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1481_, lean_object* v_k_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1481_, v_k_1482_);
lean_dec_ref(v_cs_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1484_, lean_object* v_cs_1485_, lean_object* v_k_1486_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = lean_array_get_size(v_cs_1485_);
v___x_1489_ = lean_nat_dec_lt(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec(v_k_1486_);
v___x_1490_ = lean_box(0);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = lean_nat_sub(v___x_1488_, v___x_1491_);
v___x_1493_ = lean_nat_dec_le(v___x_1487_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_dec(v___x_1492_);
lean_dec(v_k_1486_);
v___x_1494_ = lean_box(0);
return v___x_1494_;
}
else
{
lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___f_1495_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1496_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_k_1486_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1499_ = l_Array_binSearchAux___redArg(v___f_1495_, v___x_1498_, v_cs_1485_, v___x_1497_, v___x_1487_, v___x_1492_);
return v___x_1499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1500_, lean_object* v_cs_1501_, lean_object* v_k_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1500_, v_cs_1501_, v_k_1502_);
lean_dec_ref(v_cs_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1504_, lean_object* v_k_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_m_1510_; lean_object* v_a_1511_; uint8_t v___x_1512_; 
v___x_1508_ = lean_nat_add(v_x_1506_, v_x_1507_);
v___x_1509_ = lean_unsigned_to_nat(1u);
v_m_1510_ = lean_nat_shiftr(v___x_1508_, v___x_1509_);
lean_dec(v___x_1508_);
v_a_1511_ = lean_array_fget_borrowed(v_as_1504_, v_m_1510_);
v___x_1512_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1511_, v_k_1505_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; 
lean_dec(v_x_1507_);
v___x_1513_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1505_, v_a_1511_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
lean_dec(v_m_1510_);
lean_dec(v_x_1506_);
lean_inc(v_a_1511_);
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1511_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = lean_nat_dec_eq(v_m_1510_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = lean_nat_sub(v_m_1510_, v___x_1509_);
lean_dec(v_m_1510_);
v___x_1518_ = lean_nat_dec_lt(v___x_1517_, v_x_1506_);
if (v___x_1518_ == 0)
{
v_x_1507_ = v___x_1517_;
goto _start;
}
else
{
lean_object* v___x_1520_; 
lean_dec(v___x_1517_);
lean_dec(v_x_1506_);
v___x_1520_ = lean_box(0);
return v___x_1520_;
}
}
else
{
lean_object* v___x_1521_; 
lean_dec(v_m_1510_);
lean_dec(v_x_1506_);
v___x_1521_ = lean_box(0);
return v___x_1521_;
}
}
}
else
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
lean_dec(v_x_1506_);
v___x_1522_ = lean_nat_add(v_m_1510_, v___x_1509_);
lean_dec(v_m_1510_);
v___x_1523_ = lean_nat_dec_le(v___x_1522_, v_x_1507_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; 
lean_dec(v___x_1522_);
lean_dec(v_x_1507_);
v___x_1524_ = lean_box(0);
return v___x_1524_;
}
else
{
v_x_1506_ = v___x_1522_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1526_, lean_object* v_k_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1526_, v_k_1527_, v_x_1528_, v_x_1529_);
lean_dec_ref(v_k_1527_);
lean_dec_ref(v_as_1526_);
return v_res_1530_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg();
return v___x_1531_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1532_);
return v___x_1534_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1535_, lean_object* v_c_1536_, lean_object* v_result_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_c_1536_) == 0)
{
lean_object* v_key_1544_; lean_object* v_child_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_key_1544_ = lean_ctor_get(v_c_1536_, 0);
lean_inc(v_key_1544_);
v_child_1545_ = lean_ctor_get(v_c_1536_, 1);
lean_inc_ref(v_child_1545_);
lean_dec_ref_known(v_c_1536_, 2);
v___x_1546_ = lean_array_get_size(v_todo_1535_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_e_1551_; lean_object* v_todo_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_sub(v___x_1546_, v___x_1549_);
v_e_1551_ = lean_array_get(v___x_1543_, v_todo_1535_, v___x_1550_);
lean_dec(v___x_1550_);
v_todo_1552_ = lean_array_pop(v_todo_1535_);
v___x_1553_ = 1;
v___x_1554_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1551_, v___x_1553_, v___x_1548_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1570_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1570_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1570_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_fst_1559_; lean_object* v_snd_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_fst_1559_ = lean_ctor_get(v_a_1555_, 0);
lean_inc(v_fst_1559_);
v_snd_1560_ = lean_ctor_get(v_a_1555_, 1);
lean_inc(v_snd_1560_);
lean_dec(v_a_1555_);
v___x_1561_ = lean_box(0);
v___x_1562_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1544_, v___x_1561_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; 
v___x_1563_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1544_, v_fst_1559_);
lean_dec(v_fst_1559_);
lean_dec(v_key_1544_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1565_; 
lean_dec(v_snd_1560_);
lean_dec_ref(v_todo_1552_);
lean_dec_ref(v_child_1545_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v_result_1537_);
v___x_1565_ = v___x_1557_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_result_1537_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
else
{
lean_object* v___x_1567_; 
lean_del_object(v___x_1557_);
v___x_1567_ = l_Array_append___redArg(v_todo_1552_, v_snd_1560_);
lean_dec(v_snd_1560_);
v_todo_1535_ = v___x_1567_;
v_c_1536_ = v_child_1545_;
goto _start;
}
}
else
{
lean_dec(v_snd_1560_);
lean_dec(v_fst_1559_);
lean_del_object(v___x_1557_);
lean_dec(v_key_1544_);
v_todo_1535_ = v_todo_1552_;
v_c_1536_ = v_child_1545_;
goto _start;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v_todo_1552_);
lean_dec_ref(v_child_1545_);
lean_dec(v_key_1544_);
lean_dec_ref(v_result_1537_);
v_a_1571_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1554_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1554_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v___x_1579_; 
lean_dec_ref(v_child_1545_);
lean_dec(v_key_1544_);
lean_dec_ref(v_todo_1535_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_result_1537_);
return v___x_1579_;
}
}
else
{
lean_object* v_vs_1580_; lean_object* v_children_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_vs_1580_ = lean_ctor_get(v_c_1536_, 0);
lean_inc_ref(v_vs_1580_);
v_children_1581_ = lean_ctor_get(v_c_1536_, 1);
lean_inc_ref(v_children_1581_);
lean_dec_ref_known(v_c_1536_, 2);
v___x_1582_ = lean_array_get_size(v_todo_1535_);
v___x_1583_ = lean_unsigned_to_nat(0u);
v___x_1584_ = lean_nat_dec_eq(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
lean_dec_ref(v_vs_1580_);
v___x_1585_ = lean_array_get_size(v_children_1581_);
v___x_1586_ = lean_nat_dec_eq(v___x_1585_, v___x_1583_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_e_1591_; lean_object* v_todo_1592_; lean_object* v_first_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = lean_nat_sub(v___x_1582_, v___x_1589_);
v_e_1591_ = lean_array_get(v___x_1543_, v_todo_1535_, v___x_1590_);
lean_dec(v___x_1590_);
v_todo_1592_ = lean_array_pop(v_todo_1535_);
v_first_1593_ = lean_array_get_borrowed(v___x_1588_, v_children_1581_, v___x_1583_);
v___x_1594_ = 1;
v___x_1595_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1591_, v___x_1594_, v___x_1586_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1629_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1629_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1629_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1628_; 
v_fst_1600_ = lean_ctor_get(v_a_1596_, 0);
v_snd_1601_ = lean_ctor_get(v_a_1596_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_a_1596_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1603_ = v_a_1596_;
v_isShared_1604_ = v_isSharedCheck_1628_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_snd_1601_);
lean_inc(v_fst_1600_);
lean_dec(v_a_1596_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1628_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___y_1606_; lean_object* v_a_1607_; lean_object* v_fst_1620_; lean_object* v_snd_1621_; uint8_t v___x_1622_; 
v_fst_1620_ = lean_ctor_get(v_first_1593_, 0);
v_snd_1621_ = lean_ctor_get(v_first_1593_, 1);
v___x_1622_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1620_, v___x_1587_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1624_; 
lean_inc_ref(v_result_1537_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v_result_1537_);
v___x_1624_ = v___x_1598_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_result_1537_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
v___y_1606_ = v___x_1624_;
v_a_1607_ = v_result_1537_;
goto v___jp_1605_;
}
}
else
{
lean_object* v___x_1626_; 
lean_del_object(v___x_1598_);
lean_inc(v_snd_1621_);
lean_inc_ref(v_todo_1592_);
v___x_1626_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1592_, v_snd_1621_, v_result_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
v___y_1606_ = v___x_1626_;
v_a_1607_ = v_a_1627_;
goto v___jp_1605_;
}
else
{
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
lean_dec(v_fst_1600_);
lean_dec_ref(v_todo_1592_);
lean_dec_ref(v_children_1581_);
return v___x_1626_;
}
}
v___jp_1605_:
{
if (lean_obj_tag(v_fst_1600_) == 0)
{
lean_dec_ref(v_a_1607_);
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
lean_dec_ref(v_todo_1592_);
lean_dec_ref(v_children_1581_);
return v___y_1606_;
}
else
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_nat_dec_lt(v___x_1583_, v___x_1585_);
if (v___x_1608_ == 0)
{
lean_dec_ref(v_a_1607_);
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
lean_dec(v_fst_1600_);
lean_dec_ref(v_todo_1592_);
lean_dec_ref(v_children_1581_);
return v___y_1606_;
}
else
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_nat_sub(v___x_1585_, v___x_1589_);
v___x_1610_ = lean_nat_dec_le(v___x_1583_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_dec(v___x_1609_);
lean_dec_ref(v_a_1607_);
lean_del_object(v___x_1603_);
lean_dec(v_snd_1601_);
lean_dec(v_fst_1600_);
lean_dec_ref(v_todo_1592_);
lean_dec_ref(v_children_1581_);
return v___y_1606_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1611_);
v___x_1613_ = v___x_1603_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_fst_1600_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1581_, v___x_1613_, v___x_1583_, v___x_1609_);
lean_dec_ref(v___x_1613_);
lean_dec_ref(v_children_1581_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec_ref(v_a_1607_);
lean_dec(v_snd_1601_);
lean_dec_ref(v_todo_1592_);
return v___y_1606_;
}
else
{
lean_object* v_val_1615_; lean_object* v_snd_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v___y_1606_);
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v_snd_1616_ = lean_ctor_get(v_val_1615_, 1);
lean_inc(v_snd_1616_);
lean_dec(v_val_1615_);
v___x_1617_ = l_Array_append___redArg(v_todo_1592_, v_snd_1601_);
lean_dec(v_snd_1601_);
v_todo_1535_ = v___x_1617_;
v_c_1536_ = v_snd_1616_;
v_result_1537_ = v_a_1607_;
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
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_todo_1592_);
lean_dec_ref(v_children_1581_);
lean_dec_ref(v_result_1537_);
v_a_1630_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1595_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1595_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v___x_1638_; 
lean_dec_ref(v_children_1581_);
lean_dec_ref(v_todo_1535_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_result_1537_);
return v___x_1638_;
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_children_1581_);
lean_dec_ref(v_todo_1535_);
v___x_1639_ = l_Array_append___redArg(v_result_1537_, v_vs_1580_);
lean_dec_ref(v_vs_1580_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_1535_ = stack[0].m_obj;
lean_object* v_c_1536_ = stack[1].m_obj;
lean_object* v_result_1537_ = stack[2].m_obj;
lean_object* v_a_1538_ = stack[3].m_obj;
lean_object* v_a_1539_ = stack[4].m_obj;
lean_object* v_a_1540_ = stack[5].m_obj;
lean_object* v_a_1541_ = stack[6].m_obj;
lean_object* v_res_1641_;
v_res_1641_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1535_, v_c_1536_, v_result_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
stack->m_obj
 = v_res_1641_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1642_, lean_object* v_c_1643_, lean_object* v_result_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1642_, v_c_1643_, v_result_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1650_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1651_, lean_object* v_todo_1652_, lean_object* v_c_1653_, lean_object* v_result_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1652_, v_c_1653_, v_result_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_1652_ = stack[1].m_obj;
lean_object* v_c_1653_ = stack[2].m_obj;
lean_object* v_result_1654_ = stack[3].m_obj;
lean_object* v_a_1655_ = stack[4].m_obj;
lean_object* v_a_1656_ = stack[5].m_obj;
lean_object* v_a_1657_ = stack[6].m_obj;
lean_object* v_a_1658_ = stack[7].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_box(0), v_todo_1652_, v_c_1653_, v_result_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_todo_1663_, lean_object* v_c_1664_, lean_object* v_result_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1662_, v_todo_1663_, v_c_1664_, v_result_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1672_, lean_object* v_as_1673_, lean_object* v_k_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1673_, v_k_1674_, v_x_1675_, v_x_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_as_1680_, lean_object* v_k_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1679_, v_as_1680_, v_k_1681_, v_x_1682_, v_x_1683_, v_x_1684_);
lean_dec_ref(v_k_1681_);
lean_dec_ref(v_as_1680_);
return v_res_1685_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1686_, lean_object* v_k_1687_, lean_object* v_args_1688_, lean_object* v_result_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1686_, v_k_1687_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref(v_args_1688_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_result_1689_);
return v___x_1696_;
}
else
{
lean_object* v_val_1697_; lean_object* v___x_1698_; 
v_val_1697_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1698_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1688_, v_val_1697_, v_result_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1698_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1686_ = stack[0].m_obj;
lean_object* v_k_1687_ = stack[1].m_obj;
lean_object* v_args_1688_ = stack[2].m_obj;
lean_object* v_result_1689_ = stack[3].m_obj;
lean_object* v_a_1690_ = stack[4].m_obj;
lean_object* v_a_1691_ = stack[5].m_obj;
lean_object* v_a_1692_ = stack[6].m_obj;
lean_object* v_a_1693_ = stack[7].m_obj;
lean_object* v_res_1699_;
v_res_1699_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1686_, v_k_1687_, v_args_1688_, v_result_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
stack->m_obj
 = v_res_1699_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1700_, lean_object* v_k_1701_, lean_object* v_args_1702_, lean_object* v_result_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1700_, v_k_1701_, v_args_1702_, v_result_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_k_1701_);
lean_dec_ref(v_d_1700_);
return v_res_1709_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1710_, lean_object* v_d_1711_, lean_object* v_k_1712_, lean_object* v_args_1713_, lean_object* v_result_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1711_, v_k_1712_, v_args_1713_, v_result_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1711_ = stack[1].m_obj;
lean_object* v_k_1712_ = stack[2].m_obj;
lean_object* v_args_1713_ = stack[3].m_obj;
lean_object* v_result_1714_ = stack[4].m_obj;
lean_object* v_a_1715_ = stack[5].m_obj;
lean_object* v_a_1716_ = stack[6].m_obj;
lean_object* v_a_1717_ = stack[7].m_obj;
lean_object* v_a_1718_ = stack[8].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_box(0), v_d_1711_, v_k_1712_, v_args_1713_, v_result_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_d_1723_, lean_object* v_k_1724_, lean_object* v_args_1725_, lean_object* v_result_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1722_, v_d_1723_, v_k_1724_, v_args_1725_, v_result_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_k_1724_);
lean_dec_ref(v_d_1723_);
return v_res_1732_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(lean_object* v_e_1733_, uint8_t v___x_1734_, lean_object* v_result_1735_, lean_object* v_d_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1733_, v___x_1734_, v___x_1734_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1786_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1786_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1786_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_fst_1747_; 
v_fst_1747_ = lean_ctor_get(v_a_1743_, 0);
lean_inc(v_fst_1747_);
if (lean_obj_tag(v_fst_1747_) == 0)
{
lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1757_; 
v_isSharedCheck_1757_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; lean_object* v_unused_1759_; 
v_unused_1758_ = lean_ctor_get(v_a_1743_, 1);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_a_1743_, 0);
lean_dec(v_unused_1759_);
v___x_1749_ = v_a_1743_;
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
else
{
lean_dec(v_a_1743_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v_result_1735_);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_fst_1747_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_result_1735_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1752_);
v___x_1754_ = v___x_1745_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_snd_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1784_; 
lean_del_object(v___x_1745_);
v_snd_1760_ = lean_ctor_get(v_a_1743_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_a_1743_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v_a_1743_, 0);
lean_dec(v_unused_1785_);
v___x_1762_ = v_a_1743_;
v_isShared_1763_ = v_isSharedCheck_1784_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_snd_1760_);
lean_dec(v_a_1743_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1784_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1736_, v_fst_1747_, v_snd_1760_, v_result_1735_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1775_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v_a_1765_);
v___x_1770_ = v___x_1762_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_fst_1747_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_del_object(v___x_1762_);
lean_dec(v_fst_1747_);
v_a_1776_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1764_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1764_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_result_1735_);
v_a_1787_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1742_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1742_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1733_ = stack[0].m_obj;
uint8_t v___x_1734_ = stack[1].m_num;
lean_object* v_result_1735_ = stack[2].m_obj;
lean_object* v_d_1736_ = stack[3].m_obj;
lean_object* v___y_1737_ = stack[4].m_obj;
lean_object* v___y_1738_ = stack[5].m_obj;
lean_object* v___y_1739_ = stack[6].m_obj;
lean_object* v___y_1740_ = stack[7].m_obj;
lean_object* v_res_1795_;
v_res_1795_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1733_, v___x_1734_, v_result_1735_, v_d_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
stack->m_obj
 = v_res_1795_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0___boxed(lean_object* v_e_1796_, lean_object* v___x_1797_, lean_object* v_result_1798_, lean_object* v_d_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v___x_802__boxed_1805_; lean_object* v_res_1806_; 
v___x_802__boxed_1805_ = lean_unbox(v___x_1797_);
v_res_1806_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1796_, v___x_802__boxed_1805_, v_result_1798_, v_d_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_d_1799_);
return v_res_1806_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1807_, lean_object* v_e_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v___y_1815_; lean_object* v___x_1832_; uint8_t v_transparency_1833_; lean_object* v_result_1834_; uint8_t v___x_1835_; uint8_t v___x_1836_; uint8_t v___x_1837_; 
v___x_1832_ = l_Lean_Meta_Context_config(v_a_1809_);
v_transparency_1833_ = lean_ctor_get_uint8(v___x_1832_, 9);
lean_dec_ref(v___x_1832_);
v_result_1834_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1807_);
v___x_1835_ = 1;
v___x_1836_ = 2;
v___x_1837_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1833_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v_keyedConfig_1838_; uint8_t v_trackZetaDelta_1839_; lean_object* v_zetaDeltaSet_1840_; lean_object* v_lctx_1841_; lean_object* v_localInstances_1842_; lean_object* v_defEqCtx_x3f_1843_; lean_object* v_synthPendingDepth_1844_; lean_object* v_customCanUnfoldPredicate_x3f_1845_; uint8_t v_univApprox_1846_; uint8_t v_inTypeClassResolution_1847_; uint8_t v_cacheInferType_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_keyedConfig_1838_ = lean_ctor_get(v_a_1809_, 0);
v_trackZetaDelta_1839_ = lean_ctor_get_uint8(v_a_1809_, sizeof(void*)*7);
v_zetaDeltaSet_1840_ = lean_ctor_get(v_a_1809_, 1);
v_lctx_1841_ = lean_ctor_get(v_a_1809_, 2);
v_localInstances_1842_ = lean_ctor_get(v_a_1809_, 3);
v_defEqCtx_x3f_1843_ = lean_ctor_get(v_a_1809_, 4);
v_synthPendingDepth_1844_ = lean_ctor_get(v_a_1809_, 5);
v_customCanUnfoldPredicate_x3f_1845_ = lean_ctor_get(v_a_1809_, 6);
v_univApprox_1846_ = lean_ctor_get_uint8(v_a_1809_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1847_ = lean_ctor_get_uint8(v_a_1809_, sizeof(void*)*7 + 2);
v_cacheInferType_1848_ = lean_ctor_get_uint8(v_a_1809_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1838_);
v___x_1849_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1836_, v_keyedConfig_1838_);
lean_inc(v_customCanUnfoldPredicate_x3f_1845_);
lean_inc(v_synthPendingDepth_1844_);
lean_inc(v_defEqCtx_x3f_1843_);
lean_inc_ref(v_localInstances_1842_);
lean_inc_ref(v_lctx_1841_);
lean_inc(v_zetaDeltaSet_1840_);
v___x_1850_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_zetaDeltaSet_1840_);
lean_ctor_set(v___x_1850_, 2, v_lctx_1841_);
lean_ctor_set(v___x_1850_, 3, v_localInstances_1842_);
lean_ctor_set(v___x_1850_, 4, v_defEqCtx_x3f_1843_);
lean_ctor_set(v___x_1850_, 5, v_synthPendingDepth_1844_);
lean_ctor_set(v___x_1850_, 6, v_customCanUnfoldPredicate_x3f_1845_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*7, v_trackZetaDelta_1839_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*7 + 1, v_univApprox_1846_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1847_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*7 + 3, v_cacheInferType_1848_);
v___x_1851_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1808_, v___x_1835_, v_result_1834_, v_d_1807_, v___x_1850_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec_ref_known(v___x_1850_, 7);
v___y_1815_ = v___x_1851_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1808_, v___x_1835_, v_result_1834_, v_d_1807_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
v___y_1815_ = v___x_1852_;
goto v___jp_1814_;
}
v___jp_1814_:
{
if (lean_obj_tag(v___y_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_a_1816_ = lean_ctor_get(v___y_1815_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___y_1815_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___y_1815_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___y_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___y_1815_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___y_1815_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___y_1815_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___y_1815_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1807_ = stack[0].m_obj;
lean_object* v_e_1808_ = stack[1].m_obj;
lean_object* v_a_1809_ = stack[2].m_obj;
lean_object* v_a_1810_ = stack[3].m_obj;
lean_object* v_a_1811_ = stack[4].m_obj;
lean_object* v_a_1812_ = stack[5].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1807_, v_e_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1854_, lean_object* v_e_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1854_, v_e_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec_ref(v_d_1854_);
return v_res_1861_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1862_, lean_object* v_d_1863_, lean_object* v_e_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1863_, v_e_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1863_ = stack[1].m_obj;
lean_object* v_e_1864_ = stack[2].m_obj;
lean_object* v_a_1865_ = stack[3].m_obj;
lean_object* v_a_1866_ = stack[4].m_obj;
lean_object* v_a_1867_ = stack[5].m_obj;
lean_object* v_a_1868_ = stack[6].m_obj;
lean_object* v_res_1871_;
v_res_1871_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_box(0), v_d_1863_, v_e_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
stack->m_obj
 = v_res_1871_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1872_, lean_object* v_d_1873_, lean_object* v_e_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1872_, v_d_1873_, v_e_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec_ref(v_d_1873_);
return v_res_1880_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1881_, lean_object* v_e_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1881_, v_e_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1897_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1897_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_snd_1893_; lean_object* v___x_1895_; 
v_snd_1893_ = lean_ctor_get(v_a_1889_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_a_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_snd_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_snd_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1888_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1888_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1881_ = stack[0].m_obj;
lean_object* v_e_1882_ = stack[1].m_obj;
lean_object* v_a_1883_ = stack[2].m_obj;
lean_object* v_a_1884_ = stack[3].m_obj;
lean_object* v_a_1885_ = stack[4].m_obj;
lean_object* v_a_1886_ = stack[5].m_obj;
lean_object* v_res_1906_;
v_res_1906_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1881_, v_e_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
stack->m_obj
 = v_res_1906_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1907_, lean_object* v_e_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1907_, v_e_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec_ref(v_d_1907_);
return v_res_1914_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1915_, lean_object* v_d_1916_, lean_object* v_e_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1916_, v_e_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1916_ = stack[1].m_obj;
lean_object* v_e_1917_ = stack[2].m_obj;
lean_object* v_a_1918_ = stack[3].m_obj;
lean_object* v_a_1919_ = stack[4].m_obj;
lean_object* v_a_1920_ = stack[5].m_obj;
lean_object* v_a_1921_ = stack[6].m_obj;
lean_object* v_res_1924_;
v_res_1924_ = l_Lean_Meta_DiscrTree_getMatch(lean_box(0), v_d_1916_, v_e_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
stack->m_obj
 = v_res_1924_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_d_1926_, lean_object* v_e_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1925_, v_d_1926_, v_e_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec_ref(v_d_1926_);
return v_res_1933_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1934_, lean_object* v_k_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_k_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; 
switch(lean_obj_tag(v_k_1935_))
{
case 4:
{
lean_object* v_a_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1975_; 
v_a_1963_ = lean_ctor_get(v_k_1935_, 0);
v_a_1964_ = lean_ctor_get(v_k_1935_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_k_1935_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1966_ = v_k_1935_;
v_isShared_1967_ = v_isSharedCheck_1975_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_inc(v_a_1963_);
lean_dec(v_k_1935_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1975_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_zero_1968_; uint8_t v_isZero_1969_; 
v_zero_1968_ = lean_unsigned_to_nat(0u);
v_isZero_1969_ = lean_nat_dec_eq(v_a_1964_, v_zero_1968_);
if (v_isZero_1969_ == 0)
{
lean_object* v_one_1970_; lean_object* v_n_1971_; lean_object* v___x_1973_; 
v_one_1970_ = lean_unsigned_to_nat(1u);
v_n_1971_ = lean_nat_sub(v_a_1964_, v_one_1970_);
lean_dec(v_a_1964_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v_n_1971_);
v___x_1973_ = v___x_1966_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1963_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_n_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
v_k_1946_ = v___x_1973_;
v___y_1947_ = v_a_1936_;
v___y_1948_ = v_a_1937_;
v___y_1949_ = v_a_1938_;
v___y_1950_ = v_a_1939_;
goto v___jp_1945_;
}
}
else
{
lean_del_object(v___x_1966_);
lean_dec(v_a_1964_);
lean_dec(v_a_1963_);
goto v___jp_1941_;
}
}
}
case 3:
{
lean_object* v_a_1976_; lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1988_; 
v_a_1976_ = lean_ctor_get(v_k_1935_, 0);
v_a_1977_ = lean_ctor_get(v_k_1935_, 1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_k_1935_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1979_ = v_k_1935_;
v_isShared_1980_ = v_isSharedCheck_1988_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_inc(v_a_1976_);
lean_dec(v_k_1935_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1988_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_zero_1981_; uint8_t v_isZero_1982_; 
v_zero_1981_ = lean_unsigned_to_nat(0u);
v_isZero_1982_ = lean_nat_dec_eq(v_a_1977_, v_zero_1981_);
if (v_isZero_1982_ == 0)
{
lean_object* v_one_1983_; lean_object* v_n_1984_; lean_object* v___x_1986_; 
v_one_1983_ = lean_unsigned_to_nat(1u);
v_n_1984_ = lean_nat_sub(v_a_1977_, v_one_1983_);
lean_dec(v_a_1977_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v_n_1984_);
v___x_1986_ = v___x_1979_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1976_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_n_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
v_k_1946_ = v___x_1986_;
v___y_1947_ = v_a_1936_;
v___y_1948_ = v_a_1937_;
v___y_1949_ = v_a_1938_;
v___y_1950_ = v_a_1939_;
goto v___jp_1945_;
}
}
else
{
lean_del_object(v___x_1979_);
lean_dec(v_a_1977_);
lean_dec(v_a_1976_);
goto v___jp_1941_;
}
}
}
case 6:
{
lean_object* v_a_1989_; lean_object* v_a_1990_; lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2002_; 
v_a_1989_ = lean_ctor_get(v_k_1935_, 0);
v_a_1990_ = lean_ctor_get(v_k_1935_, 1);
v_a_1991_ = lean_ctor_get(v_k_1935_, 2);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_k_1935_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1993_ = v_k_1935_;
v_isShared_1994_ = v_isSharedCheck_2002_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_inc(v_a_1990_);
lean_inc(v_a_1989_);
lean_dec(v_k_1935_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2002_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_zero_1995_; uint8_t v_isZero_1996_; 
v_zero_1995_ = lean_unsigned_to_nat(0u);
v_isZero_1996_ = lean_nat_dec_eq(v_a_1991_, v_zero_1995_);
if (v_isZero_1996_ == 0)
{
lean_object* v_one_1997_; lean_object* v_n_1998_; lean_object* v___x_2000_; 
v_one_1997_ = lean_unsigned_to_nat(1u);
v_n_1998_ = lean_nat_sub(v_a_1991_, v_one_1997_);
lean_dec(v_a_1991_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 2, v_n_1998_);
v___x_2000_ = v___x_1993_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1989_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_a_1990_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_n_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
v_k_1946_ = v___x_2000_;
v___y_1947_ = v_a_1936_;
v___y_1948_ = v_a_1937_;
v___y_1949_ = v_a_1938_;
v___y_1950_ = v_a_1939_;
goto v___jp_1945_;
}
}
else
{
lean_del_object(v___x_1993_);
lean_dec(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec(v_a_1989_);
goto v___jp_1941_;
}
}
}
default: 
{
lean_dec(v_k_1935_);
goto v___jp_1941_;
}
}
v___jp_1941_:
{
uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = 0;
v___x_1943_ = lean_box(v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
v___jp_1945_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1934_, v_k_1946_);
if (lean_obj_tag(v___x_1951_) == 0)
{
v_k_1935_ = v_k_1946_;
v_a_1936_ = v___y_1947_;
v_a_1937_ = v___y_1948_;
v_a_1938_ = v___y_1949_;
v_a_1939_ = v___y_1950_;
goto _start;
}
else
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_k_1946_);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1951_, 0);
lean_dec(v_unused_1962_);
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1956_ = 1;
v___x_1957_ = lean_box(v___x_1956_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1957_);
v___x_1959_ = v___x_1954_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1934_ = stack[0].m_obj;
lean_object* v_k_1935_ = stack[1].m_obj;
lean_object* v_a_1936_ = stack[2].m_obj;
lean_object* v_a_1937_ = stack[3].m_obj;
lean_object* v_a_1938_ = stack[4].m_obj;
lean_object* v_a_1939_ = stack[5].m_obj;
lean_object* v_res_2003_;
v_res_2003_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1934_, v_k_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
stack->m_obj
 = v_res_2003_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_2004_, lean_object* v_k_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2004_, v_k_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_d_2004_);
return v_res_2011_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_2012_, lean_object* v_d_2013_, lean_object* v_k_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2013_, v_k_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2013_ = stack[1].m_obj;
lean_object* v_k_2014_ = stack[2].m_obj;
lean_object* v_a_2015_ = stack[3].m_obj;
lean_object* v_a_2016_ = stack[4].m_obj;
lean_object* v_a_2017_ = stack[5].m_obj;
lean_object* v_a_2018_ = stack[6].m_obj;
lean_object* v_res_2021_;
v_res_2021_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_box(0), v_d_2013_, v_k_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
stack->m_obj
 = v_res_2021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_d_2023_, lean_object* v_k_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_2022_, v_d_2023_, v_k_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec_ref(v_d_2023_);
return v_res_2030_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_2031_, size_t v_sz_2032_, size_t v_i_2033_, lean_object* v_bs_2034_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_lt(v_i_2033_, v_sz_2032_);
if (v___x_2035_ == 0)
{
lean_dec(v_numExtra_2031_);
return v_bs_2034_;
}
else
{
lean_object* v_v_2036_; lean_object* v___x_2037_; lean_object* v_bs_x27_2038_; lean_object* v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; 
v_v_2036_ = lean_array_uget(v_bs_2034_, v_i_2033_);
v___x_2037_ = lean_unsigned_to_nat(0u);
v_bs_x27_2038_ = lean_array_uset(v_bs_2034_, v_i_2033_, v___x_2037_);
lean_inc(v_numExtra_2031_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_v_2036_);
lean_ctor_set(v___x_2039_, 1, v_numExtra_2031_);
v___x_2040_ = ((size_t)1ULL);
v___x_2041_ = lean_usize_add(v_i_2033_, v___x_2040_);
v___x_2042_ = lean_array_uset(v_bs_x27_2038_, v_i_2033_, v___x_2039_);
v_i_2033_ = v___x_2041_;
v_bs_2034_ = v___x_2042_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numExtra_2031_ = stack[0].m_obj;
size_t v_sz_2032_ = stack[1].m_num;
size_t v_i_2033_ = stack[2].m_num;
lean_object* v_bs_2034_ = stack[3].m_obj;
lean_object* v_res_2044_;
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2031_, v_sz_2032_, v_i_2033_, v_bs_2034_);
stack->m_obj
 = v_res_2044_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_2045_, lean_object* v_sz_2046_, lean_object* v_i_2047_, lean_object* v_bs_2048_){
_start:
{
size_t v_sz_boxed_2049_; size_t v_i_boxed_2050_; lean_object* v_res_2051_; 
v_sz_boxed_2049_ = lean_unbox_usize(v_sz_2046_);
lean_dec(v_sz_2046_);
v_i_boxed_2050_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2045_, v_sz_boxed_2049_, v_i_boxed_2050_, v_bs_2048_);
return v_res_2051_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_2052_, lean_object* v_e_2053_, lean_object* v_numExtra_2054_, lean_object* v_result_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2061_; 
lean_inc_ref(v_e_2053_);
v___x_2061_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2052_, v_e_2053_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2079_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2079_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2079_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_snd_2066_; size_t v_sz_2067_; size_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_snd_2066_ = lean_ctor_get(v_a_2062_, 1);
lean_inc(v_snd_2066_);
lean_dec(v_a_2062_);
v_sz_2067_ = lean_array_size(v_snd_2066_);
v___x_2068_ = ((size_t)0ULL);
lean_inc(v_numExtra_2054_);
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2054_, v_sz_2067_, v___x_2068_, v_snd_2066_);
v___x_2070_ = l_Array_append___redArg(v_result_2055_, v___x_2069_);
lean_dec_ref(v___x_2069_);
v___x_2071_ = l_Lean_Expr_isApp(v_e_2053_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v_numExtra_2054_);
lean_dec_ref(v_e_2053_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2070_);
v___x_2073_ = v___x_2064_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2070_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_del_object(v___x_2064_);
v___x_2075_ = l_Lean_Expr_appFn_x21(v_e_2053_);
lean_dec_ref(v_e_2053_);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_add(v_numExtra_2054_, v___x_2076_);
lean_dec(v_numExtra_2054_);
v_e_2053_ = v___x_2075_;
v_numExtra_2054_ = v___x_2077_;
v_result_2055_ = v___x_2070_;
goto _start;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_result_2055_);
lean_dec(v_numExtra_2054_);
lean_dec_ref(v_e_2053_);
v_a_2080_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2061_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2061_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2052_ = stack[0].m_obj;
lean_object* v_e_2053_ = stack[1].m_obj;
lean_object* v_numExtra_2054_ = stack[2].m_obj;
lean_object* v_result_2055_ = stack[3].m_obj;
lean_object* v_a_2056_ = stack[4].m_obj;
lean_object* v_a_2057_ = stack[5].m_obj;
lean_object* v_a_2058_ = stack[6].m_obj;
lean_object* v_a_2059_ = stack[7].m_obj;
lean_object* v_res_2088_;
v_res_2088_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2052_, v_e_2053_, v_numExtra_2054_, v_result_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
stack->m_obj
 = v_res_2088_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2089_, lean_object* v_e_2090_, lean_object* v_numExtra_2091_, lean_object* v_result_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2089_, v_e_2090_, v_numExtra_2091_, v_result_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec_ref(v_d_2089_);
return v_res_2098_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2099_, lean_object* v_d_2100_, lean_object* v_e_2101_, lean_object* v_numExtra_2102_, lean_object* v_result_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2100_, v_e_2101_, v_numExtra_2102_, v_result_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2100_ = stack[1].m_obj;
lean_object* v_e_2101_ = stack[2].m_obj;
lean_object* v_numExtra_2102_ = stack[3].m_obj;
lean_object* v_result_2103_ = stack[4].m_obj;
lean_object* v_a_2104_ = stack[5].m_obj;
lean_object* v_a_2105_ = stack[6].m_obj;
lean_object* v_a_2106_ = stack[7].m_obj;
lean_object* v_a_2107_ = stack[8].m_obj;
lean_object* v_res_2110_;
v_res_2110_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_box(0), v_d_2100_, v_e_2101_, v_numExtra_2102_, v_result_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
stack->m_obj
 = v_res_2110_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2111_, lean_object* v_d_2112_, lean_object* v_e_2113_, lean_object* v_numExtra_2114_, lean_object* v_result_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2111_, v_d_2112_, v_e_2113_, v_numExtra_2114_, v_result_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_d_2112_);
return v_res_2121_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2122_, lean_object* v_numExtra_2123_, size_t v_sz_2124_, size_t v_i_2125_, lean_object* v_bs_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2123_, v_sz_2124_, v_i_2125_, v_bs_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_numExtra_2123_ = stack[1].m_obj;
size_t v_sz_2124_ = stack[2].m_num;
size_t v_i_2125_ = stack[3].m_num;
lean_object* v_bs_2126_ = stack[4].m_obj;
lean_object* v_res_2128_;
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_box(0), v_numExtra_2123_, v_sz_2124_, v_i_2125_, v_bs_2126_);
stack->m_obj
 = v_res_2128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2129_, lean_object* v_numExtra_2130_, lean_object* v_sz_2131_, lean_object* v_i_2132_, lean_object* v_bs_2133_){
_start:
{
size_t v_sz_boxed_2134_; size_t v_i_boxed_2135_; lean_object* v_res_2136_; 
v_sz_boxed_2134_ = lean_unbox_usize(v_sz_2131_);
lean_dec(v_sz_2131_);
v_i_boxed_2135_ = lean_unbox_usize(v_i_2132_);
lean_dec(v_i_2132_);
v_res_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2129_, v_numExtra_2130_, v_sz_boxed_2134_, v_i_boxed_2135_, v_bs_2133_);
return v_res_2136_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_bs_2139_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2140_ == 0)
{
return v_bs_2139_;
}
else
{
lean_object* v_v_2141_; lean_object* v___x_2142_; lean_object* v_bs_x27_2143_; lean_object* v___x_2144_; size_t v___x_2145_; size_t v___x_2146_; lean_object* v___x_2147_; 
v_v_2141_ = lean_array_uget(v_bs_2139_, v_i_2138_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v_bs_x27_2143_ = lean_array_uset(v_bs_2139_, v_i_2138_, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v_v_2141_);
lean_ctor_set(v___x_2144_, 1, v___x_2142_);
v___x_2145_ = ((size_t)1ULL);
v___x_2146_ = lean_usize_add(v_i_2138_, v___x_2145_);
v___x_2147_ = lean_array_uset(v_bs_x27_2143_, v_i_2138_, v___x_2144_);
v_i_2138_ = v___x_2146_;
v_bs_2139_ = v___x_2147_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2137_ = stack[0].m_num;
size_t v_i_2138_ = stack[1].m_num;
lean_object* v_bs_2139_ = stack[2].m_obj;
lean_object* v_res_2149_;
v_res_2149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2137_, v_i_2138_, v_bs_2139_);
stack->m_obj
 = v_res_2149_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2150_, lean_object* v_i_2151_, lean_object* v_bs_2152_){
_start:
{
size_t v_sz_boxed_2153_; size_t v_i_boxed_2154_; lean_object* v_res_2155_; 
v_sz_boxed_2153_ = lean_unbox_usize(v_sz_2150_);
lean_dec(v_sz_2150_);
v_i_boxed_2154_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2153_, v_i_boxed_2154_, v_bs_2152_);
return v_res_2155_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2156_, lean_object* v_e_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2163_; 
lean_inc_ref(v_e_2157_);
v___x_2163_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2156_, v_e_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2198_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2198_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2198_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_fst_2168_; lean_object* v_snd_2169_; size_t v_sz_2170_; size_t v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v_fst_2168_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_fst_2168_);
v_snd_2169_ = lean_ctor_get(v_a_2164_, 1);
lean_inc(v_snd_2169_);
lean_dec(v_a_2164_);
v_sz_2170_ = lean_array_size(v_snd_2169_);
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2170_, v___x_2171_, v_snd_2169_);
v___x_2173_ = l_Lean_Expr_isApp(v_e_2157_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2175_; 
lean_dec(v_fst_2168_);
lean_dec_ref(v_e_2157_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2172_);
v___x_2175_ = v___x_2166_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2172_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
else
{
lean_object* v___x_2177_; 
lean_del_object(v___x_2166_);
v___x_2177_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2156_, v_fst_2168_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2189_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2189_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2189_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_unbox(v_a_2178_);
lean_dec(v_a_2178_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2184_; 
lean_dec_ref(v_e_2157_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2172_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2172_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_del_object(v___x_2180_);
v___x_2186_ = l_Lean_Expr_appFn_x21(v_e_2157_);
lean_dec_ref(v_e_2157_);
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2156_, v___x_2186_, v___x_2187_, v___x_2172_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2188_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_e_2157_);
v_a_2190_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2177_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2177_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_e_2157_);
v_a_2199_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2163_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2163_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2156_ = stack[0].m_obj;
lean_object* v_e_2157_ = stack[1].m_obj;
lean_object* v_a_2158_ = stack[2].m_obj;
lean_object* v_a_2159_ = stack[3].m_obj;
lean_object* v_a_2160_ = stack[4].m_obj;
lean_object* v_a_2161_ = stack[5].m_obj;
lean_object* v_res_2207_;
v_res_2207_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2156_, v_e_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
stack->m_obj
 = v_res_2207_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2208_, lean_object* v_e_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2208_, v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec_ref(v_d_2208_);
return v_res_2215_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2216_, lean_object* v_d_2217_, lean_object* v_e_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2217_, v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatchWithExtra_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2217_ = stack[1].m_obj;
lean_object* v_e_2218_ = stack[2].m_obj;
lean_object* v_a_2219_ = stack[3].m_obj;
lean_object* v_a_2220_ = stack[4].m_obj;
lean_object* v_a_2221_ = stack[5].m_obj;
lean_object* v_a_2222_ = stack[6].m_obj;
lean_object* v_res_2225_;
v_res_2225_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_box(0), v_d_2217_, v_e_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
stack->m_obj
 = v_res_2225_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_d_2227_, lean_object* v_e_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2226_, v_d_2227_, v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec_ref(v_d_2227_);
return v_res_2234_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2235_, size_t v_sz_2236_, size_t v_i_2237_, lean_object* v_bs_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2236_, v_i_2237_, v_bs_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2236_ = stack[1].m_num;
size_t v_i_2237_ = stack[2].m_num;
lean_object* v_bs_2238_ = stack[3].m_obj;
lean_object* v_res_2240_;
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_box(0), v_sz_2236_, v_i_2237_, v_bs_2238_);
stack->m_obj
 = v_res_2240_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2241_, lean_object* v_sz_2242_, lean_object* v_i_2243_, lean_object* v_bs_2244_){
_start:
{
size_t v_sz_boxed_2245_; size_t v_i_boxed_2246_; lean_object* v_res_2247_; 
v_sz_boxed_2245_ = lean_unbox_usize(v_sz_2242_);
lean_dec(v_sz_2242_);
v_i_boxed_2246_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2241_, v_sz_boxed_2245_, v_i_boxed_2246_, v_bs_2244_);
return v_res_2247_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
uint8_t v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = 1;
v___x_2255_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2248_, v___x_2254_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2279_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2279_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2279_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___y_2262_; lean_object* v___x_2267_; 
v___x_2260_ = l_Lean_Expr_getAppNumArgs(v_a_2256_);
v___x_2267_ = l_Lean_Expr_getAppFn(v_a_2256_);
lean_dec(v_a_2256_);
switch(lean_obj_tag(v___x_2267_))
{
case 9:
{
lean_object* v_a_2268_; lean_object* v___x_2269_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc_ref(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_a_2268_);
v___y_2262_ = v___x_2269_;
goto v___jp_2261_;
}
case 1:
{
lean_object* v_fvarId_2270_; lean_object* v___x_2271_; 
v_fvarId_2270_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_fvarId_2270_);
lean_dec_ref_known(v___x_2267_, 1);
lean_inc(v___x_2260_);
v___x_2271_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_fvarId_2270_);
lean_ctor_set(v___x_2271_, 1, v___x_2260_);
v___y_2262_ = v___x_2271_;
goto v___jp_2261_;
}
case 11:
{
lean_object* v_typeName_2272_; lean_object* v_idx_2273_; lean_object* v___x_2274_; 
v_typeName_2272_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_typeName_2272_);
v_idx_2273_ = lean_ctor_get(v___x_2267_, 1);
lean_inc(v_idx_2273_);
lean_dec_ref_known(v___x_2267_, 3);
lean_inc(v___x_2260_);
v___x_2274_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2274_, 0, v_typeName_2272_);
lean_ctor_set(v___x_2274_, 1, v_idx_2273_);
lean_ctor_set(v___x_2274_, 2, v___x_2260_);
v___y_2262_ = v___x_2274_;
goto v___jp_2261_;
}
case 7:
{
lean_object* v___x_2275_; 
lean_dec_ref_known(v___x_2267_, 3);
v___x_2275_ = lean_box(5);
v___y_2262_ = v___x_2275_;
goto v___jp_2261_;
}
case 4:
{
lean_object* v_declName_2276_; lean_object* v___x_2277_; 
v_declName_2276_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_declName_2276_);
lean_dec_ref_known(v___x_2267_, 2);
lean_inc(v___x_2260_);
v___x_2277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2277_, 0, v_declName_2276_);
lean_ctor_set(v___x_2277_, 1, v___x_2260_);
v___y_2262_ = v___x_2277_;
goto v___jp_2261_;
}
default: 
{
lean_object* v___x_2278_; 
lean_dec_ref(v___x_2267_);
v___x_2278_ = lean_box(1);
v___y_2262_ = v___x_2278_;
goto v___jp_2261_;
}
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___y_2262_);
lean_ctor_set(v___x_2263_, 1, v___x_2260_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2263_);
v___x_2265_ = v___x_2258_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
v_a_2280_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2255_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2255_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatchKeyRootFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2248_ = stack[0].m_obj;
lean_object* v_a_2249_ = stack[1].m_obj;
lean_object* v_a_2250_ = stack[2].m_obj;
lean_object* v_a_2251_ = stack[3].m_obj;
lean_object* v_a_2252_ = stack[4].m_obj;
lean_object* v_res_2288_;
v_res_2288_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
stack->m_obj
 = v_res_2288_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2295_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2296_, size_t v_sz_2297_, size_t v_i_2298_, lean_object* v_b_2299_){
_start:
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_usize_dec_lt(v_i_2298_, v_sz_2297_);
if (v___x_2300_ == 0)
{
return v_b_2299_;
}
else
{
lean_object* v_a_2301_; lean_object* v_snd_2302_; lean_object* v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; 
v_a_2301_ = lean_array_uget_borrowed(v_as_2296_, v_i_2298_);
v_snd_2302_ = lean_ctor_get(v_a_2301_, 1);
v___x_2303_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2302_, v_b_2299_);
v___x_2304_ = ((size_t)1ULL);
v___x_2305_ = lean_usize_add(v_i_2298_, v___x_2304_);
v_i_2298_ = v___x_2305_;
v_b_2299_ = v___x_2303_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2296_ = stack[0].m_obj;
size_t v_sz_2297_ = stack[1].m_num;
size_t v_i_2298_ = stack[2].m_num;
lean_object* v_b_2299_ = stack[3].m_obj;
lean_object* v_res_2307_;
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2296_, v_sz_2297_, v_i_2298_, v_b_2299_);
stack->m_obj
 = v_res_2307_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2308_, lean_object* v_result_2309_){
_start:
{
if (lean_obj_tag(v_trie_2308_) == 0)
{
lean_object* v_child_2310_; 
v_child_2310_ = lean_ctor_get(v_trie_2308_, 1);
v_trie_2308_ = v_child_2310_;
goto _start;
}
else
{
lean_object* v_vs_2312_; lean_object* v_children_2313_; lean_object* v_result_2314_; size_t v_sz_2315_; size_t v___x_2316_; lean_object* v___x_2317_; 
v_vs_2312_ = lean_ctor_get(v_trie_2308_, 0);
v_children_2313_ = lean_ctor_get(v_trie_2308_, 1);
v_result_2314_ = l_Array_append___redArg(v_result_2309_, v_vs_2312_);
v_sz_2315_ = lean_array_size(v_children_2313_);
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2313_, v_sz_2315_, v___x_2316_, v_result_2314_);
return v___x_2317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2318_, lean_object* v_result_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2318_, v_result_2319_);
lean_dec_ref(v_trie_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2321_, lean_object* v_sz_2322_, lean_object* v_i_2323_, lean_object* v_b_2324_){
_start:
{
size_t v_sz_boxed_2325_; size_t v_i_boxed_2326_; lean_object* v_res_2327_; 
v_sz_boxed_2325_ = lean_unbox_usize(v_sz_2322_);
lean_dec(v_sz_2322_);
v_i_boxed_2326_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_res_2327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2321_, v_sz_boxed_2325_, v_i_boxed_2326_, v_b_2324_);
lean_dec_ref(v_as_2321_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2328_, lean_object* v_trie_2329_, lean_object* v_result_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2329_, v_result_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2332_, lean_object* v_trie_2333_, lean_object* v_result_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2332_, v_trie_2333_, v_result_2334_);
lean_dec_ref(v_trie_2333_);
return v_res_2335_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2336_, lean_object* v_as_2337_, size_t v_sz_2338_, size_t v_i_2339_, lean_object* v_b_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2337_, v_sz_2338_, v_i_2339_, v_b_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2337_ = stack[1].m_obj;
size_t v_sz_2338_ = stack[2].m_num;
size_t v_i_2339_ = stack[3].m_num;
lean_object* v_b_2340_ = stack[4].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_box(0), v_as_2337_, v_sz_2338_, v_i_2339_, v_b_2340_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2343_, lean_object* v_as_2344_, lean_object* v_sz_2345_, lean_object* v_i_2346_, lean_object* v_b_2347_){
_start:
{
size_t v_sz_boxed_2348_; size_t v_i_boxed_2349_; lean_object* v_res_2350_; 
v_sz_boxed_2348_ = lean_unbox_usize(v_sz_2345_);
lean_dec(v_sz_2345_);
v_i_boxed_2349_ = lean_unbox_usize(v_i_2346_);
lean_dec(v_i_2346_);
v_res_2350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2343_, v_as_2344_, v_sz_boxed_2348_, v_i_boxed_2349_, v_b_2347_);
lean_dec_ref(v_as_2344_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2351_, lean_object* v_k_2352_, lean_object* v_result_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2351_, v_k_2352_);
if (lean_obj_tag(v___x_2354_) == 0)
{
return v_result_2353_;
}
else
{
lean_object* v_val_2355_; lean_object* v___x_2356_; 
v_val_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_val_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2355_, v_result_2353_);
lean_dec(v_val_2355_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2357_, lean_object* v_k_2358_, lean_object* v_result_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2357_, v_k_2358_, v_result_2359_);
lean_dec(v_k_2358_);
lean_dec_ref(v_d_2357_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2361_, lean_object* v_d_2362_, lean_object* v_k_2363_, lean_object* v_result_2364_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2362_, v_k_2363_, v_result_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2366_, lean_object* v_d_2367_, lean_object* v_k_2368_, lean_object* v_result_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2366_, v_d_2367_, v_k_2368_, v_result_2369_);
lean_dec(v_k_2368_);
lean_dec_ref(v_d_2367_);
return v_res_2370_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(lean_object* v_e_2371_, lean_object* v_result_2372_, lean_object* v_d_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2371_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2397_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2397_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2397_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_fst_2384_; lean_object* v_snd_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2396_; 
v_fst_2384_ = lean_ctor_get(v_a_2380_, 0);
v_snd_2385_ = lean_ctor_get(v_a_2380_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_a_2380_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2387_ = v_a_2380_;
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_snd_2385_);
lean_inc(v_fst_2384_);
lean_dec(v_a_2380_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2373_, v_fst_2384_, v_result_2372_);
lean_dec(v_fst_2384_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2389_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_snd_2385_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2393_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2391_);
v___x_2393_ = v___x_2382_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v_result_2372_);
v_a_2398_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2379_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2379_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2371_ = stack[0].m_obj;
lean_object* v_result_2372_ = stack[1].m_obj;
lean_object* v_d_2373_ = stack[2].m_obj;
lean_object* v___y_2374_ = stack[3].m_obj;
lean_object* v___y_2375_ = stack[4].m_obj;
lean_object* v___y_2376_ = stack[5].m_obj;
lean_object* v___y_2377_ = stack[6].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2371_, v_result_2372_, v_d_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0___boxed(lean_object* v_e_2407_, lean_object* v_result_2408_, lean_object* v_d_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2407_, v_result_2408_, v_d_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec_ref(v_d_2409_);
return v_res_2415_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2416_, lean_object* v_e_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___y_2424_; lean_object* v___x_2441_; uint8_t v_transparency_2442_; lean_object* v_result_2443_; uint8_t v___x_2444_; uint8_t v___x_2445_; 
v___x_2441_ = l_Lean_Meta_Context_config(v_a_2418_);
v_transparency_2442_ = lean_ctor_get_uint8(v___x_2441_, 9);
lean_dec_ref(v___x_2441_);
v_result_2443_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2416_);
v___x_2444_ = 2;
v___x_2445_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2442_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v_keyedConfig_2446_; uint8_t v_trackZetaDelta_2447_; lean_object* v_zetaDeltaSet_2448_; lean_object* v_lctx_2449_; lean_object* v_localInstances_2450_; lean_object* v_defEqCtx_x3f_2451_; lean_object* v_synthPendingDepth_2452_; lean_object* v_customCanUnfoldPredicate_x3f_2453_; uint8_t v_univApprox_2454_; uint8_t v_inTypeClassResolution_2455_; uint8_t v_cacheInferType_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_keyedConfig_2446_ = lean_ctor_get(v_a_2418_, 0);
v_trackZetaDelta_2447_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7);
v_zetaDeltaSet_2448_ = lean_ctor_get(v_a_2418_, 1);
v_lctx_2449_ = lean_ctor_get(v_a_2418_, 2);
v_localInstances_2450_ = lean_ctor_get(v_a_2418_, 3);
v_defEqCtx_x3f_2451_ = lean_ctor_get(v_a_2418_, 4);
v_synthPendingDepth_2452_ = lean_ctor_get(v_a_2418_, 5);
v_customCanUnfoldPredicate_x3f_2453_ = lean_ctor_get(v_a_2418_, 6);
v_univApprox_2454_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2455_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7 + 2);
v_cacheInferType_2456_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2446_);
v___x_2457_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2444_, v_keyedConfig_2446_);
lean_inc(v_customCanUnfoldPredicate_x3f_2453_);
lean_inc(v_synthPendingDepth_2452_);
lean_inc(v_defEqCtx_x3f_2451_);
lean_inc_ref(v_localInstances_2450_);
lean_inc_ref(v_lctx_2449_);
lean_inc(v_zetaDeltaSet_2448_);
v___x_2458_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v_zetaDeltaSet_2448_);
lean_ctor_set(v___x_2458_, 2, v_lctx_2449_);
lean_ctor_set(v___x_2458_, 3, v_localInstances_2450_);
lean_ctor_set(v___x_2458_, 4, v_defEqCtx_x3f_2451_);
lean_ctor_set(v___x_2458_, 5, v_synthPendingDepth_2452_);
lean_ctor_set(v___x_2458_, 6, v_customCanUnfoldPredicate_x3f_2453_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7, v_trackZetaDelta_2447_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 1, v_univApprox_2454_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2455_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 3, v_cacheInferType_2456_);
v___x_2459_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2417_, v_result_2443_, v_d_2416_, v___x_2458_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec_ref_known(v___x_2458_, 7);
v___y_2424_ = v___x_2459_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2417_, v_result_2443_, v_d_2416_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
v___y_2424_ = v___x_2460_;
goto v___jp_2423_;
}
v___jp_2423_:
{
if (lean_obj_tag(v___y_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
v_a_2425_ = lean_ctor_get(v___y_2424_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___y_2424_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___y_2424_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___y_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v_a_2433_ = lean_ctor_get(v___y_2424_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___y_2424_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___y_2424_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___y_2424_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatchLiberal___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2416_ = stack[0].m_obj;
lean_object* v_e_2417_ = stack[1].m_obj;
lean_object* v_a_2418_ = stack[2].m_obj;
lean_object* v_a_2419_ = stack[3].m_obj;
lean_object* v_a_2420_ = stack[4].m_obj;
lean_object* v_a_2421_ = stack[5].m_obj;
lean_object* v_res_2461_;
v_res_2461_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2416_, v_e_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
stack->m_obj
 = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2462_, lean_object* v_e_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2462_, v_e_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec_ref(v_d_2462_);
return v_res_2469_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2470_, lean_object* v_d_2471_, lean_object* v_e_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2471_, v_e_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getMatchLiberal_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2471_ = stack[1].m_obj;
lean_object* v_e_2472_ = stack[2].m_obj;
lean_object* v_a_2473_ = stack[3].m_obj;
lean_object* v_a_2474_ = stack[4].m_obj;
lean_object* v_a_2475_ = stack[5].m_obj;
lean_object* v_a_2476_ = stack[6].m_obj;
lean_object* v_res_2479_;
v_res_2479_ = l_Lean_Meta_DiscrTree_getMatchLiberal(lean_box(0), v_d_2471_, v_e_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
stack->m_obj
 = v_res_2479_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2480_, lean_object* v_d_2481_, lean_object* v_e_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2480_, v_d_2481_, v_e_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec_ref(v_d_2481_);
return v_res_2488_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2489_, lean_object* v_todo_2490_, lean_object* v_as_2491_, size_t v_i_2492_, size_t v_stop_2493_, lean_object* v_b_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_eq(v_i_2492_, v_stop_2493_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v_fst_2502_; lean_object* v_snd_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2501_ = lean_array_uget_borrowed(v_as_2491_, v_i_2492_);
v_fst_2502_ = lean_ctor_get(v___x_2501_, 0);
v_snd_2503_ = lean_ctor_get(v___x_2501_, 1);
v___x_2504_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2502_);
v___x_2505_ = lean_nat_add(v_n_2489_, v___x_2504_);
lean_dec(v___x_2504_);
lean_inc(v_snd_2503_);
lean_inc_ref(v_todo_2490_);
v___x_2506_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2505_, v_todo_2490_, v_snd_2503_, v_b_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; size_t v___x_2508_; size_t v___x_2509_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = ((size_t)1ULL);
v___x_2509_ = lean_usize_add(v_i_2492_, v___x_2508_);
v_i_2492_ = v___x_2509_;
v_b_2494_ = v_a_2507_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2490_);
return v___x_2506_;
}
}
else
{
lean_object* v___x_2511_; 
lean_dec_ref(v_todo_2490_);
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_b_2494_);
return v___x_2511_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2489_ = stack[0].m_obj;
lean_object* v_todo_2490_ = stack[1].m_obj;
lean_object* v_as_2491_ = stack[2].m_obj;
size_t v_i_2492_ = stack[3].m_num;
size_t v_stop_2493_ = stack[4].m_num;
lean_object* v_b_2494_ = stack[5].m_obj;
lean_object* v___y_2495_ = stack[6].m_obj;
lean_object* v___y_2496_ = stack[7].m_obj;
lean_object* v___y_2497_ = stack[8].m_obj;
lean_object* v___y_2498_ = stack[9].m_obj;
lean_object* v_res_2512_;
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2489_, v_todo_2490_, v_as_2491_, v_i_2492_, v_stop_2493_, v_b_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
stack->m_obj
 = v_res_2512_;
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2513_, lean_object* v_todo_2514_, lean_object* v_c_2515_, lean_object* v_result_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v_a_2531_; lean_object* v___y_2544_; lean_object* v_zero_2547_; uint8_t v_isZero_2548_; 
v_zero_2547_ = lean_unsigned_to_nat(0u);
v_isZero_2548_ = lean_nat_dec_eq(v_skip_2513_, v_zero_2547_);
if (v_isZero_2548_ == 1)
{
lean_object* v___x_2549_; uint8_t v___x_2550_; 
lean_dec(v_skip_2513_);
v___x_2549_ = lean_array_get_size(v_todo_2514_);
v___x_2550_ = lean_nat_dec_eq(v___x_2549_, v_zero_2547_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___y_2555_; 
v___x_2551_ = l_Lean_instInhabitedExpr;
v___x_2552_ = lean_box(0);
v___x_2553_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
if (lean_obj_tag(v_c_2515_) == 0)
{
lean_object* v_key_2602_; lean_object* v_child_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2613_; 
v_key_2602_ = lean_ctor_get(v_c_2515_, 0);
v_child_2603_ = lean_ctor_get(v_c_2515_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_c_2515_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2605_ = v_c_2515_;
v_isShared_2606_ = v_isSharedCheck_2613_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_child_2603_);
lean_inc(v_key_2602_);
lean_dec(v_c_2515_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2613_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_key_2602_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_child_2603_);
v___x_2608_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = lean_mk_empty_array_with_capacity(v___x_2609_);
v___x_2611_ = lean_array_push(v___x_2610_, v___x_2608_);
v___y_2555_ = v___x_2611_;
goto v___jp_2554_;
}
}
}
else
{
lean_object* v_children_2614_; 
v_children_2614_ = lean_ctor_get(v_c_2515_, 1);
lean_inc_ref(v_children_2614_);
lean_dec_ref_known(v_c_2515_, 2);
v___y_2555_ = v_children_2614_;
goto v___jp_2554_;
}
v___jp_2554_:
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = lean_array_get_size(v___y_2555_);
v___x_2557_ = lean_nat_dec_eq(v___x_2556_, v_zero_2547_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_e_2560_; lean_object* v_todo_2561_; lean_object* v___x_2562_; 
v___x_2558_ = lean_unsigned_to_nat(1u);
v___x_2559_ = lean_nat_sub(v___x_2549_, v___x_2558_);
v_e_2560_ = lean_array_get(v___x_2551_, v_todo_2514_, v___x_2559_);
lean_dec(v___x_2559_);
v_todo_2561_ = lean_array_pop(v_todo_2514_);
v___x_2562_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2560_, v___x_2557_, v___x_2557_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2592_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2592_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2592_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_fst_2567_; 
v_fst_2567_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_fst_2567_);
if (lean_obj_tag(v_fst_2567_) == 0)
{
uint8_t v___x_2568_; 
lean_dec(v_a_2563_);
v___x_2568_ = lean_nat_dec_lt(v_zero_2547_, v___x_2556_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2570_; 
lean_dec_ref(v_todo_2561_);
lean_dec_ref(v___y_2555_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_result_2516_);
v___x_2570_ = v___x_2565_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_result_2516_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
else
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_le(v___x_2556_, v___x_2556_);
if (v___x_2572_ == 0)
{
if (v___x_2568_ == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref(v_todo_2561_);
lean_dec_ref(v___y_2555_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_result_2516_);
v___x_2574_ = v___x_2565_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_result_2516_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
lean_del_object(v___x_2565_);
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = lean_usize_of_nat(v___x_2556_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2561_, v___y_2555_, v___x_2576_, v___x_2577_, v_result_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v___y_2555_);
return v___x_2578_;
}
}
else
{
size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
lean_del_object(v___x_2565_);
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = lean_usize_of_nat(v___x_2556_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2561_, v___y_2555_, v___x_2579_, v___x_2580_, v_result_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v___y_2555_);
return v___x_2581_;
}
}
}
else
{
lean_object* v_snd_2582_; lean_object* v___x_2583_; lean_object* v_fst_2584_; lean_object* v_snd_2585_; uint8_t v___x_2586_; 
v_snd_2582_ = lean_ctor_get(v_a_2563_, 1);
lean_inc(v_snd_2582_);
lean_dec(v_a_2563_);
v___x_2583_ = lean_array_get_borrowed(v___x_2553_, v___y_2555_, v_zero_2547_);
v_fst_2584_ = lean_ctor_get(v___x_2583_, 0);
v_snd_2585_ = lean_ctor_get(v___x_2583_, 1);
v___x_2586_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2584_, v___x_2552_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2588_; 
lean_inc_ref(v_result_2516_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_result_2516_);
v___x_2588_ = v___x_2565_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_result_2516_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
v___y_2523_ = v___y_2555_;
v___y_2524_ = v_fst_2567_;
v___y_2525_ = v___x_2556_;
v___y_2526_ = v_todo_2561_;
v___y_2527_ = v___x_2558_;
v___y_2528_ = v_zero_2547_;
v___y_2529_ = v_snd_2582_;
v___y_2530_ = v___x_2588_;
v_a_2531_ = v_result_2516_;
goto v___jp_2522_;
}
}
else
{
lean_object* v___x_2590_; 
lean_del_object(v___x_2565_);
lean_inc(v_snd_2585_);
lean_inc_ref(v_todo_2561_);
v___x_2590_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2547_, v_todo_2561_, v_snd_2585_, v_result_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
v___y_2523_ = v___y_2555_;
v___y_2524_ = v_fst_2567_;
v___y_2525_ = v___x_2556_;
v___y_2526_ = v_todo_2561_;
v___y_2527_ = v___x_2558_;
v___y_2528_ = v_zero_2547_;
v___y_2529_ = v_snd_2582_;
v___y_2530_ = v___x_2590_;
v_a_2531_ = v_a_2591_;
goto v___jp_2522_;
}
else
{
lean_dec(v_snd_2582_);
lean_dec(v_fst_2567_);
lean_dec_ref(v_todo_2561_);
lean_dec_ref(v___y_2555_);
return v___x_2590_;
}
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v_todo_2561_);
lean_dec_ref(v___y_2555_);
lean_dec_ref(v_result_2516_);
v_a_2593_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2562_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2562_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v___x_2601_; 
lean_dec_ref(v___y_2555_);
lean_dec_ref(v_todo_2514_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_result_2516_);
return v___x_2601_;
}
}
}
else
{
lean_dec_ref(v_todo_2514_);
if (lean_obj_tag(v_c_2515_) == 0)
{
lean_object* v___x_2615_; 
lean_dec_ref_known(v_c_2515_, 2);
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_2544_ = v___x_2615_;
goto v___jp_2543_;
}
else
{
lean_object* v_vs_2616_; 
v_vs_2616_ = lean_ctor_get(v_c_2515_, 0);
lean_inc_ref(v_vs_2616_);
lean_dec_ref_known(v_c_2515_, 2);
v___y_2544_ = v_vs_2616_;
goto v___jp_2543_;
}
}
}
else
{
lean_object* v_one_2617_; lean_object* v_n_2618_; 
v_one_2617_ = lean_unsigned_to_nat(1u);
v_n_2618_ = lean_nat_sub(v_skip_2513_, v_one_2617_);
lean_dec(v_skip_2513_);
if (lean_obj_tag(v_c_2515_) == 0)
{
lean_object* v_key_2619_; lean_object* v_child_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_key_2619_ = lean_ctor_get(v_c_2515_, 0);
lean_inc(v_key_2619_);
v_child_2620_ = lean_ctor_get(v_c_2515_, 1);
lean_inc_ref(v_child_2620_);
lean_dec_ref_known(v_c_2515_, 2);
v___x_2621_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2619_);
lean_dec(v_key_2619_);
v___x_2622_ = lean_nat_add(v_n_2618_, v___x_2621_);
lean_dec(v___x_2621_);
lean_dec(v_n_2618_);
v_skip_2513_ = v___x_2622_;
v_c_2515_ = v_child_2620_;
goto _start;
}
else
{
lean_object* v_children_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_children_2624_ = lean_ctor_get(v_c_2515_, 1);
lean_inc_ref(v_children_2624_);
lean_dec_ref_known(v_c_2515_, 2);
v___x_2625_ = lean_array_get_size(v_children_2624_);
v___x_2626_ = lean_nat_dec_eq(v___x_2625_, v_zero_2547_);
if (v___x_2626_ == 0)
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_nat_dec_lt(v_zero_2547_, v___x_2625_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref(v_children_2624_);
lean_dec(v_n_2618_);
lean_dec_ref(v_todo_2514_);
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_result_2516_);
return v___x_2628_;
}
else
{
uint8_t v___x_2629_; 
v___x_2629_ = lean_nat_dec_le(v___x_2625_, v___x_2625_);
if (v___x_2629_ == 0)
{
if (v___x_2627_ == 0)
{
lean_object* v___x_2630_; 
lean_dec_ref(v_children_2624_);
lean_dec(v_n_2618_);
lean_dec_ref(v_todo_2514_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_result_2516_);
return v___x_2630_;
}
else
{
size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = ((size_t)0ULL);
v___x_2632_ = lean_usize_of_nat(v___x_2625_);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2618_, v_todo_2514_, v_children_2624_, v___x_2631_, v___x_2632_, v_result_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v_children_2624_);
lean_dec(v_n_2618_);
return v___x_2633_;
}
}
else
{
size_t v___x_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((size_t)0ULL);
v___x_2635_ = lean_usize_of_nat(v___x_2625_);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2618_, v_todo_2514_, v_children_2624_, v___x_2634_, v___x_2635_, v_result_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v_children_2624_);
lean_dec(v_n_2618_);
return v___x_2636_;
}
}
}
else
{
lean_object* v___x_2637_; 
lean_dec_ref(v_children_2624_);
lean_dec(v_n_2618_);
lean_dec_ref(v_todo_2514_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_result_2516_);
return v___x_2637_;
}
}
}
v___jp_2522_:
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_nat_dec_lt(v___y_2528_, v___y_2525_);
if (v___x_2532_ == 0)
{
lean_dec_ref(v_a_2531_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v___y_2530_;
}
else
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = lean_nat_sub(v___y_2525_, v___y_2527_);
lean_dec(v___y_2525_);
v___x_2534_ = lean_nat_dec_le(v___y_2528_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_dec(v___x_2533_);
lean_dec_ref(v_a_2531_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v___y_2530_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2535_ = lean_mk_empty_array_with_capacity(v___y_2528_);
lean_inc_ref(v___x_2535_);
v___x_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___y_2524_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_inc(v___y_2528_);
v___x_2538_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v___y_2523_, v___x_2537_, v___y_2528_, v___x_2533_);
lean_dec_ref_known(v___x_2537_, 2);
lean_dec_ref(v___y_2523_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_dec_ref(v_a_2531_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2526_);
return v___y_2530_;
}
else
{
lean_object* v_val_2539_; lean_object* v_snd_2540_; lean_object* v___x_2541_; 
lean_dec_ref(v___y_2530_);
v_val_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_val_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_snd_2540_ = lean_ctor_get(v_val_2539_, 1);
lean_inc(v_snd_2540_);
lean_dec(v_val_2539_);
v___x_2541_ = l_Array_append___redArg(v___y_2526_, v___y_2529_);
lean_dec_ref(v___y_2529_);
v_skip_2513_ = v___y_2528_;
v_todo_2514_ = v___x_2541_;
v_c_2515_ = v_snd_2540_;
v_result_2516_ = v_a_2531_;
goto _start;
}
}
}
}
v___jp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = l_Array_append___redArg(v_result_2516_, v___y_2544_);
lean_dec_ref(v___y_2544_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_skip_2513_ = stack[0].m_obj;
lean_object* v_todo_2514_ = stack[1].m_obj;
lean_object* v_c_2515_ = stack[2].m_obj;
lean_object* v_result_2516_ = stack[3].m_obj;
lean_object* v_a_2517_ = stack[4].m_obj;
lean_object* v_a_2518_ = stack[5].m_obj;
lean_object* v_a_2519_ = stack[6].m_obj;
lean_object* v_a_2520_ = stack[7].m_obj;
lean_object* v_res_2638_;
v_res_2638_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2513_, v_todo_2514_, v_c_2515_, v_result_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
stack->m_obj
 = v_res_2638_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2639_, lean_object* v_as_2640_, size_t v_i_2641_, size_t v_stop_2642_, lean_object* v_b_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
uint8_t v___x_2649_; 
v___x_2649_ = lean_usize_dec_eq(v_i_2641_, v_stop_2642_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2650_ = lean_array_uget_borrowed(v_as_2640_, v_i_2641_);
v_fst_2651_ = lean_ctor_get(v___x_2650_, 0);
v_snd_2652_ = lean_ctor_get(v___x_2650_, 1);
v___x_2653_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2651_);
lean_inc(v_snd_2652_);
lean_inc_ref(v_todo_2639_);
v___x_2654_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2653_, v_todo_2639_, v_snd_2652_, v_b_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; size_t v___x_2656_; size_t v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2641_, v___x_2656_);
v_i_2641_ = v___x_2657_;
v_b_2643_ = v_a_2655_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2639_);
return v___x_2654_;
}
}
else
{
lean_object* v___x_2659_; 
lean_dec_ref(v_todo_2639_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_b_2643_);
return v___x_2659_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_2639_ = stack[0].m_obj;
lean_object* v_as_2640_ = stack[1].m_obj;
size_t v_i_2641_ = stack[2].m_num;
size_t v_stop_2642_ = stack[3].m_num;
lean_object* v_b_2643_ = stack[4].m_obj;
lean_object* v___y_2644_ = stack[5].m_obj;
lean_object* v___y_2645_ = stack[6].m_obj;
lean_object* v___y_2646_ = stack[7].m_obj;
lean_object* v___y_2647_ = stack[8].m_obj;
lean_object* v_res_2660_;
v_res_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2639_, v_as_2640_, v_i_2641_, v_stop_2642_, v_b_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
stack->m_obj
 = v_res_2660_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2661_, lean_object* v_as_2662_, lean_object* v_i_2663_, lean_object* v_stop_2664_, lean_object* v_b_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
size_t v_i_boxed_2671_; size_t v_stop_boxed_2672_; lean_object* v_res_2673_; 
v_i_boxed_2671_ = lean_unbox_usize(v_i_2663_);
lean_dec(v_i_2663_);
v_stop_boxed_2672_ = lean_unbox_usize(v_stop_2664_);
lean_dec(v_stop_2664_);
v_res_2673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2661_, v_as_2662_, v_i_boxed_2671_, v_stop_boxed_2672_, v_b_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec_ref(v_as_2662_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2674_, lean_object* v_todo_2675_, lean_object* v_as_2676_, lean_object* v_i_2677_, lean_object* v_stop_2678_, lean_object* v_b_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
size_t v_i_boxed_2685_; size_t v_stop_boxed_2686_; lean_object* v_res_2687_; 
v_i_boxed_2685_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_stop_boxed_2686_ = lean_unbox_usize(v_stop_2678_);
lean_dec(v_stop_2678_);
v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2674_, v_todo_2675_, v_as_2676_, v_i_boxed_2685_, v_stop_boxed_2686_, v_b_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_as_2676_);
lean_dec(v_n_2674_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2688_, lean_object* v_todo_2689_, lean_object* v_c_2690_, lean_object* v_result_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2688_, v_todo_2689_, v_c_2690_, v_result_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
return v_res_2697_;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2698_, lean_object* v_skip_2699_, lean_object* v_todo_2700_, lean_object* v_c_2701_, lean_object* v_result_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2699_, v_todo_2700_, v_c_2701_, v_result_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_0interp(lean_interpreter_value* stack)
{
lean_object* v_skip_2699_ = stack[1].m_obj;
lean_object* v_todo_2700_ = stack[2].m_obj;
lean_object* v_c_2701_ = stack[3].m_obj;
lean_object* v_result_2702_ = stack[4].m_obj;
lean_object* v_a_2703_ = stack[5].m_obj;
lean_object* v_a_2704_ = stack[6].m_obj;
lean_object* v_a_2705_ = stack[7].m_obj;
lean_object* v_a_2706_ = stack[8].m_obj;
lean_object* v_res_2709_;
v_res_2709_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_box(0), v_skip_2699_, v_todo_2700_, v_c_2701_, v_result_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
stack->m_obj
 = v_res_2709_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2710_, lean_object* v_skip_2711_, lean_object* v_todo_2712_, lean_object* v_c_2713_, lean_object* v_result_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2710_, v_skip_2711_, v_todo_2712_, v_c_2713_, v_result_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
return v_res_2720_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2721_, lean_object* v_todo_2722_, lean_object* v_as_2723_, size_t v_i_2724_, size_t v_stop_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2722_, v_as_2723_, v_i_2724_, v_stop_2725_, v_b_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_2722_ = stack[1].m_obj;
lean_object* v_as_2723_ = stack[2].m_obj;
size_t v_i_2724_ = stack[3].m_num;
size_t v_stop_2725_ = stack[4].m_num;
lean_object* v_b_2726_ = stack[5].m_obj;
lean_object* v___y_2727_ = stack[6].m_obj;
lean_object* v___y_2728_ = stack[7].m_obj;
lean_object* v___y_2729_ = stack[8].m_obj;
lean_object* v___y_2730_ = stack[9].m_obj;
lean_object* v_res_2733_;
v_res_2733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_box(0), v_todo_2722_, v_as_2723_, v_i_2724_, v_stop_2725_, v_b_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
stack->m_obj
 = v_res_2733_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2734_, lean_object* v_todo_2735_, lean_object* v_as_2736_, lean_object* v_i_2737_, lean_object* v_stop_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
size_t v_i_boxed_2745_; size_t v_stop_boxed_2746_; lean_object* v_res_2747_; 
v_i_boxed_2745_ = lean_unbox_usize(v_i_2737_);
lean_dec(v_i_2737_);
v_stop_boxed_2746_ = lean_unbox_usize(v_stop_2738_);
lean_dec(v_stop_2738_);
v_res_2747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2734_, v_todo_2735_, v_as_2736_, v_i_boxed_2745_, v_stop_boxed_2746_, v_b_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec_ref(v_as_2736_);
return v_res_2747_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2748_, lean_object* v_n_2749_, lean_object* v_todo_2750_, lean_object* v_as_2751_, size_t v_i_2752_, size_t v_stop_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2749_, v_todo_2750_, v_as_2751_, v_i_2752_, v_stop_2753_, v_b_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2749_ = stack[1].m_obj;
lean_object* v_todo_2750_ = stack[2].m_obj;
lean_object* v_as_2751_ = stack[3].m_obj;
size_t v_i_2752_ = stack[4].m_num;
size_t v_stop_2753_ = stack[5].m_num;
lean_object* v_b_2754_ = stack[6].m_obj;
lean_object* v___y_2755_ = stack[7].m_obj;
lean_object* v___y_2756_ = stack[8].m_obj;
lean_object* v___y_2757_ = stack[9].m_obj;
lean_object* v___y_2758_ = stack[10].m_obj;
lean_object* v_res_2761_;
v_res_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_box(0), v_n_2749_, v_todo_2750_, v_as_2751_, v_i_2752_, v_stop_2753_, v_b_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
stack->m_obj
 = v_res_2761_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_n_2763_, lean_object* v_todo_2764_, lean_object* v_as_2765_, lean_object* v_i_2766_, lean_object* v_stop_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
size_t v_i_boxed_2774_; size_t v_stop_boxed_2775_; lean_object* v_res_2776_; 
v_i_boxed_2774_ = lean_unbox_usize(v_i_2766_);
lean_dec(v_i_2766_);
v_stop_boxed_2775_ = lean_unbox_usize(v_stop_2767_);
lean_dec(v_stop_2767_);
v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2762_, v_n_2763_, v_todo_2764_, v_as_2765_, v_i_boxed_2774_, v_stop_boxed_2775_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec_ref(v_as_2765_);
lean_dec(v_n_2763_);
return v_res_2776_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2777_, lean_object* v_k_2778_, lean_object* v_c_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2778_);
v___x_2786_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2787_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2785_, v___x_2786_, v_c_2779_, v_result_2777_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
return v___x_2787_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_result_2777_ = stack[0].m_obj;
lean_object* v_k_2778_ = stack[1].m_obj;
lean_object* v_c_2779_ = stack[2].m_obj;
lean_object* v___y_2780_ = stack[3].m_obj;
lean_object* v___y_2781_ = stack[4].m_obj;
lean_object* v___y_2782_ = stack[5].m_obj;
lean_object* v___y_2783_ = stack[6].m_obj;
lean_object* v_res_2788_;
v_res_2788_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2777_, v_k_2778_, v_c_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
stack->m_obj
 = v_res_2788_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2789_, lean_object* v_k_2790_, lean_object* v_c_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2789_, v_k_2790_, v_c_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v_k_2790_);
return v_res_2797_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2798_, lean_object* v_keys_2799_, lean_object* v_vals_2800_, lean_object* v_i_2801_, lean_object* v_acc_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = lean_array_get_size(v_keys_2799_);
v___x_2809_ = lean_nat_dec_lt(v_i_2801_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec(v_i_2801_);
lean_dec_ref(v_f_2798_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_acc_2802_);
return v___x_2810_;
}
else
{
lean_object* v_k_2811_; lean_object* v_v_2812_; lean_object* v___x_2813_; 
v_k_2811_ = lean_array_fget_borrowed(v_keys_2799_, v_i_2801_);
v_v_2812_ = lean_array_fget_borrowed(v_vals_2800_, v_i_2801_);
lean_inc_ref(v_f_2798_);
lean_inc(v___y_2806_);
lean_inc_ref(v___y_2805_);
lean_inc(v___y_2804_);
lean_inc_ref(v___y_2803_);
lean_inc(v_v_2812_);
lean_inc(v_k_2811_);
v___x_2813_ = lean_apply_8(v_f_2798_, v_acc_2802_, v_k_2811_, v_v_2812_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, lean_box(0));
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = lean_unsigned_to_nat(1u);
v___x_2816_ = lean_nat_add(v_i_2801_, v___x_2815_);
lean_dec(v_i_2801_);
v_i_2801_ = v___x_2816_;
v_acc_2802_ = v_a_2814_;
goto _start;
}
else
{
lean_dec(v_i_2801_);
lean_dec_ref(v_f_2798_);
return v___x_2813_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2798_ = stack[0].m_obj;
lean_object* v_keys_2799_ = stack[1].m_obj;
lean_object* v_vals_2800_ = stack[2].m_obj;
lean_object* v_i_2801_ = stack[3].m_obj;
lean_object* v_acc_2802_ = stack[4].m_obj;
lean_object* v___y_2803_ = stack[5].m_obj;
lean_object* v___y_2804_ = stack[6].m_obj;
lean_object* v___y_2805_ = stack[7].m_obj;
lean_object* v___y_2806_ = stack[8].m_obj;
lean_object* v_res_2818_;
v_res_2818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2798_, v_keys_2799_, v_vals_2800_, v_i_2801_, v_acc_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
stack->m_obj
 = v_res_2818_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2819_, lean_object* v_keys_2820_, lean_object* v_vals_2821_, lean_object* v_i_2822_, lean_object* v_acc_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2819_, v_keys_2820_, v_vals_2821_, v_i_2822_, v_acc_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_vals_2821_);
lean_dec_ref(v_keys_2820_);
return v_res_2829_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2830_, lean_object* v_as_2831_, size_t v_i_2832_, size_t v_stop_2833_, lean_object* v_b_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_a_2841_; lean_object* v___y_2846_; uint8_t v___x_2848_; 
v___x_2848_ = lean_usize_dec_eq(v_i_2832_, v_stop_2833_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_array_uget_borrowed(v_as_2831_, v_i_2832_);
switch(lean_obj_tag(v___x_2849_))
{
case 0:
{
lean_object* v_key_2850_; lean_object* v_val_2851_; lean_object* v___x_2852_; 
v_key_2850_ = lean_ctor_get(v___x_2849_, 0);
v_val_2851_ = lean_ctor_get(v___x_2849_, 1);
lean_inc_ref(v_f_2830_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v_val_2851_);
lean_inc(v_key_2850_);
v___x_2852_ = lean_apply_8(v_f_2830_, v_b_2834_, v_key_2850_, v_val_2851_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, lean_box(0));
v___y_2846_ = v___x_2852_;
goto v___jp_2845_;
}
case 1:
{
lean_object* v_node_2853_; lean_object* v___x_2854_; 
v_node_2853_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_node_2853_);
lean_inc_ref(v_f_2830_);
v___x_2854_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2830_, v_node_2853_, v_b_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
v___y_2846_ = v___x_2854_;
goto v___jp_2845_;
}
default: 
{
v_a_2841_ = v_b_2834_;
goto v___jp_2840_;
}
}
}
else
{
lean_object* v___x_2855_; 
lean_dec_ref(v_f_2830_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_b_2834_);
return v___x_2855_;
}
v___jp_2840_:
{
size_t v___x_2842_; size_t v___x_2843_; 
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_add(v_i_2832_, v___x_2842_);
v_i_2832_ = v___x_2843_;
v_b_2834_ = v_a_2841_;
goto _start;
}
v___jp_2845_:
{
if (lean_obj_tag(v___y_2846_) == 0)
{
lean_object* v_a_2847_; 
v_a_2847_ = lean_ctor_get(v___y_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___y_2846_, 1);
v_a_2841_ = v_a_2847_;
goto v___jp_2840_;
}
else
{
lean_dec_ref(v_f_2830_);
return v___y_2846_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2830_ = stack[0].m_obj;
lean_object* v_as_2831_ = stack[1].m_obj;
size_t v_i_2832_ = stack[2].m_num;
size_t v_stop_2833_ = stack[3].m_num;
lean_object* v_b_2834_ = stack[4].m_obj;
lean_object* v___y_2835_ = stack[5].m_obj;
lean_object* v___y_2836_ = stack[6].m_obj;
lean_object* v___y_2837_ = stack[7].m_obj;
lean_object* v___y_2838_ = stack[8].m_obj;
lean_object* v_res_2856_;
v_res_2856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2830_, v_as_2831_, v_i_2832_, v_stop_2833_, v_b_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
stack->m_obj
 = v_res_2856_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2857_, lean_object* v_x_2858_, lean_object* v_x_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
if (lean_obj_tag(v_x_2858_) == 0)
{
lean_object* v_es_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2878_; 
v_es_2865_ = lean_ctor_get(v_x_2858_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_x_2858_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2867_ = v_x_2858_;
v_isShared_2868_ = v_isSharedCheck_2878_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_es_2865_);
lean_dec(v_x_2858_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2878_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_array_get_size(v_es_2865_);
v___x_2871_ = lean_nat_dec_lt(v___x_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2873_; 
lean_dec_ref(v_es_2865_);
lean_dec_ref(v_f_2857_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v_x_2859_);
v___x_2873_ = v___x_2867_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_x_2859_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
else
{
size_t v___x_2875_; size_t v___x_2876_; lean_object* v___x_2877_; 
lean_del_object(v___x_2867_);
v___x_2875_ = ((size_t)0ULL);
v___x_2876_ = lean_usize_of_nat(v___x_2870_);
v___x_2877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2857_, v_es_2865_, v___x_2875_, v___x_2876_, v_x_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec_ref(v_es_2865_);
return v___x_2877_;
}
}
}
else
{
lean_object* v_ks_2879_; lean_object* v_vs_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_ks_2879_ = lean_ctor_get(v_x_2858_, 0);
lean_inc_ref(v_ks_2879_);
v_vs_2880_ = lean_ctor_get(v_x_2858_, 1);
lean_inc_ref(v_vs_2880_);
lean_dec_ref_known(v_x_2858_, 2);
v___x_2881_ = lean_unsigned_to_nat(0u);
v___x_2882_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2857_, v_ks_2879_, v_vs_2880_, v___x_2881_, v_x_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec_ref(v_vs_2880_);
lean_dec_ref(v_ks_2879_);
return v___x_2882_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2857_ = stack[0].m_obj;
lean_object* v_x_2858_ = stack[1].m_obj;
lean_object* v_x_2859_ = stack[2].m_obj;
lean_object* v___y_2860_ = stack[3].m_obj;
lean_object* v___y_2861_ = stack[4].m_obj;
lean_object* v___y_2862_ = stack[5].m_obj;
lean_object* v___y_2863_ = stack[6].m_obj;
lean_object* v_res_2883_;
v_res_2883_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2857_, v_x_2858_, v_x_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
stack->m_obj
 = v_res_2883_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2884_, lean_object* v_x_2885_, lean_object* v_x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2884_, v_x_2885_, v_x_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2893_, lean_object* v_as_2894_, lean_object* v_i_2895_, lean_object* v_stop_2896_, lean_object* v_b_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
size_t v_i_boxed_2903_; size_t v_stop_boxed_2904_; lean_object* v_res_2905_; 
v_i_boxed_2903_ = lean_unbox_usize(v_i_2895_);
lean_dec(v_i_2895_);
v_stop_boxed_2904_ = lean_unbox_usize(v_stop_2896_);
lean_dec(v_stop_2896_);
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2893_, v_as_2894_, v_i_boxed_2903_, v_stop_boxed_2904_, v_b_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v_as_2894_);
return v_res_2905_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(lean_object* v_e_2906_, uint8_t v___x_2907_, lean_object* v___f_2908_, lean_object* v_d_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
uint8_t v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = 0;
v___x_2916_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2906_, v___x_2915_, v___x_2907_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2933_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_2933_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2933_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_fst_2921_; 
v_fst_2921_ = lean_ctor_get(v_a_2917_, 0);
lean_inc(v_fst_2921_);
if (lean_obj_tag(v_fst_2921_) == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
lean_del_object(v___x_2919_);
lean_dec(v_a_2917_);
v___x_2922_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_2923_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2908_, v_d_2909_, v___x_2922_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2923_;
}
else
{
lean_object* v_snd_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec_ref(v___f_2908_);
v_snd_2924_ = lean_ctor_get(v_a_2917_, 1);
lean_inc(v_snd_2924_);
lean_dec(v_a_2917_);
v___x_2925_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2909_);
v___x_2926_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2909_, v_fst_2921_);
lean_dec(v_fst_2921_);
lean_dec_ref(v_d_2909_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v___x_2928_; 
lean_dec(v_snd_2924_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2925_);
v___x_2928_ = v___x_2919_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2925_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
else
{
lean_object* v_val_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_del_object(v___x_2919_);
v_val_2930_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_val_2930_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2931_, v_snd_2924_, v_val_2930_, v___x_2925_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2932_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v_d_2909_);
lean_dec_ref(v___f_2908_);
v_a_2934_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2916_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2916_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2906_ = stack[0].m_obj;
uint8_t v___x_2907_ = stack[1].m_num;
lean_object* v___f_2908_ = stack[2].m_obj;
lean_object* v_d_2909_ = stack[3].m_obj;
lean_object* v___y_2910_ = stack[4].m_obj;
lean_object* v___y_2911_ = stack[5].m_obj;
lean_object* v___y_2912_ = stack[6].m_obj;
lean_object* v___y_2913_ = stack[7].m_obj;
lean_object* v_res_2942_;
v_res_2942_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2906_, v___x_2907_, v___f_2908_, v_d_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
stack->m_obj
 = v_res_2942_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1___boxed(lean_object* v_e_2943_, lean_object* v___x_2944_, lean_object* v___f_2945_, lean_object* v_d_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
uint8_t v___x_1613__boxed_2952_; lean_object* v_res_2953_; 
v___x_1613__boxed_2952_ = lean_unbox(v___x_2944_);
v_res_2953_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2943_, v___x_1613__boxed_2952_, v___f_2945_, v_d_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2953_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2955_, lean_object* v_e_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v___y_2963_; lean_object* v___x_2980_; uint8_t v_transparency_2981_; lean_object* v___f_2982_; uint8_t v___x_2983_; uint8_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2980_ = l_Lean_Meta_Context_config(v_a_2957_);
v_transparency_2981_ = lean_ctor_get_uint8(v___x_2980_, 9);
lean_dec_ref(v___x_2980_);
v___f_2982_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2983_ = 1;
v___x_2984_ = 2;
v___x_2985_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2981_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v_keyedConfig_2986_; uint8_t v_trackZetaDelta_2987_; lean_object* v_zetaDeltaSet_2988_; lean_object* v_lctx_2989_; lean_object* v_localInstances_2990_; lean_object* v_defEqCtx_x3f_2991_; lean_object* v_synthPendingDepth_2992_; lean_object* v_customCanUnfoldPredicate_x3f_2993_; uint8_t v_univApprox_2994_; uint8_t v_inTypeClassResolution_2995_; uint8_t v_cacheInferType_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v_keyedConfig_2986_ = lean_ctor_get(v_a_2957_, 0);
v_trackZetaDelta_2987_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*7);
v_zetaDeltaSet_2988_ = lean_ctor_get(v_a_2957_, 1);
v_lctx_2989_ = lean_ctor_get(v_a_2957_, 2);
v_localInstances_2990_ = lean_ctor_get(v_a_2957_, 3);
v_defEqCtx_x3f_2991_ = lean_ctor_get(v_a_2957_, 4);
v_synthPendingDepth_2992_ = lean_ctor_get(v_a_2957_, 5);
v_customCanUnfoldPredicate_x3f_2993_ = lean_ctor_get(v_a_2957_, 6);
v_univApprox_2994_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2995_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*7 + 2);
v_cacheInferType_2996_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2986_);
v___x_2997_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2984_, v_keyedConfig_2986_);
lean_inc(v_customCanUnfoldPredicate_x3f_2993_);
lean_inc(v_synthPendingDepth_2992_);
lean_inc(v_defEqCtx_x3f_2991_);
lean_inc_ref(v_localInstances_2990_);
lean_inc_ref(v_lctx_2989_);
lean_inc(v_zetaDeltaSet_2988_);
v___x_2998_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v_zetaDeltaSet_2988_);
lean_ctor_set(v___x_2998_, 2, v_lctx_2989_);
lean_ctor_set(v___x_2998_, 3, v_localInstances_2990_);
lean_ctor_set(v___x_2998_, 4, v_defEqCtx_x3f_2991_);
lean_ctor_set(v___x_2998_, 5, v_synthPendingDepth_2992_);
lean_ctor_set(v___x_2998_, 6, v_customCanUnfoldPredicate_x3f_2993_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*7, v_trackZetaDelta_2987_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*7 + 1, v_univApprox_2994_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2995_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*7 + 3, v_cacheInferType_2996_);
v___x_2999_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2956_, v___x_2983_, v___f_2982_, v_d_2955_, v___x_2998_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec_ref_known(v___x_2998_, 7);
v___y_2963_ = v___x_2999_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2956_, v___x_2983_, v___f_2982_, v_d_2955_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
v___y_2963_ = v___x_3000_;
goto v___jp_2962_;
}
v___jp_2962_:
{
if (lean_obj_tag(v___y_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v_a_2964_ = lean_ctor_get(v___y_2963_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___y_2963_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___y_2963_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___y_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_a_2972_ = lean_ctor_get(v___y_2963_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___y_2963_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___y_2963_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___y_2963_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getUnify___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2955_ = stack[0].m_obj;
lean_object* v_e_2956_ = stack[1].m_obj;
lean_object* v_a_2957_ = stack[2].m_obj;
lean_object* v_a_2958_ = stack[3].m_obj;
lean_object* v_a_2959_ = stack[4].m_obj;
lean_object* v_a_2960_ = stack[5].m_obj;
lean_object* v_res_3001_;
v_res_3001_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2955_, v_e_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
stack->m_obj
 = v_res_3001_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_3002_, lean_object* v_e_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_3002_, v_e_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
return v_res_3009_;
}
}
lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_3010_, lean_object* v_d_3011_, lean_object* v_e_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_3011_, v_e_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_getUnify_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_3011_ = stack[1].m_obj;
lean_object* v_e_3012_ = stack[2].m_obj;
lean_object* v_a_3013_ = stack[3].m_obj;
lean_object* v_a_3014_ = stack[4].m_obj;
lean_object* v_a_3015_ = stack[5].m_obj;
lean_object* v_a_3016_ = stack[6].m_obj;
lean_object* v_res_3019_;
v_res_3019_ = l_Lean_Meta_DiscrTree_getUnify(lean_box(0), v_d_3011_, v_e_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
stack->m_obj
 = v_res_3019_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_3020_, lean_object* v_d_3021_, lean_object* v_e_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_3020_, v_d_3021_, v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
return v_res_3028_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_3029_, lean_object* v_f_3030_, lean_object* v_init_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3030_, v_map_3029_, v_init_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_3029_ = stack[0].m_obj;
lean_object* v_f_3030_ = stack[1].m_obj;
lean_object* v_init_3031_ = stack[2].m_obj;
lean_object* v___y_3032_ = stack[3].m_obj;
lean_object* v___y_3033_ = stack[4].m_obj;
lean_object* v___y_3034_ = stack[5].m_obj;
lean_object* v___y_3035_ = stack[6].m_obj;
lean_object* v_res_3038_;
v_res_3038_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_3029_, v_f_3030_, v_init_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
stack->m_obj
 = v_res_3038_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_3039_, lean_object* v_f_3040_, lean_object* v_init_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_3039_, v_f_3040_, v_init_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3047_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_3048_, lean_object* v_00_u03b2_3049_, lean_object* v_map_3050_, lean_object* v_f_3051_, lean_object* v_init_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3051_, v_map_3050_, v_init_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_3050_ = stack[2].m_obj;
lean_object* v_f_3051_ = stack[3].m_obj;
lean_object* v_init_3052_ = stack[4].m_obj;
lean_object* v___y_3053_ = stack[5].m_obj;
lean_object* v___y_3054_ = stack[6].m_obj;
lean_object* v___y_3055_ = stack[7].m_obj;
lean_object* v___y_3056_ = stack[8].m_obj;
lean_object* v_res_3059_;
v_res_3059_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_box(0), lean_box(0), v_map_3050_, v_f_3051_, v_init_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
stack->m_obj
 = v_res_3059_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_3060_, lean_object* v_00_u03b2_3061_, lean_object* v_map_3062_, lean_object* v_f_3063_, lean_object* v_init_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_3060_, v_00_u03b2_3061_, v_map_3062_, v_f_3063_, v_init_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
return v_res_3070_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_3071_, lean_object* v_00_u03b1_3072_, lean_object* v_00_u03b2_3073_, lean_object* v_f_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3074_, v_x_3075_, v_x_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
return v___x_3082_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3074_ = stack[3].m_obj;
lean_object* v_x_3075_ = stack[4].m_obj;
lean_object* v_x_3076_ = stack[5].m_obj;
lean_object* v___y_3077_ = stack[6].m_obj;
lean_object* v___y_3078_ = stack[7].m_obj;
lean_object* v___y_3079_ = stack[8].m_obj;
lean_object* v___y_3080_ = stack[9].m_obj;
lean_object* v_res_3083_;
v_res_3083_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_box(0), lean_box(0), lean_box(0), v_f_3074_, v_x_3075_, v_x_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
stack->m_obj
 = v_res_3083_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3084_, lean_object* v_00_u03b1_3085_, lean_object* v_00_u03b2_3086_, lean_object* v_f_3087_, lean_object* v_x_3088_, lean_object* v_x_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_3084_, v_00_u03b1_3085_, v_00_u03b2_3086_, v_f_3087_, v_x_3088_, v_x_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
return v_res_3095_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3096_, lean_object* v_00_u03b2_3097_, lean_object* v_00_u03c3_3098_, lean_object* v_f_3099_, lean_object* v_as_3100_, size_t v_i_3101_, size_t v_stop_3102_, lean_object* v_b_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3099_, v_as_3100_, v_i_3101_, v_stop_3102_, v_b_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3099_ = stack[3].m_obj;
lean_object* v_as_3100_ = stack[4].m_obj;
size_t v_i_3101_ = stack[5].m_num;
size_t v_stop_3102_ = stack[6].m_num;
lean_object* v_b_3103_ = stack[7].m_obj;
lean_object* v___y_3104_ = stack[8].m_obj;
lean_object* v___y_3105_ = stack[9].m_obj;
lean_object* v___y_3106_ = stack[10].m_obj;
lean_object* v___y_3107_ = stack[11].m_obj;
lean_object* v_res_3110_;
v_res_3110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_box(0), lean_box(0), lean_box(0), v_f_3099_, v_as_3100_, v_i_3101_, v_stop_3102_, v_b_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
stack->m_obj
 = v_res_3110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3111_, lean_object* v_00_u03b2_3112_, lean_object* v_00_u03c3_3113_, lean_object* v_f_3114_, lean_object* v_as_3115_, lean_object* v_i_3116_, lean_object* v_stop_3117_, lean_object* v_b_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
size_t v_i_boxed_3124_; size_t v_stop_boxed_3125_; lean_object* v_res_3126_; 
v_i_boxed_3124_ = lean_unbox_usize(v_i_3116_);
lean_dec(v_i_3116_);
v_stop_boxed_3125_ = lean_unbox_usize(v_stop_3117_);
lean_dec(v_stop_3117_);
v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_3111_, v_00_u03b2_3112_, v_00_u03c3_3113_, v_f_3114_, v_as_3115_, v_i_boxed_3124_, v_stop_boxed_3125_, v_b_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec_ref(v_as_3115_);
return v_res_3126_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_3127_, lean_object* v_00_u03b1_3128_, lean_object* v_00_u03b2_3129_, lean_object* v_f_3130_, lean_object* v_keys_3131_, lean_object* v_vals_3132_, lean_object* v_heq_3133_, lean_object* v_i_3134_, lean_object* v_acc_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3130_, v_keys_3131_, v_vals_3132_, v_i_3134_, v_acc_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3130_ = stack[3].m_obj;
lean_object* v_keys_3131_ = stack[4].m_obj;
lean_object* v_vals_3132_ = stack[5].m_obj;
lean_object* v_i_3134_ = stack[7].m_obj;
lean_object* v_acc_3135_ = stack[8].m_obj;
lean_object* v___y_3136_ = stack[9].m_obj;
lean_object* v___y_3137_ = stack[10].m_obj;
lean_object* v___y_3138_ = stack[11].m_obj;
lean_object* v___y_3139_ = stack[12].m_obj;
lean_object* v_res_3142_;
v_res_3142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_box(0), lean_box(0), lean_box(0), v_f_3130_, v_keys_3131_, v_vals_3132_, lean_box(0), v_i_3134_, v_acc_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
stack->m_obj
 = v_res_3142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_3143_, lean_object* v_00_u03b1_3144_, lean_object* v_00_u03b2_3145_, lean_object* v_f_3146_, lean_object* v_keys_3147_, lean_object* v_vals_3148_, lean_object* v_heq_3149_, lean_object* v_i_3150_, lean_object* v_acc_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_3143_, v_00_u03b1_3144_, v_00_u03b2_3145_, v_f_3146_, v_keys_3147_, v_vals_3148_, v_heq_3149_, v_i_3150_, v_acc_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v_vals_3148_);
lean_dec_ref(v_keys_3147_);
return v_res_3157_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Util(builtin);
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
lean_object* initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTree_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree_Util(builtin);
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
