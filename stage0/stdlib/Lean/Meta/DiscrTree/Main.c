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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(lean_object* v_a_18_, lean_object* v_i_19_, lean_object* v_infos_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg___boxed(lean_object* v_a_53_, lean_object* v_i_54_, lean_object* v_infos_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_a_53_, v_i_54_, v_infos_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec_ref(v_infos_55_);
lean_dec(v_i_54_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(lean_object* v_infos_62_, lean_object* v_x_63_, lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
if (lean_obj_tag(v_x_64_) == 5)
{
lean_object* v_fn_71_; lean_object* v_arg_72_; lean_object* v___x_73_; 
v_fn_71_ = lean_ctor_get(v_x_64_, 0);
lean_inc_ref(v_fn_71_);
v_arg_72_ = lean_ctor_get(v_x_64_, 1);
lean_inc_ref_n(v_arg_72_, 2);
lean_dec_ref_known(v_x_64_, 2);
v___x_73_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_arg_72_, v_x_63_, v_infos_62_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; uint8_t v___x_75_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v___x_73_, 1);
v___x_75_ = lean_unbox(v_a_74_);
lean_dec(v_a_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_sub(v_x_63_, v___x_76_);
lean_dec(v_x_63_);
v___x_78_ = lean_array_push(v_x_65_, v_arg_72_);
v_x_63_ = v___x_77_;
v_x_64_ = v_fn_71_;
v_x_65_ = v___x_78_;
goto _start;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v_arg_72_);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_sub(v_x_63_, v___x_80_);
lean_dec(v_x_63_);
v___x_82_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
v___x_83_ = lean_array_push(v_x_65_, v___x_82_);
v_x_63_ = v___x_81_;
v_x_64_ = v_fn_71_;
v_x_65_ = v___x_83_;
goto _start;
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
lean_dec_ref(v_arg_72_);
lean_dec_ref(v_fn_71_);
lean_dec_ref(v_x_65_);
lean_dec(v_x_63_);
v_a_85_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_73_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_73_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
else
{
lean_object* v___x_93_; 
lean_dec_ref(v_x_64_);
lean_dec(v_x_63_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_x_65_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(lean_object* v_infos_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_infos_94_, v_x_95_, v_x_96_, v_x_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec_ref(v_infos_94_);
return v_res_103_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(lean_object* v_e_118_){
_start:
{
uint8_t v___x_119_; uint8_t v___x_120_; 
v___x_119_ = l_Lean_Expr_isRawNatLit(v_e_118_);
v___x_120_ = 1;
if (v___x_119_ == 0)
{
lean_object* v_f_121_; uint8_t v___x_122_; 
v_f_121_ = l_Lean_Expr_getAppFn(v_e_118_);
v___x_122_ = l_Lean_Expr_isConst(v_f_121_);
if (v___x_122_ == 0)
{
lean_dec_ref(v_f_121_);
lean_dec_ref(v_e_118_);
return v___x_119_;
}
else
{
if (v___x_119_ == 0)
{
lean_object* v_fName_123_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_fName_123_ = l_Lean_Expr_constName_x21(v_f_121_);
lean_dec_ref(v_f_121_);
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_142_ = lean_name_eq(v_fName_123_, v___x_141_);
if (v___x_142_ == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = l_Lean_Expr_getAppNumArgs(v_e_118_);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_dec_eq(v___x_143_, v___x_144_);
lean_dec(v___x_143_);
if (v___x_145_ == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v___x_146_; 
lean_dec(v_fName_123_);
v___x_146_ = l_Lean_Expr_appArg_x21(v_e_118_);
lean_dec_ref(v_e_118_);
v_e_118_ = v___x_146_;
goto _start;
}
}
v___jp_124_:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2));
v___x_126_ = lean_name_eq(v_fName_123_, v___x_125_);
lean_dec(v_fName_123_);
if (v___x_126_ == 0)
{
lean_dec_ref(v_e_118_);
return v___x_119_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = l_Lean_Expr_getAppNumArgs(v_e_118_);
lean_dec_ref(v_e_118_);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_dec_eq(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
if (v___x_129_ == 0)
{
return v___x_129_;
}
else
{
return v___x_120_;
}
}
}
v___jp_130_:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5));
v___x_132_ = lean_name_eq(v_fName_123_, v___x_131_);
if (v___x_132_ == 0)
{
goto v___jp_124_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_133_ = l_Lean_Expr_getAppNumArgs(v_e_118_);
v___x_134_ = lean_unsigned_to_nat(3u);
v___x_135_ = lean_nat_dec_eq(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v___x_133_);
goto v___jp_124_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_fName_123_);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_sub(v___x_133_, v___x_136_);
lean_dec(v___x_133_);
v___x_138_ = lean_nat_sub(v___x_137_, v___x_136_);
lean_dec(v___x_137_);
v___x_139_ = l_Lean_Expr_getRevArg_x21(v_e_118_, v___x_138_);
lean_dec_ref(v_e_118_);
v_e_118_ = v___x_139_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v_f_121_);
lean_dec_ref(v_e_118_);
return v___x_119_;
}
}
}
else
{
lean_dec_ref(v_e_118_);
return v___x_120_;
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
lean_object* v_v_515_; lean_object* v___y_520_; lean_object* v_todo_521_; uint8_t v___x_524_; 
v___x_524_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_507_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_507_, v_root_505_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_654_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_654_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_654_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_654_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v_k_532_; lean_object* v_nargs_533_; lean_object* v_todo_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; 
v___x_530_ = l_Lean_Expr_getAppFn(v_a_526_);
switch(lean_obj_tag(v___x_530_))
{
case 9:
{
lean_object* v_a_563_; 
lean_del_object(v___x_528_);
lean_dec(v_a_526_);
v_a_563_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_a_563_);
lean_dec_ref_known(v___x_530_, 1);
v_v_515_ = v_a_563_;
goto v___jp_514_;
}
case 4:
{
lean_object* v_declName_564_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; 
lean_del_object(v___x_528_);
v_declName_564_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_declName_564_);
if (v_root_505_ == 0)
{
lean_object* v___x_572_; 
lean_inc(v_a_526_);
v___x_572_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_526_);
if (lean_obj_tag(v___x_572_) == 1)
{
lean_object* v_val_573_; 
lean_dec(v_declName_564_);
lean_dec_ref_known(v___x_530_, 2);
lean_dec(v_a_526_);
v_val_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v___x_572_, 1);
v_v_515_ = v_val_573_;
goto v___jp_514_;
}
else
{
lean_object* v___x_574_; 
lean_dec(v___x_572_);
v___x_574_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_declName_564_, v_a_526_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_585_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_585_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___x_579_; 
v___x_579_ = lean_unbox(v_a_575_);
lean_dec(v_a_575_);
if (v___x_579_ == 0)
{
lean_del_object(v___x_577_);
v___y_566_ = v_a_509_;
v___y_567_ = v_a_510_;
v___y_568_ = v_a_511_;
v___y_569_ = v_a_512_;
goto v___jp_565_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_dec(v_declName_564_);
lean_dec_ref_known(v___x_530_, 2);
lean_dec(v_a_526_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_todo_506_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_581_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_declName_564_);
lean_dec_ref_known(v___x_530_, 2);
lean_dec(v_a_526_);
lean_dec_ref(v_todo_506_);
v_a_586_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_574_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_574_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
v___y_566_ = v_a_509_;
v___y_567_ = v_a_510_;
v___y_568_ = v_a_511_;
v___y_569_ = v_a_512_;
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = l_Lean_Expr_getAppNumArgs(v_a_526_);
lean_inc(v___x_570_);
v___x_571_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_571_, 0, v_declName_564_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v_k_532_ = v___x_571_;
v_nargs_533_ = v___x_570_;
v_todo_534_ = v_todo_506_;
v___y_535_ = v___y_566_;
v___y_536_ = v___y_567_;
v___y_537_ = v___y_568_;
v___y_538_ = v___y_569_;
goto v___jp_531_;
}
}
case 11:
{
lean_object* v_typeName_594_; lean_object* v_idx_595_; lean_object* v_struct_596_; lean_object* v___x_597_; lean_object* v___y_599_; lean_object* v_env_603_; uint8_t v___x_604_; 
lean_del_object(v___x_528_);
v_typeName_594_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_typeName_594_);
v_idx_595_ = lean_ctor_get(v___x_530_, 1);
lean_inc(v_idx_595_);
v_struct_596_ = lean_ctor_get(v___x_530_, 2);
lean_inc_ref(v_struct_596_);
v___x_597_ = lean_st_ref_get(v_a_512_);
v_env_603_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_603_);
lean_dec(v___x_597_);
v___x_604_ = l_Lean_isClass(v_env_603_, v_typeName_594_);
if (v___x_604_ == 0)
{
v___y_599_ = v_struct_596_;
goto v___jp_598_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_596_);
v___y_599_ = v___x_605_;
goto v___jp_598_;
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_Expr_getAppNumArgs(v_a_526_);
lean_inc(v___x_600_);
v___x_601_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_601_, 0, v_typeName_594_);
lean_ctor_set(v___x_601_, 1, v_idx_595_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = lean_array_push(v_todo_506_, v___y_599_);
v_k_532_ = v___x_601_;
v_nargs_533_ = v___x_600_;
v_todo_534_ = v___x_602_;
v___y_535_ = v_a_509_;
v___y_536_ = v_a_510_;
v___y_537_ = v_a_511_;
v___y_538_ = v_a_512_;
goto v___jp_531_;
}
}
case 1:
{
lean_object* v_fvarId_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_528_);
v_fvarId_606_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_fvarId_606_);
v___x_607_ = l_Lean_Expr_getAppNumArgs(v_a_526_);
lean_inc(v___x_607_);
v___x_608_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_608_, 0, v_fvarId_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v_k_532_ = v___x_608_;
v_nargs_533_ = v___x_607_;
v_todo_534_ = v_todo_506_;
v___y_535_ = v_a_509_;
v___y_536_ = v_a_510_;
v___y_537_ = v_a_511_;
v___y_538_ = v_a_512_;
goto v___jp_531_;
}
case 2:
{
lean_object* v_mvarId_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
lean_dec(v_a_526_);
v_mvarId_609_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_mvarId_609_);
lean_dec_ref_known(v___x_530_, 1);
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId));
v___x_611_ = l_Lean_instBEqMVarId_beq(v_mvarId_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_del_object(v___x_528_);
v___x_612_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_609_, v_a_509_, v_a_510_, v_a_511_, v_a_512_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_628_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_628_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; 
v___x_617_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_todo_506_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_619_);
v___x_621_ = v___x_615_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_623_ = lean_box(1);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v_todo_506_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_624_);
v___x_626_ = v___x_615_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
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
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_todo_506_);
v_a_629_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_612_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_612_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
lean_dec(v_mvarId_609_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v_todo_506_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_638_);
v___x_640_ = v___x_528_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
case 7:
{
lean_object* v_binderType_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
lean_dec(v_a_526_);
v_binderType_642_ = lean_ctor_get(v___x_530_, 1);
lean_inc_ref(v_binderType_642_);
lean_dec_ref_known(v___x_530_, 3);
v___x_643_ = lean_box(5);
v___x_644_ = lean_array_push(v_todo_506_, v_binderType_642_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_645_);
v___x_647_ = v___x_528_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
default: 
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
lean_dec_ref(v___x_530_);
lean_dec(v_a_526_);
v___x_649_ = lean_box(1);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_todo_506_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_650_);
v___x_652_ = v___x_528_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
v___jp_531_:
{
lean_object* v___x_539_; 
lean_inc(v_nargs_533_);
v___x_539_ = l_Lean_Meta_getFunInfoNArgs(v___x_530_, v_nargs_533_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_539_) == 0)
{
if (v_noIndexAtArgs_508_ == 0)
{
lean_object* v_a_540_; lean_object* v_paramInfo_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v_paramInfo_541_ = lean_ctor_get(v_a_540_, 0);
lean_inc_ref(v_paramInfo_541_);
lean_dec(v_a_540_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_sub(v_nargs_533_, v___x_542_);
lean_dec(v_nargs_533_);
v___x_544_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_paramInfo_541_, v___x_543_, v_a_526_, v_todo_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec_ref(v_paramInfo_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___y_520_ = v_k_532_;
v_todo_521_ = v_a_545_;
goto v___jp_519_;
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_k_532_);
v_a_546_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
lean_object* v___x_554_; 
lean_dec_ref_known(v___x_539_, 1);
lean_dec(v_a_526_);
v___x_554_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(v_nargs_533_, v_todo_534_);
v___y_520_ = v_k_532_;
v_todo_521_ = v___x_554_;
goto v___jp_519_;
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_todo_534_);
lean_dec(v_nargs_533_);
lean_dec(v_k_532_);
lean_dec(v_a_526_);
v_a_555_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_539_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_539_);
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
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_todo_506_);
v_a_655_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_525_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_525_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v_e_507_);
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v_todo_506_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
v___jp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_516_, 0, v_v_515_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v_todo_506_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
v___jp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___y_520_);
lean_ctor_set(v___x_522_, 1, v_todo_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* v_root_666_, lean_object* v_todo_667_, lean_object* v_e_668_, lean_object* v_noIndexAtArgs_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
uint8_t v_root_boxed_675_; uint8_t v_noIndexAtArgs_boxed_676_; lean_object* v_res_677_; 
v_root_boxed_675_ = lean_unbox(v_root_666_);
v_noIndexAtArgs_boxed_676_ = lean_unbox(v_noIndexAtArgs_669_);
v_res_677_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_boxed_675_, v_todo_667_, v_e_668_, v_noIndexAtArgs_boxed_676_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t v_root_678_, lean_object* v_todo_679_, lean_object* v_keys_680_, uint8_t v_noIndexAtArgs_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_array_get_size(v_todo_679_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_e_693_; lean_object* v_todo_694_; lean_object* v___x_695_; 
v___x_690_ = l_Lean_instInhabitedExpr;
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_sub(v___x_687_, v___x_691_);
v_e_693_ = lean_array_get(v___x_690_, v_todo_679_, v___x_692_);
lean_dec(v___x_692_);
v_todo_694_ = lean_array_pop(v_todo_679_);
v___x_695_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_678_, v_todo_694_, v_e_693_, v_noIndexAtArgs_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v_fst_697_; lean_object* v_snd_698_; lean_object* v___x_699_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v_fst_697_ = lean_ctor_get(v_a_696_, 0);
lean_inc(v_fst_697_);
v_snd_698_ = lean_ctor_get(v_a_696_, 1);
lean_inc(v_snd_698_);
lean_dec(v_a_696_);
v___x_699_ = lean_array_push(v_keys_680_, v_fst_697_);
v_root_678_ = v___x_689_;
v_todo_679_ = v_snd_698_;
v_keys_680_ = v___x_699_;
goto _start;
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_keys_680_);
v_a_701_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_695_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_695_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v___x_709_; 
lean_dec_ref(v_todo_679_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_keys_680_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* v_root_710_, lean_object* v_todo_711_, lean_object* v_keys_712_, lean_object* v_noIndexAtArgs_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
uint8_t v_root_boxed_719_; uint8_t v_noIndexAtArgs_boxed_720_; lean_object* v_res_721_; 
v_root_boxed_719_ = lean_unbox(v_root_710_);
v_noIndexAtArgs_boxed_720_ = lean_unbox(v_noIndexAtArgs_713_);
v_res_721_ = l_Lean_Meta_DiscrTree_mkPathAux(v_root_boxed_719_, v_todo_711_, v_keys_712_, v_noIndexAtArgs_boxed_720_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_unsigned_to_nat(8u);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* v_e_723_, uint8_t v_noIndexAtArgs_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___y_731_; lean_object* v___x_748_; uint8_t v_transparency_749_; lean_object* v___x_750_; lean_object* v_todo_751_; uint8_t v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; uint8_t v___x_755_; 
v___x_748_ = l_Lean_Meta_Context_config(v_a_725_);
v_transparency_749_ = lean_ctor_get_uint8(v___x_748_, 9);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_unsigned_to_nat(8u);
v_todo_751_ = lean_mk_empty_array_with_capacity(v___x_750_);
v___x_752_ = 1;
lean_inc_ref(v_todo_751_);
v___x_753_ = lean_array_push(v_todo_751_, v_e_723_);
v___x_754_ = 2;
v___x_755_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_749_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v_keyedConfig_756_; uint8_t v_trackZetaDelta_757_; lean_object* v_zetaDeltaSet_758_; lean_object* v_lctx_759_; lean_object* v_localInstances_760_; lean_object* v_defEqCtx_x3f_761_; lean_object* v_synthPendingDepth_762_; lean_object* v_customCanUnfoldPredicate_x3f_763_; uint8_t v_univApprox_764_; uint8_t v_inTypeClassResolution_765_; uint8_t v_cacheInferType_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_keyedConfig_756_ = lean_ctor_get(v_a_725_, 0);
v_trackZetaDelta_757_ = lean_ctor_get_uint8(v_a_725_, sizeof(void*)*7);
v_zetaDeltaSet_758_ = lean_ctor_get(v_a_725_, 1);
v_lctx_759_ = lean_ctor_get(v_a_725_, 2);
v_localInstances_760_ = lean_ctor_get(v_a_725_, 3);
v_defEqCtx_x3f_761_ = lean_ctor_get(v_a_725_, 4);
v_synthPendingDepth_762_ = lean_ctor_get(v_a_725_, 5);
v_customCanUnfoldPredicate_x3f_763_ = lean_ctor_get(v_a_725_, 6);
v_univApprox_764_ = lean_ctor_get_uint8(v_a_725_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_765_ = lean_ctor_get_uint8(v_a_725_, sizeof(void*)*7 + 2);
v_cacheInferType_766_ = lean_ctor_get_uint8(v_a_725_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_756_);
v___x_767_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_754_, v_keyedConfig_756_);
lean_inc(v_customCanUnfoldPredicate_x3f_763_);
lean_inc(v_synthPendingDepth_762_);
lean_inc(v_defEqCtx_x3f_761_);
lean_inc_ref(v_localInstances_760_);
lean_inc_ref(v_lctx_759_);
lean_inc(v_zetaDeltaSet_758_);
v___x_768_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v_zetaDeltaSet_758_);
lean_ctor_set(v___x_768_, 2, v_lctx_759_);
lean_ctor_set(v___x_768_, 3, v_localInstances_760_);
lean_ctor_set(v___x_768_, 4, v_defEqCtx_x3f_761_);
lean_ctor_set(v___x_768_, 5, v_synthPendingDepth_762_);
lean_ctor_set(v___x_768_, 6, v_customCanUnfoldPredicate_x3f_763_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7, v_trackZetaDelta_757_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7 + 1, v_univApprox_764_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7 + 2, v_inTypeClassResolution_765_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7 + 3, v_cacheInferType_766_);
v___x_769_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_752_, v___x_753_, v_todo_751_, v_noIndexAtArgs_724_, v___x_768_, v_a_726_, v_a_727_, v_a_728_);
lean_dec_ref_known(v___x_768_, 7);
v___y_731_ = v___x_769_;
goto v___jp_730_;
}
else
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_752_, v___x_753_, v_todo_751_, v_noIndexAtArgs_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
v___y_731_ = v___x_770_;
goto v___jp_730_;
}
v___jp_730_:
{
if (lean_obj_tag(v___y_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
v_a_732_ = lean_ctor_get(v___y_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___y_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___y_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___y_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
v_a_740_ = lean_ctor_get(v___y_731_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___y_731_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___y_731_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___y_731_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object* v_e_771_, lean_object* v_noIndexAtArgs_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_778_; lean_object* v_res_779_; 
v_noIndexAtArgs_boxed_778_ = lean_unbox(v_noIndexAtArgs_772_);
v_res_779_ = l_Lean_Meta_DiscrTree_mkPath(v_e_771_, v_noIndexAtArgs_boxed_778_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg(lean_object* v_inst_780_, lean_object* v_d_781_, lean_object* v_e_782_, lean_object* v_v_783_, uint8_t v_noIndexAtArgs_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Meta_DiscrTree_mkPath(v_e_782_, v_noIndexAtArgs_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_799_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_780_, v_d_781_, v_a_791_, v_v_783_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_v_783_);
lean_dec_ref(v_d_781_);
lean_dec_ref(v_inst_780_);
v_a_800_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_790_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_790_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg___boxed(lean_object* v_inst_808_, lean_object* v_d_809_, lean_object* v_e_810_, lean_object* v_v_811_, lean_object* v_noIndexAtArgs_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_818_; lean_object* v_res_819_; 
v_noIndexAtArgs_boxed_818_ = lean_unbox(v_noIndexAtArgs_812_);
v_res_819_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_808_, v_d_809_, v_e_810_, v_v_811_, v_noIndexAtArgs_boxed_818_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* v_00_u03b1_820_, lean_object* v_inst_821_, lean_object* v_d_822_, lean_object* v_e_823_, lean_object* v_v_824_, uint8_t v_noIndexAtArgs_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_821_, v_d_822_, v_e_823_, v_v_824_, v_noIndexAtArgs_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___boxed(lean_object* v_00_u03b1_832_, lean_object* v_inst_833_, lean_object* v_d_834_, lean_object* v_e_835_, lean_object* v_v_836_, lean_object* v_noIndexAtArgs_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_843_; lean_object* v_res_844_; 
v_noIndexAtArgs_boxed_843_ = lean_unbox(v_noIndexAtArgs_837_);
v_res_844_ = l_Lean_Meta_DiscrTree_insert(v_00_u03b1_832_, v_inst_833_, v_d_834_, v_e_835_, v_v_836_, v_noIndexAtArgs_boxed_843_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
return v_res_844_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_860_ = lean_array_get_size(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_867_ = lean_array_get_size(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(lean_object* v_inst_868_, lean_object* v_d_869_, lean_object* v_e_870_, lean_object* v_v_871_, uint8_t v_noIndexAtArgs_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_DiscrTree_mkPath(v_e_870_, v_noIndexAtArgs_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_903_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_903_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_903_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_903_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_896_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_897_ = lean_array_get_size(v_a_879_);
v___x_898_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7);
v___x_899_ = lean_nat_dec_eq(v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
goto v___jp_888_;
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_901_ = l_Array_isEqvAux___redArg(v_a_879_, v___x_896_, v___x_900_, v___x_897_);
if (v___x_901_ == 0)
{
goto v___jp_888_;
}
else
{
lean_object* v___x_902_; 
lean_del_object(v___x_881_);
lean_dec(v_a_879_);
lean_dec(v_v_871_);
lean_dec_ref(v_inst_868_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v_d_869_);
return v___x_902_;
}
}
v___jp_883_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_868_, v_d_869_, v_a_879_, v_v_871_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_884_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
v___jp_888_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_889_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_890_ = lean_array_get_size(v_a_879_);
v___x_891_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4);
v___x_892_ = lean_nat_dec_eq(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
goto v___jp_883_;
}
else
{
lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_894_ = l_Array_isEqvAux___redArg(v_a_879_, v___x_889_, v___x_893_, v___x_890_);
if (v___x_894_ == 0)
{
goto v___jp_883_;
}
else
{
lean_object* v___x_895_; 
lean_del_object(v___x_881_);
lean_dec(v_a_879_);
lean_dec(v_v_871_);
lean_dec_ref(v_inst_868_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_d_869_);
return v___x_895_;
}
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_v_871_);
lean_dec_ref(v_d_869_);
lean_dec_ref(v_inst_868_);
v_a_904_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_878_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_878_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(lean_object* v_inst_912_, lean_object* v_d_913_, lean_object* v_e_914_, lean_object* v_v_915_, lean_object* v_noIndexAtArgs_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_922_; lean_object* v_res_923_; 
v_noIndexAtArgs_boxed_922_ = lean_unbox(v_noIndexAtArgs_916_);
v_res_923_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_912_, v_d_913_, v_e_914_, v_v_915_, v_noIndexAtArgs_boxed_922_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific(lean_object* v_00_u03b1_924_, lean_object* v_inst_925_, lean_object* v_d_926_, lean_object* v_e_927_, lean_object* v_v_928_, uint8_t v_noIndexAtArgs_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_925_, v_d_926_, v_e_927_, v_v_928_, v_noIndexAtArgs_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(lean_object* v_00_u03b1_936_, lean_object* v_inst_937_, lean_object* v_d_938_, lean_object* v_e_939_, lean_object* v_v_940_, lean_object* v_noIndexAtArgs_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_947_; lean_object* v_res_948_; 
v_noIndexAtArgs_boxed_947_ = lean_unbox(v_noIndexAtArgs_941_);
v_res_948_ = l_Lean_Meta_DiscrTree_insertIfSpecific(v_00_u03b1_936_, v_inst_937_, v_d_938_, v_e_939_, v_v_940_, v_noIndexAtArgs_boxed_947_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(lean_object* v_declName_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; lean_object* v_env_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_952_ = lean_st_ref_get(v___y_950_);
v_env_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc_ref(v_env_953_);
lean_dec(v___x_952_);
v___x_954_ = l_Lean_isRecCore(v_env_953_, v_declName_949_);
v___x_955_ = lean_box(v___x_954_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_957_, v___y_958_);
lean_dec(v___y_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(lean_object* v_declName_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_961_, v___y_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(lean_object* v_declName_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
lean_object* v_array_978_; lean_object* v_start_979_; lean_object* v_stop_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_997_; 
v_array_978_ = lean_ctor_get(v_a_975_, 0);
v_start_979_ = lean_ctor_get(v_a_975_, 1);
v_stop_980_ = lean_ctor_get(v_a_975_, 2);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_975_);
if (v_isSharedCheck_997_ == 0)
{
v___x_982_ = v_a_975_;
v_isShared_983_ = v_isSharedCheck_997_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_stop_980_);
lean_inc(v_start_979_);
lean_inc(v_array_978_);
lean_dec(v_a_975_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_997_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v___x_984_; 
v___x_984_ = lean_nat_dec_lt(v_start_979_, v_stop_980_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_del_object(v___x_982_);
lean_dec(v_stop_980_);
lean_dec(v_start_979_);
lean_dec_ref(v_array_978_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v_b_976_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_986_ = lean_box(0);
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_nat_add(v_start_979_, v___x_987_);
lean_inc_ref(v_array_978_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_988_);
v___x_990_ = v___x_982_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_array_978_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_stop_980_);
v___x_990_ = v_reuseFailAlloc_996_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_fget(v_array_978_, v_start_979_);
lean_dec(v_start_979_);
lean_dec_ref(v_array_978_);
v___x_992_ = l_Lean_Expr_hasExprMVar(v___x_991_);
lean_dec(v___x_991_);
if (v___x_992_ == 0)
{
v_a_975_ = v___x_990_;
v_b_976_ = v___x_986_;
goto _start;
}
else
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_994_) == 0)
{
lean_dec_ref_known(v___x_994_, 1);
v_a_975_ = v___x_990_;
v_b_976_ = v___x_986_;
goto _start;
}
else
{
lean_dec_ref(v___x_990_);
return v___x_994_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_998_, lean_object* v_b_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_998_, v_b_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v_env_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1005_ = lean_st_ref_get(v___y_1003_);
v_env_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc_ref(v_env_1006_);
lean_dec(v___x_1005_);
v___x_1007_ = l_Lean_getReducibilityStatusCore(v_env_1006_, v_declName_1002_);
v___x_1008_ = lean_box(v___x_1007_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1010_, v___y_1011_);
lean_dec(v___y_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(lean_object* v_declName_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1036_; 
v___x_1020_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1014_, v___y_1018_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1036_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1036_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_unbox(v_a_1021_);
lean_dec(v_a_1021_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1026_ = 1;
v___x_1027_ = lean_box(v___x_1026_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1027_);
v___x_1029_ = v___x_1023_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
else
{
uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = 0;
v___x_1032_ = lean_box(v___x_1031_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1032_);
v___x_1034_ = v___x_1023_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0___boxed(lean_object* v_declName_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1(void){
_start:
{
lean_object* v___x_1046_; lean_object* v_dummy_1047_; 
v___x_1046_ = lean_box(0);
v_dummy_1047_ = l_Lean_Expr_sort___override(v___x_1046_);
return v_dummy_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* v_e_1054_, uint8_t v_isMatch_1055_, uint8_t v_root_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1054_, v_root_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1219_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1219_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1219_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___y_1068_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; 
if (v_root_1056_ == 0)
{
lean_object* v___x_1207_; 
lean_inc(v_a_1063_);
v___x_1207_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_1063_);
if (lean_obj_tag(v___x_1207_) == 1)
{
lean_object* v_val_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1218_; 
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v_val_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_val_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 2);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_val_1208_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
}
}
else
{
lean_dec(v___x_1207_);
v___y_1078_ = v_a_1057_;
v___y_1079_ = v_a_1058_;
v___y_1080_ = v_a_1059_;
v___y_1081_ = v_a_1060_;
goto v___jp_1077_;
}
}
else
{
v___y_1078_ = v_a_1057_;
v___y_1079_ = v_a_1058_;
v___y_1080_ = v_a_1059_;
v___y_1081_ = v_a_1060_;
goto v___jp_1077_;
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1069_ = l_Lean_Expr_getAppNumArgs(v_a_1063_);
lean_inc(v___x_1069_);
v___x_1070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___y_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_mk_empty_array_with_capacity(v___x_1069_);
lean_dec(v___x_1069_);
v___x_1072_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1063_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1070_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1073_);
v___x_1075_ = v___x_1065_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
v___jp_1077_:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Expr_getAppFn(v_a_1063_);
switch(lean_obj_tag(v___x_1082_))
{
case 9:
{
lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1083_);
v___x_1085_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
case 4:
{
lean_object* v_declName_1088_; lean_object* v___x_1089_; uint8_t v_isDefEqStuckEx_1090_; 
v_declName_1088_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_declName_1088_);
lean_dec_ref_known(v___x_1082_, 2);
v___x_1089_ = l_Lean_Meta_Context_config(v___y_1078_);
v_isDefEqStuckEx_1090_ = lean_ctor_get_uint8(v___x_1089_, 4);
lean_dec_ref(v___x_1089_);
if (v_isDefEqStuckEx_1090_ == 0)
{
v___y_1068_ = v_declName_1088_;
goto v___jp_1067_;
}
else
{
uint8_t v___x_1091_; 
v___x_1091_ = l_Lean_Expr_hasExprMVar(v_a_1063_);
if (v___x_1091_ == 0)
{
v___y_1068_ = v_declName_1088_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1092_; 
lean_inc(v_declName_1088_);
v___x_1092_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1088_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; uint8_t v___x_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = lean_unbox(v_a_1093_);
lean_dec(v_a_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v_env_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_st_ref_get(v___y_1081_);
v_env_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_env_1096_);
lean_dec(v___x_1095_);
v___x_1097_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1096_, v_a_1063_);
if (lean_obj_tag(v___x_1097_) == 1)
{
lean_object* v_val_1098_; lean_object* v_numDiscrs_1099_; lean_object* v_nargs_1100_; lean_object* v_dummy_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_val_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_val_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v_numDiscrs_1099_ = lean_ctor_get(v_val_1098_, 1);
lean_inc(v_numDiscrs_1099_);
v_nargs_1100_ = l_Lean_Expr_getAppNumArgs(v_a_1063_);
v_dummy_1101_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
lean_inc(v_nargs_1100_);
v___x_1102_ = lean_mk_array(v_nargs_1100_, v_dummy_1101_);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_sub(v_nargs_1100_, v___x_1103_);
lean_dec(v_nargs_1100_);
lean_inc(v_a_1063_);
v___x_1105_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1063_, v___x_1102_, v___x_1104_);
v___x_1106_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1098_);
lean_dec(v_val_1098_);
v___x_1107_ = lean_nat_add(v___x_1106_, v_numDiscrs_1099_);
lean_dec(v_numDiscrs_1099_);
v___x_1108_ = l_Array_toSubarray___redArg(v___x_1105_, v___x_1106_, v___x_1107_);
v___x_1109_ = lean_box(0);
v___x_1110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_1108_, v___x_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v___y_1068_ = v_declName_1088_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_declName_1088_);
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v_a_1120_; uint8_t v___x_1121_; 
lean_dec(v___x_1097_);
lean_inc(v_declName_1088_);
v___x_1119_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_1088_, v___y_1081_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1119_);
v___x_1121_ = lean_unbox(v_a_1120_);
lean_dec(v_a_1120_);
if (v___x_1121_ == 0)
{
v___y_1068_ = v_declName_1088_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_dec_ref_known(v___x_1122_, 1);
v___y_1068_ = v_declName_1088_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_declName_1088_);
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
else
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_dec_ref_known(v___x_1131_, 1);
v___y_1068_ = v_declName_1088_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_declName_1088_);
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_declName_1088_);
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v_a_1140_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1092_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1092_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_del_object(v___x_1065_);
v_fvarId_1148_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_fvarId_1148_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1149_ = l_Lean_Expr_getAppNumArgs(v_a_1063_);
lean_inc(v___x_1149_);
v___x_1150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_fvarId_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_mk_empty_array_with_capacity(v___x_1149_);
lean_dec(v___x_1149_);
v___x_1152_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1063_, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1150_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
case 2:
{
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
if (v_isMatch_1055_ == 0)
{
lean_object* v_mvarId_1155_; lean_object* v___x_1156_; uint8_t v_isDefEqStuckEx_1157_; 
v_mvarId_1155_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_mvarId_1155_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1156_ = l_Lean_Meta_Context_config(v___y_1078_);
v_isDefEqStuckEx_1157_ = lean_ctor_get_uint8(v___x_1156_, 4);
lean_dec_ref(v___x_1156_);
if (v_isDefEqStuckEx_1157_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1155_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1172_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_unbox(v_a_1159_);
lean_dec(v_a_1159_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1164_);
v___x_1166_ = v___x_1161_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1168_);
v___x_1170_ = v___x_1161_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1158_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1158_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v_mvarId_1155_);
v___x_1181_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec_ref_known(v___x_1082_, 1);
v___x_1183_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
}
case 11:
{
lean_object* v_typeName_1185_; lean_object* v_idx_1186_; lean_object* v_struct_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_del_object(v___x_1065_);
v_typeName_1185_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_typeName_1185_);
v_idx_1186_ = lean_ctor_get(v___x_1082_, 1);
lean_inc(v_idx_1186_);
v_struct_1187_ = lean_ctor_get(v___x_1082_, 2);
lean_inc_ref(v_struct_1187_);
lean_dec_ref_known(v___x_1082_, 3);
v___x_1188_ = l_Lean_Expr_getAppNumArgs(v_a_1063_);
lean_inc(v___x_1188_);
v___x_1189_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1189_, 0, v_typeName_1185_);
lean_ctor_set(v___x_1189_, 1, v_idx_1186_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_mk_empty_array_with_capacity(v___x_1190_);
v___x_1192_ = lean_array_push(v___x_1191_, v_struct_1187_);
v___x_1193_ = lean_mk_empty_array_with_capacity(v___x_1188_);
lean_dec(v___x_1188_);
v___x_1194_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1063_, v___x_1193_);
v___x_1195_ = l_Array_append___redArg(v___x_1192_, v___x_1194_);
lean_dec_ref(v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1189_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
case 7:
{
lean_object* v_binderType_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v_binderType_1198_ = lean_ctor_get(v___x_1082_, 1);
lean_inc_ref(v_binderType_1198_);
lean_dec_ref_known(v___x_1082_, 3);
v___x_1199_ = lean_box(5);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
v___x_1202_ = lean_array_push(v___x_1201_, v_binderType_1198_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1199_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
default: 
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v___x_1082_);
lean_del_object(v___x_1065_);
lean_dec(v_a_1063_);
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1062_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1062_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* v_e_1228_, lean_object* v_isMatch_1229_, lean_object* v_root_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
uint8_t v_isMatch_boxed_1236_; uint8_t v_root_boxed_1237_; lean_object* v_res_1238_; 
v_isMatch_boxed_1236_ = lean_unbox(v_isMatch_1229_);
v_root_boxed_1237_ = lean_unbox(v_root_1230_);
v_res_1238_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1228_, v_isMatch_boxed_1236_, v_root_boxed_1237_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1239_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object* v_inst_1253_, lean_object* v_R_1254_, lean_object* v_a_1255_, lean_object* v_b_1256_, lean_object* v_c_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1255_, v_b_1256_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object* v_inst_1264_, lean_object* v_R_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_, lean_object* v_c_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_1264_, v_R_1265_, v_a_1266_, v_b_1267_, v_c_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* v_e_1275_, uint8_t v_root_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
uint8_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = 1;
v___x_1283_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1275_, v___x_1282_, v_root_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* v_e_1284_, lean_object* v_root_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint8_t v_root_boxed_1291_; lean_object* v_res_1292_; 
v_root_boxed_1291_ = lean_unbox(v_root_1285_);
v_res_1292_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1284_, v_root_boxed_1291_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* v_e_1293_, uint8_t v_root_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
uint8_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = 0;
v___x_1301_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1293_, v___x_1300_, v_root_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* v_e_1302_, lean_object* v_root_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
uint8_t v_root_boxed_1309_; lean_object* v_res_1310_; 
v_root_boxed_1309_ = lean_unbox(v_root_1303_);
v_res_1310_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1302_, v_root_boxed_1309_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1311_, lean_object* v_vals_1312_, lean_object* v_i_1313_, lean_object* v_k_1314_){
_start:
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = lean_array_get_size(v_keys_1311_);
v___x_1316_ = lean_nat_dec_lt(v_i_1313_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec(v_i_1313_);
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
lean_object* v_k_x27_1318_; uint8_t v___x_1319_; 
v_k_x27_1318_ = lean_array_fget_borrowed(v_keys_1311_, v_i_1313_);
v___x_1319_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1314_, v_k_x27_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_i_1313_, v___x_1320_);
lean_dec(v_i_1313_);
v_i_1313_ = v___x_1321_;
goto _start;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_array_fget_borrowed(v_vals_1312_, v_i_1313_);
lean_dec(v_i_1313_);
lean_inc(v___x_1323_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1325_, lean_object* v_vals_1326_, lean_object* v_i_1327_, lean_object* v_k_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1325_, v_vals_1326_, v_i_1327_, v_k_1328_);
lean_dec(v_k_1328_);
lean_dec_ref(v_vals_1326_);
lean_dec_ref(v_keys_1325_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1330_, size_t v_x_1331_, lean_object* v_x_1332_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 0)
{
lean_object* v_es_1333_; lean_object* v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; lean_object* v_j_1337_; lean_object* v___x_1338_; 
v_es_1333_ = lean_ctor_get(v_x_1330_, 0);
v___x_1334_ = lean_box(2);
v___x_1335_ = ((size_t)31ULL);
v___x_1336_ = lean_usize_land(v_x_1331_, v___x_1335_);
v_j_1337_ = lean_usize_to_nat(v___x_1336_);
v___x_1338_ = lean_array_get_borrowed(v___x_1334_, v_es_1333_, v_j_1337_);
lean_dec(v_j_1337_);
switch(lean_obj_tag(v___x_1338_))
{
case 0:
{
lean_object* v_key_1339_; lean_object* v_val_1340_; uint8_t v___x_1341_; 
v_key_1339_ = lean_ctor_get(v___x_1338_, 0);
v_val_1340_ = lean_ctor_get(v___x_1338_, 1);
v___x_1341_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1332_, v_key_1339_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_box(0);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; 
lean_inc(v_val_1340_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_val_1340_);
return v___x_1343_;
}
}
case 1:
{
lean_object* v_node_1344_; size_t v___x_1345_; size_t v___x_1346_; 
v_node_1344_ = lean_ctor_get(v___x_1338_, 0);
v___x_1345_ = ((size_t)5ULL);
v___x_1346_ = lean_usize_shift_right(v_x_1331_, v___x_1345_);
v_x_1330_ = v_node_1344_;
v_x_1331_ = v___x_1346_;
goto _start;
}
default: 
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_box(0);
return v___x_1348_;
}
}
}
else
{
lean_object* v_ks_1349_; lean_object* v_vs_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_ks_1349_ = lean_ctor_get(v_x_1330_, 0);
v_vs_1350_ = lean_ctor_get(v_x_1330_, 1);
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1349_, v_vs_1350_, v___x_1351_, v_x_1332_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
size_t v_x_184__boxed_1356_; lean_object* v_res_1357_; 
v_x_184__boxed_1356_ = lean_unbox_usize(v_x_1354_);
lean_dec(v_x_1354_);
v_res_1357_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1353_, v_x_184__boxed_1356_, v_x_1355_);
lean_dec(v_x_1355_);
lean_dec_ref(v_x_1353_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
uint64_t v___x_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1359_);
v___x_1361_ = lean_uint64_to_usize(v___x_1360_);
v___x_1362_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1358_, v___x_1361_, v_x_1359_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1363_, v_x_1364_);
lean_dec(v_x_1364_);
lean_dec_ref(v_x_1363_);
return v_res_1365_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_result_1370_; lean_object* v___x_1371_; 
v___x_1368_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_1369_ = lean_unsigned_to_nat(8u);
v_result_1370_ = lean_mk_empty_array_with_capacity(v___x_1369_);
v___x_1371_ = l_Array_append___redArg(v_result_1370_, v___x_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v_result_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1373_ = lean_unsigned_to_nat(8u);
v_result_1374_ = lean_mk_empty_array_with_capacity(v___x_1373_);
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1372_, v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
return v_result_1374_;
}
else
{
lean_object* v_val_1377_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1376_, 1);
if (lean_obj_tag(v_val_1377_) == 0)
{
lean_object* v___x_1378_; 
lean_dec_ref_known(v_val_1377_, 2);
lean_dec_ref(v_result_1374_);
v___x_1378_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1);
return v___x_1378_;
}
else
{
lean_object* v_vs_1379_; lean_object* v___x_1380_; 
v_vs_1379_ = lean_ctor_get(v_val_1377_, 0);
lean_inc_ref(v_vs_1379_);
lean_dec_ref_known(v_val_1377_, 2);
v___x_1380_ = l_Array_append___redArg(v_result_1374_, v_vs_1379_);
lean_dec_ref(v_vs_1379_);
return v___x_1380_;
}
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
size_t v_x_285__boxed_1406_; lean_object* v_res_1407_; 
v_x_285__boxed_1406_ = lean_unbox_usize(v_x_1404_);
lean_dec(v_x_1404_);
v_res_1407_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1402_, v_x_1403_, v_x_285__boxed_1406_, v_x_1405_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1435_, lean_object* v_k_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_array_get_size(v_cs_1435_);
v___x_1439_ = lean_nat_dec_lt(v___x_1437_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_k_1436_);
v___x_1440_ = lean_box(0);
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = lean_unsigned_to_nat(1u);
v___x_1442_ = lean_nat_sub(v___x_1438_, v___x_1441_);
v___x_1443_ = lean_nat_dec_le(v___x_1437_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec(v___x_1442_);
lean_dec(v_k_1436_);
v___x_1444_ = lean_box(0);
return v___x_1444_;
}
else
{
lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___f_1445_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_k_1436_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1449_ = l_Array_binSearchAux___redArg(v___f_1445_, v___x_1448_, v_cs_1435_, v___x_1447_, v___x_1437_, v___x_1442_);
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1450_, lean_object* v_k_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1450_, v_k_1451_);
lean_dec_ref(v_cs_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1453_, lean_object* v_cs_1454_, lean_object* v_k_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = lean_array_get_size(v_cs_1454_);
v___x_1458_ = lean_nat_dec_lt(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_k_1455_);
v___x_1459_ = lean_box(0);
return v___x_1459_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_sub(v___x_1457_, v___x_1460_);
v___x_1462_ = lean_nat_dec_le(v___x_1456_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_dec(v___x_1461_);
lean_dec(v_k_1455_);
v___x_1463_ = lean_box(0);
return v___x_1463_;
}
else
{
lean_object* v___f_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___f_1464_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1465_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_k_1455_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1468_ = l_Array_binSearchAux___redArg(v___f_1464_, v___x_1467_, v_cs_1454_, v___x_1466_, v___x_1456_, v___x_1461_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_cs_1470_, lean_object* v_k_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1469_, v_cs_1470_, v_k_1471_);
lean_dec_ref(v_cs_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1473_, lean_object* v_k_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_m_1479_; lean_object* v_a_1480_; uint8_t v___x_1481_; 
v___x_1477_ = lean_nat_add(v_x_1475_, v_x_1476_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v_m_1479_ = lean_nat_shiftr(v___x_1477_, v___x_1478_);
lean_dec(v___x_1477_);
v_a_1480_ = lean_array_fget_borrowed(v_as_1473_, v_m_1479_);
v___x_1481_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1480_, v_k_1474_);
if (v___x_1481_ == 0)
{
uint8_t v___x_1482_; 
lean_dec(v_x_1476_);
v___x_1482_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1474_, v_a_1480_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
lean_dec(v_m_1479_);
lean_dec(v_x_1475_);
lean_inc(v_a_1480_);
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_a_1480_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; uint8_t v___y_1488_; 
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_nat_dec_eq(v_m_1479_, v___x_1484_);
v___x_1486_ = lean_nat_sub(v_m_1479_, v___x_1478_);
lean_dec(v_m_1479_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_nat_dec_lt(v___x_1486_, v_x_1475_);
v___y_1488_ = v___x_1491_;
goto v___jp_1487_;
}
else
{
v___y_1488_ = v___x_1485_;
goto v___jp_1487_;
}
v___jp_1487_:
{
if (v___y_1488_ == 0)
{
v_x_1476_ = v___x_1486_;
goto _start;
}
else
{
lean_object* v___x_1490_; 
lean_dec(v___x_1486_);
lean_dec(v_x_1475_);
v___x_1490_ = lean_box(0);
return v___x_1490_;
}
}
}
}
else
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
lean_dec(v_x_1475_);
v___x_1492_ = lean_nat_add(v_m_1479_, v___x_1478_);
lean_dec(v_m_1479_);
v___x_1493_ = lean_nat_dec_le(v___x_1492_, v_x_1476_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_dec(v___x_1492_);
lean_dec(v_x_1476_);
v___x_1494_ = lean_box(0);
return v___x_1494_;
}
else
{
v_x_1475_ = v___x_1492_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1496_, lean_object* v_k_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1496_, v_k_1497_, v_x_1498_, v_x_1499_);
lean_dec_ref(v_k_1497_);
lean_dec_ref(v_as_1496_);
return v_res_1500_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg();
return v___x_1501_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1505_, lean_object* v_c_1506_, lean_object* v_result_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_c_1506_) == 0)
{
lean_object* v_key_1514_; lean_object* v_child_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_key_1514_ = lean_ctor_get(v_c_1506_, 0);
lean_inc(v_key_1514_);
v_child_1515_ = lean_ctor_get(v_c_1506_, 1);
lean_inc_ref(v_child_1515_);
lean_dec_ref_known(v_c_1506_, 2);
v___x_1516_ = lean_array_get_size(v_todo_1505_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_nat_dec_eq(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_e_1521_; lean_object* v_todo_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_nat_sub(v___x_1516_, v___x_1519_);
v_e_1521_ = lean_array_get(v___x_1513_, v_todo_1505_, v___x_1520_);
lean_dec(v___x_1520_);
v_todo_1522_ = lean_array_pop(v_todo_1505_);
v___x_1523_ = 1;
v___x_1524_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1521_, v___x_1523_, v___x_1518_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1540_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1540_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1540_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_fst_1529_; lean_object* v_snd_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_fst_1529_ = lean_ctor_get(v_a_1525_, 0);
lean_inc(v_fst_1529_);
v_snd_1530_ = lean_ctor_get(v_a_1525_, 1);
lean_inc(v_snd_1530_);
lean_dec(v_a_1525_);
v___x_1531_ = lean_box(0);
v___x_1532_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1514_, v___x_1531_);
if (v___x_1532_ == 0)
{
uint8_t v___x_1533_; 
v___x_1533_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1514_, v_fst_1529_);
lean_dec(v_fst_1529_);
lean_dec(v_key_1514_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1535_; 
lean_dec(v_snd_1530_);
lean_dec_ref(v_todo_1522_);
lean_dec_ref(v_child_1515_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_result_1507_);
v___x_1535_ = v___x_1527_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_result_1507_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_object* v___x_1537_; 
lean_del_object(v___x_1527_);
v___x_1537_ = l_Array_append___redArg(v_todo_1522_, v_snd_1530_);
lean_dec(v_snd_1530_);
v_todo_1505_ = v___x_1537_;
v_c_1506_ = v_child_1515_;
goto _start;
}
}
else
{
lean_dec(v_snd_1530_);
lean_dec(v_fst_1529_);
lean_del_object(v___x_1527_);
lean_dec(v_key_1514_);
v_todo_1505_ = v_todo_1522_;
v_c_1506_ = v_child_1515_;
goto _start;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_todo_1522_);
lean_dec_ref(v_child_1515_);
lean_dec(v_key_1514_);
lean_dec_ref(v_result_1507_);
v_a_1541_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1524_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1524_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v___x_1549_; 
lean_dec_ref(v_child_1515_);
lean_dec(v_key_1514_);
lean_dec_ref(v_todo_1505_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_result_1507_);
return v___x_1549_;
}
}
else
{
lean_object* v_vs_1550_; lean_object* v_children_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_vs_1550_ = lean_ctor_get(v_c_1506_, 0);
lean_inc_ref(v_vs_1550_);
v_children_1551_ = lean_ctor_get(v_c_1506_, 1);
lean_inc_ref(v_children_1551_);
lean_dec_ref_known(v_c_1506_, 2);
v___x_1552_ = lean_array_get_size(v_todo_1505_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_nat_dec_eq(v___x_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
lean_dec_ref(v_vs_1550_);
v___x_1555_ = lean_array_get_size(v_children_1551_);
v___x_1556_ = lean_nat_dec_eq(v___x_1555_, v___x_1553_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_e_1561_; lean_object* v_todo_1562_; lean_object* v_first_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_sub(v___x_1552_, v___x_1559_);
v_e_1561_ = lean_array_get(v___x_1513_, v_todo_1505_, v___x_1560_);
lean_dec(v___x_1560_);
v_todo_1562_ = lean_array_pop(v_todo_1505_);
v_first_1563_ = lean_array_get_borrowed(v___x_1558_, v_children_1551_, v___x_1553_);
v___x_1564_ = 1;
v___x_1565_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1561_, v___x_1564_, v___x_1556_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1599_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1599_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1599_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1598_; 
v_fst_1570_ = lean_ctor_get(v_a_1566_, 0);
v_snd_1571_ = lean_ctor_get(v_a_1566_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_a_1566_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1573_ = v_a_1566_;
v_isShared_1574_ = v_isSharedCheck_1598_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1570_);
lean_dec(v_a_1566_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1598_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___y_1576_; lean_object* v_a_1577_; lean_object* v_fst_1590_; lean_object* v_snd_1591_; uint8_t v___x_1592_; 
v_fst_1590_ = lean_ctor_get(v_first_1563_, 0);
v_snd_1591_ = lean_ctor_get(v_first_1563_, 1);
v___x_1592_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1590_, v___x_1557_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1594_; 
lean_inc_ref(v_result_1507_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_result_1507_);
v___x_1594_ = v___x_1568_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_result_1507_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v___y_1576_ = v___x_1594_;
v_a_1577_ = v_result_1507_;
goto v___jp_1575_;
}
}
else
{
lean_object* v___x_1596_; 
lean_del_object(v___x_1568_);
lean_inc(v_snd_1591_);
lean_inc_ref(v_todo_1562_);
v___x_1596_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1562_, v_snd_1591_, v_result_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
v___y_1576_ = v___x_1596_;
v_a_1577_ = v_a_1597_;
goto v___jp_1575_;
}
else
{
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec_ref(v_todo_1562_);
lean_dec_ref(v_children_1551_);
return v___x_1596_;
}
}
v___jp_1575_:
{
if (lean_obj_tag(v_fst_1570_) == 0)
{
lean_dec_ref(v_a_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
lean_dec_ref(v_todo_1562_);
lean_dec_ref(v_children_1551_);
return v___y_1576_;
}
else
{
uint8_t v___x_1578_; 
v___x_1578_ = lean_nat_dec_lt(v___x_1553_, v___x_1555_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v_a_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec_ref(v_todo_1562_);
lean_dec_ref(v_children_1551_);
return v___y_1576_;
}
else
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = lean_nat_sub(v___x_1555_, v___x_1559_);
v___x_1580_ = lean_nat_dec_le(v___x_1553_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec(v___x_1579_);
lean_dec_ref(v_a_1577_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1571_);
lean_dec(v_fst_1570_);
lean_dec_ref(v_todo_1562_);
lean_dec_ref(v_children_1551_);
return v___y_1576_;
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1581_);
v___x_1583_ = v___x_1573_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_fst_1570_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1551_, v___x_1583_, v___x_1553_, v___x_1579_);
lean_dec_ref(v___x_1583_);
lean_dec_ref(v_children_1551_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_dec_ref(v_a_1577_);
lean_dec(v_snd_1571_);
lean_dec_ref(v_todo_1562_);
return v___y_1576_;
}
else
{
lean_object* v_val_1585_; lean_object* v_snd_1586_; lean_object* v___x_1587_; 
lean_dec_ref(v___y_1576_);
v_val_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v_snd_1586_ = lean_ctor_get(v_val_1585_, 1);
lean_inc(v_snd_1586_);
lean_dec(v_val_1585_);
v___x_1587_ = l_Array_append___redArg(v_todo_1562_, v_snd_1571_);
lean_dec(v_snd_1571_);
v_todo_1505_ = v___x_1587_;
v_c_1506_ = v_snd_1586_;
v_result_1507_ = v_a_1577_;
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
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_todo_1562_);
lean_dec_ref(v_children_1551_);
lean_dec_ref(v_result_1507_);
v_a_1600_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1565_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1565_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v___x_1608_; 
lean_dec_ref(v_children_1551_);
lean_dec_ref(v_todo_1505_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_result_1507_);
return v___x_1608_;
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref(v_children_1551_);
lean_dec_ref(v_todo_1505_);
v___x_1609_ = l_Array_append___redArg(v_result_1507_, v_vs_1550_);
lean_dec_ref(v_vs_1550_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1611_, lean_object* v_c_1612_, lean_object* v_result_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1611_, v_c_1612_, v_result_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1620_, lean_object* v_todo_1621_, lean_object* v_c_1622_, lean_object* v_result_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1621_, v_c_1622_, v_result_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_todo_1631_, lean_object* v_c_1632_, lean_object* v_result_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1630_, v_todo_1631_, v_c_1632_, v_result_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1640_, lean_object* v_as_1641_, lean_object* v_k_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1641_, v_k_1642_, v_x_1643_, v_x_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1647_, lean_object* v_as_1648_, lean_object* v_k_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1647_, v_as_1648_, v_k_1649_, v_x_1650_, v_x_1651_, v_x_1652_);
lean_dec_ref(v_k_1649_);
lean_dec_ref(v_as_1648_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1654_, lean_object* v_k_1655_, lean_object* v_args_1656_, lean_object* v_result_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1654_, v_k_1655_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v___x_1664_; 
lean_dec_ref(v_args_1656_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_result_1657_);
return v___x_1664_;
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1666_; 
v_val_1665_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1666_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1656_, v_val_1665_, v_result_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1667_, lean_object* v_k_1668_, lean_object* v_args_1669_, lean_object* v_result_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1667_, v_k_1668_, v_args_1669_, v_result_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_k_1668_);
lean_dec_ref(v_d_1667_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1677_, lean_object* v_d_1678_, lean_object* v_k_1679_, lean_object* v_args_1680_, lean_object* v_result_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1678_, v_k_1679_, v_args_1680_, v_result_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1688_, lean_object* v_d_1689_, lean_object* v_k_1690_, lean_object* v_args_1691_, lean_object* v_result_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1688_, v_d_1689_, v_k_1690_, v_args_1691_, v_result_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_k_1690_);
lean_dec_ref(v_d_1689_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(lean_object* v_e_1699_, uint8_t v___x_1700_, lean_object* v_result_1701_, lean_object* v_d_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1699_, v___x_1700_, v___x_1700_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1752_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1752_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1752_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_fst_1713_; 
v_fst_1713_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_fst_1713_);
if (lean_obj_tag(v_fst_1713_) == 0)
{
lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1723_; 
v_isSharedCheck_1723_ = !lean_is_exclusive(v_a_1709_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; lean_object* v_unused_1725_; 
v_unused_1724_ = lean_ctor_get(v_a_1709_, 1);
lean_dec(v_unused_1724_);
v_unused_1725_ = lean_ctor_get(v_a_1709_, 0);
lean_dec(v_unused_1725_);
v___x_1715_ = v_a_1709_;
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
else
{
lean_dec(v_a_1709_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_result_1701_);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_fst_1713_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_result_1701_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1718_);
v___x_1720_ = v___x_1711_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v_snd_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1750_; 
lean_del_object(v___x_1711_);
v_snd_1726_ = lean_ctor_get(v_a_1709_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_a_1709_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v_a_1709_, 0);
lean_dec(v_unused_1751_);
v___x_1728_ = v_a_1709_;
v_isShared_1729_ = v_isSharedCheck_1750_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_snd_1726_);
lean_dec(v_a_1709_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1750_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1702_, v_fst_1713_, v_snd_1726_, v_result_1701_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v_a_1731_);
v___x_1736_ = v___x_1728_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_fst_1713_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1736_);
v___x_1738_ = v___x_1733_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_del_object(v___x_1728_);
lean_dec(v_fst_1713_);
v_a_1742_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1730_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1730_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_result_1701_);
v_a_1753_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1708_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1708_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0___boxed(lean_object* v_e_1761_, lean_object* v___x_1762_, lean_object* v_result_1763_, lean_object* v_d_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
uint8_t v___x_802__boxed_1770_; lean_object* v_res_1771_; 
v___x_802__boxed_1770_ = lean_unbox(v___x_1762_);
v_res_1771_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1761_, v___x_802__boxed_1770_, v_result_1763_, v_d_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v_d_1764_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1772_, lean_object* v_e_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___y_1780_; lean_object* v___x_1797_; uint8_t v_transparency_1798_; lean_object* v_result_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; 
v___x_1797_ = l_Lean_Meta_Context_config(v_a_1774_);
v_transparency_1798_ = lean_ctor_get_uint8(v___x_1797_, 9);
lean_dec_ref(v___x_1797_);
v_result_1799_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1772_);
v___x_1800_ = 1;
v___x_1801_ = 2;
v___x_1802_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1798_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v_keyedConfig_1803_; uint8_t v_trackZetaDelta_1804_; lean_object* v_zetaDeltaSet_1805_; lean_object* v_lctx_1806_; lean_object* v_localInstances_1807_; lean_object* v_defEqCtx_x3f_1808_; lean_object* v_synthPendingDepth_1809_; lean_object* v_customCanUnfoldPredicate_x3f_1810_; uint8_t v_univApprox_1811_; uint8_t v_inTypeClassResolution_1812_; uint8_t v_cacheInferType_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_keyedConfig_1803_ = lean_ctor_get(v_a_1774_, 0);
v_trackZetaDelta_1804_ = lean_ctor_get_uint8(v_a_1774_, sizeof(void*)*7);
v_zetaDeltaSet_1805_ = lean_ctor_get(v_a_1774_, 1);
v_lctx_1806_ = lean_ctor_get(v_a_1774_, 2);
v_localInstances_1807_ = lean_ctor_get(v_a_1774_, 3);
v_defEqCtx_x3f_1808_ = lean_ctor_get(v_a_1774_, 4);
v_synthPendingDepth_1809_ = lean_ctor_get(v_a_1774_, 5);
v_customCanUnfoldPredicate_x3f_1810_ = lean_ctor_get(v_a_1774_, 6);
v_univApprox_1811_ = lean_ctor_get_uint8(v_a_1774_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1812_ = lean_ctor_get_uint8(v_a_1774_, sizeof(void*)*7 + 2);
v_cacheInferType_1813_ = lean_ctor_get_uint8(v_a_1774_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1803_);
v___x_1814_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1801_, v_keyedConfig_1803_);
lean_inc(v_customCanUnfoldPredicate_x3f_1810_);
lean_inc(v_synthPendingDepth_1809_);
lean_inc(v_defEqCtx_x3f_1808_);
lean_inc_ref(v_localInstances_1807_);
lean_inc_ref(v_lctx_1806_);
lean_inc(v_zetaDeltaSet_1805_);
v___x_1815_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v_zetaDeltaSet_1805_);
lean_ctor_set(v___x_1815_, 2, v_lctx_1806_);
lean_ctor_set(v___x_1815_, 3, v_localInstances_1807_);
lean_ctor_set(v___x_1815_, 4, v_defEqCtx_x3f_1808_);
lean_ctor_set(v___x_1815_, 5, v_synthPendingDepth_1809_);
lean_ctor_set(v___x_1815_, 6, v_customCanUnfoldPredicate_x3f_1810_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*7, v_trackZetaDelta_1804_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*7 + 1, v_univApprox_1811_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1812_);
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*7 + 3, v_cacheInferType_1813_);
v___x_1816_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1773_, v___x_1800_, v_result_1799_, v_d_1772_, v___x_1815_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec_ref_known(v___x_1815_, 7);
v___y_1780_ = v___x_1816_;
goto v___jp_1779_;
}
else
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1773_, v___x_1800_, v_result_1799_, v_d_1772_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
v___y_1780_ = v___x_1817_;
goto v___jp_1779_;
}
v___jp_1779_:
{
if (lean_obj_tag(v___y_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___y_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___y_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___y_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___y_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___y_1780_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___y_1780_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___y_1780_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___y_1780_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1818_, lean_object* v_e_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1818_, v_e_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec_ref(v_d_1818_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1826_, lean_object* v_d_1827_, lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1827_, v_e_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_d_1836_, lean_object* v_e_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1835_, v_d_1836_, v_e_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec_ref(v_d_1836_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1844_, lean_object* v_e_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1844_, v_e_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_snd_1856_; lean_object* v___x_1858_; 
v_snd_1856_ = lean_ctor_get(v_a_1852_, 1);
lean_inc(v_snd_1856_);
lean_dec(v_a_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_snd_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_snd_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1851_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1851_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1869_, lean_object* v_e_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1869_, v_e_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec_ref(v_d_1869_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1877_, lean_object* v_d_1878_, lean_object* v_e_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1878_, v_e_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_d_1887_, lean_object* v_e_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1886_, v_d_1887_, v_e_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec_ref(v_d_1887_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1895_, lean_object* v_k_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_k_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; 
switch(lean_obj_tag(v_k_1896_))
{
case 4:
{
lean_object* v_a_1924_; lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1936_; 
v_a_1924_ = lean_ctor_get(v_k_1896_, 0);
v_a_1925_ = lean_ctor_get(v_k_1896_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_k_1896_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1927_ = v_k_1896_;
v_isShared_1928_ = v_isSharedCheck_1936_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_inc(v_a_1924_);
lean_dec(v_k_1896_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1936_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_zero_1929_; uint8_t v_isZero_1930_; 
v_zero_1929_ = lean_unsigned_to_nat(0u);
v_isZero_1930_ = lean_nat_dec_eq(v_a_1925_, v_zero_1929_);
if (v_isZero_1930_ == 0)
{
lean_object* v_one_1931_; lean_object* v_n_1932_; lean_object* v___x_1934_; 
v_one_1931_ = lean_unsigned_to_nat(1u);
v_n_1932_ = lean_nat_sub(v_a_1925_, v_one_1931_);
lean_dec(v_a_1925_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v_n_1932_);
v___x_1934_ = v___x_1927_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1924_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_n_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
v_k_1907_ = v___x_1934_;
v___y_1908_ = v_a_1897_;
v___y_1909_ = v_a_1898_;
v___y_1910_ = v_a_1899_;
v___y_1911_ = v_a_1900_;
goto v___jp_1906_;
}
}
else
{
lean_del_object(v___x_1927_);
lean_dec(v_a_1925_);
lean_dec(v_a_1924_);
goto v___jp_1902_;
}
}
}
case 3:
{
lean_object* v_a_1937_; lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1949_; 
v_a_1937_ = lean_ctor_get(v_k_1896_, 0);
v_a_1938_ = lean_ctor_get(v_k_1896_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_k_1896_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1940_ = v_k_1896_;
v_isShared_1941_ = v_isSharedCheck_1949_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_inc(v_a_1937_);
lean_dec(v_k_1896_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1949_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_zero_1942_; uint8_t v_isZero_1943_; 
v_zero_1942_ = lean_unsigned_to_nat(0u);
v_isZero_1943_ = lean_nat_dec_eq(v_a_1938_, v_zero_1942_);
if (v_isZero_1943_ == 0)
{
lean_object* v_one_1944_; lean_object* v_n_1945_; lean_object* v___x_1947_; 
v_one_1944_ = lean_unsigned_to_nat(1u);
v_n_1945_ = lean_nat_sub(v_a_1938_, v_one_1944_);
lean_dec(v_a_1938_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v_n_1945_);
v___x_1947_ = v___x_1940_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1937_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_n_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v_k_1907_ = v___x_1947_;
v___y_1908_ = v_a_1897_;
v___y_1909_ = v_a_1898_;
v___y_1910_ = v_a_1899_;
v___y_1911_ = v_a_1900_;
goto v___jp_1906_;
}
}
else
{
lean_del_object(v___x_1940_);
lean_dec(v_a_1938_);
lean_dec(v_a_1937_);
goto v___jp_1902_;
}
}
}
case 6:
{
lean_object* v_a_1950_; lean_object* v_a_1951_; lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1963_; 
v_a_1950_ = lean_ctor_get(v_k_1896_, 0);
v_a_1951_ = lean_ctor_get(v_k_1896_, 1);
v_a_1952_ = lean_ctor_get(v_k_1896_, 2);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_k_1896_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1954_ = v_k_1896_;
v_isShared_1955_ = v_isSharedCheck_1963_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_inc(v_a_1951_);
lean_inc(v_a_1950_);
lean_dec(v_k_1896_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1963_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_zero_1956_; uint8_t v_isZero_1957_; 
v_zero_1956_ = lean_unsigned_to_nat(0u);
v_isZero_1957_ = lean_nat_dec_eq(v_a_1952_, v_zero_1956_);
if (v_isZero_1957_ == 0)
{
lean_object* v_one_1958_; lean_object* v_n_1959_; lean_object* v___x_1961_; 
v_one_1958_ = lean_unsigned_to_nat(1u);
v_n_1959_ = lean_nat_sub(v_a_1952_, v_one_1958_);
lean_dec(v_a_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 2, v_n_1959_);
v___x_1961_ = v___x_1954_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1950_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_a_1951_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_n_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v_k_1907_ = v___x_1961_;
v___y_1908_ = v_a_1897_;
v___y_1909_ = v_a_1898_;
v___y_1910_ = v_a_1899_;
v___y_1911_ = v_a_1900_;
goto v___jp_1906_;
}
}
else
{
lean_del_object(v___x_1954_);
lean_dec(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec(v_a_1950_);
goto v___jp_1902_;
}
}
}
default: 
{
lean_dec(v_k_1896_);
goto v___jp_1902_;
}
}
v___jp_1902_:
{
uint8_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = 0;
v___x_1904_ = lean_box(v___x_1903_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
v___jp_1906_:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1895_, v_k_1907_);
if (lean_obj_tag(v___x_1912_) == 0)
{
v_k_1896_ = v_k_1907_;
v_a_1897_ = v___y_1908_;
v_a_1898_ = v___y_1909_;
v_a_1899_ = v___y_1910_;
v_a_1900_ = v___y_1911_;
goto _start;
}
else
{
lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_k_1907_);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v___x_1912_, 0);
lean_dec(v_unused_1923_);
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1922_;
goto v_resetjp_1914_;
}
else
{
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1922_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = 1;
v___x_1918_ = lean_box(v___x_1917_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1918_);
v___x_1920_ = v___x_1915_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_1964_, lean_object* v_k_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1964_, v_k_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec_ref(v_d_1964_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_1972_, lean_object* v_d_1973_, lean_object* v_k_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1973_, v_k_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_d_1982_, lean_object* v_k_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_1981_, v_d_1982_, v_k_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_d_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_1990_, size_t v_sz_1991_, size_t v_i_1992_, lean_object* v_bs_1993_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
if (v___x_1994_ == 0)
{
lean_dec(v_numExtra_1990_);
return v_bs_1993_;
}
else
{
lean_object* v_v_1995_; lean_object* v___x_1996_; lean_object* v_bs_x27_1997_; lean_object* v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; 
v_v_1995_ = lean_array_uget(v_bs_1993_, v_i_1992_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v_bs_x27_1997_ = lean_array_uset(v_bs_1993_, v_i_1992_, v___x_1996_);
lean_inc(v_numExtra_1990_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_v_1995_);
lean_ctor_set(v___x_1998_, 1, v_numExtra_1990_);
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_add(v_i_1992_, v___x_1999_);
v___x_2001_ = lean_array_uset(v_bs_x27_1997_, v_i_1992_, v___x_1998_);
v_i_1992_ = v___x_2000_;
v_bs_1993_ = v___x_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_2003_, lean_object* v_sz_2004_, lean_object* v_i_2005_, lean_object* v_bs_2006_){
_start:
{
size_t v_sz_boxed_2007_; size_t v_i_boxed_2008_; lean_object* v_res_2009_; 
v_sz_boxed_2007_ = lean_unbox_usize(v_sz_2004_);
lean_dec(v_sz_2004_);
v_i_boxed_2008_ = lean_unbox_usize(v_i_2005_);
lean_dec(v_i_2005_);
v_res_2009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2003_, v_sz_boxed_2007_, v_i_boxed_2008_, v_bs_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_2010_, lean_object* v_e_2011_, lean_object* v_numExtra_2012_, lean_object* v_result_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___x_2019_; 
lean_inc_ref(v_e_2011_);
v___x_2019_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2010_, v_e_2011_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2037_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2037_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2037_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_snd_2024_; size_t v_sz_2025_; size_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v_snd_2024_ = lean_ctor_get(v_a_2020_, 1);
lean_inc(v_snd_2024_);
lean_dec(v_a_2020_);
v_sz_2025_ = lean_array_size(v_snd_2024_);
v___x_2026_ = ((size_t)0ULL);
lean_inc(v_numExtra_2012_);
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2012_, v_sz_2025_, v___x_2026_, v_snd_2024_);
v___x_2028_ = l_Array_append___redArg(v_result_2013_, v___x_2027_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = l_Lean_Expr_isApp(v_e_2011_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v_numExtra_2012_);
lean_dec_ref(v_e_2011_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2028_);
v___x_2031_ = v___x_2022_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2028_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_del_object(v___x_2022_);
v___x_2033_ = l_Lean_Expr_appFn_x21(v_e_2011_);
lean_dec_ref(v_e_2011_);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_numExtra_2012_, v___x_2034_);
lean_dec(v_numExtra_2012_);
v_e_2011_ = v___x_2033_;
v_numExtra_2012_ = v___x_2035_;
v_result_2013_ = v___x_2028_;
goto _start;
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_result_2013_);
lean_dec(v_numExtra_2012_);
lean_dec_ref(v_e_2011_);
v_a_2038_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2019_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2019_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2046_, lean_object* v_e_2047_, lean_object* v_numExtra_2048_, lean_object* v_result_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2046_, v_e_2047_, v_numExtra_2048_, v_result_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec_ref(v_d_2046_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2056_, lean_object* v_d_2057_, lean_object* v_e_2058_, lean_object* v_numExtra_2059_, lean_object* v_result_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2057_, v_e_2058_, v_numExtra_2059_, v_result_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2067_, lean_object* v_d_2068_, lean_object* v_e_2069_, lean_object* v_numExtra_2070_, lean_object* v_result_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2067_, v_d_2068_, v_e_2069_, v_numExtra_2070_, v_result_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec_ref(v_d_2068_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2078_, lean_object* v_numExtra_2079_, size_t v_sz_2080_, size_t v_i_2081_, lean_object* v_bs_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2079_, v_sz_2080_, v_i_2081_, v_bs_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_numExtra_2085_, lean_object* v_sz_2086_, lean_object* v_i_2087_, lean_object* v_bs_2088_){
_start:
{
size_t v_sz_boxed_2089_; size_t v_i_boxed_2090_; lean_object* v_res_2091_; 
v_sz_boxed_2089_ = lean_unbox_usize(v_sz_2086_);
lean_dec(v_sz_2086_);
v_i_boxed_2090_ = lean_unbox_usize(v_i_2087_);
lean_dec(v_i_2087_);
v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2084_, v_numExtra_2085_, v_sz_boxed_2089_, v_i_boxed_2090_, v_bs_2088_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2092_, size_t v_i_2093_, lean_object* v_bs_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_usize_dec_lt(v_i_2093_, v_sz_2092_);
if (v___x_2095_ == 0)
{
return v_bs_2094_;
}
else
{
lean_object* v_v_2096_; lean_object* v___x_2097_; lean_object* v_bs_x27_2098_; lean_object* v___x_2099_; size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v_v_2096_ = lean_array_uget(v_bs_2094_, v_i_2093_);
v___x_2097_ = lean_unsigned_to_nat(0u);
v_bs_x27_2098_ = lean_array_uset(v_bs_2094_, v_i_2093_, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_v_2096_);
lean_ctor_set(v___x_2099_, 1, v___x_2097_);
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2093_, v___x_2100_);
v___x_2102_ = lean_array_uset(v_bs_x27_2098_, v_i_2093_, v___x_2099_);
v_i_2093_ = v___x_2101_;
v_bs_2094_ = v___x_2102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2104_, lean_object* v_i_2105_, lean_object* v_bs_2106_){
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2104_);
lean_dec(v_sz_2104_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2105_);
lean_dec(v_i_2105_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2107_, v_i_boxed_2108_, v_bs_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2110_, lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v___x_2117_; 
lean_inc_ref(v_e_2111_);
v___x_2117_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2110_, v_e_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2152_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2152_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2152_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_fst_2122_; lean_object* v_snd_2123_; size_t v_sz_2124_; size_t v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_fst_2122_ = lean_ctor_get(v_a_2118_, 0);
lean_inc(v_fst_2122_);
v_snd_2123_ = lean_ctor_get(v_a_2118_, 1);
lean_inc(v_snd_2123_);
lean_dec(v_a_2118_);
v_sz_2124_ = lean_array_size(v_snd_2123_);
v___x_2125_ = ((size_t)0ULL);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2124_, v___x_2125_, v_snd_2123_);
v___x_2127_ = l_Lean_Expr_isApp(v_e_2111_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2129_; 
lean_dec(v_fst_2122_);
lean_dec_ref(v_e_2111_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2126_);
v___x_2129_ = v___x_2120_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2126_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
else
{
lean_object* v___x_2131_; 
lean_del_object(v___x_2120_);
v___x_2131_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2110_, v_fst_2122_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2143_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
uint8_t v___x_2136_; 
v___x_2136_ = lean_unbox(v_a_2132_);
lean_dec(v_a_2132_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref(v_e_2111_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2126_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2126_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_del_object(v___x_2134_);
v___x_2140_ = l_Lean_Expr_appFn_x21(v_e_2111_);
lean_dec_ref(v_e_2111_);
v___x_2141_ = lean_unsigned_to_nat(1u);
v___x_2142_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2110_, v___x_2140_, v___x_2141_, v___x_2126_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___x_2126_);
lean_dec_ref(v_e_2111_);
v_a_2144_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2131_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2131_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v_e_2111_);
v_a_2153_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2117_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2117_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2161_, lean_object* v_e_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2161_, v_e_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec_ref(v_d_2161_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2169_, lean_object* v_d_2170_, lean_object* v_e_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2170_, v_e_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2178_, lean_object* v_d_2179_, lean_object* v_e_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2178_, v_d_2179_, v_e_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec_ref(v_d_2179_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2187_, size_t v_sz_2188_, size_t v_i_2189_, lean_object* v_bs_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2188_, v_i_2189_, v_bs_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_sz_2193_, lean_object* v_i_2194_, lean_object* v_bs_2195_){
_start:
{
size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2193_);
lean_dec(v_sz_2193_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2194_);
lean_dec(v_i_2194_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2192_, v_sz_boxed_2196_, v_i_boxed_2197_, v_bs_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
uint8_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = 1;
v___x_2206_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2199_, v___x_2205_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2231_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___y_2213_; lean_object* v___x_2218_; 
v___x_2211_ = l_Lean_Expr_getAppNumArgs(v_a_2207_);
v___x_2218_ = l_Lean_Expr_getAppFn(v_a_2207_);
lean_dec(v_a_2207_);
switch(lean_obj_tag(v___x_2218_))
{
case 9:
{
lean_object* v_a_2219_; lean_object* v___x_2220_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc_ref(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2220_, 0, v_a_2219_);
v___y_2213_ = v___x_2220_;
goto v___jp_2212_;
}
case 1:
{
lean_object* v_fvarId_2221_; lean_object* v___x_2222_; 
v_fvarId_2221_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_fvarId_2221_);
lean_dec_ref_known(v___x_2218_, 1);
lean_inc(v___x_2211_);
v___x_2222_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_fvarId_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2211_);
v___y_2213_ = v___x_2222_;
goto v___jp_2212_;
}
case 2:
{
lean_object* v___x_2223_; 
lean_dec_ref_known(v___x_2218_, 1);
v___x_2223_ = lean_box(1);
v___y_2213_ = v___x_2223_;
goto v___jp_2212_;
}
case 11:
{
lean_object* v_typeName_2224_; lean_object* v_idx_2225_; lean_object* v___x_2226_; 
v_typeName_2224_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_typeName_2224_);
v_idx_2225_ = lean_ctor_get(v___x_2218_, 1);
lean_inc(v_idx_2225_);
lean_dec_ref_known(v___x_2218_, 3);
lean_inc(v___x_2211_);
v___x_2226_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2226_, 0, v_typeName_2224_);
lean_ctor_set(v___x_2226_, 1, v_idx_2225_);
lean_ctor_set(v___x_2226_, 2, v___x_2211_);
v___y_2213_ = v___x_2226_;
goto v___jp_2212_;
}
case 7:
{
lean_object* v___x_2227_; 
lean_dec_ref_known(v___x_2218_, 3);
v___x_2227_ = lean_box(5);
v___y_2213_ = v___x_2227_;
goto v___jp_2212_;
}
case 4:
{
lean_object* v_declName_2228_; lean_object* v___x_2229_; 
v_declName_2228_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_declName_2228_);
lean_dec_ref_known(v___x_2218_, 2);
lean_inc(v___x_2211_);
v___x_2229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2229_, 0, v_declName_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2211_);
v___y_2213_ = v___x_2229_;
goto v___jp_2212_;
}
default: 
{
lean_object* v___x_2230_; 
lean_dec_ref(v___x_2218_);
v___x_2230_ = lean_box(1);
v___y_2213_ = v___x_2230_;
goto v___jp_2212_;
}
}
v___jp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___y_2213_);
lean_ctor_set(v___x_2214_, 1, v___x_2211_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2214_);
v___x_2216_ = v___x_2209_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
v_a_2232_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2206_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2206_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2247_, size_t v_sz_2248_, size_t v_i_2249_, lean_object* v_b_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_usize_dec_lt(v_i_2249_, v_sz_2248_);
if (v___x_2251_ == 0)
{
return v_b_2250_;
}
else
{
lean_object* v_a_2252_; lean_object* v_snd_2253_; lean_object* v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; 
v_a_2252_ = lean_array_uget_borrowed(v_as_2247_, v_i_2249_);
v_snd_2253_ = lean_ctor_get(v_a_2252_, 1);
v___x_2254_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2253_, v_b_2250_);
v___x_2255_ = ((size_t)1ULL);
v___x_2256_ = lean_usize_add(v_i_2249_, v___x_2255_);
v_i_2249_ = v___x_2256_;
v_b_2250_ = v___x_2254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2258_, lean_object* v_result_2259_){
_start:
{
if (lean_obj_tag(v_trie_2258_) == 0)
{
lean_object* v_child_2260_; 
v_child_2260_ = lean_ctor_get(v_trie_2258_, 1);
v_trie_2258_ = v_child_2260_;
goto _start;
}
else
{
lean_object* v_vs_2262_; lean_object* v_children_2263_; lean_object* v_result_2264_; size_t v_sz_2265_; size_t v___x_2266_; lean_object* v___x_2267_; 
v_vs_2262_ = lean_ctor_get(v_trie_2258_, 0);
v_children_2263_ = lean_ctor_get(v_trie_2258_, 1);
v_result_2264_ = l_Array_append___redArg(v_result_2259_, v_vs_2262_);
v_sz_2265_ = lean_array_size(v_children_2263_);
v___x_2266_ = ((size_t)0ULL);
v___x_2267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2263_, v_sz_2265_, v___x_2266_, v_result_2264_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2268_, lean_object* v_result_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2268_, v_result_2269_);
lean_dec_ref(v_trie_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2271_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2274_);
lean_dec_ref(v_as_2271_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2278_, lean_object* v_trie_2279_, lean_object* v_result_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2279_, v_result_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_trie_2283_, lean_object* v_result_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2282_, v_trie_2283_, v_result_2284_);
lean_dec_ref(v_trie_2283_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2286_, lean_object* v_as_2287_, size_t v_sz_2288_, size_t v_i_2289_, lean_object* v_b_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2287_, v_sz_2288_, v_i_2289_, v_b_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_as_2293_, lean_object* v_sz_2294_, lean_object* v_i_2295_, lean_object* v_b_2296_){
_start:
{
size_t v_sz_boxed_2297_; size_t v_i_boxed_2298_; lean_object* v_res_2299_; 
v_sz_boxed_2297_ = lean_unbox_usize(v_sz_2294_);
lean_dec(v_sz_2294_);
v_i_boxed_2298_ = lean_unbox_usize(v_i_2295_);
lean_dec(v_i_2295_);
v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2292_, v_as_2293_, v_sz_boxed_2297_, v_i_boxed_2298_, v_b_2296_);
lean_dec_ref(v_as_2293_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2300_, lean_object* v_k_2301_, lean_object* v_result_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2300_, v_k_2301_);
if (lean_obj_tag(v___x_2303_) == 0)
{
return v_result_2302_;
}
else
{
lean_object* v_val_2304_; lean_object* v___x_2305_; 
v_val_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_val_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2304_, v_result_2302_);
lean_dec(v_val_2304_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2306_, lean_object* v_k_2307_, lean_object* v_result_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2306_, v_k_2307_, v_result_2308_);
lean_dec(v_k_2307_);
lean_dec_ref(v_d_2306_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2310_, lean_object* v_d_2311_, lean_object* v_k_2312_, lean_object* v_result_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2311_, v_k_2312_, v_result_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2315_, lean_object* v_d_2316_, lean_object* v_k_2317_, lean_object* v_result_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2315_, v_d_2316_, v_k_2317_, v_result_2318_);
lean_dec(v_k_2317_);
lean_dec_ref(v_d_2316_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(lean_object* v_e_2320_, lean_object* v_result_2321_, lean_object* v_d_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2320_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2346_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2346_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2346_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_fst_2333_; lean_object* v_snd_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2345_; 
v_fst_2333_ = lean_ctor_get(v_a_2329_, 0);
v_snd_2334_ = lean_ctor_get(v_a_2329_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_a_2329_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2336_ = v_a_2329_;
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snd_2334_);
lean_inc(v_fst_2333_);
lean_dec(v_a_2329_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2322_, v_fst_2333_, v_result_2321_);
lean_dec(v_fst_2333_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2338_);
v___x_2340_ = v___x_2336_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_snd_2334_);
v___x_2340_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2340_);
v___x_2342_ = v___x_2331_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v_result_2321_);
v_a_2347_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2328_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2328_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0___boxed(lean_object* v_e_2355_, lean_object* v_result_2356_, lean_object* v_d_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2355_, v_result_2356_, v_d_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v_d_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2364_, lean_object* v_e_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___y_2372_; lean_object* v___x_2389_; uint8_t v_transparency_2390_; lean_object* v_result_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2389_ = l_Lean_Meta_Context_config(v_a_2366_);
v_transparency_2390_ = lean_ctor_get_uint8(v___x_2389_, 9);
lean_dec_ref(v___x_2389_);
v_result_2391_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2364_);
v___x_2392_ = 2;
v___x_2393_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2390_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v_keyedConfig_2394_; uint8_t v_trackZetaDelta_2395_; lean_object* v_zetaDeltaSet_2396_; lean_object* v_lctx_2397_; lean_object* v_localInstances_2398_; lean_object* v_defEqCtx_x3f_2399_; lean_object* v_synthPendingDepth_2400_; lean_object* v_customCanUnfoldPredicate_x3f_2401_; uint8_t v_univApprox_2402_; uint8_t v_inTypeClassResolution_2403_; uint8_t v_cacheInferType_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_keyedConfig_2394_ = lean_ctor_get(v_a_2366_, 0);
v_trackZetaDelta_2395_ = lean_ctor_get_uint8(v_a_2366_, sizeof(void*)*7);
v_zetaDeltaSet_2396_ = lean_ctor_get(v_a_2366_, 1);
v_lctx_2397_ = lean_ctor_get(v_a_2366_, 2);
v_localInstances_2398_ = lean_ctor_get(v_a_2366_, 3);
v_defEqCtx_x3f_2399_ = lean_ctor_get(v_a_2366_, 4);
v_synthPendingDepth_2400_ = lean_ctor_get(v_a_2366_, 5);
v_customCanUnfoldPredicate_x3f_2401_ = lean_ctor_get(v_a_2366_, 6);
v_univApprox_2402_ = lean_ctor_get_uint8(v_a_2366_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2403_ = lean_ctor_get_uint8(v_a_2366_, sizeof(void*)*7 + 2);
v_cacheInferType_2404_ = lean_ctor_get_uint8(v_a_2366_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2394_);
v___x_2405_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2392_, v_keyedConfig_2394_);
lean_inc(v_customCanUnfoldPredicate_x3f_2401_);
lean_inc(v_synthPendingDepth_2400_);
lean_inc(v_defEqCtx_x3f_2399_);
lean_inc_ref(v_localInstances_2398_);
lean_inc_ref(v_lctx_2397_);
lean_inc(v_zetaDeltaSet_2396_);
v___x_2406_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v_zetaDeltaSet_2396_);
lean_ctor_set(v___x_2406_, 2, v_lctx_2397_);
lean_ctor_set(v___x_2406_, 3, v_localInstances_2398_);
lean_ctor_set(v___x_2406_, 4, v_defEqCtx_x3f_2399_);
lean_ctor_set(v___x_2406_, 5, v_synthPendingDepth_2400_);
lean_ctor_set(v___x_2406_, 6, v_customCanUnfoldPredicate_x3f_2401_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7, v_trackZetaDelta_2395_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 1, v_univApprox_2402_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2403_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 3, v_cacheInferType_2404_);
v___x_2407_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2365_, v_result_2391_, v_d_2364_, v___x_2406_, v_a_2367_, v_a_2368_, v_a_2369_);
lean_dec_ref_known(v___x_2406_, 7);
v___y_2372_ = v___x_2407_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2365_, v_result_2391_, v_d_2364_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
v___y_2372_ = v___x_2408_;
goto v___jp_2371_;
}
v___jp_2371_:
{
if (lean_obj_tag(v___y_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_a_2373_ = lean_ctor_get(v___y_2372_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___y_2372_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___y_2372_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___y_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_a_2381_ = lean_ctor_get(v___y_2372_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___y_2372_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___y_2372_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___y_2372_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2409_, lean_object* v_e_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2409_, v_e_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec_ref(v_d_2409_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2417_, lean_object* v_d_2418_, lean_object* v_e_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2418_, v_e_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_d_2427_, lean_object* v_e_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2426_, v_d_2427_, v_e_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec_ref(v_d_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2435_, lean_object* v_todo_2436_, lean_object* v_as_2437_, size_t v_i_2438_, size_t v_stop_2439_, lean_object* v_b_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v___x_2446_; 
v___x_2446_ = lean_usize_dec_eq(v_i_2438_, v_stop_2439_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v_fst_2448_; lean_object* v_snd_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2447_ = lean_array_uget_borrowed(v_as_2437_, v_i_2438_);
v_fst_2448_ = lean_ctor_get(v___x_2447_, 0);
v_snd_2449_ = lean_ctor_get(v___x_2447_, 1);
v___x_2450_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2448_);
v___x_2451_ = lean_nat_add(v_n_2435_, v___x_2450_);
lean_dec(v___x_2450_);
lean_inc(v_snd_2449_);
lean_inc_ref(v_todo_2436_);
v___x_2452_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2451_, v_todo_2436_, v_snd_2449_, v_b_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; size_t v___x_2454_; size_t v___x_2455_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_add(v_i_2438_, v___x_2454_);
v_i_2438_ = v___x_2455_;
v_b_2440_ = v_a_2453_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2436_);
return v___x_2452_;
}
}
else
{
lean_object* v___x_2457_; 
lean_dec_ref(v_todo_2436_);
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_b_2440_);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2458_, lean_object* v_todo_2459_, lean_object* v_c_2460_, lean_object* v_result_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v_a_2476_; lean_object* v___y_2489_; lean_object* v_zero_2492_; uint8_t v_isZero_2493_; 
v_zero_2492_ = lean_unsigned_to_nat(0u);
v_isZero_2493_ = lean_nat_dec_eq(v_skip_2458_, v_zero_2492_);
if (v_isZero_2493_ == 1)
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
lean_dec(v_skip_2458_);
v___x_2494_ = lean_array_get_size(v_todo_2459_);
v___x_2495_ = lean_nat_dec_eq(v___x_2494_, v_zero_2492_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___y_2500_; 
v___x_2496_ = l_Lean_instInhabitedExpr;
v___x_2497_ = lean_box(0);
v___x_2498_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
if (lean_obj_tag(v_c_2460_) == 0)
{
lean_object* v_key_2547_; lean_object* v_child_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2558_; 
v_key_2547_ = lean_ctor_get(v_c_2460_, 0);
v_child_2548_ = lean_ctor_get(v_c_2460_, 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_c_2460_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2550_ = v_c_2460_;
v_isShared_2551_ = v_isSharedCheck_2558_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_child_2548_);
lean_inc(v_key_2547_);
lean_dec(v_c_2460_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2558_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_key_2547_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_child_2548_);
v___x_2553_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_mk_empty_array_with_capacity(v___x_2554_);
v___x_2556_ = lean_array_push(v___x_2555_, v___x_2553_);
v___y_2500_ = v___x_2556_;
goto v___jp_2499_;
}
}
}
else
{
lean_object* v_children_2559_; 
v_children_2559_ = lean_ctor_get(v_c_2460_, 1);
lean_inc_ref(v_children_2559_);
lean_dec_ref_known(v_c_2460_, 2);
v___y_2500_ = v_children_2559_;
goto v___jp_2499_;
}
v___jp_2499_:
{
lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2501_ = lean_array_get_size(v___y_2500_);
v___x_2502_ = lean_nat_dec_eq(v___x_2501_, v_zero_2492_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v_e_2505_; lean_object* v_todo_2506_; lean_object* v___x_2507_; 
v___x_2503_ = lean_unsigned_to_nat(1u);
v___x_2504_ = lean_nat_sub(v___x_2494_, v___x_2503_);
v_e_2505_ = lean_array_get(v___x_2496_, v_todo_2459_, v___x_2504_);
lean_dec(v___x_2504_);
v_todo_2506_ = lean_array_pop(v_todo_2459_);
v___x_2507_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2505_, v___x_2502_, v___x_2502_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2537_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2537_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2537_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_fst_2512_; 
v_fst_2512_ = lean_ctor_get(v_a_2508_, 0);
lean_inc(v_fst_2512_);
if (lean_obj_tag(v_fst_2512_) == 0)
{
uint8_t v___x_2513_; 
lean_dec(v_a_2508_);
v___x_2513_ = lean_nat_dec_lt(v_zero_2492_, v___x_2501_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2515_; 
lean_dec_ref(v_todo_2506_);
lean_dec_ref(v___y_2500_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v_result_2461_);
v___x_2515_ = v___x_2510_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_result_2461_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
else
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_nat_dec_le(v___x_2501_, v___x_2501_);
if (v___x_2517_ == 0)
{
if (v___x_2513_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v_todo_2506_);
lean_dec_ref(v___y_2500_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v_result_2461_);
v___x_2519_ = v___x_2510_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_result_2461_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
else
{
size_t v___x_2521_; size_t v___x_2522_; lean_object* v___x_2523_; 
lean_del_object(v___x_2510_);
v___x_2521_ = ((size_t)0ULL);
v___x_2522_ = lean_usize_of_nat(v___x_2501_);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2506_, v___y_2500_, v___x_2521_, v___x_2522_, v_result_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec_ref(v___y_2500_);
return v___x_2523_;
}
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
lean_del_object(v___x_2510_);
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2501_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2506_, v___y_2500_, v___x_2524_, v___x_2525_, v_result_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec_ref(v___y_2500_);
return v___x_2526_;
}
}
}
else
{
lean_object* v_snd_2527_; lean_object* v___x_2528_; lean_object* v_fst_2529_; lean_object* v_snd_2530_; uint8_t v___x_2531_; 
v_snd_2527_ = lean_ctor_get(v_a_2508_, 1);
lean_inc(v_snd_2527_);
lean_dec(v_a_2508_);
v___x_2528_ = lean_array_get_borrowed(v___x_2498_, v___y_2500_, v_zero_2492_);
v_fst_2529_ = lean_ctor_get(v___x_2528_, 0);
v_snd_2530_ = lean_ctor_get(v___x_2528_, 1);
v___x_2531_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2529_, v___x_2497_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2533_; 
lean_inc_ref(v_result_2461_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v_result_2461_);
v___x_2533_ = v___x_2510_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_result_2461_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
v___y_2468_ = v_zero_2492_;
v___y_2469_ = v___x_2503_;
v___y_2470_ = v___x_2501_;
v___y_2471_ = v_fst_2512_;
v___y_2472_ = v___y_2500_;
v___y_2473_ = v_todo_2506_;
v___y_2474_ = v_snd_2527_;
v___y_2475_ = v___x_2533_;
v_a_2476_ = v_result_2461_;
goto v___jp_2467_;
}
}
else
{
lean_object* v___x_2535_; 
lean_del_object(v___x_2510_);
lean_inc(v_snd_2530_);
lean_inc_ref(v_todo_2506_);
v___x_2535_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2492_, v_todo_2506_, v_snd_2530_, v_result_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
v___y_2468_ = v_zero_2492_;
v___y_2469_ = v___x_2503_;
v___y_2470_ = v___x_2501_;
v___y_2471_ = v_fst_2512_;
v___y_2472_ = v___y_2500_;
v___y_2473_ = v_todo_2506_;
v___y_2474_ = v_snd_2527_;
v___y_2475_ = v___x_2535_;
v_a_2476_ = v_a_2536_;
goto v___jp_2467_;
}
else
{
lean_dec(v_snd_2527_);
lean_dec(v_fst_2512_);
lean_dec_ref(v_todo_2506_);
lean_dec_ref(v___y_2500_);
return v___x_2535_;
}
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v_todo_2506_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v_result_2461_);
v_a_2538_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2507_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2507_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v___x_2546_; 
lean_dec_ref(v___y_2500_);
lean_dec_ref(v_todo_2459_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_result_2461_);
return v___x_2546_;
}
}
}
else
{
lean_dec_ref(v_todo_2459_);
if (lean_obj_tag(v_c_2460_) == 0)
{
lean_object* v___x_2560_; 
lean_dec_ref_known(v_c_2460_, 2);
v___x_2560_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_2489_ = v___x_2560_;
goto v___jp_2488_;
}
else
{
lean_object* v_vs_2561_; 
v_vs_2561_ = lean_ctor_get(v_c_2460_, 0);
lean_inc_ref(v_vs_2561_);
lean_dec_ref_known(v_c_2460_, 2);
v___y_2489_ = v_vs_2561_;
goto v___jp_2488_;
}
}
}
else
{
lean_object* v_one_2562_; lean_object* v_n_2563_; 
v_one_2562_ = lean_unsigned_to_nat(1u);
v_n_2563_ = lean_nat_sub(v_skip_2458_, v_one_2562_);
lean_dec(v_skip_2458_);
if (lean_obj_tag(v_c_2460_) == 0)
{
lean_object* v_key_2564_; lean_object* v_child_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_key_2564_ = lean_ctor_get(v_c_2460_, 0);
lean_inc(v_key_2564_);
v_child_2565_ = lean_ctor_get(v_c_2460_, 1);
lean_inc_ref(v_child_2565_);
lean_dec_ref_known(v_c_2460_, 2);
v___x_2566_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2564_);
lean_dec(v_key_2564_);
v___x_2567_ = lean_nat_add(v_n_2563_, v___x_2566_);
lean_dec(v___x_2566_);
lean_dec(v_n_2563_);
v_skip_2458_ = v___x_2567_;
v_c_2460_ = v_child_2565_;
goto _start;
}
else
{
lean_object* v_children_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_children_2569_ = lean_ctor_get(v_c_2460_, 1);
lean_inc_ref(v_children_2569_);
lean_dec_ref_known(v_c_2460_, 2);
v___x_2570_ = lean_array_get_size(v_children_2569_);
v___x_2571_ = lean_nat_dec_eq(v___x_2570_, v_zero_2492_);
if (v___x_2571_ == 0)
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_nat_dec_lt(v_zero_2492_, v___x_2570_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref(v_children_2569_);
lean_dec(v_n_2563_);
lean_dec_ref(v_todo_2459_);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_result_2461_);
return v___x_2573_;
}
else
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_nat_dec_le(v___x_2570_, v___x_2570_);
if (v___x_2574_ == 0)
{
if (v___x_2572_ == 0)
{
lean_object* v___x_2575_; 
lean_dec_ref(v_children_2569_);
lean_dec(v_n_2563_);
lean_dec_ref(v_todo_2459_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_result_2461_);
return v___x_2575_;
}
else
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((size_t)0ULL);
v___x_2577_ = lean_usize_of_nat(v___x_2570_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2563_, v_todo_2459_, v_children_2569_, v___x_2576_, v___x_2577_, v_result_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec_ref(v_children_2569_);
lean_dec(v_n_2563_);
return v___x_2578_;
}
}
else
{
size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = lean_usize_of_nat(v___x_2570_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2563_, v_todo_2459_, v_children_2569_, v___x_2579_, v___x_2580_, v_result_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
lean_dec_ref(v_children_2569_);
lean_dec(v_n_2563_);
return v___x_2581_;
}
}
}
else
{
lean_object* v___x_2582_; 
lean_dec_ref(v_children_2569_);
lean_dec(v_n_2563_);
lean_dec_ref(v_todo_2459_);
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_result_2461_);
return v___x_2582_;
}
}
}
v___jp_2467_:
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_nat_dec_lt(v___y_2468_, v___y_2470_);
if (v___x_2477_ == 0)
{
lean_dec_ref(v_a_2476_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec(v___y_2468_);
return v___y_2475_;
}
else
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = lean_nat_sub(v___y_2470_, v___y_2469_);
lean_dec(v___y_2470_);
v___x_2479_ = lean_nat_dec_le(v___y_2468_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_dec(v___x_2478_);
lean_dec_ref(v_a_2476_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec(v___y_2468_);
return v___y_2475_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2480_ = lean_mk_empty_array_with_capacity(v___y_2468_);
lean_inc_ref(v___x_2480_);
v___x_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___y_2471_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
lean_inc(v___y_2468_);
v___x_2483_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v___y_2472_, v___x_2482_, v___y_2468_, v___x_2478_);
lean_dec_ref_known(v___x_2482_, 2);
lean_dec_ref(v___y_2472_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_dec_ref(v_a_2476_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2468_);
return v___y_2475_;
}
else
{
lean_object* v_val_2484_; lean_object* v_snd_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v___y_2475_);
v_val_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v_snd_2485_ = lean_ctor_get(v_val_2484_, 1);
lean_inc(v_snd_2485_);
lean_dec(v_val_2484_);
v___x_2486_ = l_Array_append___redArg(v___y_2473_, v___y_2474_);
lean_dec_ref(v___y_2474_);
v_skip_2458_ = v___y_2468_;
v_todo_2459_ = v___x_2486_;
v_c_2460_ = v_snd_2485_;
v_result_2461_ = v_a_2476_;
goto _start;
}
}
}
}
v___jp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = l_Array_append___redArg(v_result_2461_, v___y_2489_);
lean_dec_ref(v___y_2489_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2583_, lean_object* v_as_2584_, size_t v_i_2585_, size_t v_stop_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_eq(v_i_2585_, v_stop_2586_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v_fst_2595_; lean_object* v_snd_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2594_ = lean_array_uget_borrowed(v_as_2584_, v_i_2585_);
v_fst_2595_ = lean_ctor_get(v___x_2594_, 0);
v_snd_2596_ = lean_ctor_get(v___x_2594_, 1);
v___x_2597_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2595_);
lean_inc(v_snd_2596_);
lean_inc_ref(v_todo_2583_);
v___x_2598_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2597_, v_todo_2583_, v_snd_2596_, v_b_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; size_t v___x_2600_; size_t v___x_2601_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = ((size_t)1ULL);
v___x_2601_ = lean_usize_add(v_i_2585_, v___x_2600_);
v_i_2585_ = v___x_2601_;
v_b_2587_ = v_a_2599_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2583_);
return v___x_2598_;
}
}
else
{
lean_object* v___x_2603_; 
lean_dec_ref(v_todo_2583_);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v_b_2587_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2604_, lean_object* v_as_2605_, lean_object* v_i_2606_, lean_object* v_stop_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
size_t v_i_boxed_2614_; size_t v_stop_boxed_2615_; lean_object* v_res_2616_; 
v_i_boxed_2614_ = lean_unbox_usize(v_i_2606_);
lean_dec(v_i_2606_);
v_stop_boxed_2615_ = lean_unbox_usize(v_stop_2607_);
lean_dec(v_stop_2607_);
v_res_2616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2604_, v_as_2605_, v_i_boxed_2614_, v_stop_boxed_2615_, v_b_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v_as_2605_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2617_, lean_object* v_todo_2618_, lean_object* v_as_2619_, lean_object* v_i_2620_, lean_object* v_stop_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
size_t v_i_boxed_2628_; size_t v_stop_boxed_2629_; lean_object* v_res_2630_; 
v_i_boxed_2628_ = lean_unbox_usize(v_i_2620_);
lean_dec(v_i_2620_);
v_stop_boxed_2629_ = lean_unbox_usize(v_stop_2621_);
lean_dec(v_stop_2621_);
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2617_, v_todo_2618_, v_as_2619_, v_i_boxed_2628_, v_stop_boxed_2629_, v_b_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v_as_2619_);
lean_dec(v_n_2617_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2631_, lean_object* v_todo_2632_, lean_object* v_c_2633_, lean_object* v_result_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2631_, v_todo_2632_, v_c_2633_, v_result_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2641_, lean_object* v_skip_2642_, lean_object* v_todo_2643_, lean_object* v_c_2644_, lean_object* v_result_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2642_, v_todo_2643_, v_c_2644_, v_result_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2652_, lean_object* v_skip_2653_, lean_object* v_todo_2654_, lean_object* v_c_2655_, lean_object* v_result_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2652_, v_skip_2653_, v_todo_2654_, v_c_2655_, v_result_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2663_, lean_object* v_todo_2664_, lean_object* v_as_2665_, size_t v_i_2666_, size_t v_stop_2667_, lean_object* v_b_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2664_, v_as_2665_, v_i_2666_, v_stop_2667_, v_b_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2675_, lean_object* v_todo_2676_, lean_object* v_as_2677_, lean_object* v_i_2678_, lean_object* v_stop_2679_, lean_object* v_b_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
size_t v_i_boxed_2686_; size_t v_stop_boxed_2687_; lean_object* v_res_2688_; 
v_i_boxed_2686_ = lean_unbox_usize(v_i_2678_);
lean_dec(v_i_2678_);
v_stop_boxed_2687_ = lean_unbox_usize(v_stop_2679_);
lean_dec(v_stop_2679_);
v_res_2688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2675_, v_todo_2676_, v_as_2677_, v_i_boxed_2686_, v_stop_boxed_2687_, v_b_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec_ref(v_as_2677_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2689_, lean_object* v_n_2690_, lean_object* v_todo_2691_, lean_object* v_as_2692_, size_t v_i_2693_, size_t v_stop_2694_, lean_object* v_b_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2690_, v_todo_2691_, v_as_2692_, v_i_2693_, v_stop_2694_, v_b_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2702_, lean_object* v_n_2703_, lean_object* v_todo_2704_, lean_object* v_as_2705_, lean_object* v_i_2706_, lean_object* v_stop_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
size_t v_i_boxed_2714_; size_t v_stop_boxed_2715_; lean_object* v_res_2716_; 
v_i_boxed_2714_ = lean_unbox_usize(v_i_2706_);
lean_dec(v_i_2706_);
v_stop_boxed_2715_ = lean_unbox_usize(v_stop_2707_);
lean_dec(v_stop_2707_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2702_, v_n_2703_, v_todo_2704_, v_as_2705_, v_i_boxed_2714_, v_stop_boxed_2715_, v_b_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_as_2705_);
lean_dec(v_n_2703_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2717_, lean_object* v_k_2718_, lean_object* v_c_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2718_);
v___x_2726_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2727_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2725_, v___x_2726_, v_c_2719_, v_result_2717_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2728_, lean_object* v_k_2729_, lean_object* v_c_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2728_, v_k_2729_, v_c_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_k_2729_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2737_, lean_object* v_keys_2738_, lean_object* v_vals_2739_, lean_object* v_i_2740_, lean_object* v_acc_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = lean_array_get_size(v_keys_2738_);
v___x_2748_ = lean_nat_dec_lt(v_i_2740_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
lean_dec(v_i_2740_);
lean_dec_ref(v_f_2737_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_acc_2741_);
return v___x_2749_;
}
else
{
lean_object* v_k_2750_; lean_object* v_v_2751_; lean_object* v___x_2752_; 
v_k_2750_ = lean_array_fget_borrowed(v_keys_2738_, v_i_2740_);
v_v_2751_ = lean_array_fget_borrowed(v_vals_2739_, v_i_2740_);
lean_inc_ref(v_f_2737_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc_ref(v___y_2742_);
lean_inc(v_v_2751_);
lean_inc(v_k_2750_);
v___x_2752_ = lean_apply_8(v_f_2737_, v_acc_2741_, v_k_2750_, v_v_2751_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, lean_box(0));
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_nat_add(v_i_2740_, v___x_2754_);
lean_dec(v_i_2740_);
v_i_2740_ = v___x_2755_;
v_acc_2741_ = v_a_2753_;
goto _start;
}
else
{
lean_dec(v_i_2740_);
lean_dec_ref(v_f_2737_);
return v___x_2752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2757_, lean_object* v_keys_2758_, lean_object* v_vals_2759_, lean_object* v_i_2760_, lean_object* v_acc_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2757_, v_keys_2758_, v_vals_2759_, v_i_2760_, v_acc_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec_ref(v_vals_2759_);
lean_dec_ref(v_keys_2758_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2768_, lean_object* v_as_2769_, size_t v_i_2770_, size_t v_stop_2771_, lean_object* v_b_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_a_2779_; lean_object* v___y_2784_; uint8_t v___x_2786_; 
v___x_2786_ = lean_usize_dec_eq(v_i_2770_, v_stop_2771_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_array_uget_borrowed(v_as_2769_, v_i_2770_);
switch(lean_obj_tag(v___x_2787_))
{
case 0:
{
lean_object* v_key_2788_; lean_object* v_val_2789_; lean_object* v___x_2790_; 
v_key_2788_ = lean_ctor_get(v___x_2787_, 0);
v_val_2789_ = lean_ctor_get(v___x_2787_, 1);
lean_inc_ref(v_f_2768_);
lean_inc(v___y_2776_);
lean_inc_ref(v___y_2775_);
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
lean_inc(v_val_2789_);
lean_inc(v_key_2788_);
v___x_2790_ = lean_apply_8(v_f_2768_, v_b_2772_, v_key_2788_, v_val_2789_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, lean_box(0));
v___y_2784_ = v___x_2790_;
goto v___jp_2783_;
}
case 1:
{
lean_object* v_node_2791_; lean_object* v___x_2792_; 
v_node_2791_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_node_2791_);
lean_inc_ref(v_f_2768_);
v___x_2792_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2768_, v_node_2791_, v_b_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
v___y_2784_ = v___x_2792_;
goto v___jp_2783_;
}
default: 
{
v_a_2779_ = v_b_2772_;
goto v___jp_2778_;
}
}
}
else
{
lean_object* v___x_2793_; 
lean_dec_ref(v_f_2768_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_b_2772_);
return v___x_2793_;
}
v___jp_2778_:
{
size_t v___x_2780_; size_t v___x_2781_; 
v___x_2780_ = ((size_t)1ULL);
v___x_2781_ = lean_usize_add(v_i_2770_, v___x_2780_);
v_i_2770_ = v___x_2781_;
v_b_2772_ = v_a_2779_;
goto _start;
}
v___jp_2783_:
{
if (lean_obj_tag(v___y_2784_) == 0)
{
lean_object* v_a_2785_; 
v_a_2785_ = lean_ctor_get(v___y_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___y_2784_, 1);
v_a_2779_ = v_a_2785_;
goto v___jp_2778_;
}
else
{
lean_dec_ref(v_f_2768_);
return v___y_2784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2794_, lean_object* v_x_2795_, lean_object* v_x_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
if (lean_obj_tag(v_x_2795_) == 0)
{
lean_object* v_es_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2815_; 
v_es_2802_ = lean_ctor_get(v_x_2795_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_x_2795_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2804_ = v_x_2795_;
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_es_2802_);
lean_dec(v_x_2795_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2806_ = lean_unsigned_to_nat(0u);
v___x_2807_ = lean_array_get_size(v_es_2802_);
v___x_2808_ = lean_nat_dec_lt(v___x_2806_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref(v_es_2802_);
lean_dec_ref(v_f_2794_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v_x_2796_);
v___x_2810_ = v___x_2804_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_x_2796_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
else
{
size_t v___x_2812_; size_t v___x_2813_; lean_object* v___x_2814_; 
lean_del_object(v___x_2804_);
v___x_2812_ = ((size_t)0ULL);
v___x_2813_ = lean_usize_of_nat(v___x_2807_);
v___x_2814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2794_, v_es_2802_, v___x_2812_, v___x_2813_, v_x_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec_ref(v_es_2802_);
return v___x_2814_;
}
}
}
else
{
lean_object* v_ks_2816_; lean_object* v_vs_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_ks_2816_ = lean_ctor_get(v_x_2795_, 0);
lean_inc_ref(v_ks_2816_);
v_vs_2817_ = lean_ctor_get(v_x_2795_, 1);
lean_inc_ref(v_vs_2817_);
lean_dec_ref_known(v_x_2795_, 2);
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2794_, v_ks_2816_, v_vs_2817_, v___x_2818_, v_x_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec_ref(v_vs_2817_);
lean_dec_ref(v_ks_2816_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2820_, v_x_2821_, v_x_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2829_, lean_object* v_as_2830_, lean_object* v_i_2831_, lean_object* v_stop_2832_, lean_object* v_b_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
size_t v_i_boxed_2839_; size_t v_stop_boxed_2840_; lean_object* v_res_2841_; 
v_i_boxed_2839_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_stop_boxed_2840_ = lean_unbox_usize(v_stop_2832_);
lean_dec(v_stop_2832_);
v_res_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2829_, v_as_2830_, v_i_boxed_2839_, v_stop_boxed_2840_, v_b_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v_as_2830_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(lean_object* v_e_2842_, uint8_t v___x_2843_, lean_object* v___f_2844_, lean_object* v_d_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = 0;
v___x_2852_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2842_, v___x_2851_, v___x_2843_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2869_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_fst_2857_; 
v_fst_2857_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_fst_2857_);
if (lean_obj_tag(v_fst_2857_) == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_del_object(v___x_2855_);
lean_dec(v_a_2853_);
v___x_2858_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_2859_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2844_, v_d_2845_, v___x_2858_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2859_;
}
else
{
lean_object* v_snd_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec_ref(v___f_2844_);
v_snd_2860_ = lean_ctor_get(v_a_2853_, 1);
lean_inc(v_snd_2860_);
lean_dec(v_a_2853_);
v___x_2861_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2845_);
v___x_2862_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2845_, v_fst_2857_);
lean_dec(v_fst_2857_);
lean_dec_ref(v_d_2845_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v___x_2864_; 
lean_dec(v_snd_2860_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2861_);
v___x_2864_ = v___x_2855_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2861_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_del_object(v___x_2855_);
v_val_2866_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_val_2866_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2867_, v_snd_2860_, v_val_2866_, v___x_2861_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref(v_d_2845_);
lean_dec_ref(v___f_2844_);
v_a_2870_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2852_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2852_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1___boxed(lean_object* v_e_2878_, lean_object* v___x_2879_, lean_object* v___f_2880_, lean_object* v_d_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v___x_1524__boxed_2887_; lean_object* v_res_2888_; 
v___x_1524__boxed_2887_ = lean_unbox(v___x_2879_);
v_res_2888_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2878_, v___x_1524__boxed_2887_, v___f_2880_, v_d_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2890_, lean_object* v_e_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___y_2898_; lean_object* v___x_2915_; uint8_t v_transparency_2916_; lean_object* v___f_2917_; uint8_t v___x_2918_; uint8_t v___x_2919_; uint8_t v___x_2920_; 
v___x_2915_ = l_Lean_Meta_Context_config(v_a_2892_);
v_transparency_2916_ = lean_ctor_get_uint8(v___x_2915_, 9);
lean_dec_ref(v___x_2915_);
v___f_2917_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2918_ = 1;
v___x_2919_ = 2;
v___x_2920_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2916_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v_keyedConfig_2921_; uint8_t v_trackZetaDelta_2922_; lean_object* v_zetaDeltaSet_2923_; lean_object* v_lctx_2924_; lean_object* v_localInstances_2925_; lean_object* v_defEqCtx_x3f_2926_; lean_object* v_synthPendingDepth_2927_; lean_object* v_customCanUnfoldPredicate_x3f_2928_; uint8_t v_univApprox_2929_; uint8_t v_inTypeClassResolution_2930_; uint8_t v_cacheInferType_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_keyedConfig_2921_ = lean_ctor_get(v_a_2892_, 0);
v_trackZetaDelta_2922_ = lean_ctor_get_uint8(v_a_2892_, sizeof(void*)*7);
v_zetaDeltaSet_2923_ = lean_ctor_get(v_a_2892_, 1);
v_lctx_2924_ = lean_ctor_get(v_a_2892_, 2);
v_localInstances_2925_ = lean_ctor_get(v_a_2892_, 3);
v_defEqCtx_x3f_2926_ = lean_ctor_get(v_a_2892_, 4);
v_synthPendingDepth_2927_ = lean_ctor_get(v_a_2892_, 5);
v_customCanUnfoldPredicate_x3f_2928_ = lean_ctor_get(v_a_2892_, 6);
v_univApprox_2929_ = lean_ctor_get_uint8(v_a_2892_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2930_ = lean_ctor_get_uint8(v_a_2892_, sizeof(void*)*7 + 2);
v_cacheInferType_2931_ = lean_ctor_get_uint8(v_a_2892_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2921_);
v___x_2932_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2919_, v_keyedConfig_2921_);
lean_inc(v_customCanUnfoldPredicate_x3f_2928_);
lean_inc(v_synthPendingDepth_2927_);
lean_inc(v_defEqCtx_x3f_2926_);
lean_inc_ref(v_localInstances_2925_);
lean_inc_ref(v_lctx_2924_);
lean_inc(v_zetaDeltaSet_2923_);
v___x_2933_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v_zetaDeltaSet_2923_);
lean_ctor_set(v___x_2933_, 2, v_lctx_2924_);
lean_ctor_set(v___x_2933_, 3, v_localInstances_2925_);
lean_ctor_set(v___x_2933_, 4, v_defEqCtx_x3f_2926_);
lean_ctor_set(v___x_2933_, 5, v_synthPendingDepth_2927_);
lean_ctor_set(v___x_2933_, 6, v_customCanUnfoldPredicate_x3f_2928_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7, v_trackZetaDelta_2922_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 1, v_univApprox_2929_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*7 + 3, v_cacheInferType_2931_);
v___x_2934_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2891_, v___x_2918_, v___f_2917_, v_d_2890_, v___x_2933_, v_a_2893_, v_a_2894_, v_a_2895_);
lean_dec_ref_known(v___x_2933_, 7);
v___y_2898_ = v___x_2934_;
goto v___jp_2897_;
}
else
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2891_, v___x_2918_, v___f_2917_, v_d_2890_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
v___y_2898_ = v___x_2935_;
goto v___jp_2897_;
}
v___jp_2897_:
{
if (lean_obj_tag(v___y_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_a_2899_ = lean_ctor_get(v___y_2898_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___y_2898_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___y_2898_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___y_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_a_2907_ = lean_ctor_get(v___y_2898_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___y_2898_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___y_2898_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___y_2898_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_2936_, lean_object* v_e_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2936_, v_e_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_2944_, lean_object* v_d_2945_, lean_object* v_e_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2945_, v_e_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_2953_, lean_object* v_d_2954_, lean_object* v_e_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_2953_, v_d_2954_, v_e_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_2962_, lean_object* v_f_2963_, lean_object* v_init_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2963_, v_map_2962_, v_init_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_2971_, lean_object* v_f_2972_, lean_object* v_init_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_2971_, v_f_2972_, v_init_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_2980_, lean_object* v_00_u03b2_2981_, lean_object* v_map_2982_, lean_object* v_f_2983_, lean_object* v_init_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2983_, v_map_2982_, v_init_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_2991_, lean_object* v_00_u03b2_2992_, lean_object* v_map_2993_, lean_object* v_f_2994_, lean_object* v_init_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_2991_, v_00_u03b2_2992_, v_map_2993_, v_f_2994_, v_init_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_3002_, lean_object* v_00_u03b1_3003_, lean_object* v_00_u03b2_3004_, lean_object* v_f_3005_, lean_object* v_x_3006_, lean_object* v_x_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3005_, v_x_3006_, v_x_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3014_, lean_object* v_00_u03b1_3015_, lean_object* v_00_u03b2_3016_, lean_object* v_f_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_3014_, v_00_u03b1_3015_, v_00_u03b2_3016_, v_f_3017_, v_x_3018_, v_x_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3026_, lean_object* v_00_u03b2_3027_, lean_object* v_00_u03c3_3028_, lean_object* v_f_3029_, lean_object* v_as_3030_, size_t v_i_3031_, size_t v_stop_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3029_, v_as_3030_, v_i_3031_, v_stop_3032_, v_b_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_00_u03b2_3041_, lean_object* v_00_u03c3_3042_, lean_object* v_f_3043_, lean_object* v_as_3044_, lean_object* v_i_3045_, lean_object* v_stop_3046_, lean_object* v_b_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
size_t v_i_boxed_3053_; size_t v_stop_boxed_3054_; lean_object* v_res_3055_; 
v_i_boxed_3053_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_stop_boxed_3054_ = lean_unbox_usize(v_stop_3046_);
lean_dec(v_stop_3046_);
v_res_3055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_3040_, v_00_u03b2_3041_, v_00_u03c3_3042_, v_f_3043_, v_as_3044_, v_i_boxed_3053_, v_stop_boxed_3054_, v_b_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v_as_3044_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_3056_, lean_object* v_00_u03b1_3057_, lean_object* v_00_u03b2_3058_, lean_object* v_f_3059_, lean_object* v_keys_3060_, lean_object* v_vals_3061_, lean_object* v_heq_3062_, lean_object* v_i_3063_, lean_object* v_acc_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3059_, v_keys_3060_, v_vals_3061_, v_i_3063_, v_acc_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_3071_, lean_object* v_00_u03b1_3072_, lean_object* v_00_u03b2_3073_, lean_object* v_f_3074_, lean_object* v_keys_3075_, lean_object* v_vals_3076_, lean_object* v_heq_3077_, lean_object* v_i_3078_, lean_object* v_acc_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_3071_, v_00_u03b1_3072_, v_00_u03b2_3073_, v_f_3074_, v_keys_3075_, v_vals_3076_, v_heq_3077_, v_i_3078_, v_acc_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_vals_3076_);
lean_dec_ref(v_keys_3075_);
return v_res_3085_;
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
