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
lean_object* v_f_154_; 
v_f_154_ = l_Lean_Expr_getAppFn(v_e_153_);
switch(lean_obj_tag(v_f_154_))
{
case 9:
{
lean_object* v_a_155_; 
lean_dec_ref(v_e_153_);
v_a_155_ = lean_ctor_get(v_f_154_, 0);
lean_inc_ref(v_a_155_);
lean_dec_ref_known(v_f_154_, 1);
if (lean_obj_tag(v_a_155_) == 0)
{
lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_val_156_ = lean_ctor_get(v_a_155_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_155_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v_a_155_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_dec(v_a_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 1);
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_val_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
else
{
lean_object* v___x_164_; 
lean_dec_ref(v_a_155_);
v___x_164_ = lean_box(0);
return v___x_164_;
}
}
case 4:
{
lean_object* v_declName_165_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_declName_165_ = lean_ctor_get(v_f_154_, 0);
lean_inc(v_declName_165_);
lean_dec_ref_known(v_f_154_, 2);
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_187_ = lean_name_eq(v_declName_165_, v___x_186_);
if (v___x_187_ == 0)
{
goto v___jp_175_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_188_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_nat_dec_eq(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
if (v___x_190_ == 0)
{
goto v___jp_175_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_declName_165_);
v___x_191_ = l_Lean_Expr_appArg_x21(v_e_153_);
lean_dec_ref(v_e_153_);
v___x_192_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v___x_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_201_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_val_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_nat_add(v_val_193_, v___x_189_);
lean_dec(v_val_193_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
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
v___jp_166_:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2));
v___x_168_ = lean_name_eq(v_declName_165_, v___x_167_);
lean_dec(v_declName_165_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec_ref(v_e_153_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
lean_dec_ref(v_e_153_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_nat_dec_eq(v___x_170_, v___x_171_);
lean_dec(v___x_170_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_box(0);
return v___x_173_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0));
return v___x_174_;
}
}
}
v___jp_175_:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5));
v___x_177_ = lean_name_eq(v_declName_165_, v___x_176_);
if (v___x_177_ == 0)
{
goto v___jp_166_;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
v___x_179_ = lean_unsigned_to_nat(3u);
v___x_180_ = lean_nat_dec_eq(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v___x_178_);
goto v___jp_166_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_declName_165_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_sub(v___x_178_, v___x_181_);
lean_dec(v___x_178_);
v___x_183_ = lean_nat_sub(v___x_182_, v___x_181_);
lean_dec(v___x_182_);
v___x_184_ = l_Lean_Expr_getRevArg_x21(v_e_153_, v___x_183_);
lean_dec_ref(v_e_153_);
v_e_153_ = v___x_184_;
goto _start;
}
}
}
}
default: 
{
lean_object* v___x_202_; 
lean_dec_ref(v_f_154_);
lean_dec_ref(v_e_153_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(lean_object* v_e_203_){
_start:
{
uint8_t v___x_204_; 
lean_inc_ref(v_e_203_);
v___x_204_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v_e_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec_ref(v_e_203_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v_e_203_);
if (lean_obj_tag(v___x_206_) == 1)
{
lean_object* v_val_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_val_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_val_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v_val_207_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v___x_206_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
lean_inc(v_a_223_);
lean_inc_ref(v_a_222_);
lean_inc(v_a_221_);
lean_inc_ref(v_a_220_);
v___x_225_ = lean_whnf(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_236_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_236_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_236_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_236_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0));
v___x_231_ = l_Lean_Expr_isConstOf(v_a_226_, v___x_230_);
lean_dec(v_a_226_);
v___x_232_ = lean_box(v___x_231_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_232_);
v___x_234_ = v___x_228_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_a_237_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_225_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_225_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___boxed(lean_object* v_e_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v_e_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(lean_object* v_fName_265_, lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6));
v___x_330_ = lean_name_eq(v_fName_265_, v___x_329_);
if (v___x_330_ == 0)
{
goto v___jp_306_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_331_ = l_Lean_Expr_getAppNumArgs(v_e_266_);
v___x_332_ = lean_unsigned_to_nat(2u);
v___x_333_ = lean_nat_dec_eq(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
if (v___x_333_ == 0)
{
goto v___jp_306_;
}
else
{
lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = l_Lean_Expr_appArg_x21(v_e_266_);
v___x_335_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_334_);
v___x_336_ = lean_box(v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
v___jp_272_:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_274_ = lean_name_eq(v_fName_265_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_277_ = l_Lean_Expr_getAppNumArgs(v_e_266_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_dec_eq(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
v___jp_282_:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2));
v___x_284_ = lean_name_eq(v_fName_265_, v___x_283_);
if (v___x_284_ == 0)
{
goto v___jp_272_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = l_Lean_Expr_getAppNumArgs(v_e_266_);
v___x_286_ = lean_unsigned_to_nat(6u);
v___x_287_ = lean_nat_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_dec(v___x_285_);
goto v___jp_272_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_sub(v___x_285_, v___x_288_);
lean_dec(v___x_285_);
v___x_290_ = lean_nat_sub(v___x_289_, v___x_288_);
lean_dec(v___x_289_);
v___x_291_ = l_Lean_Expr_getRevArg_x21(v_e_266_, v___x_290_);
v___x_292_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_291_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; uint8_t v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v___x_294_ = lean_unbox(v_a_293_);
if (v___x_294_ == 0)
{
return v___x_292_;
}
else
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v___x_292_, 0);
lean_dec(v_unused_305_);
v___x_296_ = v___x_292_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_dec(v___x_292_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_298_ = l_Lean_Expr_appArg_x21(v_e_266_);
v___x_299_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_298_);
v___x_300_ = lean_box(v___x_299_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_300_);
v___x_302_ = v___x_296_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
return v___x_292_;
}
}
}
}
v___jp_306_:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5));
v___x_308_ = lean_name_eq(v_fName_265_, v___x_307_);
if (v___x_308_ == 0)
{
goto v___jp_282_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = l_Lean_Expr_getAppNumArgs(v_e_266_);
v___x_310_ = lean_unsigned_to_nat(4u);
v___x_311_ = lean_nat_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_dec(v___x_309_);
goto v___jp_282_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_sub(v___x_309_, v___x_312_);
lean_dec(v___x_309_);
v___x_314_ = l_Lean_Expr_getRevArg_x21(v_e_266_, v___x_313_);
v___x_315_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_314_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; uint8_t v___x_317_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v___x_317_ = lean_unbox(v_a_316_);
if (v___x_317_ == 0)
{
return v___x_315_;
}
else
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_327_; 
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_315_, 0);
lean_dec(v_unused_328_);
v___x_319_ = v___x_315_;
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
else
{
lean_dec(v___x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_321_ = l_Lean_Expr_appArg_x21(v_e_266_);
v___x_322_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_321_);
v___x_323_ = lean_box(v___x_322_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_323_);
v___x_325_ = v___x_319_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object* v_fName_338_, lean_object* v_e_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_338_, v_e_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_e_339_);
lean_dec(v_fName_338_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object* v_fName_346_, lean_object* v_e_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_346_, v_e_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object* v_fName_354_, lean_object* v_e_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(v_fName_354_, v_e_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec_ref(v_e_355_);
lean_dec(v_fName_354_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object* v_e_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_whnfCore(v_e_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; uint8_t v___x_370_; lean_object* v___x_371_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc_n(v_a_369_, 2);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = 0;
v___x_371_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_369_, v___x_370_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_384_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_384_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
if (lean_obj_tag(v_a_372_) == 0)
{
lean_object* v___x_376_; 
lean_inc(v_a_369_);
v___x_376_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_369_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v___x_378_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v_a_369_);
v___x_378_ = v___x_374_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_369_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
lean_object* v_val_380_; 
lean_del_object(v___x_374_);
lean_dec(v_a_369_);
v_val_380_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v___x_376_, 1);
v_e_362_ = v_val_380_;
goto _start;
}
}
else
{
lean_object* v_val_382_; 
lean_del_object(v___x_374_);
lean_dec(v_a_369_);
v_val_382_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v_a_372_, 1);
v_e_362_ = v_val_382_;
goto _start;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_369_);
v_a_385_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_371_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_371_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Meta_DiscrTree_reduce(v_e_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_399_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(lean_object* v_fn_400_){
_start:
{
switch(lean_obj_tag(v_fn_400_))
{
case 9:
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
case 4:
{
uint8_t v___x_402_; 
v___x_402_ = 0;
return v___x_402_;
}
case 1:
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
case 11:
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
case 7:
{
uint8_t v___x_405_; 
v___x_405_ = 0;
return v___x_405_;
}
default: 
{
uint8_t v___x_406_; 
v___x_406_ = 1;
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object* v_fn_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v_fn_407_);
lean_dec_ref(v_fn_407_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_whnfCore(v_e_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc_n(v_a_417_, 2);
lean_dec_ref_known(v___x_416_, 1);
v___x_418_ = 0;
v___x_419_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_417_, v___x_418_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_434_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_434_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
if (lean_obj_tag(v_a_420_) == 0)
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_a_417_);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_417_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
else
{
lean_object* v_val_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_val_427_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v_a_420_, 1);
v___x_428_ = l_Lean_Expr_getAppFn(v_val_427_);
v___x_429_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v___x_428_);
lean_dec_ref(v___x_428_);
if (v___x_429_ == 0)
{
lean_del_object(v___x_422_);
lean_dec(v_a_417_);
v_e_410_ = v_val_427_;
goto _start;
}
else
{
lean_object* v___x_432_; 
lean_dec(v_val_427_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_a_417_);
v___x_432_ = v___x_422_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_417_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_a_417_);
v_a_435_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_419_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_419_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
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
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object* v_e_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object* v_e_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
v___x_458_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
return v___x_456_;
}
else
{
lean_object* v_val_459_; 
lean_dec_ref_known(v___x_456_, 1);
v_val_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v___x_458_, 1);
v_e_450_ = v_val_459_;
goto _start;
}
}
else
{
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object* v_e_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object* v_e_468_, uint8_t v_root_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
if (v_root_469_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Meta_DiscrTree_reduce(v_e_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_468_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT___boxed(lean_object* v_e_477_, lean_object* v_root_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
uint8_t v_root_boxed_484_; lean_object* v_res_485_; 
v_root_boxed_484_ = lean_unbox(v_root_478_);
v_res_485_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_477_, v_root_boxed_484_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(lean_object* v_n_486_, lean_object* v_todo_487_){
_start:
{
lean_object* v_zero_488_; uint8_t v_isZero_489_; 
v_zero_488_ = lean_unsigned_to_nat(0u);
v_isZero_489_ = lean_nat_dec_eq(v_n_486_, v_zero_488_);
if (v_isZero_489_ == 1)
{
lean_dec(v_n_486_);
return v_todo_487_;
}
else
{
lean_object* v_one_490_; lean_object* v_n_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_one_490_ = lean_unsigned_to_nat(1u);
v_n_491_ = lean_nat_sub(v_n_486_, v_one_490_);
lean_dec(v_n_486_);
v___x_492_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
v___x_493_ = lean_array_push(v_todo_487_, v___x_492_);
v_n_486_ = v_n_491_;
v_todo_487_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(uint8_t v_root_495_, lean_object* v_todo_496_, lean_object* v_e_497_, uint8_t v_noIndexAtArgs_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_v_505_; lean_object* v___y_510_; lean_object* v_todo_511_; uint8_t v___x_514_; 
v___x_514_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_497_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_497_, v_root_495_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_644_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_644_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_644_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_644_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v_k_522_; lean_object* v_nargs_523_; lean_object* v_todo_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; 
v___x_520_ = l_Lean_Expr_getAppFn(v_a_516_);
switch(lean_obj_tag(v___x_520_))
{
case 9:
{
lean_object* v_a_553_; 
lean_del_object(v___x_518_);
lean_dec(v_a_516_);
v_a_553_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_a_553_);
lean_dec_ref_known(v___x_520_, 1);
v_v_505_ = v_a_553_;
goto v___jp_504_;
}
case 4:
{
lean_object* v_declName_554_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; 
lean_del_object(v___x_518_);
v_declName_554_ = lean_ctor_get(v___x_520_, 0);
if (v_root_495_ == 0)
{
lean_object* v___x_562_; 
lean_inc(v_a_516_);
v___x_562_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_516_);
if (lean_obj_tag(v___x_562_) == 1)
{
lean_object* v_val_563_; 
lean_dec_ref_known(v___x_520_, 2);
lean_dec(v_a_516_);
v_val_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v___x_562_, 1);
v_v_505_ = v_val_563_;
goto v___jp_504_;
}
else
{
lean_object* v___x_564_; 
lean_dec(v___x_562_);
v___x_564_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_declName_554_, v_a_516_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_575_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_575_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_575_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
uint8_t v___x_569_; 
v___x_569_ = lean_unbox(v_a_565_);
lean_dec(v_a_565_);
if (v___x_569_ == 0)
{
lean_del_object(v___x_567_);
v___y_556_ = v_a_499_;
v___y_557_ = v_a_500_;
v___y_558_ = v_a_501_;
v___y_559_ = v_a_502_;
goto v___jp_555_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec_ref_known(v___x_520_, 2);
lean_dec(v_a_516_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_todo_496_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref_known(v___x_520_, 2);
lean_dec(v_a_516_);
lean_dec_ref(v_todo_496_);
v_a_576_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_564_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_564_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
else
{
v___y_556_ = v_a_499_;
v___y_557_ = v_a_500_;
v___y_558_ = v_a_501_;
v___y_559_ = v_a_502_;
goto v___jp_555_;
}
v___jp_555_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l_Lean_Expr_getAppNumArgs(v_a_516_);
lean_inc(v___x_560_);
lean_inc(v_declName_554_);
v___x_561_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_561_, 0, v_declName_554_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v_k_522_ = v___x_561_;
v_nargs_523_ = v___x_560_;
v_todo_524_ = v_todo_496_;
v___y_525_ = v___y_556_;
v___y_526_ = v___y_557_;
v___y_527_ = v___y_558_;
v___y_528_ = v___y_559_;
goto v___jp_521_;
}
}
case 11:
{
lean_object* v_typeName_584_; lean_object* v_idx_585_; lean_object* v_struct_586_; lean_object* v___x_587_; lean_object* v___y_589_; lean_object* v_env_593_; uint8_t v___x_594_; 
lean_del_object(v___x_518_);
v_typeName_584_ = lean_ctor_get(v___x_520_, 0);
v_idx_585_ = lean_ctor_get(v___x_520_, 1);
v_struct_586_ = lean_ctor_get(v___x_520_, 2);
v___x_587_ = lean_st_ref_get(v_a_502_);
v_env_593_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_env_593_);
lean_dec(v___x_587_);
v___x_594_ = l_Lean_isClass(v_env_593_, v_typeName_584_);
if (v___x_594_ == 0)
{
lean_inc_ref(v_struct_586_);
v___y_589_ = v_struct_586_;
goto v___jp_588_;
}
else
{
lean_object* v___x_595_; 
lean_inc_ref(v_struct_586_);
v___x_595_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_586_);
v___y_589_ = v___x_595_;
goto v___jp_588_;
}
v___jp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = l_Lean_Expr_getAppNumArgs(v_a_516_);
lean_inc(v___x_590_);
lean_inc(v_idx_585_);
lean_inc(v_typeName_584_);
v___x_591_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_591_, 0, v_typeName_584_);
lean_ctor_set(v___x_591_, 1, v_idx_585_);
lean_ctor_set(v___x_591_, 2, v___x_590_);
v___x_592_ = lean_array_push(v_todo_496_, v___y_589_);
v_k_522_ = v___x_591_;
v_nargs_523_ = v___x_590_;
v_todo_524_ = v___x_592_;
v___y_525_ = v_a_499_;
v___y_526_ = v_a_500_;
v___y_527_ = v_a_501_;
v___y_528_ = v_a_502_;
goto v___jp_521_;
}
}
case 1:
{
lean_object* v_fvarId_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_del_object(v___x_518_);
v_fvarId_596_ = lean_ctor_get(v___x_520_, 0);
v___x_597_ = l_Lean_Expr_getAppNumArgs(v_a_516_);
lean_inc(v___x_597_);
lean_inc(v_fvarId_596_);
v___x_598_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_598_, 0, v_fvarId_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v_k_522_ = v___x_598_;
v_nargs_523_ = v___x_597_;
v_todo_524_ = v_todo_496_;
v___y_525_ = v_a_499_;
v___y_526_ = v_a_500_;
v___y_527_ = v_a_501_;
v___y_528_ = v_a_502_;
goto v___jp_521_;
}
case 2:
{
lean_object* v_mvarId_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
lean_dec(v_a_516_);
v_mvarId_599_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_mvarId_599_);
lean_dec_ref_known(v___x_520_, 1);
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId));
v___x_601_ = l_Lean_instBEqMVarId_beq(v_mvarId_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_del_object(v___x_518_);
v___x_602_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_599_, v_a_499_, v_a_500_, v_a_501_, v_a_502_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_618_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_618_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
uint8_t v___x_607_; 
v___x_607_ = lean_unbox(v_a_603_);
lean_dec(v_a_603_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_box(0);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v_todo_496_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_613_ = lean_box(1);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_todo_496_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_614_);
v___x_616_ = v___x_605_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v_todo_496_);
v_a_619_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_602_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_602_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
lean_dec(v_mvarId_599_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_todo_496_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_628_);
v___x_630_ = v___x_518_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
case 7:
{
lean_object* v_binderType_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_dec(v_a_516_);
v_binderType_632_ = lean_ctor_get(v___x_520_, 1);
lean_inc_ref(v_binderType_632_);
lean_dec_ref_known(v___x_520_, 3);
v___x_633_ = lean_box(5);
v___x_634_ = lean_array_push(v_todo_496_, v_binderType_632_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_635_);
v___x_637_ = v___x_518_;
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
default: 
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
lean_dec_ref(v___x_520_);
lean_dec(v_a_516_);
v___x_639_ = lean_box(1);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_todo_496_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_640_);
v___x_642_ = v___x_518_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
v___jp_521_:
{
lean_object* v___x_529_; 
lean_inc(v_nargs_523_);
v___x_529_ = l_Lean_Meta_getFunInfoNArgs(v___x_520_, v_nargs_523_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
if (v_noIndexAtArgs_498_ == 0)
{
lean_object* v_a_530_; lean_object* v_paramInfo_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v_paramInfo_531_ = lean_ctor_get(v_a_530_, 0);
lean_inc_ref(v_paramInfo_531_);
lean_dec(v_a_530_);
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_sub(v_nargs_523_, v___x_532_);
lean_dec(v_nargs_523_);
v___x_534_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_paramInfo_531_, v___x_533_, v_a_516_, v_todo_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec_ref(v_paramInfo_531_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___y_510_ = v_k_522_;
v_todo_511_ = v_a_535_;
goto v___jp_509_;
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_k_522_);
v_a_536_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_534_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v___x_544_; 
lean_dec_ref_known(v___x_529_, 1);
lean_dec(v_a_516_);
v___x_544_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(v_nargs_523_, v_todo_524_);
v___y_510_ = v_k_522_;
v_todo_511_ = v___x_544_;
goto v___jp_509_;
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_todo_524_);
lean_dec(v_nargs_523_);
lean_dec(v_k_522_);
lean_dec(v_a_516_);
v_a_545_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_529_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_529_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_todo_496_);
v_a_645_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_515_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_515_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref(v_e_497_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_todo_496_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_506_, 0, v_v_505_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_todo_496_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
v___jp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___y_510_);
lean_ctor_set(v___x_512_, 1, v_todo_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* v_root_656_, lean_object* v_todo_657_, lean_object* v_e_658_, lean_object* v_noIndexAtArgs_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
uint8_t v_root_boxed_665_; uint8_t v_noIndexAtArgs_boxed_666_; lean_object* v_res_667_; 
v_root_boxed_665_ = lean_unbox(v_root_656_);
v_noIndexAtArgs_boxed_666_ = lean_unbox(v_noIndexAtArgs_659_);
v_res_667_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_boxed_665_, v_todo_657_, v_e_658_, v_noIndexAtArgs_boxed_666_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t v_root_668_, lean_object* v_todo_669_, lean_object* v_keys_670_, uint8_t v_noIndexAtArgs_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_677_ = lean_array_get_size(v_todo_669_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_nat_dec_eq(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_e_683_; lean_object* v_todo_684_; lean_object* v___x_685_; 
v___x_680_ = l_Lean_instInhabitedExpr;
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_sub(v___x_677_, v___x_681_);
v_e_683_ = lean_array_get(v___x_680_, v_todo_669_, v___x_682_);
lean_dec(v___x_682_);
v_todo_684_ = lean_array_pop(v_todo_669_);
v___x_685_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_668_, v_todo_684_, v_e_683_, v_noIndexAtArgs_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_689_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v_fst_687_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_fst_687_);
v_snd_688_ = lean_ctor_get(v_a_686_, 1);
lean_inc(v_snd_688_);
lean_dec(v_a_686_);
v___x_689_ = lean_array_push(v_keys_670_, v_fst_687_);
v_root_668_ = v___x_679_;
v_todo_669_ = v_snd_688_;
v_keys_670_ = v___x_689_;
goto _start;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_keys_670_);
v_a_691_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_685_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_685_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v___x_699_; 
lean_dec_ref(v_todo_669_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v_keys_670_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* v_root_700_, lean_object* v_todo_701_, lean_object* v_keys_702_, lean_object* v_noIndexAtArgs_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
uint8_t v_root_boxed_709_; uint8_t v_noIndexAtArgs_boxed_710_; lean_object* v_res_711_; 
v_root_boxed_709_ = lean_unbox(v_root_700_);
v_noIndexAtArgs_boxed_710_ = lean_unbox(v_noIndexAtArgs_703_);
v_res_711_ = l_Lean_Meta_DiscrTree_mkPathAux(v_root_boxed_709_, v_todo_701_, v_keys_702_, v_noIndexAtArgs_boxed_710_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
return v_res_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_unsigned_to_nat(8u);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* v_e_713_, uint8_t v_noIndexAtArgs_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___y_721_; lean_object* v___x_738_; uint8_t v_transparency_739_; lean_object* v___x_740_; lean_object* v_todo_741_; uint8_t v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; 
v___x_738_ = l_Lean_Meta_Context_config(v_a_715_);
v_transparency_739_ = lean_ctor_get_uint8(v___x_738_, 9);
lean_dec_ref(v___x_738_);
v___x_740_ = lean_unsigned_to_nat(8u);
v_todo_741_ = lean_mk_empty_array_with_capacity(v___x_740_);
v___x_742_ = 1;
lean_inc_ref(v_todo_741_);
v___x_743_ = lean_array_push(v_todo_741_, v_e_713_);
v___x_744_ = 2;
v___x_745_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_739_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v_keyedConfig_746_; uint8_t v_trackZetaDelta_747_; lean_object* v_zetaDeltaSet_748_; lean_object* v_lctx_749_; lean_object* v_localInstances_750_; lean_object* v_defEqCtx_x3f_751_; lean_object* v_synthPendingDepth_752_; lean_object* v_customCanUnfoldPredicate_x3f_753_; uint8_t v_univApprox_754_; uint8_t v_inTypeClassResolution_755_; uint8_t v_cacheInferType_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_keyedConfig_746_ = lean_ctor_get(v_a_715_, 0);
v_trackZetaDelta_747_ = lean_ctor_get_uint8(v_a_715_, sizeof(void*)*7);
v_zetaDeltaSet_748_ = lean_ctor_get(v_a_715_, 1);
v_lctx_749_ = lean_ctor_get(v_a_715_, 2);
v_localInstances_750_ = lean_ctor_get(v_a_715_, 3);
v_defEqCtx_x3f_751_ = lean_ctor_get(v_a_715_, 4);
v_synthPendingDepth_752_ = lean_ctor_get(v_a_715_, 5);
v_customCanUnfoldPredicate_x3f_753_ = lean_ctor_get(v_a_715_, 6);
v_univApprox_754_ = lean_ctor_get_uint8(v_a_715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_755_ = lean_ctor_get_uint8(v_a_715_, sizeof(void*)*7 + 2);
v_cacheInferType_756_ = lean_ctor_get_uint8(v_a_715_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_746_);
v___x_757_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_744_, v_keyedConfig_746_);
lean_inc(v_customCanUnfoldPredicate_x3f_753_);
lean_inc(v_synthPendingDepth_752_);
lean_inc(v_defEqCtx_x3f_751_);
lean_inc_ref(v_localInstances_750_);
lean_inc_ref(v_lctx_749_);
lean_inc(v_zetaDeltaSet_748_);
v___x_758_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_zetaDeltaSet_748_);
lean_ctor_set(v___x_758_, 2, v_lctx_749_);
lean_ctor_set(v___x_758_, 3, v_localInstances_750_);
lean_ctor_set(v___x_758_, 4, v_defEqCtx_x3f_751_);
lean_ctor_set(v___x_758_, 5, v_synthPendingDepth_752_);
lean_ctor_set(v___x_758_, 6, v_customCanUnfoldPredicate_x3f_753_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*7, v_trackZetaDelta_747_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*7 + 1, v_univApprox_754_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*7 + 2, v_inTypeClassResolution_755_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*7 + 3, v_cacheInferType_756_);
v___x_759_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_742_, v___x_743_, v_todo_741_, v_noIndexAtArgs_714_, v___x_758_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref_known(v___x_758_, 7);
v___y_721_ = v___x_759_;
goto v___jp_720_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_742_, v___x_743_, v_todo_741_, v_noIndexAtArgs_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
v___y_721_ = v___x_760_;
goto v___jp_720_;
}
v___jp_720_:
{
if (lean_obj_tag(v___y_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___y_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___y_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___y_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___y_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___y_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___y_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___y_721_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___y_721_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object* v_e_761_, lean_object* v_noIndexAtArgs_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_768_; lean_object* v_res_769_; 
v_noIndexAtArgs_boxed_768_ = lean_unbox(v_noIndexAtArgs_762_);
v_res_769_ = l_Lean_Meta_DiscrTree_mkPath(v_e_761_, v_noIndexAtArgs_boxed_768_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg(lean_object* v_inst_770_, lean_object* v_d_771_, lean_object* v_e_772_, lean_object* v_v_773_, uint8_t v_noIndexAtArgs_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_DiscrTree_mkPath(v_e_772_, v_noIndexAtArgs_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_789_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_770_, v_d_771_, v_a_781_, v_v_773_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_785_);
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_v_773_);
lean_dec_ref(v_d_771_);
lean_dec_ref(v_inst_770_);
v_a_790_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_780_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg___boxed(lean_object* v_inst_798_, lean_object* v_d_799_, lean_object* v_e_800_, lean_object* v_v_801_, lean_object* v_noIndexAtArgs_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_808_; lean_object* v_res_809_; 
v_noIndexAtArgs_boxed_808_ = lean_unbox(v_noIndexAtArgs_802_);
v_res_809_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_798_, v_d_799_, v_e_800_, v_v_801_, v_noIndexAtArgs_boxed_808_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* v_00_u03b1_810_, lean_object* v_inst_811_, lean_object* v_d_812_, lean_object* v_e_813_, lean_object* v_v_814_, uint8_t v_noIndexAtArgs_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_811_, v_d_812_, v_e_813_, v_v_814_, v_noIndexAtArgs_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___boxed(lean_object* v_00_u03b1_822_, lean_object* v_inst_823_, lean_object* v_d_824_, lean_object* v_e_825_, lean_object* v_v_826_, lean_object* v_noIndexAtArgs_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_833_; lean_object* v_res_834_; 
v_noIndexAtArgs_boxed_833_ = lean_unbox(v_noIndexAtArgs_827_);
v_res_834_ = l_Lean_Meta_DiscrTree_insert(v_00_u03b1_822_, v_inst_823_, v_d_824_, v_e_825_, v_v_826_, v_noIndexAtArgs_boxed_833_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_834_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_850_ = lean_array_get_size(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_857_ = lean_array_get_size(v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(lean_object* v_inst_858_, lean_object* v_d_859_, lean_object* v_e_860_, lean_object* v_v_861_, uint8_t v_noIndexAtArgs_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Meta_DiscrTree_mkPath(v_e_860_, v_noIndexAtArgs_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_893_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_893_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_893_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_893_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_886_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_887_ = lean_array_get_size(v_a_869_);
v___x_888_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7);
v___x_889_ = lean_nat_dec_eq(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
goto v___jp_878_;
}
else
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_891_ = l_Array_isEqvAux___redArg(v_a_869_, v___x_886_, v___x_890_, v___x_887_);
if (v___x_891_ == 0)
{
goto v___jp_878_;
}
else
{
lean_object* v___x_892_; 
lean_del_object(v___x_871_);
lean_dec(v_a_869_);
lean_dec(v_v_861_);
lean_dec_ref(v_inst_858_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_d_859_);
return v___x_892_;
}
}
v___jp_873_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_858_, v_d_859_, v_a_869_, v_v_861_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
v___jp_878_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_879_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_880_ = lean_array_get_size(v_a_869_);
v___x_881_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4);
v___x_882_ = lean_nat_dec_eq(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
goto v___jp_873_;
}
else
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_884_ = l_Array_isEqvAux___redArg(v_a_869_, v___x_879_, v___x_883_, v___x_880_);
if (v___x_884_ == 0)
{
goto v___jp_873_;
}
else
{
lean_object* v___x_885_; 
lean_del_object(v___x_871_);
lean_dec(v_a_869_);
lean_dec(v_v_861_);
lean_dec_ref(v_inst_858_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_d_859_);
return v___x_885_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_v_861_);
lean_dec_ref(v_d_859_);
lean_dec_ref(v_inst_858_);
v_a_894_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_868_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_868_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(lean_object* v_inst_902_, lean_object* v_d_903_, lean_object* v_e_904_, lean_object* v_v_905_, lean_object* v_noIndexAtArgs_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_912_; lean_object* v_res_913_; 
v_noIndexAtArgs_boxed_912_ = lean_unbox(v_noIndexAtArgs_906_);
v_res_913_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_902_, v_d_903_, v_e_904_, v_v_905_, v_noIndexAtArgs_boxed_912_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific(lean_object* v_00_u03b1_914_, lean_object* v_inst_915_, lean_object* v_d_916_, lean_object* v_e_917_, lean_object* v_v_918_, uint8_t v_noIndexAtArgs_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_915_, v_d_916_, v_e_917_, v_v_918_, v_noIndexAtArgs_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(lean_object* v_00_u03b1_926_, lean_object* v_inst_927_, lean_object* v_d_928_, lean_object* v_e_929_, lean_object* v_v_930_, lean_object* v_noIndexAtArgs_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_937_; lean_object* v_res_938_; 
v_noIndexAtArgs_boxed_937_ = lean_unbox(v_noIndexAtArgs_931_);
v_res_938_ = l_Lean_Meta_DiscrTree_insertIfSpecific(v_00_u03b1_926_, v_inst_927_, v_d_928_, v_e_929_, v_v_930_, v_noIndexAtArgs_boxed_937_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(lean_object* v_declName_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v_env_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_942_ = lean_st_ref_get(v___y_940_);
v_env_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc_ref(v_env_943_);
lean_dec(v___x_942_);
v___x_944_ = l_Lean_isRecCore(v_env_943_, v_declName_939_);
v___x_945_ = lean_box(v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_947_, v___y_948_);
lean_dec(v___y_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(lean_object* v_declName_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_951_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(lean_object* v_declName_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(lean_object* v_a_965_, lean_object* v_b_966_){
_start:
{
lean_object* v_array_968_; lean_object* v_start_969_; lean_object* v_stop_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_987_; 
v_array_968_ = lean_ctor_get(v_a_965_, 0);
v_start_969_ = lean_ctor_get(v_a_965_, 1);
v_stop_970_ = lean_ctor_get(v_a_965_, 2);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_987_ == 0)
{
v___x_972_ = v_a_965_;
v_isShared_973_ = v_isSharedCheck_987_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_stop_970_);
lean_inc(v_start_969_);
lean_inc(v_array_968_);
lean_dec(v_a_965_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_987_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_lt(v_start_969_, v_stop_970_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_del_object(v___x_972_);
lean_dec(v_stop_970_);
lean_dec(v_start_969_);
lean_dec_ref(v_array_968_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_b_966_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_976_ = lean_box(0);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_add(v_start_969_, v___x_977_);
lean_inc_ref(v_array_968_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_978_);
v___x_980_ = v___x_972_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_array_968_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_stop_970_);
v___x_980_ = v_reuseFailAlloc_986_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_array_fget(v_array_968_, v_start_969_);
lean_dec(v_start_969_);
lean_dec_ref(v_array_968_);
v___x_982_ = l_Lean_Expr_hasExprMVar(v___x_981_);
lean_dec(v___x_981_);
if (v___x_982_ == 0)
{
v_a_965_ = v___x_980_;
v_b_966_ = v___x_976_;
goto _start;
}
else
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
v_a_965_ = v___x_980_;
v_b_966_ = v___x_976_;
goto _start;
}
else
{
lean_dec_ref(v___x_980_);
return v___x_984_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_988_, lean_object* v_b_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_988_, v_b_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_env_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_995_ = lean_st_ref_get(v___y_993_);
v_env_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_env_996_);
lean_dec(v___x_995_);
v___x_997_ = l_Lean_getReducibilityStatusCore(v_env_996_, v_declName_992_);
v___x_998_ = lean_box(v___x_997_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1000_, v___y_1001_);
lean_dec(v___y_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(lean_object* v_declName_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1026_; 
v___x_1010_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1004_, v___y_1008_);
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1026_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1026_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_unbox(v_a_1011_);
lean_dec(v_a_1011_);
if (v___x_1015_ == 0)
{
uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1016_ = 1;
v___x_1017_ = lean_box(v___x_1016_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1021_ = 0;
v___x_1022_ = lean_box(v___x_1021_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1022_);
v___x_1024_ = v___x_1013_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0___boxed(lean_object* v_declName_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1(void){
_start:
{
lean_object* v___x_1036_; lean_object* v_dummy_1037_; 
v___x_1036_ = lean_box(0);
v_dummy_1037_ = l_Lean_Expr_sort___override(v___x_1036_);
return v_dummy_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* v_e_1044_, uint8_t v_isMatch_1045_, uint8_t v_root_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1044_, v_root_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1209_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1209_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1209_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___y_1058_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; 
if (v_root_1046_ == 0)
{
lean_object* v___x_1197_; 
lean_inc(v_a_1053_);
v___x_1197_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_1053_);
if (lean_obj_tag(v___x_1197_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1208_; 
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 2);
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_val_1198_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
else
{
lean_dec(v___x_1197_);
v___y_1068_ = v_a_1047_;
v___y_1069_ = v_a_1048_;
v___y_1070_ = v_a_1049_;
v___y_1071_ = v_a_1050_;
goto v___jp_1067_;
}
}
else
{
v___y_1068_ = v_a_1047_;
v___y_1069_ = v_a_1048_;
v___y_1070_ = v_a_1049_;
v___y_1071_ = v_a_1050_;
goto v___jp_1067_;
}
v___jp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1059_ = l_Lean_Expr_getAppNumArgs(v_a_1053_);
lean_inc(v___x_1059_);
v___x_1060_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___y_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_mk_empty_array_with_capacity(v___x_1059_);
lean_dec(v___x_1059_);
v___x_1062_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1053_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1063_);
v___x_1065_ = v___x_1055_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
v___jp_1067_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Expr_getAppFn(v_a_1053_);
switch(lean_obj_tag(v___x_1072_))
{
case 9:
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1073_);
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
case 4:
{
lean_object* v_declName_1078_; lean_object* v___x_1079_; uint8_t v_isDefEqStuckEx_1080_; 
v_declName_1078_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_declName_1078_);
lean_dec_ref_known(v___x_1072_, 2);
v___x_1079_ = l_Lean_Meta_Context_config(v___y_1068_);
v_isDefEqStuckEx_1080_ = lean_ctor_get_uint8(v___x_1079_, 4);
lean_dec_ref(v___x_1079_);
if (v_isDefEqStuckEx_1080_ == 0)
{
v___y_1058_ = v_declName_1078_;
goto v___jp_1057_;
}
else
{
uint8_t v___x_1081_; 
v___x_1081_ = l_Lean_Expr_hasExprMVar(v_a_1053_);
if (v___x_1081_ == 0)
{
v___y_1058_ = v_declName_1078_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1082_; 
lean_inc(v_declName_1078_);
v___x_1082_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1078_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; uint8_t v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = lean_unbox(v_a_1083_);
lean_dec(v_a_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v_env_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_st_ref_get(v___y_1071_);
v_env_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_env_1086_);
lean_dec(v___x_1085_);
v___x_1087_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1086_, v_a_1053_);
if (lean_obj_tag(v___x_1087_) == 1)
{
lean_object* v_val_1088_; lean_object* v_numDiscrs_1089_; lean_object* v_nargs_1090_; lean_object* v_dummy_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_val_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v_numDiscrs_1089_ = lean_ctor_get(v_val_1088_, 1);
lean_inc(v_numDiscrs_1089_);
v_nargs_1090_ = l_Lean_Expr_getAppNumArgs(v_a_1053_);
v_dummy_1091_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
lean_inc(v_nargs_1090_);
v___x_1092_ = lean_mk_array(v_nargs_1090_, v_dummy_1091_);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_sub(v_nargs_1090_, v___x_1093_);
lean_dec(v_nargs_1090_);
lean_inc(v_a_1053_);
v___x_1095_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1053_, v___x_1092_, v___x_1094_);
v___x_1096_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1088_);
lean_dec(v_val_1088_);
v___x_1097_ = lean_nat_add(v___x_1096_, v_numDiscrs_1089_);
lean_dec(v_numDiscrs_1089_);
v___x_1098_ = l_Array_toSubarray___redArg(v___x_1095_, v___x_1096_, v___x_1097_);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_1098_, v___x_1099_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_dec_ref_known(v___x_1100_, 1);
v___y_1058_ = v_declName_1078_;
goto v___jp_1057_;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v_declName_1078_);
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_object* v___x_1109_; lean_object* v_a_1110_; uint8_t v___x_1111_; 
lean_dec(v___x_1087_);
lean_inc(v_declName_1078_);
v___x_1109_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_1078_, v___y_1071_);
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = lean_unbox(v_a_1110_);
lean_dec(v_a_1110_);
if (v___x_1111_ == 0)
{
v___y_1058_ = v_declName_1078_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_dec_ref_known(v___x_1112_, 1);
v___y_1058_ = v_declName_1078_;
goto v___jp_1057_;
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_declName_1078_);
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_dec_ref_known(v___x_1121_, 1);
v___y_1058_ = v_declName_1078_;
goto v___jp_1057_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_declName_1078_);
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_declName_1078_);
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v_a_1130_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1082_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1082_);
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
case 1:
{
lean_object* v_fvarId_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_del_object(v___x_1055_);
v_fvarId_1138_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_fvarId_1138_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1139_ = l_Lean_Expr_getAppNumArgs(v_a_1053_);
lean_inc(v___x_1139_);
v___x_1140_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_fvarId_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_mk_empty_array_with_capacity(v___x_1139_);
lean_dec(v___x_1139_);
v___x_1142_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1053_, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1140_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
case 2:
{
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
if (v_isMatch_1045_ == 0)
{
lean_object* v_mvarId_1145_; lean_object* v___x_1146_; uint8_t v_isDefEqStuckEx_1147_; 
v_mvarId_1145_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_mvarId_1145_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1146_ = l_Lean_Meta_Context_config(v___y_1068_);
v_isDefEqStuckEx_1147_ = lean_ctor_get_uint8(v___x_1146_, 4);
lean_dec_ref(v___x_1146_);
if (v_isDefEqStuckEx_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1145_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1162_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1162_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1162_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_unbox(v_a_1149_);
lean_dec(v_a_1149_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1158_);
v___x_1160_ = v___x_1151_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
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
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1148_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1148_);
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
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v_mvarId_1145_);
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref_known(v___x_1072_, 1);
v___x_1173_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
case 11:
{
lean_object* v_typeName_1175_; lean_object* v_idx_1176_; lean_object* v_struct_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_del_object(v___x_1055_);
v_typeName_1175_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_typeName_1175_);
v_idx_1176_ = lean_ctor_get(v___x_1072_, 1);
lean_inc(v_idx_1176_);
v_struct_1177_ = lean_ctor_get(v___x_1072_, 2);
lean_inc_ref(v_struct_1177_);
lean_dec_ref_known(v___x_1072_, 3);
v___x_1178_ = l_Lean_Expr_getAppNumArgs(v_a_1053_);
lean_inc(v___x_1178_);
v___x_1179_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1179_, 0, v_typeName_1175_);
lean_ctor_set(v___x_1179_, 1, v_idx_1176_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_mk_empty_array_with_capacity(v___x_1180_);
v___x_1182_ = lean_array_push(v___x_1181_, v_struct_1177_);
v___x_1183_ = lean_mk_empty_array_with_capacity(v___x_1178_);
lean_dec(v___x_1178_);
v___x_1184_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1053_, v___x_1183_);
v___x_1185_ = l_Array_append___redArg(v___x_1182_, v___x_1184_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1179_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
case 7:
{
lean_object* v_binderType_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v_binderType_1188_ = lean_ctor_get(v___x_1072_, 1);
lean_inc_ref(v_binderType_1188_);
lean_dec_ref_known(v___x_1072_, 3);
v___x_1189_ = lean_box(5);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_mk_empty_array_with_capacity(v___x_1190_);
v___x_1192_ = lean_array_push(v___x_1191_, v_binderType_1188_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1189_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
default: 
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v___x_1072_);
lean_del_object(v___x_1055_);
lean_dec(v_a_1053_);
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
v_a_1210_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1052_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1052_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* v_e_1218_, lean_object* v_isMatch_1219_, lean_object* v_root_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
uint8_t v_isMatch_boxed_1226_; uint8_t v_root_boxed_1227_; lean_object* v_res_1228_; 
v_isMatch_boxed_1226_ = lean_unbox(v_isMatch_1219_);
v_root_boxed_1227_ = lean_unbox(v_root_1220_);
v_res_1228_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1218_, v_isMatch_boxed_1226_, v_root_boxed_1227_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1229_, v___y_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object* v_inst_1243_, lean_object* v_R_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_c_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1245_, v_b_1246_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object* v_inst_1254_, lean_object* v_R_1255_, lean_object* v_a_1256_, lean_object* v_b_1257_, lean_object* v_c_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_1254_, v_R_1255_, v_a_1256_, v_b_1257_, v_c_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* v_e_1265_, uint8_t v_root_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
uint8_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = 1;
v___x_1273_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1265_, v___x_1272_, v_root_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* v_e_1274_, lean_object* v_root_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
uint8_t v_root_boxed_1281_; lean_object* v_res_1282_; 
v_root_boxed_1281_ = lean_unbox(v_root_1275_);
v_res_1282_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1274_, v_root_boxed_1281_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* v_e_1283_, uint8_t v_root_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
uint8_t v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = 0;
v___x_1291_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1283_, v___x_1290_, v_root_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* v_e_1292_, lean_object* v_root_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
uint8_t v_root_boxed_1299_; lean_object* v_res_1300_; 
v_root_boxed_1299_ = lean_unbox(v_root_1293_);
v_res_1300_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1292_, v_root_boxed_1299_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1301_, lean_object* v_vals_1302_, lean_object* v_i_1303_, lean_object* v_k_1304_){
_start:
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = lean_array_get_size(v_keys_1301_);
v___x_1306_ = lean_nat_dec_lt(v_i_1303_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec(v_i_1303_);
v___x_1307_ = lean_box(0);
return v___x_1307_;
}
else
{
lean_object* v_k_x27_1308_; uint8_t v___x_1309_; 
v_k_x27_1308_ = lean_array_fget_borrowed(v_keys_1301_, v_i_1303_);
v___x_1309_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1304_, v_k_x27_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_add(v_i_1303_, v___x_1310_);
lean_dec(v_i_1303_);
v_i_1303_ = v___x_1311_;
goto _start;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_array_fget_borrowed(v_vals_1302_, v_i_1303_);
lean_dec(v_i_1303_);
lean_inc(v___x_1313_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1315_, lean_object* v_vals_1316_, lean_object* v_i_1317_, lean_object* v_k_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1315_, v_vals_1316_, v_i_1317_, v_k_1318_);
lean_dec(v_k_1318_);
lean_dec_ref(v_vals_1316_);
lean_dec_ref(v_keys_1315_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1320_, size_t v_x_1321_, lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1320_) == 0)
{
lean_object* v_es_1323_; lean_object* v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v_j_1327_; lean_object* v___x_1328_; 
v_es_1323_ = lean_ctor_get(v_x_1320_, 0);
v___x_1324_ = lean_box(2);
v___x_1325_ = ((size_t)31ULL);
v___x_1326_ = lean_usize_land(v_x_1321_, v___x_1325_);
v_j_1327_ = lean_usize_to_nat(v___x_1326_);
v___x_1328_ = lean_array_get_borrowed(v___x_1324_, v_es_1323_, v_j_1327_);
lean_dec(v_j_1327_);
switch(lean_obj_tag(v___x_1328_))
{
case 0:
{
lean_object* v_key_1329_; lean_object* v_val_1330_; uint8_t v___x_1331_; 
v_key_1329_ = lean_ctor_get(v___x_1328_, 0);
v_val_1330_ = lean_ctor_get(v___x_1328_, 1);
v___x_1331_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1322_, v_key_1329_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_box(0);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; 
lean_inc(v_val_1330_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_val_1330_);
return v___x_1333_;
}
}
case 1:
{
lean_object* v_node_1334_; size_t v___x_1335_; size_t v___x_1336_; 
v_node_1334_ = lean_ctor_get(v___x_1328_, 0);
v___x_1335_ = ((size_t)5ULL);
v___x_1336_ = lean_usize_shift_right(v_x_1321_, v___x_1335_);
v_x_1320_ = v_node_1334_;
v_x_1321_ = v___x_1336_;
goto _start;
}
default: 
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_box(0);
return v___x_1338_;
}
}
}
else
{
lean_object* v_ks_1339_; lean_object* v_vs_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_ks_1339_ = lean_ctor_get(v_x_1320_, 0);
v_vs_1340_ = lean_ctor_get(v_x_1320_, 1);
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1339_, v_vs_1340_, v___x_1341_, v_x_1322_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
size_t v_x_184__boxed_1346_; lean_object* v_res_1347_; 
v_x_184__boxed_1346_ = lean_unbox_usize(v_x_1344_);
lean_dec(v_x_1344_);
v_res_1347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1343_, v_x_184__boxed_1346_, v_x_1345_);
lean_dec(v_x_1345_);
lean_dec_ref(v_x_1343_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
uint64_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1349_);
v___x_1351_ = lean_uint64_to_usize(v___x_1350_);
v___x_1352_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1348_, v___x_1351_, v_x_1349_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1353_, v_x_1354_);
lean_dec(v_x_1354_);
lean_dec_ref(v_x_1353_);
return v_res_1355_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_result_1360_; lean_object* v___x_1361_; 
v___x_1358_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_1359_ = lean_unsigned_to_nat(8u);
v_result_1360_ = lean_mk_empty_array_with_capacity(v___x_1359_);
v___x_1361_ = l_Array_append___redArg(v_result_1360_, v___x_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v_result_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1363_ = lean_unsigned_to_nat(8u);
v_result_1364_ = lean_mk_empty_array_with_capacity(v___x_1363_);
v___x_1365_ = lean_box(0);
v___x_1366_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1362_, v___x_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
return v_result_1364_;
}
else
{
lean_object* v_val_1367_; 
v_val_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v___x_1366_, 1);
if (lean_obj_tag(v_val_1367_) == 0)
{
lean_object* v___x_1368_; 
lean_dec_ref_known(v_val_1367_, 2);
lean_dec_ref(v_result_1364_);
v___x_1368_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1);
return v___x_1368_;
}
else
{
lean_object* v_vs_1369_; lean_object* v___x_1370_; 
v_vs_1369_ = lean_ctor_get(v_val_1367_, 0);
lean_inc_ref(v_vs_1369_);
lean_dec_ref_known(v_val_1367_, 2);
v___x_1370_ = l_Array_append___redArg(v_result_1364_, v_vs_1369_);
lean_dec_ref(v_vs_1369_);
return v___x_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___boxed(lean_object* v_d_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1371_);
lean_dec_ref(v_d_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1373_, lean_object* v_d_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_d_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(v_00_u03b1_1376_, v_d_1377_);
lean_dec_ref(v_d_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1380_, v_x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1383_, v_x_1384_, v_x_1385_);
lean_dec(v_x_1385_);
lean_dec_ref(v_x_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1387_, lean_object* v_x_1388_, size_t v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1388_, v_x_1389_, v_x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
size_t v_x_285__boxed_1396_; lean_object* v_res_1397_; 
v_x_285__boxed_1396_ = lean_unbox_usize(v_x_1394_);
lean_dec(v_x_1394_);
v_res_1397_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1392_, v_x_1393_, v_x_285__boxed_1396_, v_x_1395_);
lean_dec(v_x_1395_);
lean_dec_ref(v_x_1393_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1398_, lean_object* v_keys_1399_, lean_object* v_vals_1400_, lean_object* v_heq_1401_, lean_object* v_i_1402_, lean_object* v_k_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1399_, v_vals_1400_, v_i_1402_, v_k_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1405_, lean_object* v_keys_1406_, lean_object* v_vals_1407_, lean_object* v_heq_1408_, lean_object* v_i_1409_, lean_object* v_k_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1405_, v_keys_1406_, v_vals_1407_, v_heq_1408_, v_i_1409_, v_k_1410_);
lean_dec(v_k_1410_);
lean_dec_ref(v_vals_1407_);
lean_dec_ref(v_keys_1406_);
return v_res_1411_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object* v_a_1412_, lean_object* v_b_1413_){
_start:
{
lean_object* v_fst_1414_; lean_object* v_fst_1415_; uint8_t v___x_1416_; 
v_fst_1414_ = lean_ctor_get(v_a_1412_, 0);
v_fst_1415_ = lean_ctor_get(v_b_1413_, 0);
v___x_1416_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1414_, v_fst_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object* v_a_1417_, lean_object* v_b_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1417_, v_b_1418_);
lean_dec_ref(v_b_1418_);
lean_dec_ref(v_a_1417_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1425_, lean_object* v_k_1426_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_array_get_size(v_cs_1425_);
v___x_1429_ = lean_nat_dec_lt(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_k_1426_);
v___x_1430_ = lean_box(0);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_sub(v___x_1428_, v___x_1431_);
v___x_1433_ = lean_nat_dec_le(v___x_1427_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
lean_dec(v___x_1432_);
lean_dec(v_k_1426_);
v___x_1434_ = lean_box(0);
return v___x_1434_;
}
else
{
lean_object* v___f_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___f_1435_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1436_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_k_1426_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1439_ = l_Array_binSearchAux___redArg(v___f_1435_, v___x_1438_, v_cs_1425_, v___x_1437_, v___x_1427_, v___x_1432_);
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1440_, lean_object* v_k_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1440_, v_k_1441_);
lean_dec_ref(v_cs_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1443_, lean_object* v_cs_1444_, lean_object* v_k_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_array_get_size(v_cs_1444_);
v___x_1448_ = lean_nat_dec_lt(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_k_1445_);
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_sub(v___x_1447_, v___x_1450_);
v___x_1452_ = lean_nat_dec_le(v___x_1446_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec(v___x_1451_);
lean_dec(v_k_1445_);
v___x_1453_ = lean_box(0);
return v___x_1453_;
}
else
{
lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___f_1454_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_k_1445_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1458_ = l_Array_binSearchAux___redArg(v___f_1454_, v___x_1457_, v_cs_1444_, v___x_1456_, v___x_1446_, v___x_1451_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1459_, lean_object* v_cs_1460_, lean_object* v_k_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1459_, v_cs_1460_, v_k_1461_);
lean_dec_ref(v_cs_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1463_, lean_object* v_k_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v_m_1469_; lean_object* v_a_1470_; uint8_t v___x_1471_; 
v___x_1467_ = lean_nat_add(v_x_1465_, v_x_1466_);
v___x_1468_ = lean_unsigned_to_nat(1u);
v_m_1469_ = lean_nat_shiftr(v___x_1467_, v___x_1468_);
lean_dec(v___x_1467_);
v_a_1470_ = lean_array_fget_borrowed(v_as_1463_, v_m_1469_);
v___x_1471_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1470_, v_k_1464_);
if (v___x_1471_ == 0)
{
uint8_t v___x_1472_; 
lean_dec(v_x_1466_);
v___x_1472_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1464_, v_a_1470_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec(v_m_1469_);
lean_dec(v_x_1465_);
lean_inc(v_a_1470_);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_a_1470_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_nat_dec_eq(v_m_1469_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_nat_sub(v_m_1469_, v___x_1468_);
lean_dec(v_m_1469_);
v___x_1477_ = lean_nat_dec_lt(v___x_1476_, v_x_1465_);
if (v___x_1477_ == 0)
{
v_x_1466_ = v___x_1476_;
goto _start;
}
else
{
lean_object* v___x_1479_; 
lean_dec(v___x_1476_);
lean_dec(v_x_1465_);
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
}
else
{
lean_object* v___x_1480_; 
lean_dec(v_m_1469_);
lean_dec(v_x_1465_);
v___x_1480_ = lean_box(0);
return v___x_1480_;
}
}
}
else
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
lean_dec(v_x_1465_);
v___x_1481_ = lean_nat_add(v_m_1469_, v___x_1468_);
lean_dec(v_m_1469_);
v___x_1482_ = lean_nat_dec_le(v___x_1481_, v_x_1466_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
lean_dec(v___x_1481_);
lean_dec(v_x_1466_);
v___x_1483_ = lean_box(0);
return v___x_1483_;
}
else
{
v_x_1465_ = v___x_1481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1485_, lean_object* v_k_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1485_, v_k_1486_, v_x_1487_, v_x_1488_);
lean_dec_ref(v_k_1486_);
lean_dec_ref(v_as_1485_);
return v_res_1489_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Meta_DiscrTree_instInhabitedTrie___redArg();
return v___x_1490_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v___x_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1494_, lean_object* v_c_1495_, lean_object* v_result_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_c_1495_) == 0)
{
lean_object* v_key_1503_; lean_object* v_child_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v_key_1503_ = lean_ctor_get(v_c_1495_, 0);
lean_inc(v_key_1503_);
v_child_1504_ = lean_ctor_get(v_c_1495_, 1);
lean_inc_ref(v_child_1504_);
lean_dec_ref_known(v_c_1495_, 2);
v___x_1505_ = lean_array_get_size(v_todo_1494_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_nat_dec_eq(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_e_1510_; lean_object* v_todo_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_nat_sub(v___x_1505_, v___x_1508_);
v_e_1510_ = lean_array_get(v___x_1502_, v_todo_1494_, v___x_1509_);
lean_dec(v___x_1509_);
v_todo_1511_ = lean_array_pop(v_todo_1494_);
v___x_1512_ = 1;
v___x_1513_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1510_, v___x_1512_, v___x_1507_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1529_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1529_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1529_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_fst_1518_; lean_object* v_snd_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_fst_1518_ = lean_ctor_get(v_a_1514_, 0);
lean_inc(v_fst_1518_);
v_snd_1519_ = lean_ctor_get(v_a_1514_, 1);
lean_inc(v_snd_1519_);
lean_dec(v_a_1514_);
v___x_1520_ = lean_box(0);
v___x_1521_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1503_, v___x_1520_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; 
v___x_1522_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1503_, v_fst_1518_);
lean_dec(v_fst_1518_);
lean_dec(v_key_1503_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1524_; 
lean_dec(v_snd_1519_);
lean_dec_ref(v_todo_1511_);
lean_dec_ref(v_child_1504_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v_result_1496_);
v___x_1524_ = v___x_1516_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_result_1496_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
else
{
lean_object* v___x_1526_; 
lean_del_object(v___x_1516_);
v___x_1526_ = l_Array_append___redArg(v_todo_1511_, v_snd_1519_);
lean_dec(v_snd_1519_);
v_todo_1494_ = v___x_1526_;
v_c_1495_ = v_child_1504_;
goto _start;
}
}
else
{
lean_dec(v_snd_1519_);
lean_dec(v_fst_1518_);
lean_del_object(v___x_1516_);
lean_dec(v_key_1503_);
v_todo_1494_ = v_todo_1511_;
v_c_1495_ = v_child_1504_;
goto _start;
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_todo_1511_);
lean_dec_ref(v_child_1504_);
lean_dec(v_key_1503_);
lean_dec_ref(v_result_1496_);
v_a_1530_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1513_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1513_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v___x_1538_; 
lean_dec_ref(v_child_1504_);
lean_dec(v_key_1503_);
lean_dec_ref(v_todo_1494_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_result_1496_);
return v___x_1538_;
}
}
else
{
lean_object* v_vs_1539_; lean_object* v_children_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_vs_1539_ = lean_ctor_get(v_c_1495_, 0);
lean_inc_ref(v_vs_1539_);
v_children_1540_ = lean_ctor_get(v_c_1495_, 1);
lean_inc_ref(v_children_1540_);
lean_dec_ref_known(v_c_1495_, 2);
v___x_1541_ = lean_array_get_size(v_todo_1494_);
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = lean_nat_dec_eq(v___x_1541_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
lean_dec_ref(v_vs_1539_);
v___x_1544_ = lean_array_get_size(v_children_1540_);
v___x_1545_ = lean_nat_dec_eq(v___x_1544_, v___x_1542_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_e_1550_; lean_object* v_todo_1551_; lean_object* v_first_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_nat_sub(v___x_1541_, v___x_1548_);
v_e_1550_ = lean_array_get(v___x_1502_, v_todo_1494_, v___x_1549_);
lean_dec(v___x_1549_);
v_todo_1551_ = lean_array_pop(v_todo_1494_);
v_first_1552_ = lean_array_get_borrowed(v___x_1547_, v_children_1540_, v___x_1542_);
v___x_1553_ = 1;
v___x_1554_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1550_, v___x_1553_, v___x_1545_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1588_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1588_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1588_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_fst_1559_; lean_object* v_snd_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1587_; 
v_fst_1559_ = lean_ctor_get(v_a_1555_, 0);
v_snd_1560_ = lean_ctor_get(v_a_1555_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_a_1555_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1562_ = v_a_1555_;
v_isShared_1563_ = v_isSharedCheck_1587_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snd_1560_);
lean_inc(v_fst_1559_);
lean_dec(v_a_1555_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1587_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___y_1565_; lean_object* v_a_1566_; lean_object* v_fst_1579_; lean_object* v_snd_1580_; uint8_t v___x_1581_; 
v_fst_1579_ = lean_ctor_get(v_first_1552_, 0);
v_snd_1580_ = lean_ctor_get(v_first_1552_, 1);
v___x_1581_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1579_, v___x_1546_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1583_; 
lean_inc_ref(v_result_1496_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v_result_1496_);
v___x_1583_ = v___x_1557_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_result_1496_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
v___y_1565_ = v___x_1583_;
v_a_1566_ = v_result_1496_;
goto v___jp_1564_;
}
}
else
{
lean_object* v___x_1585_; 
lean_del_object(v___x_1557_);
lean_inc(v_snd_1580_);
lean_inc_ref(v_todo_1551_);
v___x_1585_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1551_, v_snd_1580_, v_result_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
v___y_1565_ = v___x_1585_;
v_a_1566_ = v_a_1586_;
goto v___jp_1564_;
}
else
{
lean_del_object(v___x_1562_);
lean_dec(v_snd_1560_);
lean_dec(v_fst_1559_);
lean_dec_ref(v_todo_1551_);
lean_dec_ref(v_children_1540_);
return v___x_1585_;
}
}
v___jp_1564_:
{
if (lean_obj_tag(v_fst_1559_) == 0)
{
lean_dec_ref(v_a_1566_);
lean_del_object(v___x_1562_);
lean_dec(v_snd_1560_);
lean_dec_ref(v_todo_1551_);
lean_dec_ref(v_children_1540_);
return v___y_1565_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_nat_dec_lt(v___x_1542_, v___x_1544_);
if (v___x_1567_ == 0)
{
lean_dec_ref(v_a_1566_);
lean_del_object(v___x_1562_);
lean_dec(v_snd_1560_);
lean_dec(v_fst_1559_);
lean_dec_ref(v_todo_1551_);
lean_dec_ref(v_children_1540_);
return v___y_1565_;
}
else
{
lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = lean_nat_sub(v___x_1544_, v___x_1548_);
v___x_1569_ = lean_nat_dec_le(v___x_1542_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_dec(v___x_1568_);
lean_dec_ref(v_a_1566_);
lean_del_object(v___x_1562_);
lean_dec(v_snd_1560_);
lean_dec(v_fst_1559_);
lean_dec_ref(v_todo_1551_);
lean_dec_ref(v_children_1540_);
return v___y_1565_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___x_1570_);
v___x_1572_ = v___x_1562_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_fst_1559_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1540_, v___x_1572_, v___x_1542_, v___x_1568_);
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_children_1540_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_dec_ref(v_a_1566_);
lean_dec(v_snd_1560_);
lean_dec_ref(v_todo_1551_);
return v___y_1565_;
}
else
{
lean_object* v_val_1574_; lean_object* v_snd_1575_; lean_object* v___x_1576_; 
lean_dec_ref(v___y_1565_);
v_val_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v_snd_1575_ = lean_ctor_get(v_val_1574_, 1);
lean_inc(v_snd_1575_);
lean_dec(v_val_1574_);
v___x_1576_ = l_Array_append___redArg(v_todo_1551_, v_snd_1560_);
lean_dec(v_snd_1560_);
v_todo_1494_ = v___x_1576_;
v_c_1495_ = v_snd_1575_;
v_result_1496_ = v_a_1566_;
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
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_todo_1551_);
lean_dec_ref(v_children_1540_);
lean_dec_ref(v_result_1496_);
v_a_1589_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1554_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1554_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v___x_1597_; 
lean_dec_ref(v_children_1540_);
lean_dec_ref(v_todo_1494_);
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_result_1496_);
return v___x_1597_;
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v_children_1540_);
lean_dec_ref(v_todo_1494_);
v___x_1598_ = l_Array_append___redArg(v_result_1496_, v_vs_1539_);
lean_dec_ref(v_vs_1539_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1600_, lean_object* v_c_1601_, lean_object* v_result_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1600_, v_c_1601_, v_result_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1609_, lean_object* v_todo_1610_, lean_object* v_c_1611_, lean_object* v_result_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1610_, v_c_1611_, v_result_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_todo_1620_, lean_object* v_c_1621_, lean_object* v_result_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1619_, v_todo_1620_, v_c_1621_, v_result_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1629_, lean_object* v_as_1630_, lean_object* v_k_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1630_, v_k_1631_, v_x_1632_, v_x_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1636_, lean_object* v_as_1637_, lean_object* v_k_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1636_, v_as_1637_, v_k_1638_, v_x_1639_, v_x_1640_, v_x_1641_);
lean_dec_ref(v_k_1638_);
lean_dec_ref(v_as_1637_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1643_, lean_object* v_k_1644_, lean_object* v_args_1645_, lean_object* v_result_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1643_, v_k_1644_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v_args_1645_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_result_1646_);
return v___x_1653_;
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1655_; 
v_val_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1655_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1645_, v_val_1654_, v_result_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1656_, lean_object* v_k_1657_, lean_object* v_args_1658_, lean_object* v_result_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1656_, v_k_1657_, v_args_1658_, v_result_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_k_1657_);
lean_dec_ref(v_d_1656_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1666_, lean_object* v_d_1667_, lean_object* v_k_1668_, lean_object* v_args_1669_, lean_object* v_result_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1667_, v_k_1668_, v_args_1669_, v_result_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1677_, lean_object* v_d_1678_, lean_object* v_k_1679_, lean_object* v_args_1680_, lean_object* v_result_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1677_, v_d_1678_, v_k_1679_, v_args_1680_, v_result_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_k_1679_);
lean_dec_ref(v_d_1678_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(lean_object* v_e_1688_, uint8_t v___x_1689_, lean_object* v_result_1690_, lean_object* v_d_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1688_, v___x_1689_, v___x_1689_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1741_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1741_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1741_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_fst_1702_; 
v_fst_1702_ = lean_ctor_get(v_a_1698_, 0);
lean_inc(v_fst_1702_);
if (lean_obj_tag(v_fst_1702_) == 0)
{
lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1712_; 
v_isSharedCheck_1712_ = !lean_is_exclusive(v_a_1698_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; lean_object* v_unused_1714_; 
v_unused_1713_ = lean_ctor_get(v_a_1698_, 1);
lean_dec(v_unused_1713_);
v_unused_1714_ = lean_ctor_get(v_a_1698_, 0);
lean_dec(v_unused_1714_);
v___x_1704_ = v_a_1698_;
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
else
{
lean_dec(v_a_1698_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_result_1690_);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_fst_1702_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_result_1690_);
v___x_1707_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1707_);
v___x_1709_ = v___x_1700_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_snd_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1739_; 
lean_del_object(v___x_1700_);
v_snd_1715_ = lean_ctor_get(v_a_1698_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_a_1698_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v_a_1698_, 0);
lean_dec(v_unused_1740_);
v___x_1717_ = v_a_1698_;
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_snd_1715_);
lean_dec(v_a_1698_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1739_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; 
v___x_1719_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1691_, v_fst_1702_, v_snd_1715_, v_result_1690_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1730_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1730_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v_a_1720_);
v___x_1725_ = v___x_1717_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_fst_1702_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_del_object(v___x_1717_);
lean_dec(v_fst_1702_);
v_a_1731_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1719_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1719_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_result_1690_);
v_a_1742_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1697_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1697_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0___boxed(lean_object* v_e_1750_, lean_object* v___x_1751_, lean_object* v_result_1752_, lean_object* v_d_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v___x_802__boxed_1759_; lean_object* v_res_1760_; 
v___x_802__boxed_1759_ = lean_unbox(v___x_1751_);
v_res_1760_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1750_, v___x_802__boxed_1759_, v_result_1752_, v_d_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v_d_1753_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1761_, lean_object* v_e_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___y_1769_; lean_object* v___x_1786_; uint8_t v_transparency_1787_; lean_object* v_result_1788_; uint8_t v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; 
v___x_1786_ = l_Lean_Meta_Context_config(v_a_1763_);
v_transparency_1787_ = lean_ctor_get_uint8(v___x_1786_, 9);
lean_dec_ref(v___x_1786_);
v_result_1788_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1761_);
v___x_1789_ = 1;
v___x_1790_ = 2;
v___x_1791_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1787_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v_keyedConfig_1792_; uint8_t v_trackZetaDelta_1793_; lean_object* v_zetaDeltaSet_1794_; lean_object* v_lctx_1795_; lean_object* v_localInstances_1796_; lean_object* v_defEqCtx_x3f_1797_; lean_object* v_synthPendingDepth_1798_; lean_object* v_customCanUnfoldPredicate_x3f_1799_; uint8_t v_univApprox_1800_; uint8_t v_inTypeClassResolution_1801_; uint8_t v_cacheInferType_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_keyedConfig_1792_ = lean_ctor_get(v_a_1763_, 0);
v_trackZetaDelta_1793_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*7);
v_zetaDeltaSet_1794_ = lean_ctor_get(v_a_1763_, 1);
v_lctx_1795_ = lean_ctor_get(v_a_1763_, 2);
v_localInstances_1796_ = lean_ctor_get(v_a_1763_, 3);
v_defEqCtx_x3f_1797_ = lean_ctor_get(v_a_1763_, 4);
v_synthPendingDepth_1798_ = lean_ctor_get(v_a_1763_, 5);
v_customCanUnfoldPredicate_x3f_1799_ = lean_ctor_get(v_a_1763_, 6);
v_univApprox_1800_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1801_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*7 + 2);
v_cacheInferType_1802_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1792_);
v___x_1803_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1790_, v_keyedConfig_1792_);
lean_inc(v_customCanUnfoldPredicate_x3f_1799_);
lean_inc(v_synthPendingDepth_1798_);
lean_inc(v_defEqCtx_x3f_1797_);
lean_inc_ref(v_localInstances_1796_);
lean_inc_ref(v_lctx_1795_);
lean_inc(v_zetaDeltaSet_1794_);
v___x_1804_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v_zetaDeltaSet_1794_);
lean_ctor_set(v___x_1804_, 2, v_lctx_1795_);
lean_ctor_set(v___x_1804_, 3, v_localInstances_1796_);
lean_ctor_set(v___x_1804_, 4, v_defEqCtx_x3f_1797_);
lean_ctor_set(v___x_1804_, 5, v_synthPendingDepth_1798_);
lean_ctor_set(v___x_1804_, 6, v_customCanUnfoldPredicate_x3f_1799_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*7, v_trackZetaDelta_1793_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*7 + 1, v_univApprox_1800_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1801_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*7 + 3, v_cacheInferType_1802_);
v___x_1805_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1762_, v___x_1789_, v_result_1788_, v_d_1761_, v___x_1804_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec_ref_known(v___x_1804_, 7);
v___y_1769_ = v___x_1805_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1762_, v___x_1789_, v_result_1788_, v_d_1761_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
v___y_1769_ = v___x_1806_;
goto v___jp_1768_;
}
v___jp_1768_:
{
if (lean_obj_tag(v___y_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___y_1769_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___y_1769_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___y_1769_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___y_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_a_1778_ = lean_ctor_get(v___y_1769_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___y_1769_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___y_1769_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___y_1769_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1807_, lean_object* v_e_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1807_, v_e_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec_ref(v_d_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1815_, lean_object* v_d_1816_, lean_object* v_e_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1816_, v_e_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_d_1825_, lean_object* v_e_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1824_, v_d_1825_, v_e_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec_ref(v_d_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1833_, lean_object* v_e_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1833_, v_e_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1849_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1849_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_snd_1845_; lean_object* v___x_1847_; 
v_snd_1845_ = lean_ctor_get(v_a_1841_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_a_1841_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v_snd_1845_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_snd_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1840_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1840_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1858_, lean_object* v_e_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1858_, v_e_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec_ref(v_d_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1866_, lean_object* v_d_1867_, lean_object* v_e_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1867_, v_e_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1875_, lean_object* v_d_1876_, lean_object* v_e_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1875_, v_d_1876_, v_e_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec_ref(v_d_1876_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1884_, lean_object* v_k_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_k_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; 
switch(lean_obj_tag(v_k_1885_))
{
case 4:
{
lean_object* v_a_1913_; lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1925_; 
v_a_1913_ = lean_ctor_get(v_k_1885_, 0);
v_a_1914_ = lean_ctor_get(v_k_1885_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_k_1885_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1916_ = v_k_1885_;
v_isShared_1917_ = v_isSharedCheck_1925_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_inc(v_a_1913_);
lean_dec(v_k_1885_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1925_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_zero_1918_; uint8_t v_isZero_1919_; 
v_zero_1918_ = lean_unsigned_to_nat(0u);
v_isZero_1919_ = lean_nat_dec_eq(v_a_1914_, v_zero_1918_);
if (v_isZero_1919_ == 0)
{
lean_object* v_one_1920_; lean_object* v_n_1921_; lean_object* v___x_1923_; 
v_one_1920_ = lean_unsigned_to_nat(1u);
v_n_1921_ = lean_nat_sub(v_a_1914_, v_one_1920_);
lean_dec(v_a_1914_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_n_1921_);
v___x_1923_ = v___x_1916_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1913_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_n_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
v_k_1896_ = v___x_1923_;
v___y_1897_ = v_a_1886_;
v___y_1898_ = v_a_1887_;
v___y_1899_ = v_a_1888_;
v___y_1900_ = v_a_1889_;
goto v___jp_1895_;
}
}
else
{
lean_del_object(v___x_1916_);
lean_dec(v_a_1914_);
lean_dec(v_a_1913_);
goto v___jp_1891_;
}
}
}
case 3:
{
lean_object* v_a_1926_; lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1938_; 
v_a_1926_ = lean_ctor_get(v_k_1885_, 0);
v_a_1927_ = lean_ctor_get(v_k_1885_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_k_1885_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1929_ = v_k_1885_;
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_inc(v_a_1926_);
lean_dec(v_k_1885_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_zero_1931_; uint8_t v_isZero_1932_; 
v_zero_1931_ = lean_unsigned_to_nat(0u);
v_isZero_1932_ = lean_nat_dec_eq(v_a_1927_, v_zero_1931_);
if (v_isZero_1932_ == 0)
{
lean_object* v_one_1933_; lean_object* v_n_1934_; lean_object* v___x_1936_; 
v_one_1933_ = lean_unsigned_to_nat(1u);
v_n_1934_ = lean_nat_sub(v_a_1927_, v_one_1933_);
lean_dec(v_a_1927_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v_n_1934_);
v___x_1936_ = v___x_1929_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1926_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_n_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
v_k_1896_ = v___x_1936_;
v___y_1897_ = v_a_1886_;
v___y_1898_ = v_a_1887_;
v___y_1899_ = v_a_1888_;
v___y_1900_ = v_a_1889_;
goto v___jp_1895_;
}
}
else
{
lean_del_object(v___x_1929_);
lean_dec(v_a_1927_);
lean_dec(v_a_1926_);
goto v___jp_1891_;
}
}
}
case 6:
{
lean_object* v_a_1939_; lean_object* v_a_1940_; lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1952_; 
v_a_1939_ = lean_ctor_get(v_k_1885_, 0);
v_a_1940_ = lean_ctor_get(v_k_1885_, 1);
v_a_1941_ = lean_ctor_get(v_k_1885_, 2);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_k_1885_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1943_ = v_k_1885_;
v_isShared_1944_ = v_isSharedCheck_1952_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_inc(v_a_1940_);
lean_inc(v_a_1939_);
lean_dec(v_k_1885_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1952_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v_zero_1945_; uint8_t v_isZero_1946_; 
v_zero_1945_ = lean_unsigned_to_nat(0u);
v_isZero_1946_ = lean_nat_dec_eq(v_a_1941_, v_zero_1945_);
if (v_isZero_1946_ == 0)
{
lean_object* v_one_1947_; lean_object* v_n_1948_; lean_object* v___x_1950_; 
v_one_1947_ = lean_unsigned_to_nat(1u);
v_n_1948_ = lean_nat_sub(v_a_1941_, v_one_1947_);
lean_dec(v_a_1941_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 2, v_n_1948_);
v___x_1950_ = v___x_1943_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1939_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_a_1940_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_n_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
v_k_1896_ = v___x_1950_;
v___y_1897_ = v_a_1886_;
v___y_1898_ = v_a_1887_;
v___y_1899_ = v_a_1888_;
v___y_1900_ = v_a_1889_;
goto v___jp_1895_;
}
}
else
{
lean_del_object(v___x_1943_);
lean_dec(v_a_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
goto v___jp_1891_;
}
}
}
default: 
{
lean_dec(v_k_1885_);
goto v___jp_1891_;
}
}
v___jp_1891_:
{
uint8_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = 0;
v___x_1893_ = lean_box(v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
v___jp_1895_:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1884_, v_k_1896_);
if (lean_obj_tag(v___x_1901_) == 0)
{
v_k_1885_ = v_k_1896_;
v_a_1886_ = v___y_1897_;
v_a_1887_ = v___y_1898_;
v_a_1888_ = v___y_1899_;
v_a_1889_ = v___y_1900_;
goto _start;
}
else
{
lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_k_1896_);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1901_, 0);
lean_dec(v_unused_1912_);
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
else
{
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
uint8_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1906_ = 1;
v___x_1907_ = lean_box(v___x_1906_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1907_);
v___x_1909_ = v___x_1904_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_1953_, lean_object* v_k_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1953_, v_k_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec_ref(v_d_1953_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_1961_, lean_object* v_d_1962_, lean_object* v_k_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1962_, v_k_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_1970_, lean_object* v_d_1971_, lean_object* v_k_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_1970_, v_d_1971_, v_k_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec_ref(v_d_1971_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_1979_, size_t v_sz_1980_, size_t v_i_1981_, lean_object* v_bs_1982_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_lt(v_i_1981_, v_sz_1980_);
if (v___x_1983_ == 0)
{
lean_dec(v_numExtra_1979_);
return v_bs_1982_;
}
else
{
lean_object* v_v_1984_; lean_object* v___x_1985_; lean_object* v_bs_x27_1986_; lean_object* v___x_1987_; size_t v___x_1988_; size_t v___x_1989_; lean_object* v___x_1990_; 
v_v_1984_ = lean_array_uget(v_bs_1982_, v_i_1981_);
v___x_1985_ = lean_unsigned_to_nat(0u);
v_bs_x27_1986_ = lean_array_uset(v_bs_1982_, v_i_1981_, v___x_1985_);
lean_inc(v_numExtra_1979_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_v_1984_);
lean_ctor_set(v___x_1987_, 1, v_numExtra_1979_);
v___x_1988_ = ((size_t)1ULL);
v___x_1989_ = lean_usize_add(v_i_1981_, v___x_1988_);
v___x_1990_ = lean_array_uset(v_bs_x27_1986_, v_i_1981_, v___x_1987_);
v_i_1981_ = v___x_1989_;
v_bs_1982_ = v___x_1990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_1992_, lean_object* v_sz_1993_, lean_object* v_i_1994_, lean_object* v_bs_1995_){
_start:
{
size_t v_sz_boxed_1996_; size_t v_i_boxed_1997_; lean_object* v_res_1998_; 
v_sz_boxed_1996_ = lean_unbox_usize(v_sz_1993_);
lean_dec(v_sz_1993_);
v_i_boxed_1997_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_res_1998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1992_, v_sz_boxed_1996_, v_i_boxed_1997_, v_bs_1995_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_1999_, lean_object* v_e_2000_, lean_object* v_numExtra_2001_, lean_object* v_result_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; 
lean_inc_ref(v_e_2000_);
v___x_2008_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1999_, v_e_2000_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2026_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2026_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2026_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_snd_2013_; size_t v_sz_2014_; size_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_snd_2013_ = lean_ctor_get(v_a_2009_, 1);
lean_inc(v_snd_2013_);
lean_dec(v_a_2009_);
v_sz_2014_ = lean_array_size(v_snd_2013_);
v___x_2015_ = ((size_t)0ULL);
lean_inc(v_numExtra_2001_);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2001_, v_sz_2014_, v___x_2015_, v_snd_2013_);
v___x_2017_ = l_Array_append___redArg(v_result_2002_, v___x_2016_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = l_Lean_Expr_isApp(v_e_2000_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v_numExtra_2001_);
lean_dec_ref(v_e_2000_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2017_);
v___x_2020_ = v___x_2011_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2017_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_del_object(v___x_2011_);
v___x_2022_ = l_Lean_Expr_appFn_x21(v_e_2000_);
lean_dec_ref(v_e_2000_);
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_add(v_numExtra_2001_, v___x_2023_);
lean_dec(v_numExtra_2001_);
v_e_2000_ = v___x_2022_;
v_numExtra_2001_ = v___x_2024_;
v_result_2002_ = v___x_2017_;
goto _start;
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v_result_2002_);
lean_dec(v_numExtra_2001_);
lean_dec_ref(v_e_2000_);
v_a_2027_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2008_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2008_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2035_, lean_object* v_e_2036_, lean_object* v_numExtra_2037_, lean_object* v_result_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2035_, v_e_2036_, v_numExtra_2037_, v_result_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_d_2035_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2045_, lean_object* v_d_2046_, lean_object* v_e_2047_, lean_object* v_numExtra_2048_, lean_object* v_result_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2046_, v_e_2047_, v_numExtra_2048_, v_result_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_d_2057_, lean_object* v_e_2058_, lean_object* v_numExtra_2059_, lean_object* v_result_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2056_, v_d_2057_, v_e_2058_, v_numExtra_2059_, v_result_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec_ref(v_d_2057_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2067_, lean_object* v_numExtra_2068_, size_t v_sz_2069_, size_t v_i_2070_, lean_object* v_bs_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2068_, v_sz_2069_, v_i_2070_, v_bs_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2073_, lean_object* v_numExtra_2074_, lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_bs_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2073_, v_numExtra_2074_, v_sz_boxed_2078_, v_i_boxed_2079_, v_bs_2077_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2081_, size_t v_i_2082_, lean_object* v_bs_2083_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_lt(v_i_2082_, v_sz_2081_);
if (v___x_2084_ == 0)
{
return v_bs_2083_;
}
else
{
lean_object* v_v_2085_; lean_object* v___x_2086_; lean_object* v_bs_x27_2087_; lean_object* v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v_v_2085_ = lean_array_uget(v_bs_2083_, v_i_2082_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v_bs_x27_2087_ = lean_array_uset(v_bs_2083_, v_i_2082_, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_v_2085_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_i_2082_, v___x_2089_);
v___x_2091_ = lean_array_uset(v_bs_x27_2087_, v_i_2082_, v___x_2088_);
v_i_2082_ = v___x_2090_;
v_bs_2083_ = v___x_2091_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2093_, lean_object* v_i_2094_, lean_object* v_bs_2095_){
_start:
{
size_t v_sz_boxed_2096_; size_t v_i_boxed_2097_; lean_object* v_res_2098_; 
v_sz_boxed_2096_ = lean_unbox_usize(v_sz_2093_);
lean_dec(v_sz_2093_);
v_i_boxed_2097_ = lean_unbox_usize(v_i_2094_);
lean_dec(v_i_2094_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2096_, v_i_boxed_2097_, v_bs_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2099_, lean_object* v_e_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2106_; 
lean_inc_ref(v_e_2100_);
v___x_2106_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2099_, v_e_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2141_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2141_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2141_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_fst_2111_; lean_object* v_snd_2112_; size_t v_sz_2113_; size_t v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_fst_2111_ = lean_ctor_get(v_a_2107_, 0);
lean_inc(v_fst_2111_);
v_snd_2112_ = lean_ctor_get(v_a_2107_, 1);
lean_inc(v_snd_2112_);
lean_dec(v_a_2107_);
v_sz_2113_ = lean_array_size(v_snd_2112_);
v___x_2114_ = ((size_t)0ULL);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2113_, v___x_2114_, v_snd_2112_);
v___x_2116_ = l_Lean_Expr_isApp(v_e_2100_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2118_; 
lean_dec(v_fst_2111_);
lean_dec_ref(v_e_2100_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2115_);
v___x_2118_ = v___x_2109_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2115_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
else
{
lean_object* v___x_2120_; 
lean_del_object(v___x_2109_);
v___x_2120_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2099_, v_fst_2111_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2132_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2132_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2132_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_unbox(v_a_2121_);
lean_dec(v_a_2121_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2127_; 
lean_dec_ref(v_e_2100_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2115_);
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2115_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_del_object(v___x_2123_);
v___x_2129_ = l_Lean_Expr_appFn_x21(v_e_2100_);
lean_dec_ref(v_e_2100_);
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2099_, v___x_2129_, v___x_2130_, v___x_2115_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
return v___x_2131_;
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v_e_2100_);
v_a_2133_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2120_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2120_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_e_2100_);
v_a_2142_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2106_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2106_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2150_, lean_object* v_e_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2150_, v_e_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec_ref(v_d_2150_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2158_, lean_object* v_d_2159_, lean_object* v_e_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2159_, v_e_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_d_2168_, lean_object* v_e_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2167_, v_d_2168_, v_e_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
lean_dec_ref(v_d_2168_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2176_, size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_bs_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2177_, v_i_2178_, v_bs_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_sz_2182_, lean_object* v_i_2183_, lean_object* v_bs_2184_){
_start:
{
size_t v_sz_boxed_2185_; size_t v_i_boxed_2186_; lean_object* v_res_2187_; 
v_sz_boxed_2185_ = lean_unbox_usize(v_sz_2182_);
lean_dec(v_sz_2182_);
v_i_boxed_2186_ = lean_unbox_usize(v_i_2183_);
lean_dec(v_i_2183_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2181_, v_sz_boxed_2185_, v_i_boxed_2186_, v_bs_2184_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
uint8_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = 1;
v___x_2195_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2188_, v___x_2194_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2219_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2219_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2219_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___y_2202_; lean_object* v___x_2207_; 
v___x_2200_ = l_Lean_Expr_getAppNumArgs(v_a_2196_);
v___x_2207_ = l_Lean_Expr_getAppFn(v_a_2196_);
lean_dec(v_a_2196_);
switch(lean_obj_tag(v___x_2207_))
{
case 9:
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_ref(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2208_);
v___y_2202_ = v___x_2209_;
goto v___jp_2201_;
}
case 1:
{
lean_object* v_fvarId_2210_; lean_object* v___x_2211_; 
v_fvarId_2210_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_fvarId_2210_);
lean_dec_ref_known(v___x_2207_, 1);
lean_inc(v___x_2200_);
v___x_2211_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_fvarId_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2200_);
v___y_2202_ = v___x_2211_;
goto v___jp_2201_;
}
case 11:
{
lean_object* v_typeName_2212_; lean_object* v_idx_2213_; lean_object* v___x_2214_; 
v_typeName_2212_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_typeName_2212_);
v_idx_2213_ = lean_ctor_get(v___x_2207_, 1);
lean_inc(v_idx_2213_);
lean_dec_ref_known(v___x_2207_, 3);
lean_inc(v___x_2200_);
v___x_2214_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2214_, 0, v_typeName_2212_);
lean_ctor_set(v___x_2214_, 1, v_idx_2213_);
lean_ctor_set(v___x_2214_, 2, v___x_2200_);
v___y_2202_ = v___x_2214_;
goto v___jp_2201_;
}
case 7:
{
lean_object* v___x_2215_; 
lean_dec_ref_known(v___x_2207_, 3);
v___x_2215_ = lean_box(5);
v___y_2202_ = v___x_2215_;
goto v___jp_2201_;
}
case 4:
{
lean_object* v_declName_2216_; lean_object* v___x_2217_; 
v_declName_2216_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_declName_2216_);
lean_dec_ref_known(v___x_2207_, 2);
lean_inc(v___x_2200_);
v___x_2217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_declName_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2200_);
v___y_2202_ = v___x_2217_;
goto v___jp_2201_;
}
default: 
{
lean_object* v___x_2218_; 
lean_dec_ref(v___x_2207_);
v___x_2218_ = lean_box(1);
v___y_2202_ = v___x_2218_;
goto v___jp_2201_;
}
}
v___jp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___y_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2200_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2203_);
v___x_2205_ = v___x_2198_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2195_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2195_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2235_, size_t v_sz_2236_, size_t v_i_2237_, lean_object* v_b_2238_){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = lean_usize_dec_lt(v_i_2237_, v_sz_2236_);
if (v___x_2239_ == 0)
{
return v_b_2238_;
}
else
{
lean_object* v_a_2240_; lean_object* v_snd_2241_; lean_object* v___x_2242_; size_t v___x_2243_; size_t v___x_2244_; 
v_a_2240_ = lean_array_uget_borrowed(v_as_2235_, v_i_2237_);
v_snd_2241_ = lean_ctor_get(v_a_2240_, 1);
v___x_2242_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2241_, v_b_2238_);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2237_, v___x_2243_);
v_i_2237_ = v___x_2244_;
v_b_2238_ = v___x_2242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2246_, lean_object* v_result_2247_){
_start:
{
if (lean_obj_tag(v_trie_2246_) == 0)
{
lean_object* v_child_2248_; 
v_child_2248_ = lean_ctor_get(v_trie_2246_, 1);
v_trie_2246_ = v_child_2248_;
goto _start;
}
else
{
lean_object* v_vs_2250_; lean_object* v_children_2251_; lean_object* v_result_2252_; size_t v_sz_2253_; size_t v___x_2254_; lean_object* v___x_2255_; 
v_vs_2250_ = lean_ctor_get(v_trie_2246_, 0);
v_children_2251_ = lean_ctor_get(v_trie_2246_, 1);
v_result_2252_ = l_Array_append___redArg(v_result_2247_, v_vs_2250_);
v_sz_2253_ = lean_array_size(v_children_2251_);
v___x_2254_ = ((size_t)0ULL);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2251_, v_sz_2253_, v___x_2254_, v_result_2252_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2256_, lean_object* v_result_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2256_, v_result_2257_);
lean_dec_ref(v_trie_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2259_, lean_object* v_sz_2260_, lean_object* v_i_2261_, lean_object* v_b_2262_){
_start:
{
size_t v_sz_boxed_2263_; size_t v_i_boxed_2264_; lean_object* v_res_2265_; 
v_sz_boxed_2263_ = lean_unbox_usize(v_sz_2260_);
lean_dec(v_sz_2260_);
v_i_boxed_2264_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_res_2265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2259_, v_sz_boxed_2263_, v_i_boxed_2264_, v_b_2262_);
lean_dec_ref(v_as_2259_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2266_, lean_object* v_trie_2267_, lean_object* v_result_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2267_, v_result_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_trie_2271_, lean_object* v_result_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2270_, v_trie_2271_, v_result_2272_);
lean_dec_ref(v_trie_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2274_, lean_object* v_as_2275_, size_t v_sz_2276_, size_t v_i_2277_, lean_object* v_b_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2275_, v_sz_2276_, v_i_2277_, v_b_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_as_2281_, lean_object* v_sz_2282_, lean_object* v_i_2283_, lean_object* v_b_2284_){
_start:
{
size_t v_sz_boxed_2285_; size_t v_i_boxed_2286_; lean_object* v_res_2287_; 
v_sz_boxed_2285_ = lean_unbox_usize(v_sz_2282_);
lean_dec(v_sz_2282_);
v_i_boxed_2286_ = lean_unbox_usize(v_i_2283_);
lean_dec(v_i_2283_);
v_res_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2280_, v_as_2281_, v_sz_boxed_2285_, v_i_boxed_2286_, v_b_2284_);
lean_dec_ref(v_as_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2288_, lean_object* v_k_2289_, lean_object* v_result_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2288_, v_k_2289_);
if (lean_obj_tag(v___x_2291_) == 0)
{
return v_result_2290_;
}
else
{
lean_object* v_val_2292_; lean_object* v___x_2293_; 
v_val_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2292_, v_result_2290_);
lean_dec(v_val_2292_);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2294_, lean_object* v_k_2295_, lean_object* v_result_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2294_, v_k_2295_, v_result_2296_);
lean_dec(v_k_2295_);
lean_dec_ref(v_d_2294_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2298_, lean_object* v_d_2299_, lean_object* v_k_2300_, lean_object* v_result_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2299_, v_k_2300_, v_result_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2303_, lean_object* v_d_2304_, lean_object* v_k_2305_, lean_object* v_result_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2303_, v_d_2304_, v_k_2305_, v_result_2306_);
lean_dec(v_k_2305_);
lean_dec_ref(v_d_2304_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(lean_object* v_e_2308_, lean_object* v_result_2309_, lean_object* v_d_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2308_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2334_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2334_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2334_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_fst_2321_; lean_object* v_snd_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2333_; 
v_fst_2321_ = lean_ctor_get(v_a_2317_, 0);
v_snd_2322_ = lean_ctor_get(v_a_2317_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2317_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2324_ = v_a_2317_;
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snd_2322_);
lean_inc(v_fst_2321_);
lean_dec(v_a_2317_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2310_, v_fst_2321_, v_result_2309_);
lean_dec(v_fst_2321_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2326_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_snd_2322_);
v___x_2328_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2328_);
v___x_2330_ = v___x_2319_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_result_2309_);
v_a_2335_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2316_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2316_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0___boxed(lean_object* v_e_2343_, lean_object* v_result_2344_, lean_object* v_d_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2343_, v_result_2344_, v_d_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v_d_2345_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2352_, lean_object* v_e_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___y_2360_; lean_object* v___x_2377_; uint8_t v_transparency_2378_; lean_object* v_result_2379_; uint8_t v___x_2380_; uint8_t v___x_2381_; 
v___x_2377_ = l_Lean_Meta_Context_config(v_a_2354_);
v_transparency_2378_ = lean_ctor_get_uint8(v___x_2377_, 9);
lean_dec_ref(v___x_2377_);
v_result_2379_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2352_);
v___x_2380_ = 2;
v___x_2381_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2378_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v_keyedConfig_2382_; uint8_t v_trackZetaDelta_2383_; lean_object* v_zetaDeltaSet_2384_; lean_object* v_lctx_2385_; lean_object* v_localInstances_2386_; lean_object* v_defEqCtx_x3f_2387_; lean_object* v_synthPendingDepth_2388_; lean_object* v_customCanUnfoldPredicate_x3f_2389_; uint8_t v_univApprox_2390_; uint8_t v_inTypeClassResolution_2391_; uint8_t v_cacheInferType_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_keyedConfig_2382_ = lean_ctor_get(v_a_2354_, 0);
v_trackZetaDelta_2383_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*7);
v_zetaDeltaSet_2384_ = lean_ctor_get(v_a_2354_, 1);
v_lctx_2385_ = lean_ctor_get(v_a_2354_, 2);
v_localInstances_2386_ = lean_ctor_get(v_a_2354_, 3);
v_defEqCtx_x3f_2387_ = lean_ctor_get(v_a_2354_, 4);
v_synthPendingDepth_2388_ = lean_ctor_get(v_a_2354_, 5);
v_customCanUnfoldPredicate_x3f_2389_ = lean_ctor_get(v_a_2354_, 6);
v_univApprox_2390_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2391_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*7 + 2);
v_cacheInferType_2392_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2382_);
v___x_2393_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2380_, v_keyedConfig_2382_);
lean_inc(v_customCanUnfoldPredicate_x3f_2389_);
lean_inc(v_synthPendingDepth_2388_);
lean_inc(v_defEqCtx_x3f_2387_);
lean_inc_ref(v_localInstances_2386_);
lean_inc_ref(v_lctx_2385_);
lean_inc(v_zetaDeltaSet_2384_);
v___x_2394_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v_zetaDeltaSet_2384_);
lean_ctor_set(v___x_2394_, 2, v_lctx_2385_);
lean_ctor_set(v___x_2394_, 3, v_localInstances_2386_);
lean_ctor_set(v___x_2394_, 4, v_defEqCtx_x3f_2387_);
lean_ctor_set(v___x_2394_, 5, v_synthPendingDepth_2388_);
lean_ctor_set(v___x_2394_, 6, v_customCanUnfoldPredicate_x3f_2389_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7, v_trackZetaDelta_2383_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7 + 1, v_univApprox_2390_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2391_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*7 + 3, v_cacheInferType_2392_);
v___x_2395_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2353_, v_result_2379_, v_d_2352_, v___x_2394_, v_a_2355_, v_a_2356_, v_a_2357_);
lean_dec_ref_known(v___x_2394_, 7);
v___y_2360_ = v___x_2395_;
goto v___jp_2359_;
}
else
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2353_, v_result_2379_, v_d_2352_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
v___y_2360_ = v___x_2396_;
goto v___jp_2359_;
}
v___jp_2359_:
{
if (lean_obj_tag(v___y_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v___y_2360_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___y_2360_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___y_2360_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___y_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___y_2360_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___y_2360_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___y_2360_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___y_2360_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2397_, lean_object* v_e_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2397_, v_e_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec_ref(v_d_2397_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2405_, lean_object* v_d_2406_, lean_object* v_e_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2406_, v_e_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_d_2415_, lean_object* v_e_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2414_, v_d_2415_, v_e_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec_ref(v_d_2415_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2423_, lean_object* v_todo_2424_, lean_object* v_as_2425_, size_t v_i_2426_, size_t v_stop_2427_, lean_object* v_b_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_usize_dec_eq(v_i_2426_, v_stop_2427_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v_fst_2436_; lean_object* v_snd_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2435_ = lean_array_uget_borrowed(v_as_2425_, v_i_2426_);
v_fst_2436_ = lean_ctor_get(v___x_2435_, 0);
v_snd_2437_ = lean_ctor_get(v___x_2435_, 1);
v___x_2438_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2436_);
v___x_2439_ = lean_nat_add(v_n_2423_, v___x_2438_);
lean_dec(v___x_2438_);
lean_inc(v_snd_2437_);
lean_inc_ref(v_todo_2424_);
v___x_2440_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2439_, v_todo_2424_, v_snd_2437_, v_b_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; size_t v___x_2442_; size_t v___x_2443_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2426_, v___x_2442_);
v_i_2426_ = v___x_2443_;
v_b_2428_ = v_a_2441_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2424_);
return v___x_2440_;
}
}
else
{
lean_object* v___x_2445_; 
lean_dec_ref(v_todo_2424_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_b_2428_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2446_, lean_object* v_todo_2447_, lean_object* v_c_2448_, lean_object* v_result_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v_a_2464_; lean_object* v___y_2477_; lean_object* v_zero_2480_; uint8_t v_isZero_2481_; 
v_zero_2480_ = lean_unsigned_to_nat(0u);
v_isZero_2481_ = lean_nat_dec_eq(v_skip_2446_, v_zero_2480_);
if (v_isZero_2481_ == 1)
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
lean_dec(v_skip_2446_);
v___x_2482_ = lean_array_get_size(v_todo_2447_);
v___x_2483_ = lean_nat_dec_eq(v___x_2482_, v_zero_2480_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___y_2488_; 
v___x_2484_ = l_Lean_instInhabitedExpr;
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
if (lean_obj_tag(v_c_2448_) == 0)
{
lean_object* v_key_2528_; lean_object* v_child_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2539_; 
v_key_2528_ = lean_ctor_get(v_c_2448_, 0);
v_child_2529_ = lean_ctor_get(v_c_2448_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_c_2448_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2531_ = v_c_2448_;
v_isShared_2532_ = v_isSharedCheck_2539_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_child_2529_);
lean_inc(v_key_2528_);
lean_dec(v_c_2448_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2539_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_key_2528_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_child_2529_);
v___x_2534_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_unsigned_to_nat(1u);
v___x_2536_ = lean_mk_empty_array_with_capacity(v___x_2535_);
v___x_2537_ = lean_array_push(v___x_2536_, v___x_2534_);
v___y_2488_ = v___x_2537_;
goto v___jp_2487_;
}
}
}
else
{
lean_object* v_children_2540_; 
v_children_2540_ = lean_ctor_get(v_c_2448_, 1);
lean_inc_ref(v_children_2540_);
lean_dec_ref_known(v_c_2448_, 2);
v___y_2488_ = v_children_2540_;
goto v___jp_2487_;
}
v___jp_2487_:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = lean_array_get_size(v___y_2488_);
v___x_2490_ = lean_nat_dec_eq(v___x_2489_, v_zero_2480_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v_e_2493_; lean_object* v_todo_2494_; lean_object* v___x_2495_; 
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_sub(v___x_2482_, v___x_2491_);
v_e_2493_ = lean_array_get(v___x_2484_, v_todo_2447_, v___x_2492_);
lean_dec(v___x_2492_);
v_todo_2494_ = lean_array_pop(v_todo_2447_);
v___x_2495_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2493_, v___x_2490_, v___x_2490_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2518_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2518_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2518_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_fst_2500_; 
v_fst_2500_ = lean_ctor_get(v_a_2496_, 0);
lean_inc(v_fst_2500_);
if (lean_obj_tag(v_fst_2500_) == 0)
{
uint8_t v___x_2501_; 
lean_dec(v_a_2496_);
v___x_2501_ = lean_nat_dec_lt(v_zero_2480_, v___x_2489_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2503_; 
lean_dec_ref(v_todo_2494_);
lean_dec_ref(v___y_2488_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v_result_2449_);
v___x_2503_ = v___x_2498_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_result_2449_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
else
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
lean_del_object(v___x_2498_);
v___x_2505_ = ((size_t)0ULL);
v___x_2506_ = lean_usize_of_nat(v___x_2489_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2494_, v___y_2488_, v___x_2505_, v___x_2506_, v_result_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec_ref(v___y_2488_);
return v___x_2507_;
}
}
else
{
lean_object* v_snd_2508_; lean_object* v___x_2509_; lean_object* v_fst_2510_; lean_object* v_snd_2511_; uint8_t v___x_2512_; 
v_snd_2508_ = lean_ctor_get(v_a_2496_, 1);
lean_inc(v_snd_2508_);
lean_dec(v_a_2496_);
v___x_2509_ = lean_array_get_borrowed(v___x_2486_, v___y_2488_, v_zero_2480_);
v_fst_2510_ = lean_ctor_get(v___x_2509_, 0);
v_snd_2511_ = lean_ctor_get(v___x_2509_, 1);
v___x_2512_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2510_, v___x_2485_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2514_; 
lean_inc_ref(v_result_2449_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v_result_2449_);
v___x_2514_ = v___x_2498_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_result_2449_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
v___y_2456_ = v_todo_2494_;
v___y_2457_ = v_snd_2508_;
v___y_2458_ = v___x_2489_;
v___y_2459_ = v_fst_2500_;
v___y_2460_ = v_zero_2480_;
v___y_2461_ = v___x_2491_;
v___y_2462_ = v___y_2488_;
v___y_2463_ = v___x_2514_;
v_a_2464_ = v_result_2449_;
goto v___jp_2455_;
}
}
else
{
lean_object* v___x_2516_; 
lean_del_object(v___x_2498_);
lean_inc(v_snd_2511_);
lean_inc_ref(v_todo_2494_);
v___x_2516_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2480_, v_todo_2494_, v_snd_2511_, v_result_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
v___y_2456_ = v_todo_2494_;
v___y_2457_ = v_snd_2508_;
v___y_2458_ = v___x_2489_;
v___y_2459_ = v_fst_2500_;
v___y_2460_ = v_zero_2480_;
v___y_2461_ = v___x_2491_;
v___y_2462_ = v___y_2488_;
v___y_2463_ = v___x_2516_;
v_a_2464_ = v_a_2517_;
goto v___jp_2455_;
}
else
{
lean_dec(v_snd_2508_);
lean_dec(v_fst_2500_);
lean_dec_ref(v_todo_2494_);
lean_dec_ref(v___y_2488_);
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v_todo_2494_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_result_2449_);
v_a_2519_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2495_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2495_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v___x_2527_; 
lean_dec_ref(v___y_2488_);
lean_dec_ref(v_todo_2447_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_result_2449_);
return v___x_2527_;
}
}
}
else
{
lean_dec_ref(v_todo_2447_);
if (lean_obj_tag(v_c_2448_) == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref_known(v_c_2448_, 2);
v___x_2541_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_2477_ = v___x_2541_;
goto v___jp_2476_;
}
else
{
lean_object* v_vs_2542_; 
v_vs_2542_ = lean_ctor_get(v_c_2448_, 0);
lean_inc_ref(v_vs_2542_);
lean_dec_ref_known(v_c_2448_, 2);
v___y_2477_ = v_vs_2542_;
goto v___jp_2476_;
}
}
}
else
{
lean_object* v_one_2543_; lean_object* v_n_2544_; 
v_one_2543_ = lean_unsigned_to_nat(1u);
v_n_2544_ = lean_nat_sub(v_skip_2446_, v_one_2543_);
lean_dec(v_skip_2446_);
if (lean_obj_tag(v_c_2448_) == 0)
{
lean_object* v_key_2545_; lean_object* v_child_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_key_2545_ = lean_ctor_get(v_c_2448_, 0);
lean_inc(v_key_2545_);
v_child_2546_ = lean_ctor_get(v_c_2448_, 1);
lean_inc_ref(v_child_2546_);
lean_dec_ref_known(v_c_2448_, 2);
v___x_2547_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2545_);
lean_dec(v_key_2545_);
v___x_2548_ = lean_nat_add(v_n_2544_, v___x_2547_);
lean_dec(v___x_2547_);
lean_dec(v_n_2544_);
v_skip_2446_ = v___x_2548_;
v_c_2448_ = v_child_2546_;
goto _start;
}
else
{
lean_object* v_children_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v_children_2550_ = lean_ctor_get(v_c_2448_, 1);
lean_inc_ref(v_children_2550_);
lean_dec_ref_known(v_c_2448_, 2);
v___x_2551_ = lean_array_get_size(v_children_2550_);
v___x_2552_ = lean_nat_dec_eq(v___x_2551_, v_zero_2480_);
if (v___x_2552_ == 0)
{
uint8_t v___x_2553_; 
v___x_2553_ = lean_nat_dec_lt(v_zero_2480_, v___x_2551_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref(v_children_2550_);
lean_dec(v_n_2544_);
lean_dec_ref(v_todo_2447_);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_result_2449_);
return v___x_2554_;
}
else
{
size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = lean_usize_of_nat(v___x_2551_);
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2544_, v_todo_2447_, v_children_2550_, v___x_2555_, v___x_2556_, v_result_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec_ref(v_children_2550_);
lean_dec(v_n_2544_);
return v___x_2557_;
}
}
else
{
lean_object* v___x_2558_; 
lean_dec_ref(v_children_2550_);
lean_dec(v_n_2544_);
lean_dec_ref(v_todo_2447_);
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v_result_2449_);
return v___x_2558_;
}
}
}
v___jp_2455_:
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_lt(v___y_2460_, v___y_2458_);
if (v___x_2465_ == 0)
{
lean_dec_ref(v_a_2464_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v___y_2463_;
}
else
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_nat_sub(v___y_2458_, v___y_2461_);
lean_dec(v___y_2458_);
v___x_2467_ = lean_nat_dec_le(v___y_2460_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_dec(v___x_2466_);
lean_dec_ref(v_a_2464_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v___y_2463_;
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2468_ = lean_mk_empty_array_with_capacity(v___y_2460_);
lean_inc_ref(v___x_2468_);
v___x_2469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___y_2459_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
lean_inc(v___y_2460_);
v___x_2471_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v___y_2462_, v___x_2470_, v___y_2460_, v___x_2466_);
lean_dec_ref_known(v___x_2470_, 2);
lean_dec_ref(v___y_2462_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_dec_ref(v_a_2464_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v___y_2463_;
}
else
{
lean_object* v_val_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; 
lean_dec_ref(v___y_2463_);
v_val_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_val_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v_snd_2473_ = lean_ctor_get(v_val_2472_, 1);
lean_inc(v_snd_2473_);
lean_dec(v_val_2472_);
v___x_2474_ = l_Array_append___redArg(v___y_2456_, v___y_2457_);
lean_dec_ref(v___y_2457_);
v_skip_2446_ = v___y_2460_;
v_todo_2447_ = v___x_2474_;
v_c_2448_ = v_snd_2473_;
v_result_2449_ = v_a_2464_;
goto _start;
}
}
}
}
v___jp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = l_Array_append___redArg(v_result_2449_, v___y_2477_);
lean_dec_ref(v___y_2477_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2559_, lean_object* v_as_2560_, size_t v_i_2561_, size_t v_stop_2562_, lean_object* v_b_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_usize_dec_eq(v_i_2561_, v_stop_2562_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2570_ = lean_array_uget_borrowed(v_as_2560_, v_i_2561_);
v_fst_2571_ = lean_ctor_get(v___x_2570_, 0);
v_snd_2572_ = lean_ctor_get(v___x_2570_, 1);
v___x_2573_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2571_);
lean_inc(v_snd_2572_);
lean_inc_ref(v_todo_2559_);
v___x_2574_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2573_, v_todo_2559_, v_snd_2572_, v_b_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; size_t v___x_2576_; size_t v___x_2577_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = ((size_t)1ULL);
v___x_2577_ = lean_usize_add(v_i_2561_, v___x_2576_);
v_i_2561_ = v___x_2577_;
v_b_2563_ = v_a_2575_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2559_);
return v___x_2574_;
}
}
else
{
lean_object* v___x_2579_; 
lean_dec_ref(v_todo_2559_);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_b_2563_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2580_, lean_object* v_as_2581_, lean_object* v_i_2582_, lean_object* v_stop_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
size_t v_i_boxed_2590_; size_t v_stop_boxed_2591_; lean_object* v_res_2592_; 
v_i_boxed_2590_ = lean_unbox_usize(v_i_2582_);
lean_dec(v_i_2582_);
v_stop_boxed_2591_ = lean_unbox_usize(v_stop_2583_);
lean_dec(v_stop_2583_);
v_res_2592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2580_, v_as_2581_, v_i_boxed_2590_, v_stop_boxed_2591_, v_b_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v_as_2581_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2593_, lean_object* v_todo_2594_, lean_object* v_as_2595_, lean_object* v_i_2596_, lean_object* v_stop_2597_, lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
size_t v_i_boxed_2604_; size_t v_stop_boxed_2605_; lean_object* v_res_2606_; 
v_i_boxed_2604_ = lean_unbox_usize(v_i_2596_);
lean_dec(v_i_2596_);
v_stop_boxed_2605_ = lean_unbox_usize(v_stop_2597_);
lean_dec(v_stop_2597_);
v_res_2606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2593_, v_todo_2594_, v_as_2595_, v_i_boxed_2604_, v_stop_boxed_2605_, v_b_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v_as_2595_);
lean_dec(v_n_2593_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2607_, lean_object* v_todo_2608_, lean_object* v_c_2609_, lean_object* v_result_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2607_, v_todo_2608_, v_c_2609_, v_result_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2617_, lean_object* v_skip_2618_, lean_object* v_todo_2619_, lean_object* v_c_2620_, lean_object* v_result_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2618_, v_todo_2619_, v_c_2620_, v_result_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2628_, lean_object* v_skip_2629_, lean_object* v_todo_2630_, lean_object* v_c_2631_, lean_object* v_result_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2628_, v_skip_2629_, v_todo_2630_, v_c_2631_, v_result_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2639_, lean_object* v_todo_2640_, lean_object* v_as_2641_, size_t v_i_2642_, size_t v_stop_2643_, lean_object* v_b_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2640_, v_as_2641_, v_i_2642_, v_stop_2643_, v_b_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2651_, lean_object* v_todo_2652_, lean_object* v_as_2653_, lean_object* v_i_2654_, lean_object* v_stop_2655_, lean_object* v_b_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
size_t v_i_boxed_2662_; size_t v_stop_boxed_2663_; lean_object* v_res_2664_; 
v_i_boxed_2662_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_stop_boxed_2663_ = lean_unbox_usize(v_stop_2655_);
lean_dec(v_stop_2655_);
v_res_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2651_, v_todo_2652_, v_as_2653_, v_i_boxed_2662_, v_stop_boxed_2663_, v_b_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec_ref(v_as_2653_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2665_, lean_object* v_n_2666_, lean_object* v_todo_2667_, lean_object* v_as_2668_, size_t v_i_2669_, size_t v_stop_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2666_, v_todo_2667_, v_as_2668_, v_i_2669_, v_stop_2670_, v_b_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2678_, lean_object* v_n_2679_, lean_object* v_todo_2680_, lean_object* v_as_2681_, lean_object* v_i_2682_, lean_object* v_stop_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
size_t v_i_boxed_2690_; size_t v_stop_boxed_2691_; lean_object* v_res_2692_; 
v_i_boxed_2690_ = lean_unbox_usize(v_i_2682_);
lean_dec(v_i_2682_);
v_stop_boxed_2691_ = lean_unbox_usize(v_stop_2683_);
lean_dec(v_stop_2683_);
v_res_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2678_, v_n_2679_, v_todo_2680_, v_as_2681_, v_i_boxed_2690_, v_stop_boxed_2691_, v_b_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v_as_2681_);
lean_dec(v_n_2679_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2693_, lean_object* v_k_2694_, lean_object* v_c_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2694_);
v___x_2702_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2703_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2701_, v___x_2702_, v_c_2695_, v_result_2693_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2704_, lean_object* v_k_2705_, lean_object* v_c_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2704_, v_k_2705_, v_c_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_k_2705_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2713_, lean_object* v_keys_2714_, lean_object* v_vals_2715_, lean_object* v_i_2716_, lean_object* v_acc_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = lean_array_get_size(v_keys_2714_);
v___x_2724_ = lean_nat_dec_lt(v_i_2716_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
lean_dec(v_i_2716_);
lean_dec_ref(v_f_2713_);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v_acc_2717_);
return v___x_2725_;
}
else
{
lean_object* v_k_2726_; lean_object* v_v_2727_; lean_object* v___x_2728_; 
v_k_2726_ = lean_array_fget_borrowed(v_keys_2714_, v_i_2716_);
v_v_2727_ = lean_array_fget_borrowed(v_vals_2715_, v_i_2716_);
lean_inc_ref(v_f_2713_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v_v_2727_);
lean_inc(v_k_2726_);
v___x_2728_ = lean_apply_8(v_f_2713_, v_acc_2717_, v_k_2726_, v_v_2727_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, lean_box(0));
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = lean_unsigned_to_nat(1u);
v___x_2731_ = lean_nat_add(v_i_2716_, v___x_2730_);
lean_dec(v_i_2716_);
v_i_2716_ = v___x_2731_;
v_acc_2717_ = v_a_2729_;
goto _start;
}
else
{
lean_dec(v_i_2716_);
lean_dec_ref(v_f_2713_);
return v___x_2728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2733_, lean_object* v_keys_2734_, lean_object* v_vals_2735_, lean_object* v_i_2736_, lean_object* v_acc_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2733_, v_keys_2734_, v_vals_2735_, v_i_2736_, v_acc_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v_vals_2735_);
lean_dec_ref(v_keys_2734_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2744_, lean_object* v_as_2745_, size_t v_i_2746_, size_t v_stop_2747_, lean_object* v_b_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_a_2755_; lean_object* v___y_2760_; uint8_t v___x_2762_; 
v___x_2762_ = lean_usize_dec_eq(v_i_2746_, v_stop_2747_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_array_uget_borrowed(v_as_2745_, v_i_2746_);
switch(lean_obj_tag(v___x_2763_))
{
case 0:
{
lean_object* v_key_2764_; lean_object* v_val_2765_; lean_object* v___x_2766_; 
v_key_2764_ = lean_ctor_get(v___x_2763_, 0);
v_val_2765_ = lean_ctor_get(v___x_2763_, 1);
lean_inc_ref(v_f_2744_);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v_val_2765_);
lean_inc(v_key_2764_);
v___x_2766_ = lean_apply_8(v_f_2744_, v_b_2748_, v_key_2764_, v_val_2765_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, lean_box(0));
v___y_2760_ = v___x_2766_;
goto v___jp_2759_;
}
case 1:
{
lean_object* v_node_2767_; lean_object* v___x_2768_; 
v_node_2767_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_node_2767_);
lean_inc_ref(v_f_2744_);
v___x_2768_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2744_, v_node_2767_, v_b_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
v___y_2760_ = v___x_2768_;
goto v___jp_2759_;
}
default: 
{
v_a_2755_ = v_b_2748_;
goto v___jp_2754_;
}
}
}
else
{
lean_object* v___x_2769_; 
lean_dec_ref(v_f_2744_);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_b_2748_);
return v___x_2769_;
}
v___jp_2754_:
{
size_t v___x_2756_; size_t v___x_2757_; 
v___x_2756_ = ((size_t)1ULL);
v___x_2757_ = lean_usize_add(v_i_2746_, v___x_2756_);
v_i_2746_ = v___x_2757_;
v_b_2748_ = v_a_2755_;
goto _start;
}
v___jp_2759_:
{
if (lean_obj_tag(v___y_2760_) == 0)
{
lean_object* v_a_2761_; 
v_a_2761_ = lean_ctor_get(v___y_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___y_2760_, 1);
v_a_2755_ = v_a_2761_;
goto v___jp_2754_;
}
else
{
lean_dec_ref(v_f_2744_);
return v___y_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2770_, lean_object* v_x_2771_, lean_object* v_x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
if (lean_obj_tag(v_x_2771_) == 0)
{
lean_object* v_es_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2791_; 
v_es_2778_ = lean_ctor_get(v_x_2771_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_x_2771_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2780_ = v_x_2771_;
v_isShared_2781_ = v_isSharedCheck_2791_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_es_2778_);
lean_dec(v_x_2771_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2791_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = lean_array_get_size(v_es_2778_);
v___x_2784_ = lean_nat_dec_lt(v___x_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2786_; 
lean_dec_ref(v_es_2778_);
lean_dec_ref(v_f_2770_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_x_2772_);
v___x_2786_ = v___x_2780_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_x_2772_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
else
{
size_t v___x_2788_; size_t v___x_2789_; lean_object* v___x_2790_; 
lean_del_object(v___x_2780_);
v___x_2788_ = ((size_t)0ULL);
v___x_2789_ = lean_usize_of_nat(v___x_2783_);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2770_, v_es_2778_, v___x_2788_, v___x_2789_, v_x_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec_ref(v_es_2778_);
return v___x_2790_;
}
}
}
else
{
lean_object* v_ks_2792_; lean_object* v_vs_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_ks_2792_ = lean_ctor_get(v_x_2771_, 0);
lean_inc_ref(v_ks_2792_);
v_vs_2793_ = lean_ctor_get(v_x_2771_, 1);
lean_inc_ref(v_vs_2793_);
lean_dec_ref_known(v_x_2771_, 2);
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2770_, v_ks_2792_, v_vs_2793_, v___x_2794_, v_x_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec_ref(v_vs_2793_);
lean_dec_ref(v_ks_2792_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2796_, lean_object* v_x_2797_, lean_object* v_x_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2796_, v_x_2797_, v_x_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2805_, lean_object* v_as_2806_, lean_object* v_i_2807_, lean_object* v_stop_2808_, lean_object* v_b_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
size_t v_i_boxed_2815_; size_t v_stop_boxed_2816_; lean_object* v_res_2817_; 
v_i_boxed_2815_ = lean_unbox_usize(v_i_2807_);
lean_dec(v_i_2807_);
v_stop_boxed_2816_ = lean_unbox_usize(v_stop_2808_);
lean_dec(v_stop_2808_);
v_res_2817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2805_, v_as_2806_, v_i_boxed_2815_, v_stop_boxed_2816_, v_b_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec_ref(v_as_2806_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(lean_object* v_e_2818_, uint8_t v___x_2819_, lean_object* v___f_2820_, lean_object* v_d_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
uint8_t v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = 0;
v___x_2828_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2818_, v___x_2827_, v___x_2819_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2845_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2845_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2845_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_fst_2833_; 
v_fst_2833_ = lean_ctor_get(v_a_2829_, 0);
lean_inc(v_fst_2833_);
if (lean_obj_tag(v_fst_2833_) == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_del_object(v___x_2831_);
lean_dec(v_a_2829_);
v___x_2834_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_2835_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2820_, v_d_2821_, v___x_2834_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2835_;
}
else
{
lean_object* v_snd_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
lean_dec_ref(v___f_2820_);
v_snd_2836_ = lean_ctor_get(v_a_2829_, 1);
lean_inc(v_snd_2836_);
lean_dec(v_a_2829_);
v___x_2837_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2821_);
v___x_2838_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2821_, v_fst_2833_);
lean_dec(v_fst_2833_);
lean_dec_ref(v_d_2821_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2840_; 
lean_dec(v_snd_2836_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2837_);
v___x_2840_ = v___x_2831_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2837_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
else
{
lean_object* v_val_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_del_object(v___x_2831_);
v_val_2842_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2843_, v_snd_2836_, v_val_2842_, v___x_2837_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v_d_2821_);
lean_dec_ref(v___f_2820_);
v_a_2846_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2828_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2828_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1___boxed(lean_object* v_e_2854_, lean_object* v___x_2855_, lean_object* v___f_2856_, lean_object* v_d_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v___x_1524__boxed_2863_; lean_object* v_res_2864_; 
v___x_1524__boxed_2863_ = lean_unbox(v___x_2855_);
v_res_2864_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2854_, v___x_1524__boxed_2863_, v___f_2856_, v_d_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2866_, lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v___y_2874_; lean_object* v___x_2891_; uint8_t v_transparency_2892_; lean_object* v___f_2893_; uint8_t v___x_2894_; uint8_t v___x_2895_; uint8_t v___x_2896_; 
v___x_2891_ = l_Lean_Meta_Context_config(v_a_2868_);
v_transparency_2892_ = lean_ctor_get_uint8(v___x_2891_, 9);
lean_dec_ref(v___x_2891_);
v___f_2893_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2894_ = 1;
v___x_2895_ = 2;
v___x_2896_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2892_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_object* v_keyedConfig_2897_; uint8_t v_trackZetaDelta_2898_; lean_object* v_zetaDeltaSet_2899_; lean_object* v_lctx_2900_; lean_object* v_localInstances_2901_; lean_object* v_defEqCtx_x3f_2902_; lean_object* v_synthPendingDepth_2903_; lean_object* v_customCanUnfoldPredicate_x3f_2904_; uint8_t v_univApprox_2905_; uint8_t v_inTypeClassResolution_2906_; uint8_t v_cacheInferType_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_keyedConfig_2897_ = lean_ctor_get(v_a_2868_, 0);
v_trackZetaDelta_2898_ = lean_ctor_get_uint8(v_a_2868_, sizeof(void*)*7);
v_zetaDeltaSet_2899_ = lean_ctor_get(v_a_2868_, 1);
v_lctx_2900_ = lean_ctor_get(v_a_2868_, 2);
v_localInstances_2901_ = lean_ctor_get(v_a_2868_, 3);
v_defEqCtx_x3f_2902_ = lean_ctor_get(v_a_2868_, 4);
v_synthPendingDepth_2903_ = lean_ctor_get(v_a_2868_, 5);
v_customCanUnfoldPredicate_x3f_2904_ = lean_ctor_get(v_a_2868_, 6);
v_univApprox_2905_ = lean_ctor_get_uint8(v_a_2868_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2906_ = lean_ctor_get_uint8(v_a_2868_, sizeof(void*)*7 + 2);
v_cacheInferType_2907_ = lean_ctor_get_uint8(v_a_2868_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2897_);
v___x_2908_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2895_, v_keyedConfig_2897_);
lean_inc(v_customCanUnfoldPredicate_x3f_2904_);
lean_inc(v_synthPendingDepth_2903_);
lean_inc(v_defEqCtx_x3f_2902_);
lean_inc_ref(v_localInstances_2901_);
lean_inc_ref(v_lctx_2900_);
lean_inc(v_zetaDeltaSet_2899_);
v___x_2909_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v_zetaDeltaSet_2899_);
lean_ctor_set(v___x_2909_, 2, v_lctx_2900_);
lean_ctor_set(v___x_2909_, 3, v_localInstances_2901_);
lean_ctor_set(v___x_2909_, 4, v_defEqCtx_x3f_2902_);
lean_ctor_set(v___x_2909_, 5, v_synthPendingDepth_2903_);
lean_ctor_set(v___x_2909_, 6, v_customCanUnfoldPredicate_x3f_2904_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*7, v_trackZetaDelta_2898_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*7 + 1, v_univApprox_2905_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2906_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*7 + 3, v_cacheInferType_2907_);
v___x_2910_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2867_, v___x_2894_, v___f_2893_, v_d_2866_, v___x_2909_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec_ref_known(v___x_2909_, 7);
v___y_2874_ = v___x_2910_;
goto v___jp_2873_;
}
else
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_2867_, v___x_2894_, v___f_2893_, v_d_2866_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
v___y_2874_ = v___x_2911_;
goto v___jp_2873_;
}
v___jp_2873_:
{
if (lean_obj_tag(v___y_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2875_ = lean_ctor_get(v___y_2874_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___y_2874_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___y_2874_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___y_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_a_2883_ = lean_ctor_get(v___y_2874_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___y_2874_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___y_2874_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___y_2874_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_2912_, lean_object* v_e_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2912_, v_e_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_2920_, lean_object* v_d_2921_, lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2921_, v_e_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_2929_, lean_object* v_d_2930_, lean_object* v_e_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_2929_, v_d_2930_, v_e_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_2938_, lean_object* v_f_2939_, lean_object* v_init_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2939_, v_map_2938_, v_init_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_2947_, lean_object* v_f_2948_, lean_object* v_init_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_2947_, v_f_2948_, v_init_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_2956_, lean_object* v_00_u03b2_2957_, lean_object* v_map_2958_, lean_object* v_f_2959_, lean_object* v_init_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2959_, v_map_2958_, v_init_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_2967_, lean_object* v_00_u03b2_2968_, lean_object* v_map_2969_, lean_object* v_f_2970_, lean_object* v_init_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_2967_, v_00_u03b2_2968_, v_map_2969_, v_f_2970_, v_init_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_2978_, lean_object* v_00_u03b1_2979_, lean_object* v_00_u03b2_2980_, lean_object* v_f_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2981_, v_x_2982_, v_x_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2990_, lean_object* v_00_u03b1_2991_, lean_object* v_00_u03b2_2992_, lean_object* v_f_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_2990_, v_00_u03b1_2991_, v_00_u03b2_2992_, v_f_2993_, v_x_2994_, v_x_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3002_, lean_object* v_00_u03b2_3003_, lean_object* v_00_u03c3_3004_, lean_object* v_f_3005_, lean_object* v_as_3006_, size_t v_i_3007_, size_t v_stop_3008_, lean_object* v_b_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3005_, v_as_3006_, v_i_3007_, v_stop_3008_, v_b_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3016_, lean_object* v_00_u03b2_3017_, lean_object* v_00_u03c3_3018_, lean_object* v_f_3019_, lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_stop_3022_, lean_object* v_b_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
size_t v_i_boxed_3029_; size_t v_stop_boxed_3030_; lean_object* v_res_3031_; 
v_i_boxed_3029_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_stop_boxed_3030_ = lean_unbox_usize(v_stop_3022_);
lean_dec(v_stop_3022_);
v_res_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_3016_, v_00_u03b2_3017_, v_00_u03c3_3018_, v_f_3019_, v_as_3020_, v_i_boxed_3029_, v_stop_boxed_3030_, v_b_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec_ref(v_as_3020_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_3032_, lean_object* v_00_u03b1_3033_, lean_object* v_00_u03b2_3034_, lean_object* v_f_3035_, lean_object* v_keys_3036_, lean_object* v_vals_3037_, lean_object* v_heq_3038_, lean_object* v_i_3039_, lean_object* v_acc_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3035_, v_keys_3036_, v_vals_3037_, v_i_3039_, v_acc_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_3047_, lean_object* v_00_u03b1_3048_, lean_object* v_00_u03b2_3049_, lean_object* v_f_3050_, lean_object* v_keys_3051_, lean_object* v_vals_3052_, lean_object* v_heq_3053_, lean_object* v_i_3054_, lean_object* v_acc_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_3047_, v_00_u03b1_3048_, v_00_u03b2_3049_, v_f_3050_, v_keys_3051_, v_vals_3052_, v_heq_3053_, v_i_3054_, v_acc_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v_vals_3052_);
lean_dec_ref(v_keys_3051_);
return v_res_3061_;
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
