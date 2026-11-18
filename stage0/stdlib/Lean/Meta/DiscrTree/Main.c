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
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_209__boxed_1346_; lean_object* v_res_1347_; 
v_x_209__boxed_1346_ = lean_unbox_usize(v_x_1344_);
lean_dec(v_x_1344_);
v_res_1347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1343_, v_x_209__boxed_1346_, v_x_1345_);
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
lean_object* v___x_1363_; lean_object* v_result_1364_; lean_object* v_val_1366_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1363_ = lean_unsigned_to_nat(8u);
v_result_1364_ = lean_mk_empty_array_with_capacity(v___x_1363_);
v___x_1370_ = lean_box(0);
v___x_1371_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1362_, v___x_1370_);
if (lean_obj_tag(v___x_1371_) == 0)
{
return v_result_1364_;
}
else
{
lean_object* v_val_1372_; 
v_val_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v___x_1371_, 1);
switch(lean_obj_tag(v_val_1372_))
{
case 2:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_val_1372_);
v_val_1366_ = v___x_1373_;
goto v___jp_1365_;
}
case 3:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_val_1372_);
v_val_1366_ = v___x_1374_;
goto v___jp_1365_;
}
default: 
{
v_val_1366_ = v_val_1372_;
goto v___jp_1365_;
}
}
}
v___jp_1365_:
{
if (lean_obj_tag(v_val_1366_) == 0)
{
lean_object* v___x_1367_; 
lean_dec_ref_known(v_val_1366_, 2);
lean_dec_ref(v_result_1364_);
v___x_1367_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__1);
return v___x_1367_;
}
else
{
lean_object* v_vs_1368_; lean_object* v___x_1369_; 
v_vs_1368_ = lean_ctor_get(v_val_1366_, 0);
lean_inc_ref(v_vs_1368_);
lean_dec_ref_known(v_val_1366_, 2);
v___x_1369_ = l_Array_append___redArg(v_result_1364_, v_vs_1368_);
lean_dec_ref(v_vs_1368_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___boxed(lean_object* v_d_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1375_);
lean_dec_ref(v_d_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1377_, lean_object* v_d_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_1380_, lean_object* v_d_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(v_00_u03b1_1380_, v_d_1381_);
lean_dec_ref(v_d_1381_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1384_, v_x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1387_, v_x_1388_, v_x_1389_);
lean_dec(v_x_1389_);
lean_dec_ref(v_x_1388_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1391_, lean_object* v_x_1392_, size_t v_x_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1392_, v_x_1393_, v_x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
size_t v_x_322__boxed_1400_; lean_object* v_res_1401_; 
v_x_322__boxed_1400_ = lean_unbox_usize(v_x_1398_);
lean_dec(v_x_1398_);
v_res_1401_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1396_, v_x_1397_, v_x_322__boxed_1400_, v_x_1399_);
lean_dec(v_x_1399_);
lean_dec_ref(v_x_1397_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1402_, lean_object* v_keys_1403_, lean_object* v_vals_1404_, lean_object* v_heq_1405_, lean_object* v_i_1406_, lean_object* v_k_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1403_, v_vals_1404_, v_i_1406_, v_k_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1409_, lean_object* v_keys_1410_, lean_object* v_vals_1411_, lean_object* v_heq_1412_, lean_object* v_i_1413_, lean_object* v_k_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1409_, v_keys_1410_, v_vals_1411_, v_heq_1412_, v_i_1413_, v_k_1414_);
lean_dec(v_k_1414_);
lean_dec_ref(v_vals_1411_);
lean_dec_ref(v_keys_1410_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__1(lean_object* v_todo_1416_, lean_object* v_ks_1417_, lean_object* v_i_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = lean_array_get_size(v_ks_1417_);
v___x_1425_ = lean_nat_dec_lt(v_i_1418_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_i_1418_);
v___x_1426_ = lean_array_get_size(v_todo_1416_);
lean_dec_ref(v_todo_1416_);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_nat_dec_eq(v___x_1426_, v___x_1427_);
v___x_1429_ = lean_box(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = lean_array_get_size(v_todo_1416_);
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_nat_dec_eq(v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_e_1437_; lean_object* v_todo_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1434_ = l_Lean_instInhabitedExpr;
v___x_1435_ = lean_unsigned_to_nat(1u);
v___x_1436_ = lean_nat_sub(v___x_1431_, v___x_1435_);
v_e_1437_ = lean_array_get(v___x_1434_, v_todo_1416_, v___x_1436_);
lean_dec(v___x_1436_);
v_todo_1438_ = lean_array_pop(v_todo_1416_);
v___x_1439_ = lean_array_fget_borrowed(v_ks_1417_, v_i_1418_);
v___x_1440_ = lean_box(0);
v___x_1441_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1437_, v___x_1425_, v___x_1441_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1457_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1457_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1457_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v_fst_1447_; lean_object* v_snd_1448_; uint8_t v___x_1449_; 
v_fst_1447_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_fst_1447_);
v_snd_1448_ = lean_ctor_get(v_a_1443_, 1);
lean_inc(v_snd_1448_);
lean_dec(v_a_1443_);
v___x_1449_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_1439_, v_fst_1447_);
lean_dec(v_fst_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_dec(v_snd_1448_);
lean_dec_ref(v_todo_1438_);
lean_dec(v_i_1418_);
v___x_1450_ = lean_box(v___x_1449_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1450_);
v___x_1452_ = v___x_1445_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_del_object(v___x_1445_);
v___x_1454_ = l_Array_append___redArg(v_todo_1438_, v_snd_1448_);
lean_dec(v_snd_1448_);
v___x_1455_ = lean_nat_add(v_i_1418_, v___x_1435_);
lean_dec(v_i_1418_);
v_todo_1416_ = v___x_1454_;
v_i_1418_ = v___x_1455_;
goto _start;
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_todo_1438_);
lean_dec(v_i_1418_);
v_a_1458_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1442_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1442_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_e_1437_);
v___x_1466_ = lean_nat_add(v_i_1418_, v___x_1435_);
lean_dec(v_i_1418_);
v_todo_1416_ = v_todo_1438_;
v_i_1418_ = v___x_1466_;
goto _start;
}
}
else
{
uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec(v_i_1418_);
lean_dec_ref(v_todo_1416_);
v___x_1468_ = 0;
v___x_1469_ = lean_box(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__1___boxed(lean_object* v_todo_1471_, lean_object* v_ks_1472_, lean_object* v_i_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__1(v_todo_1471_, v_ks_1472_, v_i_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec_ref(v_ks_1472_);
return v_res_1479_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___lam__0(lean_object* v_a_1480_, lean_object* v_b_1481_){
_start:
{
lean_object* v_fst_1482_; lean_object* v_fst_1483_; uint8_t v___x_1484_; 
v_fst_1482_ = lean_ctor_get(v_a_1480_, 0);
v_fst_1483_ = lean_ctor_get(v_b_1481_, 0);
v___x_1484_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1482_, v_fst_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_a_1485_, lean_object* v_b_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___lam__0(v_a_1485_, v_b_1486_);
lean_dec_ref(v_b_1486_);
lean_dec_ref(v_a_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg(lean_object* v_as_1489_, lean_object* v_k_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_m_1495_; lean_object* v_a_1496_; uint8_t v___x_1497_; 
v___x_1493_ = lean_nat_add(v_x_1491_, v_x_1492_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v_m_1495_ = lean_nat_shiftr(v___x_1493_, v___x_1494_);
lean_dec(v___x_1493_);
v_a_1496_ = lean_array_fget_borrowed(v_as_1489_, v_m_1495_);
v___x_1497_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___lam__0(v_a_1496_, v_k_1490_);
if (v___x_1497_ == 0)
{
uint8_t v___x_1498_; 
lean_dec(v_x_1492_);
v___x_1498_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___lam__0(v_k_1490_, v_a_1496_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_m_1495_);
lean_dec(v_x_1491_);
lean_inc(v_a_1496_);
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_a_1496_);
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_nat_dec_eq(v_m_1495_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = lean_nat_sub(v_m_1495_, v___x_1494_);
lean_dec(v_m_1495_);
v___x_1503_ = lean_nat_dec_lt(v___x_1502_, v_x_1491_);
if (v___x_1503_ == 0)
{
v_x_1492_ = v___x_1502_;
goto _start;
}
else
{
lean_object* v___x_1505_; 
lean_dec(v___x_1502_);
lean_dec(v_x_1491_);
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_m_1495_);
lean_dec(v_x_1491_);
v___x_1506_ = lean_box(0);
return v___x_1506_;
}
}
}
else
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
lean_dec(v_x_1491_);
v___x_1507_ = lean_nat_add(v_m_1495_, v___x_1494_);
lean_dec(v_m_1495_);
v___x_1508_ = lean_nat_dec_le(v___x_1507_, v_x_1492_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
lean_dec(v___x_1507_);
lean_dec(v_x_1492_);
v___x_1509_ = lean_box(0);
return v___x_1509_;
}
else
{
v_x_1491_ = v___x_1507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg___boxed(lean_object* v_as_1511_, lean_object* v_k_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg(v_as_1511_, v_k_1512_, v_x_1513_, v_x_1514_);
lean_dec_ref(v_k_1512_);
lean_dec_ref(v_as_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_todo_1518_, lean_object* v_c_1519_, lean_object* v_result_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___y_1527_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v_val_1538_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v_val_1551_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v_result_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v_val_1597_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v_val_1605_; 
if (lean_obj_tag(v_c_1519_) == 3)
{
lean_object* v_keys_1619_; lean_object* v_i_1620_; lean_object* v_v_1621_; lean_object* v___x_1622_; 
v_keys_1619_ = lean_ctor_get(v_c_1519_, 0);
lean_inc_ref(v_keys_1619_);
v_i_1620_ = lean_ctor_get(v_c_1519_, 1);
lean_inc(v_i_1620_);
v_v_1621_ = lean_ctor_get(v_c_1519_, 2);
lean_inc(v_v_1621_);
lean_dec_ref_known(v_c_1519_, 3);
v___x_1622_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__1(v_todo_1518_, v_keys_1619_, v_i_1620_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec_ref(v_keys_1619_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1635_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1635_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
uint8_t v___x_1627_; 
v___x_1627_ = lean_unbox(v_a_1623_);
lean_dec(v_a_1623_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1629_; 
lean_dec(v_v_1621_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_result_1520_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_result_1520_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_array_push(v_result_1520_, v_v_1621_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1631_);
v___x_1633_ = v___x_1625_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_v_1621_);
lean_dec_ref(v_result_1520_);
v_a_1636_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1622_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1622_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_val_1647_; uint8_t v___x_1650_; 
v___x_1644_ = lean_array_get_size(v_todo_1518_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1650_ = lean_nat_dec_eq(v___x_1644_, v___x_1645_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v_val_1677_; 
v___x_1651_ = l_Lean_instInhabitedExpr;
switch(lean_obj_tag(v_c_1519_))
{
case 2:
{
lean_object* v___x_1682_; 
lean_inc_ref(v_c_1519_);
v___x_1682_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1677_ = v___x_1682_;
goto v___jp_1676_;
}
case 3:
{
lean_object* v___x_1683_; 
lean_inc_ref(v_c_1519_);
v___x_1683_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1677_ = v___x_1683_;
goto v___jp_1676_;
}
default: 
{
lean_inc_ref(v_c_1519_);
v_val_1677_ = v_c_1519_;
goto v___jp_1676_;
}
}
v___jp_1652_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v_e_1655_; lean_object* v_todo_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_nat_sub(v___x_1644_, v___x_1653_);
v_e_1655_ = lean_array_get(v___x_1651_, v_todo_1518_, v___x_1654_);
lean_dec(v___x_1654_);
v_todo_1656_ = lean_array_pop(v_todo_1518_);
v___x_1657_ = 1;
v___x_1658_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1655_, v___x_1657_, v___x_1650_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
switch(lean_obj_tag(v_c_1519_))
{
case 2:
{
lean_object* v_fst_1660_; lean_object* v_snd_1661_; lean_object* v___x_1662_; 
v_fst_1660_ = lean_ctor_get(v_a_1659_, 0);
lean_inc(v_fst_1660_);
v_snd_1661_ = lean_ctor_get(v_a_1659_, 1);
lean_inc(v_snd_1661_);
lean_dec(v_a_1659_);
lean_inc_ref(v_c_1519_);
v___x_1662_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1601_ = v___x_1653_;
v___y_1602_ = v_fst_1660_;
v___y_1603_ = v_snd_1661_;
v___y_1604_ = v_todo_1656_;
v_val_1605_ = v___x_1662_;
goto v___jp_1600_;
}
case 3:
{
lean_object* v_fst_1663_; lean_object* v_snd_1664_; lean_object* v___x_1665_; 
v_fst_1663_ = lean_ctor_get(v_a_1659_, 0);
lean_inc(v_fst_1663_);
v_snd_1664_ = lean_ctor_get(v_a_1659_, 1);
lean_inc(v_snd_1664_);
lean_dec(v_a_1659_);
lean_inc_ref(v_c_1519_);
v___x_1665_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1601_ = v___x_1653_;
v___y_1602_ = v_fst_1663_;
v___y_1603_ = v_snd_1664_;
v___y_1604_ = v_todo_1656_;
v_val_1605_ = v___x_1665_;
goto v___jp_1600_;
}
default: 
{
lean_object* v_fst_1666_; lean_object* v_snd_1667_; 
v_fst_1666_ = lean_ctor_get(v_a_1659_, 0);
lean_inc(v_fst_1666_);
v_snd_1667_ = lean_ctor_get(v_a_1659_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_a_1659_);
lean_inc_ref(v_c_1519_);
v___y_1601_ = v___x_1653_;
v___y_1602_ = v_fst_1666_;
v___y_1603_ = v_snd_1667_;
v___y_1604_ = v_todo_1656_;
v_val_1605_ = v_c_1519_;
goto v___jp_1600_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref(v_todo_1656_);
lean_dec_ref(v_result_1520_);
lean_dec_ref(v_c_1519_);
v_a_1668_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1658_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1658_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
v___jp_1676_:
{
if (lean_obj_tag(v_val_1677_) == 0)
{
lean_dec_ref_known(v_val_1677_, 2);
goto v___jp_1652_;
}
else
{
lean_object* v_children_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_children_1678_ = lean_ctor_get(v_val_1677_, 1);
lean_inc_ref(v_children_1678_);
lean_dec_ref_known(v_val_1677_, 2);
v___x_1679_ = lean_array_get_size(v_children_1678_);
lean_dec_ref(v_children_1678_);
v___x_1680_ = lean_nat_dec_eq(v___x_1679_, v___x_1645_);
if (v___x_1680_ == 0)
{
goto v___jp_1652_;
}
else
{
lean_object* v___x_1681_; 
lean_dec_ref(v_c_1519_);
lean_dec_ref(v_todo_1518_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v_result_1520_);
return v___x_1681_;
}
}
}
}
else
{
lean_dec_ref(v_todo_1518_);
switch(lean_obj_tag(v_c_1519_))
{
case 2:
{
lean_object* v___x_1684_; 
v___x_1684_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1647_ = v___x_1684_;
goto v___jp_1646_;
}
case 3:
{
lean_object* v___x_1685_; 
v___x_1685_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1647_ = v___x_1685_;
goto v___jp_1646_;
}
default: 
{
v_val_1647_ = v_c_1519_;
goto v___jp_1646_;
}
}
}
v___jp_1646_:
{
if (lean_obj_tag(v_val_1647_) == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref_known(v_val_1647_, 2);
v___x_1648_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_1527_ = v___x_1648_;
goto v___jp_1526_;
}
else
{
lean_object* v_vs_1649_; 
v_vs_1649_ = lean_ctor_get(v_val_1647_, 0);
lean_inc_ref(v_vs_1649_);
lean_dec_ref_known(v_val_1647_, 2);
v___y_1527_ = v_vs_1649_;
goto v___jp_1526_;
}
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = l_Array_append___redArg(v_result_1520_, v___y_1527_);
lean_dec_ref(v___y_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
v___jp_1530_:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Array_append___redArg(v___y_1535_, v___y_1534_);
lean_dec_ref(v___y_1534_);
v_todo_1518_ = v___x_1539_;
v_c_1519_ = v_val_1538_;
v_result_1520_ = v___y_1531_;
v___y_1521_ = v___y_1536_;
v___y_1522_ = v___y_1533_;
v___y_1523_ = v___y_1537_;
v___y_1524_ = v___y_1532_;
goto _start;
}
v___jp_1541_:
{
if (lean_obj_tag(v_val_1551_) == 0)
{
lean_object* v_key_1552_; lean_object* v_child_1553_; uint8_t v___x_1554_; 
v_key_1552_ = lean_ctor_get(v_val_1551_, 0);
lean_inc(v_key_1552_);
v_child_1553_ = lean_ctor_get(v_val_1551_, 1);
lean_inc_ref(v_child_1553_);
lean_dec_ref_known(v_val_1551_, 2);
v___x_1554_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1552_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec(v_key_1552_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref(v_child_1553_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v___y_1547_);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___y_1542_);
return v___x_1555_;
}
else
{
v___y_1531_ = v___y_1542_;
v___y_1532_ = v___y_1544_;
v___y_1533_ = v___y_1546_;
v___y_1534_ = v___y_1547_;
v___y_1535_ = v___y_1548_;
v___y_1536_ = v___y_1549_;
v___y_1537_ = v___y_1550_;
v_val_1538_ = v_child_1553_;
goto v___jp_1530_;
}
}
else
{
lean_object* v_children_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1575_; 
v_children_1556_ = lean_ctor_get(v_val_1551_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_val_1551_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_val_1551_, 0);
lean_dec(v_unused_1576_);
v___x_1558_ = v_val_1551_;
v_isShared_1559_ = v_isSharedCheck_1575_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_children_1556_);
lean_dec(v_val_1551_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1575_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = lean_array_get_size(v_children_1556_);
v___x_1562_ = lean_nat_dec_lt(v___x_1560_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_del_object(v___x_1558_);
lean_dec_ref(v_children_1556_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1545_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___y_1542_);
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_nat_sub(v___x_1561_, v___y_1543_);
v___x_1565_ = lean_nat_dec_le(v___x_1560_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; 
lean_dec(v___x_1564_);
lean_del_object(v___x_1558_);
lean_dec_ref(v_children_1556_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1545_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___y_1542_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___closed__0));
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 0);
lean_ctor_set(v___x_1558_, 1, v___x_1567_);
lean_ctor_set(v___x_1558_, 0, v___y_1545_);
v___x_1569_ = v___x_1558_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___y_1545_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg(v_children_1556_, v___x_1569_, v___x_1560_, v___x_1564_);
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_children_1556_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1571_; 
lean_dec_ref(v___y_1548_);
lean_dec_ref(v___y_1547_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___y_1542_);
return v___x_1571_;
}
else
{
lean_object* v_val_1572_; lean_object* v_snd_1573_; 
v_val_1572_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___x_1570_, 1);
v_snd_1573_ = lean_ctor_get(v_val_1572_, 1);
lean_inc(v_snd_1573_);
lean_dec(v_val_1572_);
v___y_1531_ = v___y_1542_;
v___y_1532_ = v___y_1544_;
v___y_1533_ = v___y_1546_;
v___y_1534_ = v___y_1547_;
v___y_1535_ = v___y_1548_;
v___y_1536_ = v___y_1549_;
v___y_1537_ = v___y_1550_;
v_val_1538_ = v_snd_1573_;
goto v___jp_1530_;
}
}
}
}
}
}
}
v___jp_1577_:
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___y_1579_, v___x_1587_);
if (v___x_1588_ == 0)
{
switch(lean_obj_tag(v_c_1519_))
{
case 2:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1542_ = v_result_1582_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1586_;
v___y_1545_ = v___y_1579_;
v___y_1546_ = v___y_1584_;
v___y_1547_ = v___y_1580_;
v___y_1548_ = v___y_1581_;
v___y_1549_ = v___y_1583_;
v___y_1550_ = v___y_1585_;
v_val_1551_ = v___x_1589_;
goto v___jp_1541_;
}
case 3:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1542_ = v_result_1582_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1586_;
v___y_1545_ = v___y_1579_;
v___y_1546_ = v___y_1584_;
v___y_1547_ = v___y_1580_;
v___y_1548_ = v___y_1581_;
v___y_1549_ = v___y_1583_;
v___y_1550_ = v___y_1585_;
v_val_1551_ = v___x_1590_;
goto v___jp_1541_;
}
default: 
{
v___y_1542_ = v_result_1582_;
v___y_1543_ = v___y_1578_;
v___y_1544_ = v___y_1586_;
v___y_1545_ = v___y_1579_;
v___y_1546_ = v___y_1584_;
v___y_1547_ = v___y_1580_;
v___y_1548_ = v___y_1581_;
v___y_1549_ = v___y_1583_;
v___y_1550_ = v___y_1585_;
v_val_1551_ = v_c_1519_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1591_; 
lean_dec_ref(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v_c_1519_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_result_1582_);
return v___x_1591_;
}
}
v___jp_1592_:
{
lean_object* v___x_1598_; 
lean_inc_ref(v___y_1596_);
v___x_1598_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v___y_1596_, v_val_1597_, v_result_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___y_1578_ = v___y_1593_;
v___y_1579_ = v___y_1594_;
v___y_1580_ = v___y_1595_;
v___y_1581_ = v___y_1596_;
v_result_1582_ = v_a_1599_;
v___y_1583_ = v___y_1521_;
v___y_1584_ = v___y_1522_;
v___y_1585_ = v___y_1523_;
v___y_1586_ = v___y_1524_;
goto v___jp_1577_;
}
else
{
lean_dec_ref(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v_c_1519_);
return v___x_1598_;
}
}
v___jp_1600_:
{
if (lean_obj_tag(v_val_1605_) == 0)
{
lean_object* v_key_1606_; lean_object* v_child_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_key_1606_ = lean_ctor_get(v_val_1605_, 0);
lean_inc(v_key_1606_);
v_child_1607_ = lean_ctor_get(v_val_1605_, 1);
lean_inc_ref(v_child_1607_);
lean_dec_ref_known(v_val_1605_, 2);
v___x_1608_ = lean_box(0);
v___x_1609_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1606_, v___x_1608_);
lean_dec(v_key_1606_);
if (v___x_1609_ == 0)
{
lean_dec_ref(v_child_1607_);
v___y_1578_ = v___y_1601_;
v___y_1579_ = v___y_1602_;
v___y_1580_ = v___y_1603_;
v___y_1581_ = v___y_1604_;
v_result_1582_ = v_result_1520_;
v___y_1583_ = v___y_1521_;
v___y_1584_ = v___y_1522_;
v___y_1585_ = v___y_1523_;
v___y_1586_ = v___y_1524_;
goto v___jp_1577_;
}
else
{
v___y_1593_ = v___y_1601_;
v___y_1594_ = v___y_1602_;
v___y_1595_ = v___y_1603_;
v___y_1596_ = v___y_1604_;
v_val_1597_ = v_child_1607_;
goto v___jp_1592_;
}
}
else
{
lean_object* v_children_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_children_1610_ = lean_ctor_get(v_val_1605_, 1);
lean_inc_ref(v_children_1610_);
lean_dec_ref_known(v_val_1605_, 2);
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = lean_array_get_size(v_children_1610_);
v___x_1613_ = lean_nat_dec_lt(v___x_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_dec_ref(v_children_1610_);
v___y_1578_ = v___y_1601_;
v___y_1579_ = v___y_1602_;
v___y_1580_ = v___y_1603_;
v___y_1581_ = v___y_1604_;
v_result_1582_ = v_result_1520_;
v___y_1583_ = v___y_1521_;
v___y_1584_ = v___y_1522_;
v___y_1585_ = v___y_1523_;
v___y_1586_ = v___y_1524_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1614_; lean_object* v_fst_1615_; lean_object* v_snd_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1614_ = lean_array_fget(v_children_1610_, v___x_1611_);
lean_dec_ref(v_children_1610_);
v_fst_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_fst_1615_);
v_snd_1616_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_snd_1616_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v___x_1618_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1615_, v___x_1617_);
lean_dec(v_fst_1615_);
if (v___x_1618_ == 0)
{
lean_dec(v_snd_1616_);
v___y_1578_ = v___y_1601_;
v___y_1579_ = v___y_1602_;
v___y_1580_ = v___y_1603_;
v___y_1581_ = v___y_1604_;
v_result_1582_ = v_result_1520_;
v___y_1583_ = v___y_1521_;
v___y_1584_ = v___y_1522_;
v___y_1585_ = v___y_1523_;
v___y_1586_ = v___y_1524_;
goto v___jp_1577_;
}
else
{
v___y_1593_ = v___y_1601_;
v___y_1594_ = v___y_1602_;
v___y_1595_ = v___y_1603_;
v___y_1596_ = v___y_1604_;
v_val_1597_ = v_snd_1616_;
goto v___jp_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_todo_1686_, lean_object* v_c_1687_, lean_object* v_result_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_todo_1686_, v_c_1687_, v_result_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1695_, lean_object* v_c_1696_, lean_object* v_result_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_todo_1695_, v_c_1696_, v_result_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1704_, lean_object* v_c_1705_, lean_object* v_result_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1704_, v_c_1705_, v_result_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1713_, lean_object* v_todo_1714_, lean_object* v_c_1715_, lean_object* v_result_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_todo_1714_, v_c_1715_, v_result_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1723_, lean_object* v_todo_1724_, lean_object* v_c_1725_, lean_object* v_result_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1723_, v_todo_1724_, v_c_1725_, v_result_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1733_, lean_object* v_todo_1734_, lean_object* v_c_1735_, lean_object* v_result_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_todo_1734_, v_c_1735_, v_result_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1743_, lean_object* v_todo_1744_, lean_object* v_c_1745_, lean_object* v_result_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1743_, v_todo_1744_, v_c_1745_, v_result_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0(lean_object* v_00_u03b1_1753_, lean_object* v_as_1754_, lean_object* v_k_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg(v_as_1754_, v_k_1755_, v_x_1756_, v_x_1757_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1760_, lean_object* v_as_1761_, lean_object* v_k_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0(v_00_u03b1_1760_, v_as_1761_, v_k_1762_, v_x_1763_, v_x_1764_, v_x_1765_);
lean_dec_ref(v_k_1762_);
lean_dec_ref(v_as_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1767_, lean_object* v_k_1768_, lean_object* v_args_1769_, lean_object* v_result_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1767_, v_k_1768_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1777_; 
lean_dec_ref(v_args_1769_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_result_1770_);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; lean_object* v___x_1779_; 
v_val_1778_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1779_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_args_1769_, v_val_1778_, v_result_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1780_, lean_object* v_k_1781_, lean_object* v_args_1782_, lean_object* v_result_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1780_, v_k_1781_, v_args_1782_, v_result_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_k_1781_);
lean_dec_ref(v_d_1780_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1790_, lean_object* v_d_1791_, lean_object* v_k_1792_, lean_object* v_args_1793_, lean_object* v_result_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1791_, v_k_1792_, v_args_1793_, v_result_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_d_1802_, lean_object* v_k_1803_, lean_object* v_args_1804_, lean_object* v_result_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1801_, v_d_1802_, v_k_1803_, v_args_1804_, v_result_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_k_1803_);
lean_dec_ref(v_d_1802_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(lean_object* v_e_1812_, uint8_t v___x_1813_, lean_object* v_result_1814_, lean_object* v_d_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1812_, v___x_1813_, v___x_1813_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1865_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1865_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1865_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_fst_1826_; 
v_fst_1826_ = lean_ctor_get(v_a_1822_, 0);
lean_inc(v_fst_1826_);
if (lean_obj_tag(v_fst_1826_) == 0)
{
lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1836_; 
v_isSharedCheck_1836_ = !lean_is_exclusive(v_a_1822_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; lean_object* v_unused_1838_; 
v_unused_1837_ = lean_ctor_get(v_a_1822_, 1);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_a_1822_, 0);
lean_dec(v_unused_1838_);
v___x_1828_ = v_a_1822_;
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
else
{
lean_dec(v_a_1822_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v_result_1814_);
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_fst_1826_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_result_1814_);
v___x_1831_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1833_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1831_);
v___x_1833_ = v___x_1824_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_snd_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1863_; 
lean_del_object(v___x_1824_);
v_snd_1839_ = lean_ctor_get(v_a_1822_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_a_1822_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v_a_1822_, 0);
lean_dec(v_unused_1864_);
v___x_1841_ = v_a_1822_;
v_isShared_1842_ = v_isSharedCheck_1863_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_snd_1839_);
lean_dec(v_a_1822_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1863_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; 
v___x_1843_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1815_, v_fst_1826_, v_snd_1839_, v_result_1814_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1854_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v_a_1844_);
v___x_1849_ = v___x_1841_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_fst_1826_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1849_);
v___x_1851_ = v___x_1846_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_del_object(v___x_1841_);
lean_dec(v_fst_1826_);
v_a_1855_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1843_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1843_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v_result_1814_);
v_a_1866_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1821_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1821_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0___boxed(lean_object* v_e_1874_, lean_object* v___x_1875_, lean_object* v_result_1876_, lean_object* v_d_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v___x_802__boxed_1883_; lean_object* v_res_1884_; 
v___x_802__boxed_1883_ = lean_unbox(v___x_1875_);
v_res_1884_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1874_, v___x_802__boxed_1883_, v_result_1876_, v_d_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_d_1877_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1885_, lean_object* v_e_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___y_1893_; lean_object* v___x_1910_; uint8_t v_transparency_1911_; lean_object* v_result_1912_; uint8_t v___x_1913_; uint8_t v___x_1914_; uint8_t v___x_1915_; 
v___x_1910_ = l_Lean_Meta_Context_config(v_a_1887_);
v_transparency_1911_ = lean_ctor_get_uint8(v___x_1910_, 9);
lean_dec_ref(v___x_1910_);
v_result_1912_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1885_);
v___x_1913_ = 1;
v___x_1914_ = 2;
v___x_1915_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1911_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v_keyedConfig_1916_; uint8_t v_trackZetaDelta_1917_; lean_object* v_zetaDeltaSet_1918_; lean_object* v_lctx_1919_; lean_object* v_localInstances_1920_; lean_object* v_defEqCtx_x3f_1921_; lean_object* v_synthPendingDepth_1922_; lean_object* v_customCanUnfoldPredicate_x3f_1923_; uint8_t v_univApprox_1924_; uint8_t v_inTypeClassResolution_1925_; uint8_t v_cacheInferType_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_keyedConfig_1916_ = lean_ctor_get(v_a_1887_, 0);
v_trackZetaDelta_1917_ = lean_ctor_get_uint8(v_a_1887_, sizeof(void*)*7);
v_zetaDeltaSet_1918_ = lean_ctor_get(v_a_1887_, 1);
v_lctx_1919_ = lean_ctor_get(v_a_1887_, 2);
v_localInstances_1920_ = lean_ctor_get(v_a_1887_, 3);
v_defEqCtx_x3f_1921_ = lean_ctor_get(v_a_1887_, 4);
v_synthPendingDepth_1922_ = lean_ctor_get(v_a_1887_, 5);
v_customCanUnfoldPredicate_x3f_1923_ = lean_ctor_get(v_a_1887_, 6);
v_univApprox_1924_ = lean_ctor_get_uint8(v_a_1887_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1925_ = lean_ctor_get_uint8(v_a_1887_, sizeof(void*)*7 + 2);
v_cacheInferType_1926_ = lean_ctor_get_uint8(v_a_1887_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1916_);
v___x_1927_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1914_, v_keyedConfig_1916_);
lean_inc(v_customCanUnfoldPredicate_x3f_1923_);
lean_inc(v_synthPendingDepth_1922_);
lean_inc(v_defEqCtx_x3f_1921_);
lean_inc_ref(v_localInstances_1920_);
lean_inc_ref(v_lctx_1919_);
lean_inc(v_zetaDeltaSet_1918_);
v___x_1928_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v_zetaDeltaSet_1918_);
lean_ctor_set(v___x_1928_, 2, v_lctx_1919_);
lean_ctor_set(v___x_1928_, 3, v_localInstances_1920_);
lean_ctor_set(v___x_1928_, 4, v_defEqCtx_x3f_1921_);
lean_ctor_set(v___x_1928_, 5, v_synthPendingDepth_1922_);
lean_ctor_set(v___x_1928_, 6, v_customCanUnfoldPredicate_x3f_1923_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7, v_trackZetaDelta_1917_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7 + 1, v_univApprox_1924_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1925_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7 + 3, v_cacheInferType_1926_);
v___x_1929_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1886_, v___x_1913_, v_result_1912_, v_d_1885_, v___x_1928_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec_ref_known(v___x_1928_, 7);
v___y_1893_ = v___x_1929_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1886_, v___x_1913_, v_result_1912_, v_d_1885_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
v___y_1893_ = v___x_1930_;
goto v___jp_1892_;
}
v___jp_1892_:
{
if (lean_obj_tag(v___y_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___y_1893_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___y_1893_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___y_1893_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___y_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___y_1893_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1893_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___y_1893_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___y_1893_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1931_, lean_object* v_e_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1931_, v_e_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec_ref(v_d_1931_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1939_, lean_object* v_d_1940_, lean_object* v_e_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1940_, v_e_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1948_, lean_object* v_d_1949_, lean_object* v_e_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1948_, v_d_1949_, v_e_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec_ref(v_d_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1957_, lean_object* v_e_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1957_, v_e_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_snd_1969_; lean_object* v___x_1971_; 
v_snd_1969_ = lean_ctor_get(v_a_1965_, 1);
lean_inc(v_snd_1969_);
lean_dec(v_a_1965_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_snd_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_snd_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1964_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1964_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1982_, lean_object* v_e_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1982_, v_e_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_d_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1990_, lean_object* v_d_1991_, lean_object* v_e_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1991_, v_e_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_d_2000_, lean_object* v_e_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1999_, v_d_2000_, v_e_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec_ref(v_d_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_2008_, lean_object* v_k_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_k_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; 
switch(lean_obj_tag(v_k_2009_))
{
case 4:
{
lean_object* v_a_2037_; lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2049_; 
v_a_2037_ = lean_ctor_get(v_k_2009_, 0);
v_a_2038_ = lean_ctor_get(v_k_2009_, 1);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_k_2009_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2040_ = v_k_2009_;
v_isShared_2041_ = v_isSharedCheck_2049_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_inc(v_a_2037_);
lean_dec(v_k_2009_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2049_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_zero_2042_; uint8_t v_isZero_2043_; 
v_zero_2042_ = lean_unsigned_to_nat(0u);
v_isZero_2043_ = lean_nat_dec_eq(v_a_2038_, v_zero_2042_);
if (v_isZero_2043_ == 0)
{
lean_object* v_one_2044_; lean_object* v_n_2045_; lean_object* v___x_2047_; 
v_one_2044_ = lean_unsigned_to_nat(1u);
v_n_2045_ = lean_nat_sub(v_a_2038_, v_one_2044_);
lean_dec(v_a_2038_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v_n_2045_);
v___x_2047_ = v___x_2040_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2037_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_n_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v_k_2020_ = v___x_2047_;
v___y_2021_ = v_a_2010_;
v___y_2022_ = v_a_2011_;
v___y_2023_ = v_a_2012_;
v___y_2024_ = v_a_2013_;
goto v___jp_2019_;
}
}
else
{
lean_del_object(v___x_2040_);
lean_dec(v_a_2038_);
lean_dec(v_a_2037_);
goto v___jp_2015_;
}
}
}
case 3:
{
lean_object* v_a_2050_; lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2062_; 
v_a_2050_ = lean_ctor_get(v_k_2009_, 0);
v_a_2051_ = lean_ctor_get(v_k_2009_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_k_2009_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2053_ = v_k_2009_;
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_inc(v_a_2050_);
lean_dec(v_k_2009_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_zero_2055_; uint8_t v_isZero_2056_; 
v_zero_2055_ = lean_unsigned_to_nat(0u);
v_isZero_2056_ = lean_nat_dec_eq(v_a_2051_, v_zero_2055_);
if (v_isZero_2056_ == 0)
{
lean_object* v_one_2057_; lean_object* v_n_2058_; lean_object* v___x_2060_; 
v_one_2057_ = lean_unsigned_to_nat(1u);
v_n_2058_ = lean_nat_sub(v_a_2051_, v_one_2057_);
lean_dec(v_a_2051_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v_n_2058_);
v___x_2060_ = v___x_2053_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2050_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_n_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
v_k_2020_ = v___x_2060_;
v___y_2021_ = v_a_2010_;
v___y_2022_ = v_a_2011_;
v___y_2023_ = v_a_2012_;
v___y_2024_ = v_a_2013_;
goto v___jp_2019_;
}
}
else
{
lean_del_object(v___x_2053_);
lean_dec(v_a_2051_);
lean_dec(v_a_2050_);
goto v___jp_2015_;
}
}
}
case 6:
{
lean_object* v_a_2063_; lean_object* v_a_2064_; lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2076_; 
v_a_2063_ = lean_ctor_get(v_k_2009_, 0);
v_a_2064_ = lean_ctor_get(v_k_2009_, 1);
v_a_2065_ = lean_ctor_get(v_k_2009_, 2);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_k_2009_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2067_ = v_k_2009_;
v_isShared_2068_ = v_isSharedCheck_2076_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_inc(v_a_2064_);
lean_inc(v_a_2063_);
lean_dec(v_k_2009_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2076_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_zero_2069_; uint8_t v_isZero_2070_; 
v_zero_2069_ = lean_unsigned_to_nat(0u);
v_isZero_2070_ = lean_nat_dec_eq(v_a_2065_, v_zero_2069_);
if (v_isZero_2070_ == 0)
{
lean_object* v_one_2071_; lean_object* v_n_2072_; lean_object* v___x_2074_; 
v_one_2071_ = lean_unsigned_to_nat(1u);
v_n_2072_ = lean_nat_sub(v_a_2065_, v_one_2071_);
lean_dec(v_a_2065_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 2, v_n_2072_);
v___x_2074_ = v___x_2067_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2063_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_a_2064_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_n_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v_k_2020_ = v___x_2074_;
v___y_2021_ = v_a_2010_;
v___y_2022_ = v_a_2011_;
v___y_2023_ = v_a_2012_;
v___y_2024_ = v_a_2013_;
goto v___jp_2019_;
}
}
else
{
lean_del_object(v___x_2067_);
lean_dec(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec(v_a_2063_);
goto v___jp_2015_;
}
}
}
default: 
{
lean_dec(v_k_2009_);
goto v___jp_2015_;
}
}
v___jp_2015_:
{
uint8_t v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = 0;
v___x_2017_ = lean_box(v___x_2016_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
v___jp_2019_:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2008_, v_k_2020_);
if (lean_obj_tag(v___x_2025_) == 0)
{
v_k_2009_ = v_k_2020_;
v_a_2010_ = v___y_2021_;
v_a_2011_ = v___y_2022_;
v_a_2012_ = v___y_2023_;
v_a_2013_ = v___y_2024_;
goto _start;
}
else
{
lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_k_2020_);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_2025_, 0);
lean_dec(v_unused_2036_);
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2035_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2035_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2030_ = 1;
v___x_2031_ = lean_box(v___x_2030_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2031_);
v___x_2033_ = v___x_2028_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_2077_, lean_object* v_k_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2077_, v_k_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec_ref(v_d_2077_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_2085_, lean_object* v_d_2086_, lean_object* v_k_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2086_, v_k_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_d_2095_, lean_object* v_k_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_2094_, v_d_2095_, v_k_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec_ref(v_d_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_2103_, size_t v_sz_2104_, size_t v_i_2105_, lean_object* v_bs_2106_){
_start:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_usize_dec_lt(v_i_2105_, v_sz_2104_);
if (v___x_2107_ == 0)
{
lean_dec(v_numExtra_2103_);
return v_bs_2106_;
}
else
{
lean_object* v_v_2108_; lean_object* v___x_2109_; lean_object* v_bs_x27_2110_; lean_object* v___x_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
v_v_2108_ = lean_array_uget(v_bs_2106_, v_i_2105_);
v___x_2109_ = lean_unsigned_to_nat(0u);
v_bs_x27_2110_ = lean_array_uset(v_bs_2106_, v_i_2105_, v___x_2109_);
lean_inc(v_numExtra_2103_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v_v_2108_);
lean_ctor_set(v___x_2111_, 1, v_numExtra_2103_);
v___x_2112_ = ((size_t)1ULL);
v___x_2113_ = lean_usize_add(v_i_2105_, v___x_2112_);
v___x_2114_ = lean_array_uset(v_bs_x27_2110_, v_i_2105_, v___x_2111_);
v_i_2105_ = v___x_2113_;
v_bs_2106_ = v___x_2114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_2116_, lean_object* v_sz_2117_, lean_object* v_i_2118_, lean_object* v_bs_2119_){
_start:
{
size_t v_sz_boxed_2120_; size_t v_i_boxed_2121_; lean_object* v_res_2122_; 
v_sz_boxed_2120_ = lean_unbox_usize(v_sz_2117_);
lean_dec(v_sz_2117_);
v_i_boxed_2121_ = lean_unbox_usize(v_i_2118_);
lean_dec(v_i_2118_);
v_res_2122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2116_, v_sz_boxed_2120_, v_i_boxed_2121_, v_bs_2119_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_2123_, lean_object* v_e_2124_, lean_object* v_numExtra_2125_, lean_object* v_result_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; 
lean_inc_ref(v_e_2124_);
v___x_2132_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2123_, v_e_2124_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2150_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2150_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2150_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_snd_2137_; size_t v_sz_2138_; size_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_snd_2137_ = lean_ctor_get(v_a_2133_, 1);
lean_inc(v_snd_2137_);
lean_dec(v_a_2133_);
v_sz_2138_ = lean_array_size(v_snd_2137_);
v___x_2139_ = ((size_t)0ULL);
lean_inc(v_numExtra_2125_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2125_, v_sz_2138_, v___x_2139_, v_snd_2137_);
v___x_2141_ = l_Array_append___redArg(v_result_2126_, v___x_2140_);
lean_dec_ref(v___x_2140_);
v___x_2142_ = l_Lean_Expr_isApp(v_e_2124_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2144_; 
lean_dec(v_numExtra_2125_);
lean_dec_ref(v_e_2124_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2141_);
v___x_2144_ = v___x_2135_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2141_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_del_object(v___x_2135_);
v___x_2146_ = l_Lean_Expr_appFn_x21(v_e_2124_);
lean_dec_ref(v_e_2124_);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_add(v_numExtra_2125_, v___x_2147_);
lean_dec(v_numExtra_2125_);
v_e_2124_ = v___x_2146_;
v_numExtra_2125_ = v___x_2148_;
v_result_2126_ = v___x_2141_;
goto _start;
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_result_2126_);
lean_dec(v_numExtra_2125_);
lean_dec_ref(v_e_2124_);
v_a_2151_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2132_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2132_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2159_, lean_object* v_e_2160_, lean_object* v_numExtra_2161_, lean_object* v_result_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2159_, v_e_2160_, v_numExtra_2161_, v_result_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec_ref(v_d_2159_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2169_, lean_object* v_d_2170_, lean_object* v_e_2171_, lean_object* v_numExtra_2172_, lean_object* v_result_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2170_, v_e_2171_, v_numExtra_2172_, v_result_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_d_2181_, lean_object* v_e_2182_, lean_object* v_numExtra_2183_, lean_object* v_result_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2180_, v_d_2181_, v_e_2182_, v_numExtra_2183_, v_result_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec_ref(v_d_2181_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2191_, lean_object* v_numExtra_2192_, size_t v_sz_2193_, size_t v_i_2194_, lean_object* v_bs_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2192_, v_sz_2193_, v_i_2194_, v_bs_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_numExtra_2198_, lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_bs_2201_){
_start:
{
size_t v_sz_boxed_2202_; size_t v_i_boxed_2203_; lean_object* v_res_2204_; 
v_sz_boxed_2202_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2203_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2197_, v_numExtra_2198_, v_sz_boxed_2202_, v_i_boxed_2203_, v_bs_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2205_, size_t v_i_2206_, lean_object* v_bs_2207_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = lean_usize_dec_lt(v_i_2206_, v_sz_2205_);
if (v___x_2208_ == 0)
{
return v_bs_2207_;
}
else
{
lean_object* v_v_2209_; lean_object* v___x_2210_; lean_object* v_bs_x27_2211_; lean_object* v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v_v_2209_ = lean_array_uget(v_bs_2207_, v_i_2206_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v_bs_x27_2211_ = lean_array_uset(v_bs_2207_, v_i_2206_, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v_v_2209_);
lean_ctor_set(v___x_2212_, 1, v___x_2210_);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_add(v_i_2206_, v___x_2213_);
v___x_2215_ = lean_array_uset(v_bs_x27_2211_, v_i_2206_, v___x_2212_);
v_i_2206_ = v___x_2214_;
v_bs_2207_ = v___x_2215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2217_, lean_object* v_i_2218_, lean_object* v_bs_2219_){
_start:
{
size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2217_);
lean_dec(v_sz_2217_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2218_);
lean_dec(v_i_2218_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2220_, v_i_boxed_2221_, v_bs_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2223_, lean_object* v_e_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___x_2230_; 
lean_inc_ref(v_e_2224_);
v___x_2230_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2223_, v_e_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2265_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2265_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2265_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v_fst_2235_; lean_object* v_snd_2236_; size_t v_sz_2237_; size_t v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_fst_2235_ = lean_ctor_get(v_a_2231_, 0);
lean_inc(v_fst_2235_);
v_snd_2236_ = lean_ctor_get(v_a_2231_, 1);
lean_inc(v_snd_2236_);
lean_dec(v_a_2231_);
v_sz_2237_ = lean_array_size(v_snd_2236_);
v___x_2238_ = ((size_t)0ULL);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2237_, v___x_2238_, v_snd_2236_);
v___x_2240_ = l_Lean_Expr_isApp(v_e_2224_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_fst_2235_);
lean_dec_ref(v_e_2224_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2239_);
v___x_2242_ = v___x_2233_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2239_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
else
{
lean_object* v___x_2244_; 
lean_del_object(v___x_2233_);
v___x_2244_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2223_, v_fst_2235_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2256_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2256_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2256_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_unbox(v_a_2245_);
lean_dec(v_a_2245_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2251_; 
lean_dec_ref(v_e_2224_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2239_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2239_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_del_object(v___x_2247_);
v___x_2253_ = l_Lean_Expr_appFn_x21(v_e_2224_);
lean_dec_ref(v_e_2224_);
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2223_, v___x_2253_, v___x_2254_, v___x_2239_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2255_;
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v___x_2239_);
lean_dec_ref(v_e_2224_);
v_a_2257_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2244_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2244_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v_e_2224_);
v_a_2266_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2230_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2230_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2274_, lean_object* v_e_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2274_, v_e_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec_ref(v_d_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2282_, lean_object* v_d_2283_, lean_object* v_e_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2283_, v_e_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2291_, lean_object* v_d_2292_, lean_object* v_e_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2291_, v_d_2292_, v_e_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec_ref(v_d_2292_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2300_, size_t v_sz_2301_, size_t v_i_2302_, lean_object* v_bs_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2301_, v_i_2302_, v_bs_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2305_, lean_object* v_sz_2306_, lean_object* v_i_2307_, lean_object* v_bs_2308_){
_start:
{
size_t v_sz_boxed_2309_; size_t v_i_boxed_2310_; lean_object* v_res_2311_; 
v_sz_boxed_2309_ = lean_unbox_usize(v_sz_2306_);
lean_dec(v_sz_2306_);
v_i_boxed_2310_ = lean_unbox_usize(v_i_2307_);
lean_dec(v_i_2307_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2305_, v_sz_boxed_2309_, v_i_boxed_2310_, v_bs_2308_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
uint8_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = 1;
v___x_2319_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2312_, v___x_2318_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2343_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2343_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2343_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___y_2326_; lean_object* v___x_2331_; 
v___x_2324_ = l_Lean_Expr_getAppNumArgs(v_a_2320_);
v___x_2331_ = l_Lean_Expr_getAppFn(v_a_2320_);
lean_dec(v_a_2320_);
switch(lean_obj_tag(v___x_2331_))
{
case 9:
{
lean_object* v_a_2332_; lean_object* v___x_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc_ref(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2332_);
v___y_2326_ = v___x_2333_;
goto v___jp_2325_;
}
case 1:
{
lean_object* v_fvarId_2334_; lean_object* v___x_2335_; 
v_fvarId_2334_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_fvarId_2334_);
lean_dec_ref_known(v___x_2331_, 1);
lean_inc(v___x_2324_);
v___x_2335_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_fvarId_2334_);
lean_ctor_set(v___x_2335_, 1, v___x_2324_);
v___y_2326_ = v___x_2335_;
goto v___jp_2325_;
}
case 11:
{
lean_object* v_typeName_2336_; lean_object* v_idx_2337_; lean_object* v___x_2338_; 
v_typeName_2336_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_typeName_2336_);
v_idx_2337_ = lean_ctor_get(v___x_2331_, 1);
lean_inc(v_idx_2337_);
lean_dec_ref_known(v___x_2331_, 3);
lean_inc(v___x_2324_);
v___x_2338_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2338_, 0, v_typeName_2336_);
lean_ctor_set(v___x_2338_, 1, v_idx_2337_);
lean_ctor_set(v___x_2338_, 2, v___x_2324_);
v___y_2326_ = v___x_2338_;
goto v___jp_2325_;
}
case 7:
{
lean_object* v___x_2339_; 
lean_dec_ref_known(v___x_2331_, 3);
v___x_2339_ = lean_box(5);
v___y_2326_ = v___x_2339_;
goto v___jp_2325_;
}
case 4:
{
lean_object* v_declName_2340_; lean_object* v___x_2341_; 
v_declName_2340_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_declName_2340_);
lean_dec_ref_known(v___x_2331_, 2);
lean_inc(v___x_2324_);
v___x_2341_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_declName_2340_);
lean_ctor_set(v___x_2341_, 1, v___x_2324_);
v___y_2326_ = v___x_2341_;
goto v___jp_2325_;
}
default: 
{
lean_object* v___x_2342_; 
lean_dec_ref(v___x_2331_);
v___x_2342_ = lean_box(1);
v___y_2326_ = v___x_2342_;
goto v___jp_2325_;
}
}
v___jp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___y_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2324_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2327_);
v___x_2329_ = v___x_2322_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2319_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2319_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2359_, lean_object* v_result_2360_){
_start:
{
lean_object* v___y_2362_; lean_object* v_val_2363_; lean_object* v___y_2374_; lean_object* v_val_2379_; 
if (lean_obj_tag(v_trie_2359_) == 3)
{
lean_object* v_v_2382_; lean_object* v___x_2383_; 
v_v_2382_ = lean_ctor_get(v_trie_2359_, 2);
lean_inc(v_v_2382_);
lean_dec_ref_known(v_trie_2359_, 3);
v___x_2383_ = lean_array_push(v_result_2360_, v_v_2382_);
return v___x_2383_;
}
else
{
switch(lean_obj_tag(v_trie_2359_))
{
case 2:
{
lean_object* v___x_2384_; 
lean_inc_ref(v_trie_2359_);
v___x_2384_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2359_);
v_val_2379_ = v___x_2384_;
goto v___jp_2378_;
}
case 3:
{
lean_object* v___x_2385_; 
lean_inc_ref(v_trie_2359_);
v___x_2385_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2359_);
v_val_2379_ = v___x_2385_;
goto v___jp_2378_;
}
default: 
{
lean_inc_ref(v_trie_2359_);
v_val_2379_ = v_trie_2359_;
goto v___jp_2378_;
}
}
}
v___jp_2361_:
{
if (lean_obj_tag(v_val_2363_) == 0)
{
lean_object* v_child_2364_; 
v_child_2364_ = lean_ctor_get(v_val_2363_, 1);
lean_inc_ref(v_child_2364_);
lean_dec_ref_known(v_val_2363_, 2);
v_trie_2359_ = v_child_2364_;
v_result_2360_ = v___y_2362_;
goto _start;
}
else
{
lean_object* v_children_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_children_2366_ = lean_ctor_get(v_val_2363_, 1);
lean_inc_ref(v_children_2366_);
lean_dec_ref_known(v_val_2363_, 2);
v___x_2367_ = lean_unsigned_to_nat(0u);
v___x_2368_ = lean_array_get_size(v_children_2366_);
v___x_2369_ = lean_nat_dec_lt(v___x_2367_, v___x_2368_);
if (v___x_2369_ == 0)
{
lean_dec_ref(v_children_2366_);
return v___y_2362_;
}
else
{
size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = lean_usize_of_nat(v___x_2368_);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2366_, v___x_2370_, v___x_2371_, v___y_2362_);
lean_dec_ref(v_children_2366_);
return v___x_2372_;
}
}
}
v___jp_2373_:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Array_append___redArg(v_result_2360_, v___y_2374_);
lean_dec_ref(v___y_2374_);
switch(lean_obj_tag(v_trie_2359_))
{
case 2:
{
lean_object* v___x_2376_; 
v___x_2376_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2359_);
v___y_2362_ = v___x_2375_;
v_val_2363_ = v___x_2376_;
goto v___jp_2361_;
}
case 3:
{
lean_object* v___x_2377_; 
v___x_2377_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2359_);
v___y_2362_ = v___x_2375_;
v_val_2363_ = v___x_2377_;
goto v___jp_2361_;
}
default: 
{
v___y_2362_ = v___x_2375_;
v_val_2363_ = v_trie_2359_;
goto v___jp_2361_;
}
}
}
v___jp_2378_:
{
if (lean_obj_tag(v_val_2379_) == 0)
{
lean_object* v___x_2380_; 
lean_dec_ref_known(v_val_2379_, 2);
v___x_2380_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_2374_ = v___x_2380_;
goto v___jp_2373_;
}
else
{
lean_object* v_vs_2381_; 
v_vs_2381_ = lean_ctor_get(v_val_2379_, 0);
lean_inc_ref(v_vs_2381_);
lean_dec_ref_known(v_val_2379_, 2);
v___y_2374_ = v_vs_2381_;
goto v___jp_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2386_, size_t v_i_2387_, size_t v_stop_2388_, lean_object* v_b_2389_){
_start:
{
uint8_t v___x_2390_; 
v___x_2390_ = lean_usize_dec_eq(v_i_2387_, v_stop_2388_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v_snd_2392_; lean_object* v___x_2393_; size_t v___x_2394_; size_t v___x_2395_; 
v___x_2391_ = lean_array_uget_borrowed(v_as_2386_, v_i_2387_);
v_snd_2392_ = lean_ctor_get(v___x_2391_, 1);
lean_inc(v_snd_2392_);
v___x_2393_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2392_, v_b_2389_);
v___x_2394_ = ((size_t)1ULL);
v___x_2395_ = lean_usize_add(v_i_2387_, v___x_2394_);
v_i_2387_ = v___x_2395_;
v_b_2389_ = v___x_2393_;
goto _start;
}
else
{
return v_b_2389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2397_, lean_object* v_i_2398_, lean_object* v_stop_2399_, lean_object* v_b_2400_){
_start:
{
size_t v_i_boxed_2401_; size_t v_stop_boxed_2402_; lean_object* v_res_2403_; 
v_i_boxed_2401_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_stop_boxed_2402_ = lean_unbox_usize(v_stop_2399_);
lean_dec(v_stop_2399_);
v_res_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2397_, v_i_boxed_2401_, v_stop_boxed_2402_, v_b_2400_);
lean_dec_ref(v_as_2397_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2404_, lean_object* v_trie_2405_, lean_object* v_result_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2405_, v_result_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2408_, lean_object* v_as_2409_, size_t v_i_2410_, size_t v_stop_2411_, lean_object* v_b_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2409_, v_i_2410_, v_stop_2411_, v_b_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_as_2415_, lean_object* v_i_2416_, lean_object* v_stop_2417_, lean_object* v_b_2418_){
_start:
{
size_t v_i_boxed_2419_; size_t v_stop_boxed_2420_; lean_object* v_res_2421_; 
v_i_boxed_2419_ = lean_unbox_usize(v_i_2416_);
lean_dec(v_i_2416_);
v_stop_boxed_2420_ = lean_unbox_usize(v_stop_2417_);
lean_dec(v_stop_2417_);
v_res_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2414_, v_as_2415_, v_i_boxed_2419_, v_stop_boxed_2420_, v_b_2418_);
lean_dec_ref(v_as_2415_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2422_, lean_object* v_k_2423_, lean_object* v_result_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2422_, v_k_2423_);
if (lean_obj_tag(v___x_2425_) == 0)
{
return v_result_2424_;
}
else
{
lean_object* v_val_2426_; lean_object* v___x_2427_; 
v_val_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_val_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2426_, v_result_2424_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2428_, lean_object* v_k_2429_, lean_object* v_result_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2428_, v_k_2429_, v_result_2430_);
lean_dec(v_k_2429_);
lean_dec_ref(v_d_2428_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2432_, lean_object* v_d_2433_, lean_object* v_k_2434_, lean_object* v_result_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2433_, v_k_2434_, v_result_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2437_, lean_object* v_d_2438_, lean_object* v_k_2439_, lean_object* v_result_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2437_, v_d_2438_, v_k_2439_, v_result_2440_);
lean_dec(v_k_2439_);
lean_dec_ref(v_d_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(lean_object* v_e_2442_, lean_object* v_result_2443_, lean_object* v_d_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2442_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2468_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2468_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2468_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2467_; 
v_fst_2455_ = lean_ctor_get(v_a_2451_, 0);
v_snd_2456_ = lean_ctor_get(v_a_2451_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_a_2451_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2458_ = v_a_2451_;
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_snd_2456_);
lean_inc(v_fst_2455_);
lean_dec(v_a_2451_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2467_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2444_, v_fst_2455_, v_result_2443_);
lean_dec(v_fst_2455_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2460_);
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_snd_2456_);
v___x_2462_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2464_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2462_);
v___x_2464_ = v___x_2453_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_result_2443_);
v_a_2469_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2450_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2450_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0___boxed(lean_object* v_e_2477_, lean_object* v_result_2478_, lean_object* v_d_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2477_, v_result_2478_, v_d_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_d_2479_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2486_, lean_object* v_e_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___y_2494_; lean_object* v___x_2511_; uint8_t v_transparency_2512_; lean_object* v_result_2513_; uint8_t v___x_2514_; uint8_t v___x_2515_; 
v___x_2511_ = l_Lean_Meta_Context_config(v_a_2488_);
v_transparency_2512_ = lean_ctor_get_uint8(v___x_2511_, 9);
lean_dec_ref(v___x_2511_);
v_result_2513_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2486_);
v___x_2514_ = 2;
v___x_2515_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2512_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_object* v_keyedConfig_2516_; uint8_t v_trackZetaDelta_2517_; lean_object* v_zetaDeltaSet_2518_; lean_object* v_lctx_2519_; lean_object* v_localInstances_2520_; lean_object* v_defEqCtx_x3f_2521_; lean_object* v_synthPendingDepth_2522_; lean_object* v_customCanUnfoldPredicate_x3f_2523_; uint8_t v_univApprox_2524_; uint8_t v_inTypeClassResolution_2525_; uint8_t v_cacheInferType_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_keyedConfig_2516_ = lean_ctor_get(v_a_2488_, 0);
v_trackZetaDelta_2517_ = lean_ctor_get_uint8(v_a_2488_, sizeof(void*)*7);
v_zetaDeltaSet_2518_ = lean_ctor_get(v_a_2488_, 1);
v_lctx_2519_ = lean_ctor_get(v_a_2488_, 2);
v_localInstances_2520_ = lean_ctor_get(v_a_2488_, 3);
v_defEqCtx_x3f_2521_ = lean_ctor_get(v_a_2488_, 4);
v_synthPendingDepth_2522_ = lean_ctor_get(v_a_2488_, 5);
v_customCanUnfoldPredicate_x3f_2523_ = lean_ctor_get(v_a_2488_, 6);
v_univApprox_2524_ = lean_ctor_get_uint8(v_a_2488_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2525_ = lean_ctor_get_uint8(v_a_2488_, sizeof(void*)*7 + 2);
v_cacheInferType_2526_ = lean_ctor_get_uint8(v_a_2488_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2516_);
v___x_2527_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2514_, v_keyedConfig_2516_);
lean_inc(v_customCanUnfoldPredicate_x3f_2523_);
lean_inc(v_synthPendingDepth_2522_);
lean_inc(v_defEqCtx_x3f_2521_);
lean_inc_ref(v_localInstances_2520_);
lean_inc_ref(v_lctx_2519_);
lean_inc(v_zetaDeltaSet_2518_);
v___x_2528_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v_zetaDeltaSet_2518_);
lean_ctor_set(v___x_2528_, 2, v_lctx_2519_);
lean_ctor_set(v___x_2528_, 3, v_localInstances_2520_);
lean_ctor_set(v___x_2528_, 4, v_defEqCtx_x3f_2521_);
lean_ctor_set(v___x_2528_, 5, v_synthPendingDepth_2522_);
lean_ctor_set(v___x_2528_, 6, v_customCanUnfoldPredicate_x3f_2523_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7, v_trackZetaDelta_2517_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7 + 1, v_univApprox_2524_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2525_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7 + 3, v_cacheInferType_2526_);
v___x_2529_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2487_, v_result_2513_, v_d_2486_, v___x_2528_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec_ref_known(v___x_2528_, 7);
v___y_2494_ = v___x_2529_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2487_, v_result_2513_, v_d_2486_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
v___y_2494_ = v___x_2530_;
goto v___jp_2493_;
}
v___jp_2493_:
{
if (lean_obj_tag(v___y_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2495_ = lean_ctor_get(v___y_2494_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___y_2494_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___y_2494_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___y_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_a_2503_ = lean_ctor_get(v___y_2494_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___y_2494_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___y_2494_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___y_2494_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2531_, lean_object* v_e_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2531_, v_e_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec_ref(v_d_2531_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2539_, lean_object* v_d_2540_, lean_object* v_e_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2540_, v_e_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2548_, lean_object* v_d_2549_, lean_object* v_e_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2548_, v_d_2549_, v_e_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec_ref(v_d_2549_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(lean_object* v_skip_2557_, lean_object* v_todo_2558_, lean_object* v_ks_2559_, lean_object* v_i_2560_, lean_object* v_v_2561_, lean_object* v_result_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = lean_array_get_size(v_ks_2559_);
v___x_2569_ = lean_nat_dec_lt(v_i_2560_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
lean_dec(v_i_2560_);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_nat_dec_eq(v_skip_2557_, v___x_2570_);
lean_dec(v_skip_2557_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_dec(v_v_2561_);
lean_dec_ref(v_todo_2558_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_result_2562_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = lean_array_get_size(v_todo_2558_);
lean_dec_ref(v_todo_2558_);
v___x_2574_ = lean_nat_dec_eq(v___x_2573_, v___x_2570_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
lean_dec(v_v_2561_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_result_2562_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_array_push(v_result_2562_, v_v_2561_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
}
}
else
{
lean_object* v_key_2578_; lean_object* v_zero_2579_; uint8_t v_isZero_2580_; 
v_key_2578_ = lean_array_fget_borrowed(v_ks_2559_, v_i_2560_);
v_zero_2579_ = lean_unsigned_to_nat(0u);
v_isZero_2580_ = lean_nat_dec_eq(v_skip_2557_, v_zero_2579_);
if (v_isZero_2580_ == 1)
{
lean_object* v___x_2581_; uint8_t v___x_2582_; 
lean_dec(v_skip_2557_);
v___x_2581_ = lean_array_get_size(v_todo_2558_);
v___x_2582_ = lean_nat_dec_eq(v___x_2581_, v_zero_2579_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_e_2586_; lean_object* v_todo_2587_; lean_object* v___x_2588_; 
v___x_2583_ = l_Lean_instInhabitedExpr;
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_nat_sub(v___x_2581_, v___x_2584_);
v_e_2586_ = lean_array_get(v___x_2583_, v_todo_2558_, v___x_2585_);
lean_dec(v___x_2585_);
v_todo_2587_ = lean_array_pop(v_todo_2558_);
v___x_2588_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2586_, v___x_2582_, v___x_2582_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2616_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2616_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2616_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_fst_2593_; lean_object* v_snd_2594_; lean_object* v_result_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; 
v_fst_2593_ = lean_ctor_get(v_a_2589_, 0);
lean_inc(v_fst_2593_);
v_snd_2594_ = lean_ctor_get(v_a_2589_, 1);
lean_inc(v_snd_2594_);
lean_dec(v_a_2589_);
if (lean_obj_tag(v_fst_2593_) == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec(v_snd_2594_);
lean_del_object(v___x_2591_);
v___x_2608_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2578_);
v___x_2609_ = lean_nat_add(v_i_2560_, v___x_2584_);
lean_dec(v_i_2560_);
v_skip_2557_ = v___x_2608_;
v_todo_2558_ = v_todo_2587_;
v_i_2560_ = v___x_2609_;
goto _start;
}
else
{
lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = lean_box(0);
v___x_2612_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2578_, v___x_2611_);
if (v___x_2612_ == 0)
{
v_result_2596_ = v_result_2562_;
v___y_2597_ = v_a_2563_;
v___y_2598_ = v_a_2564_;
v___y_2599_ = v_a_2565_;
v___y_2600_ = v_a_2566_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_nat_add(v_i_2560_, v___x_2584_);
lean_inc(v_v_2561_);
lean_inc_ref(v_todo_2587_);
v___x_2614_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_zero_2579_, v_todo_2587_, v_ks_2559_, v___x_2613_, v_v_2561_, v_result_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_result_2596_ = v_a_2615_;
v___y_2597_ = v_a_2563_;
v___y_2598_ = v_a_2564_;
v___y_2599_ = v_a_2565_;
v___y_2600_ = v_a_2566_;
goto v___jp_2595_;
}
else
{
lean_dec(v_snd_2594_);
lean_dec(v_fst_2593_);
lean_del_object(v___x_2591_);
lean_dec_ref(v_todo_2587_);
lean_dec(v_v_2561_);
lean_dec(v_i_2560_);
return v___x_2614_;
}
}
}
v___jp_2595_:
{
uint8_t v___x_2601_; 
v___x_2601_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2578_, v_fst_2593_);
lean_dec(v_fst_2593_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2603_; 
lean_dec(v_snd_2594_);
lean_dec_ref(v_todo_2587_);
lean_dec(v_v_2561_);
lean_dec(v_i_2560_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_result_2596_);
v___x_2603_ = v___x_2591_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_result_2596_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_del_object(v___x_2591_);
v___x_2605_ = l_Array_append___redArg(v_todo_2587_, v_snd_2594_);
lean_dec(v_snd_2594_);
v___x_2606_ = lean_nat_add(v_i_2560_, v___x_2584_);
lean_dec(v_i_2560_);
v_skip_2557_ = v_zero_2579_;
v_todo_2558_ = v___x_2605_;
v_i_2560_ = v___x_2606_;
v_result_2562_ = v_result_2596_;
v_a_2563_ = v___y_2597_;
v_a_2564_ = v___y_2598_;
v_a_2565_ = v___y_2599_;
v_a_2566_ = v___y_2600_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_todo_2587_);
lean_dec_ref(v_result_2562_);
lean_dec(v_v_2561_);
lean_dec(v_i_2560_);
v_a_2617_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2588_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2588_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v___x_2625_; 
lean_dec(v_v_2561_);
lean_dec(v_i_2560_);
lean_dec_ref(v_todo_2558_);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_result_2562_);
return v___x_2625_;
}
}
else
{
lean_object* v_one_2626_; lean_object* v_n_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_one_2626_ = lean_unsigned_to_nat(1u);
v_n_2627_ = lean_nat_sub(v_skip_2557_, v_one_2626_);
lean_dec(v_skip_2557_);
v___x_2628_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2578_);
v___x_2629_ = lean_nat_add(v_n_2627_, v___x_2628_);
lean_dec(v___x_2628_);
lean_dec(v_n_2627_);
v___x_2630_ = lean_nat_add(v_i_2560_, v_one_2626_);
lean_dec(v_i_2560_);
v_skip_2557_ = v___x_2629_;
v_i_2560_ = v___x_2630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg___boxed(lean_object* v_skip_2632_, lean_object* v_todo_2633_, lean_object* v_ks_2634_, lean_object* v_i_2635_, lean_object* v_v_2636_, lean_object* v_result_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_skip_2632_, v_todo_2633_, v_ks_2634_, v_i_2635_, v_v_2636_, v_result_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec_ref(v_ks_2634_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix(lean_object* v_00_u03b1_2644_, lean_object* v_skip_2645_, lean_object* v_todo_2646_, lean_object* v_ks_2647_, lean_object* v_i_2648_, lean_object* v_v_2649_, lean_object* v_result_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_skip_2645_, v_todo_2646_, v_ks_2647_, v_i_2648_, v_v_2649_, v_result_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___boxed(lean_object* v_00_u03b1_2657_, lean_object* v_skip_2658_, lean_object* v_todo_2659_, lean_object* v_ks_2660_, lean_object* v_i_2661_, lean_object* v_v_2662_, lean_object* v_result_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix(v_00_u03b1_2657_, v_skip_2658_, v_todo_2659_, v_ks_2660_, v_i_2661_, v_v_2662_, v_result_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec_ref(v_ks_2660_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2670_, lean_object* v_as_2671_, size_t v_i_2672_, size_t v_stop_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
uint8_t v___x_2680_; 
v___x_2680_ = lean_usize_dec_eq(v_i_2672_, v_stop_2673_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2681_ = lean_array_uget_borrowed(v_as_2671_, v_i_2672_);
v_fst_2682_ = lean_ctor_get(v___x_2681_, 0);
v_snd_2683_ = lean_ctor_get(v___x_2681_, 1);
v___x_2684_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2682_);
lean_inc(v_snd_2683_);
lean_inc_ref(v_todo_2670_);
v___x_2685_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2684_, v_todo_2670_, v_snd_2683_, v_b_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = ((size_t)1ULL);
v___x_2688_ = lean_usize_add(v_i_2672_, v___x_2687_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(v_todo_2670_, v_as_2671_, v___x_2688_, v_stop_2673_, v_a_2686_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v___x_2689_;
}
else
{
lean_dec_ref(v_todo_2670_);
return v___x_2685_;
}
}
else
{
lean_object* v___x_2690_; 
lean_dec_ref(v_todo_2670_);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v_b_2674_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(lean_object* v_n_2691_, lean_object* v_todo_2692_, lean_object* v_as_2693_, size_t v_i_2694_, size_t v_stop_2695_, lean_object* v_b_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_usize_dec_eq(v_i_2694_, v_stop_2695_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; lean_object* v_fst_2704_; lean_object* v_snd_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2703_ = lean_array_uget_borrowed(v_as_2693_, v_i_2694_);
v_fst_2704_ = lean_ctor_get(v___x_2703_, 0);
v_snd_2705_ = lean_ctor_get(v___x_2703_, 1);
v___x_2706_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2704_);
v___x_2707_ = lean_nat_add(v_n_2691_, v___x_2706_);
lean_dec(v___x_2706_);
lean_inc(v_snd_2705_);
lean_inc_ref(v_todo_2692_);
v___x_2708_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2707_, v_todo_2692_, v_snd_2705_, v_b_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; size_t v___x_2710_; size_t v___x_2711_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
v___x_2710_ = ((size_t)1ULL);
v___x_2711_ = lean_usize_add(v_i_2694_, v___x_2710_);
v_i_2694_ = v___x_2711_;
v_b_2696_ = v_a_2709_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2692_);
return v___x_2708_;
}
}
else
{
lean_object* v___x_2713_; 
lean_dec_ref(v_todo_2692_);
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v_b_2696_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2714_, lean_object* v_todo_2715_, lean_object* v_as_2716_, size_t v_i_2717_, size_t v_stop_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_usize_dec_eq(v_i_2717_, v_stop_2718_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v_fst_2727_; lean_object* v_snd_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2726_ = lean_array_uget_borrowed(v_as_2716_, v_i_2717_);
v_fst_2727_ = lean_ctor_get(v___x_2726_, 0);
v_snd_2728_ = lean_ctor_get(v___x_2726_, 1);
v___x_2729_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2727_);
v___x_2730_ = lean_nat_add(v_n_2714_, v___x_2729_);
lean_dec(v___x_2729_);
lean_inc(v_snd_2728_);
lean_inc_ref(v_todo_2715_);
v___x_2731_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2730_, v_todo_2715_, v_snd_2728_, v_b_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; size_t v___x_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = ((size_t)1ULL);
v___x_2734_ = lean_usize_add(v_i_2717_, v___x_2733_);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(v_n_2714_, v_todo_2715_, v_as_2716_, v___x_2734_, v_stop_2718_, v_a_2732_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2735_;
}
else
{
lean_dec_ref(v_todo_2715_);
return v___x_2731_;
}
}
else
{
lean_object* v___x_2736_; 
lean_dec_ref(v_todo_2715_);
v___x_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_b_2719_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2737_, lean_object* v_todo_2738_, lean_object* v_c_2739_, lean_object* v_result_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___y_2747_; lean_object* v_val_2751_; 
if (lean_obj_tag(v_c_2739_) == 3)
{
lean_object* v_keys_2754_; lean_object* v_i_2755_; lean_object* v_v_2756_; lean_object* v___x_2757_; 
v_keys_2754_ = lean_ctor_get(v_c_2739_, 0);
lean_inc_ref(v_keys_2754_);
v_i_2755_ = lean_ctor_get(v_c_2739_, 1);
lean_inc(v_i_2755_);
v_v_2756_ = lean_ctor_get(v_c_2739_, 2);
lean_inc(v_v_2756_);
lean_dec_ref_known(v_c_2739_, 3);
v___x_2757_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_skip_2737_, v_todo_2738_, v_keys_2754_, v_i_2755_, v_v_2756_, v_result_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
lean_dec_ref(v_keys_2754_);
return v___x_2757_;
}
else
{
lean_object* v_zero_2758_; uint8_t v_isZero_2759_; 
v_zero_2758_ = lean_unsigned_to_nat(0u);
v_isZero_2759_ = lean_nat_dec_eq(v_skip_2737_, v_zero_2758_);
if (v_isZero_2759_ == 1)
{
lean_object* v___x_2760_; lean_object* v___y_2762_; lean_object* v_val_2763_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v_val_2783_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v_val_2796_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v_result_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v_val_2838_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v_val_2846_; uint8_t v___x_2859_; 
lean_dec(v_skip_2737_);
v___x_2760_ = lean_array_get_size(v_todo_2738_);
v___x_2859_ = lean_nat_dec_eq(v___x_2760_, v_zero_2758_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v_val_2885_; 
v___x_2860_ = l_Lean_instInhabitedExpr;
switch(lean_obj_tag(v_c_2739_))
{
case 2:
{
lean_object* v___x_2890_; 
lean_inc_ref(v_c_2739_);
v___x_2890_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v_val_2885_ = v___x_2890_;
goto v___jp_2884_;
}
case 3:
{
lean_object* v___x_2891_; 
lean_inc_ref(v_c_2739_);
v___x_2891_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v_val_2885_ = v___x_2891_;
goto v___jp_2884_;
}
default: 
{
lean_inc_ref(v_c_2739_);
v_val_2885_ = v_c_2739_;
goto v___jp_2884_;
}
}
v___jp_2861_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v_e_2864_; lean_object* v_todo_2865_; lean_object* v___x_2866_; 
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_sub(v___x_2760_, v___x_2862_);
v_e_2864_ = lean_array_get(v___x_2860_, v_todo_2738_, v___x_2863_);
lean_dec(v___x_2863_);
v_todo_2865_ = lean_array_pop(v_todo_2738_);
v___x_2866_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2864_, v___x_2859_, v___x_2859_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v_fst_2868_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v_fst_2868_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_fst_2868_);
if (lean_obj_tag(v_fst_2868_) == 0)
{
lean_dec(v_a_2867_);
switch(lean_obj_tag(v_c_2739_))
{
case 2:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v___y_2762_ = v_todo_2865_;
v_val_2763_ = v___x_2869_;
goto v___jp_2761_;
}
case 3:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v___y_2762_ = v_todo_2865_;
v_val_2763_ = v___x_2870_;
goto v___jp_2761_;
}
default: 
{
v___y_2762_ = v_todo_2865_;
v_val_2763_ = v_c_2739_;
goto v___jp_2761_;
}
}
}
else
{
switch(lean_obj_tag(v_c_2739_))
{
case 2:
{
lean_object* v_snd_2871_; lean_object* v___x_2872_; 
v_snd_2871_ = lean_ctor_get(v_a_2867_, 1);
lean_inc(v_snd_2871_);
lean_dec(v_a_2867_);
lean_inc_ref(v_c_2739_);
v___x_2872_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v___y_2842_ = v_snd_2871_;
v___y_2843_ = v_todo_2865_;
v___y_2844_ = v_fst_2868_;
v___y_2845_ = v___x_2862_;
v_val_2846_ = v___x_2872_;
goto v___jp_2841_;
}
case 3:
{
lean_object* v_snd_2873_; lean_object* v___x_2874_; 
v_snd_2873_ = lean_ctor_get(v_a_2867_, 1);
lean_inc(v_snd_2873_);
lean_dec(v_a_2867_);
lean_inc_ref(v_c_2739_);
v___x_2874_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v___y_2842_ = v_snd_2873_;
v___y_2843_ = v_todo_2865_;
v___y_2844_ = v_fst_2868_;
v___y_2845_ = v___x_2862_;
v_val_2846_ = v___x_2874_;
goto v___jp_2841_;
}
default: 
{
lean_object* v_snd_2875_; 
v_snd_2875_ = lean_ctor_get(v_a_2867_, 1);
lean_inc(v_snd_2875_);
lean_dec(v_a_2867_);
lean_inc_ref(v_c_2739_);
v___y_2842_ = v_snd_2875_;
v___y_2843_ = v_todo_2865_;
v___y_2844_ = v_fst_2868_;
v___y_2845_ = v___x_2862_;
v_val_2846_ = v_c_2739_;
goto v___jp_2841_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v_todo_2865_);
lean_dec_ref(v_result_2740_);
lean_dec_ref(v_c_2739_);
v_a_2876_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2866_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2866_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
v___jp_2884_:
{
if (lean_obj_tag(v_val_2885_) == 0)
{
lean_dec_ref_known(v_val_2885_, 2);
goto v___jp_2861_;
}
else
{
lean_object* v_children_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_children_2886_ = lean_ctor_get(v_val_2885_, 1);
lean_inc_ref(v_children_2886_);
lean_dec_ref_known(v_val_2885_, 2);
v___x_2887_ = lean_array_get_size(v_children_2886_);
lean_dec_ref(v_children_2886_);
v___x_2888_ = lean_nat_dec_eq(v___x_2887_, v_zero_2758_);
if (v___x_2888_ == 0)
{
goto v___jp_2861_;
}
else
{
lean_object* v___x_2889_; 
lean_dec_ref(v_c_2739_);
lean_dec_ref(v_todo_2738_);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_result_2740_);
return v___x_2889_;
}
}
}
}
else
{
lean_dec_ref(v_todo_2738_);
switch(lean_obj_tag(v_c_2739_))
{
case 2:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v_val_2751_ = v___x_2892_;
goto v___jp_2750_;
}
case 3:
{
lean_object* v___x_2893_; 
v___x_2893_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v_val_2751_ = v___x_2893_;
goto v___jp_2750_;
}
default: 
{
v_val_2751_ = v_c_2739_;
goto v___jp_2750_;
}
}
}
v___jp_2761_:
{
if (lean_obj_tag(v_val_2763_) == 0)
{
lean_object* v_key_2764_; lean_object* v_child_2765_; lean_object* v___x_2766_; 
v_key_2764_ = lean_ctor_get(v_val_2763_, 0);
lean_inc(v_key_2764_);
v_child_2765_ = lean_ctor_get(v_val_2763_, 1);
lean_inc_ref(v_child_2765_);
lean_dec_ref_known(v_val_2763_, 2);
v___x_2766_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2764_);
lean_dec(v_key_2764_);
v_skip_2737_ = v___x_2766_;
v_todo_2738_ = v___y_2762_;
v_c_2739_ = v_child_2765_;
goto _start;
}
else
{
lean_object* v_children_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v_children_2768_ = lean_ctor_get(v_val_2763_, 1);
lean_inc_ref(v_children_2768_);
lean_dec_ref_known(v_val_2763_, 2);
v___x_2769_ = lean_array_get_size(v_children_2768_);
v___x_2770_ = lean_nat_dec_lt(v_zero_2758_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; 
lean_dec_ref(v_children_2768_);
lean_dec_ref(v___y_2762_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_result_2740_);
return v___x_2771_;
}
else
{
size_t v___x_2772_; size_t v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = ((size_t)0ULL);
v___x_2773_ = lean_usize_of_nat(v___x_2769_);
v___x_2774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v___y_2762_, v_children_2768_, v___x_2772_, v___x_2773_, v_result_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
lean_dec_ref(v_children_2768_);
return v___x_2774_;
}
}
}
v___jp_2775_:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Array_append___redArg(v___y_2779_, v___y_2778_);
lean_dec_ref(v___y_2778_);
v_skip_2737_ = v_zero_2758_;
v_todo_2738_ = v___x_2784_;
v_c_2739_ = v_val_2783_;
v_result_2740_ = v___y_2781_;
v_a_2741_ = v___y_2782_;
v_a_2742_ = v___y_2777_;
v_a_2743_ = v___y_2780_;
v_a_2744_ = v___y_2776_;
goto _start;
}
v___jp_2786_:
{
if (lean_obj_tag(v_val_2796_) == 0)
{
lean_object* v_key_2797_; lean_object* v_child_2798_; uint8_t v___x_2799_; 
v_key_2797_ = lean_ctor_get(v_val_2796_, 0);
lean_inc(v_key_2797_);
v_child_2798_ = lean_ctor_get(v_val_2796_, 1);
lean_inc_ref(v_child_2798_);
lean_dec_ref_known(v_val_2796_, 2);
v___x_2799_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2797_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec(v_key_2797_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_dec_ref(v_child_2798_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v___y_2789_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___y_2792_);
return v___x_2800_;
}
else
{
v___y_2776_ = v___y_2787_;
v___y_2777_ = v___y_2788_;
v___y_2778_ = v___y_2790_;
v___y_2779_ = v___y_2789_;
v___y_2780_ = v___y_2791_;
v___y_2781_ = v___y_2792_;
v___y_2782_ = v___y_2793_;
v_val_2783_ = v_child_2798_;
goto v___jp_2775_;
}
}
else
{
lean_object* v_children_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2819_; 
v_children_2801_ = lean_ctor_get(v_val_2796_, 1);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_val_2796_);
if (v_isSharedCheck_2819_ == 0)
{
lean_object* v_unused_2820_; 
v_unused_2820_ = lean_ctor_get(v_val_2796_, 0);
lean_dec(v_unused_2820_);
v___x_2803_ = v_val_2796_;
v_isShared_2804_ = v_isSharedCheck_2819_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_children_2801_);
lean_dec(v_val_2796_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2819_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = lean_array_get_size(v_children_2801_);
v___x_2806_ = lean_nat_dec_lt(v_zero_2758_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
lean_del_object(v___x_2803_);
lean_dec_ref(v_children_2801_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v___y_2789_);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___y_2792_);
return v___x_2807_;
}
else
{
lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = lean_nat_sub(v___x_2805_, v___y_2795_);
v___x_2809_ = lean_nat_dec_le(v_zero_2758_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec(v___x_2808_);
lean_del_object(v___x_2803_);
lean_dec_ref(v_children_2801_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v___y_2789_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v___y_2792_);
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2811_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___closed__0));
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 0);
lean_ctor_set(v___x_2803_, 1, v___x_2811_);
lean_ctor_set(v___x_2803_, 0, v___y_2794_);
v___x_2813_ = v___x_2803_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___y_2794_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0_spec__0___redArg(v_children_2801_, v___x_2813_, v_zero_2758_, v___x_2808_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_children_2801_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v___x_2815_; 
lean_dec_ref(v___y_2790_);
lean_dec_ref(v___y_2789_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___y_2792_);
return v___x_2815_;
}
else
{
lean_object* v_val_2816_; lean_object* v_snd_2817_; 
v_val_2816_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v___x_2814_, 1);
v_snd_2817_ = lean_ctor_get(v_val_2816_, 1);
lean_inc(v_snd_2817_);
lean_dec(v_val_2816_);
v___y_2776_ = v___y_2787_;
v___y_2777_ = v___y_2788_;
v___y_2778_ = v___y_2790_;
v___y_2779_ = v___y_2789_;
v___y_2780_ = v___y_2791_;
v___y_2781_ = v___y_2792_;
v___y_2782_ = v___y_2793_;
v_val_2783_ = v_snd_2817_;
goto v___jp_2775_;
}
}
}
}
}
}
}
v___jp_2821_:
{
switch(lean_obj_tag(v_c_2739_))
{
case 2:
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v___y_2787_ = v___y_2830_;
v___y_2788_ = v___y_2828_;
v___y_2789_ = v___y_2822_;
v___y_2790_ = v___y_2823_;
v___y_2791_ = v___y_2829_;
v___y_2792_ = v_result_2826_;
v___y_2793_ = v___y_2827_;
v___y_2794_ = v___y_2824_;
v___y_2795_ = v___y_2825_;
v_val_2796_ = v___x_2831_;
goto v___jp_2786_;
}
case 3:
{
lean_object* v___x_2832_; 
v___x_2832_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v___y_2787_ = v___y_2830_;
v___y_2788_ = v___y_2828_;
v___y_2789_ = v___y_2822_;
v___y_2790_ = v___y_2823_;
v___y_2791_ = v___y_2829_;
v___y_2792_ = v_result_2826_;
v___y_2793_ = v___y_2827_;
v___y_2794_ = v___y_2824_;
v___y_2795_ = v___y_2825_;
v_val_2796_ = v___x_2832_;
goto v___jp_2786_;
}
default: 
{
v___y_2787_ = v___y_2830_;
v___y_2788_ = v___y_2828_;
v___y_2789_ = v___y_2822_;
v___y_2790_ = v___y_2823_;
v___y_2791_ = v___y_2829_;
v___y_2792_ = v_result_2826_;
v___y_2793_ = v___y_2827_;
v___y_2794_ = v___y_2824_;
v___y_2795_ = v___y_2825_;
v_val_2796_ = v_c_2739_;
goto v___jp_2786_;
}
}
}
v___jp_2833_:
{
lean_object* v___x_2839_; 
lean_inc_ref(v___y_2835_);
v___x_2839_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2758_, v___y_2835_, v_val_2838_, v_result_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___y_2822_ = v___y_2835_;
v___y_2823_ = v___y_2834_;
v___y_2824_ = v___y_2836_;
v___y_2825_ = v___y_2837_;
v_result_2826_ = v_a_2840_;
v___y_2827_ = v_a_2741_;
v___y_2828_ = v_a_2742_;
v___y_2829_ = v_a_2743_;
v___y_2830_ = v_a_2744_;
goto v___jp_2821_;
}
else
{
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v_c_2739_);
return v___x_2839_;
}
}
v___jp_2841_:
{
if (lean_obj_tag(v_val_2846_) == 0)
{
lean_object* v_key_2847_; lean_object* v_child_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_key_2847_ = lean_ctor_get(v_val_2846_, 0);
lean_inc(v_key_2847_);
v_child_2848_ = lean_ctor_get(v_val_2846_, 1);
lean_inc_ref(v_child_2848_);
lean_dec_ref_known(v_val_2846_, 2);
v___x_2849_ = lean_box(0);
v___x_2850_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2847_, v___x_2849_);
lean_dec(v_key_2847_);
if (v___x_2850_ == 0)
{
lean_dec_ref(v_child_2848_);
v___y_2822_ = v___y_2843_;
v___y_2823_ = v___y_2842_;
v___y_2824_ = v___y_2844_;
v___y_2825_ = v___y_2845_;
v_result_2826_ = v_result_2740_;
v___y_2827_ = v_a_2741_;
v___y_2828_ = v_a_2742_;
v___y_2829_ = v_a_2743_;
v___y_2830_ = v_a_2744_;
goto v___jp_2821_;
}
else
{
v___y_2834_ = v___y_2842_;
v___y_2835_ = v___y_2843_;
v___y_2836_ = v___y_2844_;
v___y_2837_ = v___y_2845_;
v_val_2838_ = v_child_2848_;
goto v___jp_2833_;
}
}
else
{
lean_object* v_children_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_children_2851_ = lean_ctor_get(v_val_2846_, 1);
lean_inc_ref(v_children_2851_);
lean_dec_ref_known(v_val_2846_, 2);
v___x_2852_ = lean_array_get_size(v_children_2851_);
v___x_2853_ = lean_nat_dec_lt(v_zero_2758_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_dec_ref(v_children_2851_);
v___y_2822_ = v___y_2843_;
v___y_2823_ = v___y_2842_;
v___y_2824_ = v___y_2844_;
v___y_2825_ = v___y_2845_;
v_result_2826_ = v_result_2740_;
v___y_2827_ = v_a_2741_;
v___y_2828_ = v_a_2742_;
v___y_2829_ = v_a_2743_;
v___y_2830_ = v_a_2744_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2854_; lean_object* v_fst_2855_; lean_object* v_snd_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2854_ = lean_array_fget(v_children_2851_, v_zero_2758_);
lean_dec_ref(v_children_2851_);
v_fst_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_fst_2855_);
v_snd_2856_ = lean_ctor_get(v___x_2854_, 1);
lean_inc(v_snd_2856_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v___x_2858_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2855_, v___x_2857_);
lean_dec(v_fst_2855_);
if (v___x_2858_ == 0)
{
lean_dec(v_snd_2856_);
v___y_2822_ = v___y_2843_;
v___y_2823_ = v___y_2842_;
v___y_2824_ = v___y_2844_;
v___y_2825_ = v___y_2845_;
v_result_2826_ = v_result_2740_;
v___y_2827_ = v_a_2741_;
v___y_2828_ = v_a_2742_;
v___y_2829_ = v_a_2743_;
v___y_2830_ = v_a_2744_;
goto v___jp_2821_;
}
else
{
v___y_2834_ = v___y_2842_;
v___y_2835_ = v___y_2843_;
v___y_2836_ = v___y_2844_;
v___y_2837_ = v___y_2845_;
v_val_2838_ = v_snd_2856_;
goto v___jp_2833_;
}
}
}
}
}
else
{
lean_object* v_one_2894_; lean_object* v_n_2895_; lean_object* v_val_2897_; 
v_one_2894_ = lean_unsigned_to_nat(1u);
v_n_2895_ = lean_nat_sub(v_skip_2737_, v_one_2894_);
lean_dec(v_skip_2737_);
switch(lean_obj_tag(v_c_2739_))
{
case 2:
{
lean_object* v___x_2910_; 
v___x_2910_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v_val_2897_ = v___x_2910_;
goto v___jp_2896_;
}
case 3:
{
lean_object* v___x_2911_; 
v___x_2911_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2739_);
v_val_2897_ = v___x_2911_;
goto v___jp_2896_;
}
default: 
{
v_val_2897_ = v_c_2739_;
goto v___jp_2896_;
}
}
v___jp_2896_:
{
if (lean_obj_tag(v_val_2897_) == 0)
{
lean_object* v_key_2898_; lean_object* v_child_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_key_2898_ = lean_ctor_get(v_val_2897_, 0);
lean_inc(v_key_2898_);
v_child_2899_ = lean_ctor_get(v_val_2897_, 1);
lean_inc_ref(v_child_2899_);
lean_dec_ref_known(v_val_2897_, 2);
v___x_2900_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2898_);
lean_dec(v_key_2898_);
v___x_2901_ = lean_nat_add(v_n_2895_, v___x_2900_);
lean_dec(v___x_2900_);
lean_dec(v_n_2895_);
v_skip_2737_ = v___x_2901_;
v_c_2739_ = v_child_2899_;
goto _start;
}
else
{
lean_object* v_children_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_children_2903_ = lean_ctor_get(v_val_2897_, 1);
lean_inc_ref(v_children_2903_);
lean_dec_ref_known(v_val_2897_, 2);
v___x_2904_ = lean_array_get_size(v_children_2903_);
v___x_2905_ = lean_nat_dec_lt(v_zero_2758_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_dec_ref(v_children_2903_);
lean_dec(v_n_2895_);
lean_dec_ref(v_todo_2738_);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_result_2740_);
return v___x_2906_;
}
else
{
size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = lean_usize_of_nat(v___x_2904_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2895_, v_todo_2738_, v_children_2903_, v___x_2907_, v___x_2908_, v_result_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
lean_dec_ref(v_children_2903_);
lean_dec(v_n_2895_);
return v___x_2909_;
}
}
}
}
}
v___jp_2746_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = l_Array_append___redArg(v_result_2740_, v___y_2747_);
lean_dec_ref(v___y_2747_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
v___jp_2750_:
{
if (lean_obj_tag(v_val_2751_) == 0)
{
lean_object* v___x_2752_; 
lean_dec_ref_known(v_val_2751_, 2);
v___x_2752_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_2747_ = v___x_2752_;
goto v___jp_2746_;
}
else
{
lean_object* v_vs_2753_; 
v_vs_2753_ = lean_ctor_get(v_val_2751_, 0);
lean_inc_ref(v_vs_2753_);
lean_dec_ref_known(v_val_2751_, 2);
v___y_2747_ = v_vs_2753_;
goto v___jp_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(lean_object* v_todo_2912_, lean_object* v_as_2913_, size_t v_i_2914_, size_t v_stop_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_usize_dec_eq(v_i_2914_, v_stop_2915_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v_fst_2924_; lean_object* v_snd_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2923_ = lean_array_uget_borrowed(v_as_2913_, v_i_2914_);
v_fst_2924_ = lean_ctor_get(v___x_2923_, 0);
v_snd_2925_ = lean_ctor_get(v___x_2923_, 1);
v___x_2926_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2924_);
lean_inc(v_snd_2925_);
lean_inc_ref(v_todo_2912_);
v___x_2927_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2926_, v_todo_2912_, v_snd_2925_, v_b_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; size_t v___x_2929_; size_t v___x_2930_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = ((size_t)1ULL);
v___x_2930_ = lean_usize_add(v_i_2914_, v___x_2929_);
v_i_2914_ = v___x_2930_;
v_b_2916_ = v_a_2928_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2912_);
return v___x_2927_;
}
}
else
{
lean_object* v___x_2932_; 
lean_dec_ref(v_todo_2912_);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_b_2916_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg___boxed(lean_object* v_todo_2933_, lean_object* v_as_2934_, lean_object* v_i_2935_, lean_object* v_stop_2936_, lean_object* v_b_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
size_t v_i_boxed_2943_; size_t v_stop_boxed_2944_; lean_object* v_res_2945_; 
v_i_boxed_2943_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_stop_boxed_2944_ = lean_unbox_usize(v_stop_2936_);
lean_dec(v_stop_2936_);
v_res_2945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(v_todo_2933_, v_as_2934_, v_i_boxed_2943_, v_stop_boxed_2944_, v_b_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v_as_2934_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2946_, lean_object* v_as_2947_, lean_object* v_i_2948_, lean_object* v_stop_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
size_t v_i_boxed_2956_; size_t v_stop_boxed_2957_; lean_object* v_res_2958_; 
v_i_boxed_2956_ = lean_unbox_usize(v_i_2948_);
lean_dec(v_i_2948_);
v_stop_boxed_2957_ = lean_unbox_usize(v_stop_2949_);
lean_dec(v_stop_2949_);
v_res_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2946_, v_as_2947_, v_i_boxed_2956_, v_stop_boxed_2957_, v_b_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_as_2947_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg___boxed(lean_object* v_n_2959_, lean_object* v_todo_2960_, lean_object* v_as_2961_, lean_object* v_i_2962_, lean_object* v_stop_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
size_t v_i_boxed_2970_; size_t v_stop_boxed_2971_; lean_object* v_res_2972_; 
v_i_boxed_2970_ = lean_unbox_usize(v_i_2962_);
lean_dec(v_i_2962_);
v_stop_boxed_2971_ = lean_unbox_usize(v_stop_2963_);
lean_dec(v_stop_2963_);
v_res_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(v_n_2959_, v_todo_2960_, v_as_2961_, v_i_boxed_2970_, v_stop_boxed_2971_, v_b_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v_as_2961_);
lean_dec(v_n_2959_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2973_, lean_object* v_todo_2974_, lean_object* v_as_2975_, lean_object* v_i_2976_, lean_object* v_stop_2977_, lean_object* v_b_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
size_t v_i_boxed_2984_; size_t v_stop_boxed_2985_; lean_object* v_res_2986_; 
v_i_boxed_2984_ = lean_unbox_usize(v_i_2976_);
lean_dec(v_i_2976_);
v_stop_boxed_2985_ = lean_unbox_usize(v_stop_2977_);
lean_dec(v_stop_2977_);
v_res_2986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2973_, v_todo_2974_, v_as_2975_, v_i_boxed_2984_, v_stop_boxed_2985_, v_b_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v_as_2975_);
lean_dec(v_n_2973_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2987_, lean_object* v_todo_2988_, lean_object* v_c_2989_, lean_object* v_result_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2987_, v_todo_2988_, v_c_2989_, v_result_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2997_, lean_object* v_skip_2998_, lean_object* v_todo_2999_, lean_object* v_c_3000_, lean_object* v_result_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2998_, v_todo_2999_, v_c_3000_, v_result_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_3008_, lean_object* v_skip_3009_, lean_object* v_todo_3010_, lean_object* v_c_3011_, lean_object* v_result_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_3008_, v_skip_3009_, v_todo_3010_, v_c_3011_, v_result_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_3019_, lean_object* v_todo_3020_, lean_object* v_as_3021_, size_t v_i_3022_, size_t v_stop_3023_, lean_object* v_b_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_3020_, v_as_3021_, v_i_3022_, v_stop_3023_, v_b_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_3031_, lean_object* v_todo_3032_, lean_object* v_as_3033_, lean_object* v_i_3034_, lean_object* v_stop_3035_, lean_object* v_b_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
size_t v_i_boxed_3042_; size_t v_stop_boxed_3043_; lean_object* v_res_3044_; 
v_i_boxed_3042_ = lean_unbox_usize(v_i_3034_);
lean_dec(v_i_3034_);
v_stop_boxed_3043_ = lean_unbox_usize(v_stop_3035_);
lean_dec(v_stop_3035_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_3031_, v_todo_3032_, v_as_3033_, v_i_boxed_3042_, v_stop_boxed_3043_, v_b_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec_ref(v_as_3033_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_3045_, lean_object* v_n_3046_, lean_object* v_todo_3047_, lean_object* v_as_3048_, size_t v_i_3049_, size_t v_stop_3050_, lean_object* v_b_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_3046_, v_todo_3047_, v_as_3048_, v_i_3049_, v_stop_3050_, v_b_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_3058_, lean_object* v_n_3059_, lean_object* v_todo_3060_, lean_object* v_as_3061_, lean_object* v_i_3062_, lean_object* v_stop_3063_, lean_object* v_b_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
size_t v_i_boxed_3070_; size_t v_stop_boxed_3071_; lean_object* v_res_3072_; 
v_i_boxed_3070_ = lean_unbox_usize(v_i_3062_);
lean_dec(v_i_3062_);
v_stop_boxed_3071_ = lean_unbox_usize(v_stop_3063_);
lean_dec(v_stop_3063_);
v_res_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_3058_, v_n_3059_, v_todo_3060_, v_as_3061_, v_i_boxed_3070_, v_stop_boxed_3071_, v_b_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec_ref(v_as_3061_);
lean_dec(v_n_3059_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0(lean_object* v_00_u03b1_3073_, lean_object* v_todo_3074_, lean_object* v_as_3075_, size_t v_i_3076_, size_t v_stop_3077_, lean_object* v_b_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(v_todo_3074_, v_as_3075_, v_i_3076_, v_stop_3077_, v_b_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_todo_3086_, lean_object* v_as_3087_, lean_object* v_i_3088_, lean_object* v_stop_3089_, lean_object* v_b_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
size_t v_i_boxed_3096_; size_t v_stop_boxed_3097_; lean_object* v_res_3098_; 
v_i_boxed_3096_ = lean_unbox_usize(v_i_3088_);
lean_dec(v_i_3088_);
v_stop_boxed_3097_ = lean_unbox_usize(v_stop_3089_);
lean_dec(v_stop_3089_);
v_res_3098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0(v_00_u03b1_3085_, v_todo_3086_, v_as_3087_, v_i_boxed_3096_, v_stop_boxed_3097_, v_b_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec_ref(v_as_3087_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2(lean_object* v_00_u03b1_3099_, lean_object* v_n_3100_, lean_object* v_todo_3101_, lean_object* v_as_3102_, size_t v_i_3103_, size_t v_stop_3104_, lean_object* v_b_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(v_n_3100_, v_todo_3101_, v_as_3102_, v_i_3103_, v_stop_3104_, v_b_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3112_, lean_object* v_n_3113_, lean_object* v_todo_3114_, lean_object* v_as_3115_, lean_object* v_i_3116_, lean_object* v_stop_3117_, lean_object* v_b_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
size_t v_i_boxed_3124_; size_t v_stop_boxed_3125_; lean_object* v_res_3126_; 
v_i_boxed_3124_ = lean_unbox_usize(v_i_3116_);
lean_dec(v_i_3116_);
v_stop_boxed_3125_ = lean_unbox_usize(v_stop_3117_);
lean_dec(v_stop_3117_);
v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2(v_00_u03b1_3112_, v_n_3113_, v_todo_3114_, v_as_3115_, v_i_boxed_3124_, v_stop_boxed_3125_, v_b_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec_ref(v_as_3115_);
lean_dec(v_n_3113_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_3127_, lean_object* v_k_3128_, lean_object* v_c_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_3128_);
v___x_3136_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_3137_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_3135_, v___x_3136_, v_c_3129_, v_result_3127_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_3138_, lean_object* v_k_3139_, lean_object* v_c_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_3138_, v_k_3139_, v_c_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v_k_3139_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_3147_, lean_object* v_keys_3148_, lean_object* v_vals_3149_, lean_object* v_i_3150_, lean_object* v_acc_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = lean_array_get_size(v_keys_3148_);
v___x_3158_ = lean_nat_dec_lt(v_i_3150_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
lean_dec(v_i_3150_);
lean_dec_ref(v_f_3147_);
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_acc_3151_);
return v___x_3159_;
}
else
{
lean_object* v_k_3160_; lean_object* v_v_3161_; lean_object* v___x_3162_; 
v_k_3160_ = lean_array_fget_borrowed(v_keys_3148_, v_i_3150_);
v_v_3161_ = lean_array_fget_borrowed(v_vals_3149_, v_i_3150_);
lean_inc_ref(v_f_3147_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
lean_inc(v_v_3161_);
lean_inc(v_k_3160_);
v___x_3162_ = lean_apply_8(v_f_3147_, v_acc_3151_, v_k_3160_, v_v_3161_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, lean_box(0));
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_nat_add(v_i_3150_, v___x_3164_);
lean_dec(v_i_3150_);
v_i_3150_ = v___x_3165_;
v_acc_3151_ = v_a_3163_;
goto _start;
}
else
{
lean_dec(v_i_3150_);
lean_dec_ref(v_f_3147_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_3167_, lean_object* v_keys_3168_, lean_object* v_vals_3169_, lean_object* v_i_3170_, lean_object* v_acc_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3167_, v_keys_3168_, v_vals_3169_, v_i_3170_, v_acc_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v_vals_3169_);
lean_dec_ref(v_keys_3168_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3178_, lean_object* v_as_3179_, size_t v_i_3180_, size_t v_stop_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_a_3189_; lean_object* v___y_3194_; uint8_t v___x_3196_; 
v___x_3196_ = lean_usize_dec_eq(v_i_3180_, v_stop_3181_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_array_uget_borrowed(v_as_3179_, v_i_3180_);
switch(lean_obj_tag(v___x_3197_))
{
case 0:
{
lean_object* v_key_3198_; lean_object* v_val_3199_; lean_object* v___x_3200_; 
v_key_3198_ = lean_ctor_get(v___x_3197_, 0);
v_val_3199_ = lean_ctor_get(v___x_3197_, 1);
lean_inc_ref(v_f_3178_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
lean_inc(v_val_3199_);
lean_inc(v_key_3198_);
v___x_3200_ = lean_apply_8(v_f_3178_, v_b_3182_, v_key_3198_, v_val_3199_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, lean_box(0));
v___y_3194_ = v___x_3200_;
goto v___jp_3193_;
}
case 1:
{
lean_object* v_node_3201_; lean_object* v___x_3202_; 
v_node_3201_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_node_3201_);
lean_inc_ref(v_f_3178_);
v___x_3202_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3178_, v_node_3201_, v_b_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
v___y_3194_ = v___x_3202_;
goto v___jp_3193_;
}
default: 
{
v_a_3189_ = v_b_3182_;
goto v___jp_3188_;
}
}
}
else
{
lean_object* v___x_3203_; 
lean_dec_ref(v_f_3178_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_b_3182_);
return v___x_3203_;
}
v___jp_3188_:
{
size_t v___x_3190_; size_t v___x_3191_; 
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_add(v_i_3180_, v___x_3190_);
v_i_3180_ = v___x_3191_;
v_b_3182_ = v_a_3189_;
goto _start;
}
v___jp_3193_:
{
if (lean_obj_tag(v___y_3194_) == 0)
{
lean_object* v_a_3195_; 
v_a_3195_ = lean_ctor_get(v___y_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___y_3194_, 1);
v_a_3189_ = v_a_3195_;
goto v___jp_3188_;
}
else
{
lean_dec_ref(v_f_3178_);
return v___y_3194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_3204_, lean_object* v_x_3205_, lean_object* v_x_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
if (lean_obj_tag(v_x_3205_) == 0)
{
lean_object* v_es_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3225_; 
v_es_3212_ = lean_ctor_get(v_x_3205_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_x_3205_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3214_ = v_x_3205_;
v_isShared_3215_ = v_isSharedCheck_3225_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_es_3212_);
lean_dec(v_x_3205_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3225_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3216_ = lean_unsigned_to_nat(0u);
v___x_3217_ = lean_array_get_size(v_es_3212_);
v___x_3218_ = lean_nat_dec_lt(v___x_3216_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3220_; 
lean_dec_ref(v_es_3212_);
lean_dec_ref(v_f_3204_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v_x_3206_);
v___x_3220_ = v___x_3214_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_x_3206_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
else
{
size_t v___x_3222_; size_t v___x_3223_; lean_object* v___x_3224_; 
lean_del_object(v___x_3214_);
v___x_3222_ = ((size_t)0ULL);
v___x_3223_ = lean_usize_of_nat(v___x_3217_);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3204_, v_es_3212_, v___x_3222_, v___x_3223_, v_x_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v_es_3212_);
return v___x_3224_;
}
}
}
else
{
lean_object* v_ks_3226_; lean_object* v_vs_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_ks_3226_ = lean_ctor_get(v_x_3205_, 0);
lean_inc_ref(v_ks_3226_);
v_vs_3227_ = lean_ctor_get(v_x_3205_, 1);
lean_inc_ref(v_vs_3227_);
lean_dec_ref_known(v_x_3205_, 2);
v___x_3228_ = lean_unsigned_to_nat(0u);
v___x_3229_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3204_, v_ks_3226_, v_vs_3227_, v___x_3228_, v_x_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v_vs_3227_);
lean_dec_ref(v_ks_3226_);
return v___x_3229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3230_, v_x_3231_, v_x_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3239_, lean_object* v_as_3240_, lean_object* v_i_3241_, lean_object* v_stop_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
size_t v_i_boxed_3249_; size_t v_stop_boxed_3250_; lean_object* v_res_3251_; 
v_i_boxed_3249_ = lean_unbox_usize(v_i_3241_);
lean_dec(v_i_3241_);
v_stop_boxed_3250_ = lean_unbox_usize(v_stop_3242_);
lean_dec(v_stop_3242_);
v_res_3251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3239_, v_as_3240_, v_i_boxed_3249_, v_stop_boxed_3250_, v_b_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v_as_3240_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(lean_object* v_e_3252_, uint8_t v___x_3253_, lean_object* v___f_3254_, lean_object* v_d_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
uint8_t v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = 0;
v___x_3262_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_3252_, v___x_3261_, v___x_3253_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3279_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3265_ = v___x_3262_;
v_isShared_3266_ = v_isSharedCheck_3279_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3279_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_fst_3267_; 
v_fst_3267_ = lean_ctor_get(v_a_3263_, 0);
lean_inc(v_fst_3267_);
if (lean_obj_tag(v_fst_3267_) == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_del_object(v___x_3265_);
lean_dec(v_a_3263_);
v___x_3268_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_3269_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_3254_, v_d_3255_, v___x_3268_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
return v___x_3269_;
}
else
{
lean_object* v_snd_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec_ref(v___f_3254_);
v_snd_3270_ = lean_ctor_get(v_a_3263_, 1);
lean_inc(v_snd_3270_);
lean_dec(v_a_3263_);
v___x_3271_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_3255_);
v___x_3272_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_3255_, v_fst_3267_);
lean_dec(v_fst_3267_);
lean_dec_ref(v_d_3255_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v___x_3274_; 
lean_dec(v_snd_3270_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3271_);
v___x_3274_ = v___x_3265_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3271_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
else
{
lean_object* v_val_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_del_object(v___x_3265_);
v_val_3276_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_val_3276_);
lean_dec_ref_known(v___x_3272_, 1);
v___x_3277_ = lean_unsigned_to_nat(0u);
v___x_3278_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_3277_, v_snd_3270_, v_val_3276_, v___x_3271_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
return v___x_3278_;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v_d_3255_);
lean_dec_ref(v___f_3254_);
v_a_3280_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3262_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3262_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1___boxed(lean_object* v_e_3288_, lean_object* v___x_3289_, lean_object* v___f_3290_, lean_object* v_d_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v___x_1524__boxed_3297_; lean_object* v_res_3298_; 
v___x_1524__boxed_3297_ = lean_unbox(v___x_3289_);
v_res_3298_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_3288_, v___x_1524__boxed_3297_, v___f_3290_, v_d_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_3300_, lean_object* v_e_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v___y_3308_; lean_object* v___x_3325_; uint8_t v_transparency_3326_; lean_object* v___f_3327_; uint8_t v___x_3328_; uint8_t v___x_3329_; uint8_t v___x_3330_; 
v___x_3325_ = l_Lean_Meta_Context_config(v_a_3302_);
v_transparency_3326_ = lean_ctor_get_uint8(v___x_3325_, 9);
lean_dec_ref(v___x_3325_);
v___f_3327_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_3328_ = 1;
v___x_3329_ = 2;
v___x_3330_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3326_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_object* v_keyedConfig_3331_; uint8_t v_trackZetaDelta_3332_; lean_object* v_zetaDeltaSet_3333_; lean_object* v_lctx_3334_; lean_object* v_localInstances_3335_; lean_object* v_defEqCtx_x3f_3336_; lean_object* v_synthPendingDepth_3337_; lean_object* v_customCanUnfoldPredicate_x3f_3338_; uint8_t v_univApprox_3339_; uint8_t v_inTypeClassResolution_3340_; uint8_t v_cacheInferType_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_keyedConfig_3331_ = lean_ctor_get(v_a_3302_, 0);
v_trackZetaDelta_3332_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7);
v_zetaDeltaSet_3333_ = lean_ctor_get(v_a_3302_, 1);
v_lctx_3334_ = lean_ctor_get(v_a_3302_, 2);
v_localInstances_3335_ = lean_ctor_get(v_a_3302_, 3);
v_defEqCtx_x3f_3336_ = lean_ctor_get(v_a_3302_, 4);
v_synthPendingDepth_3337_ = lean_ctor_get(v_a_3302_, 5);
v_customCanUnfoldPredicate_x3f_3338_ = lean_ctor_get(v_a_3302_, 6);
v_univApprox_3339_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3340_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7 + 2);
v_cacheInferType_3341_ = lean_ctor_get_uint8(v_a_3302_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3331_);
v___x_3342_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3329_, v_keyedConfig_3331_);
lean_inc(v_customCanUnfoldPredicate_x3f_3338_);
lean_inc(v_synthPendingDepth_3337_);
lean_inc(v_defEqCtx_x3f_3336_);
lean_inc_ref(v_localInstances_3335_);
lean_inc_ref(v_lctx_3334_);
lean_inc(v_zetaDeltaSet_3333_);
v___x_3343_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
lean_ctor_set(v___x_3343_, 1, v_zetaDeltaSet_3333_);
lean_ctor_set(v___x_3343_, 2, v_lctx_3334_);
lean_ctor_set(v___x_3343_, 3, v_localInstances_3335_);
lean_ctor_set(v___x_3343_, 4, v_defEqCtx_x3f_3336_);
lean_ctor_set(v___x_3343_, 5, v_synthPendingDepth_3337_);
lean_ctor_set(v___x_3343_, 6, v_customCanUnfoldPredicate_x3f_3338_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7, v_trackZetaDelta_3332_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 1, v_univApprox_3339_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3340_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 3, v_cacheInferType_3341_);
v___x_3344_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_3301_, v___x_3328_, v___f_3327_, v_d_3300_, v___x_3343_, v_a_3303_, v_a_3304_, v_a_3305_);
lean_dec_ref_known(v___x_3343_, 7);
v___y_3308_ = v___x_3344_;
goto v___jp_3307_;
}
else
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_3301_, v___x_3328_, v___f_3327_, v_d_3300_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
v___y_3308_ = v___x_3345_;
goto v___jp_3307_;
}
v___jp_3307_:
{
if (lean_obj_tag(v___y_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_a_3309_ = lean_ctor_get(v___y_3308_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___y_3308_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___y_3308_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___y_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___y_3308_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___y_3308_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___y_3308_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___y_3308_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_3346_, lean_object* v_e_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_3346_, v_e_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_3354_, lean_object* v_d_3355_, lean_object* v_e_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_3355_, v_e_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_3363_, lean_object* v_d_3364_, lean_object* v_e_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_3363_, v_d_3364_, v_e_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_3372_, lean_object* v_f_3373_, lean_object* v_init_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3373_, v_map_3372_, v_init_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_3381_, lean_object* v_f_3382_, lean_object* v_init_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_3381_, v_f_3382_, v_init_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_3390_, lean_object* v_00_u03b2_3391_, lean_object* v_map_3392_, lean_object* v_f_3393_, lean_object* v_init_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3393_, v_map_3392_, v_init_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_3401_, lean_object* v_00_u03b2_3402_, lean_object* v_map_3403_, lean_object* v_f_3404_, lean_object* v_init_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_3401_, v_00_u03b2_3402_, v_map_3403_, v_f_3404_, v_init_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_3412_, lean_object* v_00_u03b1_3413_, lean_object* v_00_u03b2_3414_, lean_object* v_f_3415_, lean_object* v_x_3416_, lean_object* v_x_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3415_, v_x_3416_, v_x_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3424_, lean_object* v_00_u03b1_3425_, lean_object* v_00_u03b2_3426_, lean_object* v_f_3427_, lean_object* v_x_3428_, lean_object* v_x_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_3424_, v_00_u03b1_3425_, v_00_u03b2_3426_, v_f_3427_, v_x_3428_, v_x_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3436_, lean_object* v_00_u03b2_3437_, lean_object* v_00_u03c3_3438_, lean_object* v_f_3439_, lean_object* v_as_3440_, size_t v_i_3441_, size_t v_stop_3442_, lean_object* v_b_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3439_, v_as_3440_, v_i_3441_, v_stop_3442_, v_b_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3450_, lean_object* v_00_u03b2_3451_, lean_object* v_00_u03c3_3452_, lean_object* v_f_3453_, lean_object* v_as_3454_, lean_object* v_i_3455_, lean_object* v_stop_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
size_t v_i_boxed_3463_; size_t v_stop_boxed_3464_; lean_object* v_res_3465_; 
v_i_boxed_3463_ = lean_unbox_usize(v_i_3455_);
lean_dec(v_i_3455_);
v_stop_boxed_3464_ = lean_unbox_usize(v_stop_3456_);
lean_dec(v_stop_3456_);
v_res_3465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_3450_, v_00_u03b2_3451_, v_00_u03c3_3452_, v_f_3453_, v_as_3454_, v_i_boxed_3463_, v_stop_boxed_3464_, v_b_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v_as_3454_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_3466_, lean_object* v_00_u03b1_3467_, lean_object* v_00_u03b2_3468_, lean_object* v_f_3469_, lean_object* v_keys_3470_, lean_object* v_vals_3471_, lean_object* v_heq_3472_, lean_object* v_i_3473_, lean_object* v_acc_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3469_, v_keys_3470_, v_vals_3471_, v_i_3473_, v_acc_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_3481_, lean_object* v_00_u03b1_3482_, lean_object* v_00_u03b2_3483_, lean_object* v_f_3484_, lean_object* v_keys_3485_, lean_object* v_vals_3486_, lean_object* v_heq_3487_, lean_object* v_i_3488_, lean_object* v_acc_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_3481_, v_00_u03b1_3482_, v_00_u03b2_3483_, v_f_3484_, v_keys_3485_, v_vals_3486_, v_heq_3487_, v_i_3488_, v_acc_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v_vals_3486_);
lean_dec_ref(v_keys_3485_);
return v_res_3495_;
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
