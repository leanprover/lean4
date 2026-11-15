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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_todo_1416_, lean_object* v_ks_1417_, lean_object* v_i_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_todo_1471_, lean_object* v_ks_1472_, lean_object* v_i_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_todo_1471_, v_ks_1472_, v_i_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec_ref(v_ks_1472_);
return v_res_1479_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___lam__0(lean_object* v_a_1480_, lean_object* v_b_1481_){
_start:
{
lean_object* v_fst_1482_; lean_object* v_fst_1483_; uint8_t v___x_1484_; 
v_fst_1482_ = lean_ctor_get(v_a_1480_, 0);
v_fst_1483_ = lean_ctor_get(v_b_1481_, 0);
v___x_1484_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1482_, v_fst_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___lam__0___boxed(lean_object* v_a_1485_, lean_object* v_b_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___lam__0(v_a_1485_, v_b_1486_);
lean_dec_ref(v_b_1486_);
lean_dec_ref(v_a_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg(lean_object* v_as_1489_, lean_object* v_k_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_m_1495_; lean_object* v_a_1496_; uint8_t v___x_1497_; 
v___x_1493_ = lean_nat_add(v_x_1491_, v_x_1492_);
v___x_1494_ = lean_unsigned_to_nat(1u);
v_m_1495_ = lean_nat_shiftr(v___x_1493_, v___x_1494_);
lean_dec(v___x_1493_);
v_a_1496_ = lean_array_fget_borrowed(v_as_1489_, v_m_1495_);
v___x_1497_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___lam__0(v_a_1496_, v_k_1490_);
if (v___x_1497_ == 0)
{
uint8_t v___x_1498_; 
lean_dec(v_x_1492_);
v___x_1498_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___lam__0(v_k_1490_, v_a_1496_);
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg___boxed(lean_object* v_as_1511_, lean_object* v_k_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg(v_as_1511_, v_k_1512_, v_x_1513_, v_x_1514_);
lean_dec_ref(v_k_1512_);
lean_dec_ref(v_as_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1518_, lean_object* v_c_1519_, lean_object* v_result_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___y_1527_; lean_object* v_val_1531_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v_val_1542_; 
if (lean_obj_tag(v_c_1519_) == 3)
{
lean_object* v_keys_1545_; lean_object* v_i_1546_; lean_object* v_v_1547_; lean_object* v___x_1548_; 
v_keys_1545_ = lean_ctor_get(v_c_1519_, 0);
lean_inc_ref(v_keys_1545_);
v_i_1546_ = lean_ctor_get(v_c_1519_, 1);
lean_inc(v_i_1546_);
v_v_1547_ = lean_ctor_get(v_c_1519_, 2);
lean_inc(v_v_1547_);
lean_dec_ref_known(v_c_1519_, 3);
v___x_1548_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_todo_1518_, v_keys_1545_, v_i_1546_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
lean_dec_ref(v_keys_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1561_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1561_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_unbox(v_a_1549_);
lean_dec(v_a_1549_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1555_; 
lean_dec(v_v_1547_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v_result_1520_);
v___x_1555_ = v___x_1551_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_result_1520_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_array_push(v_result_1520_, v_v_1547_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1557_);
v___x_1559_ = v___x_1551_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_v_1547_);
lean_dec_ref(v_result_1520_);
v_a_1562_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1548_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1548_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v_val_1582_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v_result_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v_val_1625_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v_val_1633_; uint8_t v___x_1646_; 
v___x_1570_ = lean_array_get_size(v_todo_1518_);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_nat_dec_eq(v___x_1570_, v___x_1571_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___y_1649_; lean_object* v_val_1673_; 
v___x_1647_ = l_Lean_instInhabitedExpr;
switch(lean_obj_tag(v_c_1519_))
{
case 2:
{
lean_object* v___x_1680_; 
lean_inc_ref(v_c_1519_);
v___x_1680_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1673_ = v___x_1680_;
goto v___jp_1672_;
}
case 3:
{
lean_object* v___x_1681_; 
lean_inc_ref(v_c_1519_);
v___x_1681_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1673_ = v___x_1681_;
goto v___jp_1672_;
}
default: 
{
lean_inc_ref(v_c_1519_);
v_val_1673_ = v_c_1519_;
goto v___jp_1672_;
}
}
v___jp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_e_1652_; lean_object* v_todo_1653_; lean_object* v___x_1654_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_nat_sub(v___x_1570_, v___x_1650_);
v_e_1652_ = lean_array_get(v___x_1647_, v_todo_1518_, v___x_1651_);
lean_dec(v___x_1651_);
v_todo_1653_ = lean_array_pop(v_todo_1518_);
v___x_1654_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1652_, v___y_1649_, v___x_1646_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
switch(lean_obj_tag(v_c_1519_))
{
case 2:
{
lean_object* v_fst_1656_; lean_object* v_snd_1657_; lean_object* v___x_1658_; 
v_fst_1656_ = lean_ctor_get(v_a_1655_, 0);
lean_inc(v_fst_1656_);
v_snd_1657_ = lean_ctor_get(v_a_1655_, 1);
lean_inc(v_snd_1657_);
lean_dec(v_a_1655_);
lean_inc_ref(v_c_1519_);
v___x_1658_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1629_ = v_snd_1657_;
v___y_1630_ = v_todo_1653_;
v___y_1631_ = v___x_1650_;
v___y_1632_ = v_fst_1656_;
v_val_1633_ = v___x_1658_;
goto v___jp_1628_;
}
case 3:
{
lean_object* v_fst_1659_; lean_object* v_snd_1660_; lean_object* v___x_1661_; 
v_fst_1659_ = lean_ctor_get(v_a_1655_, 0);
lean_inc(v_fst_1659_);
v_snd_1660_ = lean_ctor_get(v_a_1655_, 1);
lean_inc(v_snd_1660_);
lean_dec(v_a_1655_);
lean_inc_ref(v_c_1519_);
v___x_1661_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1629_ = v_snd_1660_;
v___y_1630_ = v_todo_1653_;
v___y_1631_ = v___x_1650_;
v___y_1632_ = v_fst_1659_;
v_val_1633_ = v___x_1661_;
goto v___jp_1628_;
}
default: 
{
lean_object* v_fst_1662_; lean_object* v_snd_1663_; 
v_fst_1662_ = lean_ctor_get(v_a_1655_, 0);
lean_inc(v_fst_1662_);
v_snd_1663_ = lean_ctor_get(v_a_1655_, 1);
lean_inc(v_snd_1663_);
lean_dec(v_a_1655_);
lean_inc_ref(v_c_1519_);
v___y_1629_ = v_snd_1663_;
v___y_1630_ = v_todo_1653_;
v___y_1631_ = v___x_1650_;
v___y_1632_ = v_fst_1662_;
v_val_1633_ = v_c_1519_;
goto v___jp_1628_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v_todo_1653_);
lean_dec_ref(v_result_1520_);
lean_dec_ref(v_c_1519_);
v_a_1664_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1654_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1654_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
v___jp_1672_:
{
if (lean_obj_tag(v_val_1673_) == 0)
{
uint8_t v___x_1674_; 
lean_dec_ref_known(v_val_1673_, 2);
v___x_1674_ = 1;
v___y_1649_ = v___x_1674_;
goto v___jp_1648_;
}
else
{
lean_object* v_children_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_children_1675_ = lean_ctor_get(v_val_1673_, 1);
lean_inc_ref(v_children_1675_);
lean_dec_ref_known(v_val_1673_, 2);
v___x_1676_ = lean_array_get_size(v_children_1675_);
lean_dec_ref(v_children_1675_);
v___x_1677_ = lean_nat_dec_eq(v___x_1676_, v___x_1571_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; 
v___x_1678_ = 1;
v___y_1649_ = v___x_1678_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1679_; 
lean_dec_ref(v_c_1519_);
lean_dec_ref(v_todo_1518_);
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_result_1520_);
return v___x_1679_;
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
lean_object* v___x_1682_; 
v___x_1682_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1531_ = v___x_1682_;
goto v___jp_1530_;
}
case 3:
{
lean_object* v___x_1683_; 
v___x_1683_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v_val_1531_ = v___x_1683_;
goto v___jp_1530_;
}
default: 
{
v_val_1531_ = v_c_1519_;
goto v___jp_1530_;
}
}
}
v___jp_1572_:
{
if (lean_obj_tag(v_val_1582_) == 0)
{
lean_object* v_key_1583_; lean_object* v_child_1584_; uint8_t v___x_1585_; 
v_key_1583_ = lean_ctor_get(v_val_1582_, 0);
lean_inc(v_key_1583_);
v_child_1584_ = lean_ctor_get(v_val_1582_, 1);
lean_inc_ref(v_child_1584_);
lean_dec_ref_known(v_val_1582_, 2);
v___x_1585_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1583_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec(v_key_1583_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref(v_child_1584_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v___y_1574_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___y_1581_);
return v___x_1586_;
}
else
{
v___y_1535_ = v___y_1573_;
v___y_1536_ = v___y_1574_;
v___y_1537_ = v___y_1575_;
v___y_1538_ = v___y_1576_;
v___y_1539_ = v___y_1578_;
v___y_1540_ = v___y_1577_;
v___y_1541_ = v___y_1581_;
v_val_1542_ = v_child_1584_;
goto v___jp_1534_;
}
}
else
{
lean_object* v_children_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1605_; 
v_children_1587_ = lean_ctor_get(v_val_1582_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_val_1582_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v_val_1582_, 0);
lean_dec(v_unused_1606_);
v___x_1589_ = v_val_1582_;
v_isShared_1590_ = v_isSharedCheck_1605_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_children_1587_);
lean_dec(v_val_1582_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1605_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_array_get_size(v_children_1587_);
v___x_1592_ = lean_nat_dec_lt(v___x_1571_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
lean_del_object(v___x_1589_);
lean_dec_ref(v_children_1587_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v___y_1574_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___y_1581_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = lean_nat_sub(v___x_1591_, v___y_1579_);
v___x_1595_ = lean_nat_dec_le(v___x_1571_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec(v___x_1594_);
lean_del_object(v___x_1589_);
lean_dec_ref(v_children_1587_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1576_);
lean_dec_ref(v___y_1574_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___y_1581_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0));
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 0);
lean_ctor_set(v___x_1589_, 1, v___x_1597_);
lean_ctor_set(v___x_1589_, 0, v___y_1580_);
v___x_1599_ = v___x_1589_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___y_1580_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg(v_children_1587_, v___x_1599_, v___x_1571_, v___x_1594_);
lean_dec_ref(v___x_1599_);
lean_dec_ref(v_children_1587_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v___y_1576_);
lean_dec_ref(v___y_1574_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___y_1581_);
return v___x_1601_;
}
else
{
lean_object* v_val_1602_; lean_object* v_snd_1603_; 
v_val_1602_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v___x_1600_, 1);
v_snd_1603_ = lean_ctor_get(v_val_1602_, 1);
lean_inc(v_snd_1603_);
lean_dec(v_val_1602_);
v___y_1535_ = v___y_1573_;
v___y_1536_ = v___y_1574_;
v___y_1537_ = v___y_1575_;
v___y_1538_ = v___y_1576_;
v___y_1539_ = v___y_1578_;
v___y_1540_ = v___y_1577_;
v___y_1541_ = v___y_1581_;
v_val_1542_ = v_snd_1603_;
goto v___jp_1534_;
}
}
}
}
}
}
}
v___jp_1607_:
{
if (lean_obj_tag(v___y_1611_) == 0)
{
lean_object* v___x_1617_; 
lean_dec_ref(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v_c_1519_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_result_1612_);
return v___x_1617_;
}
else
{
switch(lean_obj_tag(v_c_1519_))
{
case 2:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1573_ = v___y_1616_;
v___y_1574_ = v___y_1608_;
v___y_1575_ = v___y_1615_;
v___y_1576_ = v___y_1609_;
v___y_1577_ = v___y_1613_;
v___y_1578_ = v___y_1614_;
v___y_1579_ = v___y_1610_;
v___y_1580_ = v___y_1611_;
v___y_1581_ = v_result_1612_;
v_val_1582_ = v___x_1618_;
goto v___jp_1572_;
}
case 3:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1519_);
v___y_1573_ = v___y_1616_;
v___y_1574_ = v___y_1608_;
v___y_1575_ = v___y_1615_;
v___y_1576_ = v___y_1609_;
v___y_1577_ = v___y_1613_;
v___y_1578_ = v___y_1614_;
v___y_1579_ = v___y_1610_;
v___y_1580_ = v___y_1611_;
v___y_1581_ = v_result_1612_;
v_val_1582_ = v___x_1619_;
goto v___jp_1572_;
}
default: 
{
v___y_1573_ = v___y_1616_;
v___y_1574_ = v___y_1608_;
v___y_1575_ = v___y_1615_;
v___y_1576_ = v___y_1609_;
v___y_1577_ = v___y_1613_;
v___y_1578_ = v___y_1614_;
v___y_1579_ = v___y_1610_;
v___y_1580_ = v___y_1611_;
v___y_1581_ = v_result_1612_;
v_val_1582_ = v_c_1519_;
goto v___jp_1572_;
}
}
}
}
v___jp_1620_:
{
lean_object* v___x_1626_; 
lean_inc_ref(v___y_1622_);
v___x_1626_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v___y_1622_, v_val_1625_, v_result_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___y_1608_ = v___y_1621_;
v___y_1609_ = v___y_1622_;
v___y_1610_ = v___y_1623_;
v___y_1611_ = v___y_1624_;
v_result_1612_ = v_a_1627_;
v___y_1613_ = v_a_1521_;
v___y_1614_ = v_a_1522_;
v___y_1615_ = v_a_1523_;
v___y_1616_ = v_a_1524_;
goto v___jp_1607_;
}
else
{
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v_c_1519_);
return v___x_1626_;
}
}
v___jp_1628_:
{
if (lean_obj_tag(v_val_1633_) == 0)
{
lean_object* v_key_1634_; lean_object* v_child_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v_key_1634_ = lean_ctor_get(v_val_1633_, 0);
lean_inc(v_key_1634_);
v_child_1635_ = lean_ctor_get(v_val_1633_, 1);
lean_inc_ref(v_child_1635_);
lean_dec_ref_known(v_val_1633_, 2);
v___x_1636_ = lean_box(0);
v___x_1637_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_1634_, v___x_1636_);
lean_dec(v_key_1634_);
if (v___x_1637_ == 0)
{
lean_dec_ref(v_child_1635_);
v___y_1608_ = v___y_1629_;
v___y_1609_ = v___y_1630_;
v___y_1610_ = v___y_1631_;
v___y_1611_ = v___y_1632_;
v_result_1612_ = v_result_1520_;
v___y_1613_ = v_a_1521_;
v___y_1614_ = v_a_1522_;
v___y_1615_ = v_a_1523_;
v___y_1616_ = v_a_1524_;
goto v___jp_1607_;
}
else
{
v___y_1621_ = v___y_1629_;
v___y_1622_ = v___y_1630_;
v___y_1623_ = v___y_1631_;
v___y_1624_ = v___y_1632_;
v_val_1625_ = v_child_1635_;
goto v___jp_1620_;
}
}
else
{
lean_object* v_children_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_children_1638_ = lean_ctor_get(v_val_1633_, 1);
lean_inc_ref(v_children_1638_);
lean_dec_ref_known(v_val_1633_, 2);
v___x_1639_ = lean_array_get_size(v_children_1638_);
v___x_1640_ = lean_nat_dec_lt(v___x_1571_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_dec_ref(v_children_1638_);
v___y_1608_ = v___y_1629_;
v___y_1609_ = v___y_1630_;
v___y_1610_ = v___y_1631_;
v___y_1611_ = v___y_1632_;
v_result_1612_ = v_result_1520_;
v___y_1613_ = v_a_1521_;
v___y_1614_ = v_a_1522_;
v___y_1615_ = v_a_1523_;
v___y_1616_ = v_a_1524_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1641_; lean_object* v_fst_1642_; lean_object* v_snd_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1641_ = lean_array_fget(v_children_1638_, v___x_1571_);
lean_dec_ref(v_children_1638_);
v_fst_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_fst_1642_);
v_snd_1643_ = lean_ctor_get(v___x_1641_, 1);
lean_inc(v_snd_1643_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1642_, v___x_1644_);
lean_dec(v_fst_1642_);
if (v___x_1645_ == 0)
{
lean_dec(v_snd_1643_);
v___y_1608_ = v___y_1629_;
v___y_1609_ = v___y_1630_;
v___y_1610_ = v___y_1631_;
v___y_1611_ = v___y_1632_;
v_result_1612_ = v_result_1520_;
v___y_1613_ = v_a_1521_;
v___y_1614_ = v_a_1522_;
v___y_1615_ = v_a_1523_;
v___y_1616_ = v_a_1524_;
goto v___jp_1607_;
}
else
{
v___y_1621_ = v___y_1629_;
v___y_1622_ = v___y_1630_;
v___y_1623_ = v___y_1631_;
v___y_1624_ = v___y_1632_;
v_val_1625_ = v_snd_1643_;
goto v___jp_1620_;
}
}
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
if (lean_obj_tag(v_val_1531_) == 0)
{
lean_object* v___x_1532_; 
lean_dec_ref_known(v_val_1531_, 2);
v___x_1532_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_1527_ = v___x_1532_;
goto v___jp_1526_;
}
else
{
lean_object* v_vs_1533_; 
v_vs_1533_ = lean_ctor_get(v_val_1531_, 0);
lean_inc_ref(v_vs_1533_);
lean_dec_ref_known(v_val_1531_, 2);
v___y_1527_ = v_vs_1533_;
goto v___jp_1526_;
}
}
v___jp_1534_:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Array_append___redArg(v___y_1538_, v___y_1536_);
lean_dec_ref(v___y_1536_);
v_todo_1518_ = v___x_1543_;
v_c_1519_ = v_val_1542_;
v_result_1520_ = v___y_1541_;
v_a_1521_ = v___y_1540_;
v_a_1522_ = v___y_1539_;
v_a_1523_ = v___y_1537_;
v_a_1524_ = v___y_1535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1684_, lean_object* v_c_1685_, lean_object* v_result_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1684_, v_c_1685_, v_result_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1693_, lean_object* v_todo_1694_, lean_object* v_c_1695_, lean_object* v_result_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1694_, v_c_1695_, v_result_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_todo_1704_, lean_object* v_c_1705_, lean_object* v_result_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1703_, v_todo_1704_, v_c_1705_, v_result_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1(lean_object* v_00_u03b1_1713_, lean_object* v_as_1714_, lean_object* v_k_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg(v_as_1714_, v_k_1715_, v_x_1716_, v_x_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_as_1721_, lean_object* v_k_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1(v_00_u03b1_1720_, v_as_1721_, v_k_1722_, v_x_1723_, v_x_1724_, v_x_1725_);
lean_dec_ref(v_k_1722_);
lean_dec_ref(v_as_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1727_, lean_object* v_k_1728_, lean_object* v_args_1729_, lean_object* v_result_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1727_, v_k_1728_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref(v_args_1729_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_result_1730_);
return v___x_1737_;
}
else
{
lean_object* v_val_1738_; lean_object* v___x_1739_; 
v_val_1738_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1739_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1729_, v_val_1738_, v_result_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1740_, lean_object* v_k_1741_, lean_object* v_args_1742_, lean_object* v_result_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1740_, v_k_1741_, v_args_1742_, v_result_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_k_1741_);
lean_dec_ref(v_d_1740_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1750_, lean_object* v_d_1751_, lean_object* v_k_1752_, lean_object* v_args_1753_, lean_object* v_result_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1751_, v_k_1752_, v_args_1753_, v_result_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_d_1762_, lean_object* v_k_1763_, lean_object* v_args_1764_, lean_object* v_result_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1761_, v_d_1762_, v_k_1763_, v_args_1764_, v_result_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_k_1763_);
lean_dec_ref(v_d_1762_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(lean_object* v_e_1772_, uint8_t v___x_1773_, lean_object* v_result_1774_, lean_object* v_d_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1772_, v___x_1773_, v___x_1773_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1825_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1825_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1825_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v_fst_1786_; 
v_fst_1786_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_fst_1786_);
if (lean_obj_tag(v_fst_1786_) == 0)
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1796_; 
v_isSharedCheck_1796_ = !lean_is_exclusive(v_a_1782_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; lean_object* v_unused_1798_; 
v_unused_1797_ = lean_ctor_get(v_a_1782_, 1);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_a_1782_, 0);
lean_dec(v_unused_1798_);
v___x_1788_ = v_a_1782_;
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_a_1782_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v_result_1774_);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_fst_1786_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_result_1774_);
v___x_1791_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1791_);
v___x_1793_ = v___x_1784_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1823_; 
lean_del_object(v___x_1784_);
v_snd_1799_ = lean_ctor_get(v_a_1782_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_a_1782_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_a_1782_, 0);
lean_dec(v_unused_1824_);
v___x_1801_ = v_a_1782_;
v_isShared_1802_ = v_isSharedCheck_1823_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_dec(v_a_1782_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1823_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; 
v___x_1803_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1775_, v_fst_1786_, v_snd_1799_, v_result_1774_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1814_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_a_1804_);
v___x_1809_ = v___x_1801_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_fst_1786_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1809_);
v___x_1811_ = v___x_1806_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_del_object(v___x_1801_);
lean_dec(v_fst_1786_);
v_a_1815_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1803_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1803_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_result_1774_);
v_a_1826_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1781_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1781_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0___boxed(lean_object* v_e_1834_, lean_object* v___x_1835_, lean_object* v_result_1836_, lean_object* v_d_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v___x_802__boxed_1843_; lean_object* v_res_1844_; 
v___x_802__boxed_1843_ = lean_unbox(v___x_1835_);
v_res_1844_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1834_, v___x_802__boxed_1843_, v_result_1836_, v_d_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec_ref(v_d_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1845_, lean_object* v_e_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___y_1853_; lean_object* v___x_1870_; uint8_t v_transparency_1871_; lean_object* v_result_1872_; uint8_t v___x_1873_; uint8_t v___x_1874_; uint8_t v___x_1875_; 
v___x_1870_ = l_Lean_Meta_Context_config(v_a_1847_);
v_transparency_1871_ = lean_ctor_get_uint8(v___x_1870_, 9);
lean_dec_ref(v___x_1870_);
v_result_1872_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1845_);
v___x_1873_ = 1;
v___x_1874_ = 2;
v___x_1875_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1871_, v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v_keyedConfig_1876_; uint8_t v_trackZetaDelta_1877_; lean_object* v_zetaDeltaSet_1878_; lean_object* v_lctx_1879_; lean_object* v_localInstances_1880_; lean_object* v_defEqCtx_x3f_1881_; lean_object* v_synthPendingDepth_1882_; lean_object* v_customCanUnfoldPredicate_x3f_1883_; uint8_t v_univApprox_1884_; uint8_t v_inTypeClassResolution_1885_; uint8_t v_cacheInferType_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_keyedConfig_1876_ = lean_ctor_get(v_a_1847_, 0);
v_trackZetaDelta_1877_ = lean_ctor_get_uint8(v_a_1847_, sizeof(void*)*7);
v_zetaDeltaSet_1878_ = lean_ctor_get(v_a_1847_, 1);
v_lctx_1879_ = lean_ctor_get(v_a_1847_, 2);
v_localInstances_1880_ = lean_ctor_get(v_a_1847_, 3);
v_defEqCtx_x3f_1881_ = lean_ctor_get(v_a_1847_, 4);
v_synthPendingDepth_1882_ = lean_ctor_get(v_a_1847_, 5);
v_customCanUnfoldPredicate_x3f_1883_ = lean_ctor_get(v_a_1847_, 6);
v_univApprox_1884_ = lean_ctor_get_uint8(v_a_1847_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1885_ = lean_ctor_get_uint8(v_a_1847_, sizeof(void*)*7 + 2);
v_cacheInferType_1886_ = lean_ctor_get_uint8(v_a_1847_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1876_);
v___x_1887_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1874_, v_keyedConfig_1876_);
lean_inc(v_customCanUnfoldPredicate_x3f_1883_);
lean_inc(v_synthPendingDepth_1882_);
lean_inc(v_defEqCtx_x3f_1881_);
lean_inc_ref(v_localInstances_1880_);
lean_inc_ref(v_lctx_1879_);
lean_inc(v_zetaDeltaSet_1878_);
v___x_1888_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_zetaDeltaSet_1878_);
lean_ctor_set(v___x_1888_, 2, v_lctx_1879_);
lean_ctor_set(v___x_1888_, 3, v_localInstances_1880_);
lean_ctor_set(v___x_1888_, 4, v_defEqCtx_x3f_1881_);
lean_ctor_set(v___x_1888_, 5, v_synthPendingDepth_1882_);
lean_ctor_set(v___x_1888_, 6, v_customCanUnfoldPredicate_x3f_1883_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*7, v_trackZetaDelta_1877_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*7 + 1, v_univApprox_1884_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1885_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*7 + 3, v_cacheInferType_1886_);
v___x_1889_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1846_, v___x_1873_, v_result_1872_, v_d_1845_, v___x_1888_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec_ref_known(v___x_1888_, 7);
v___y_1853_ = v___x_1889_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1890_; 
v___x_1890_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___lam__0(v_e_1846_, v___x_1873_, v_result_1872_, v_d_1845_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
v___y_1853_ = v___x_1890_;
goto v___jp_1852_;
}
v___jp_1852_:
{
if (lean_obj_tag(v___y_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___y_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___y_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___y_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___y_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___y_1853_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___y_1853_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___y_1853_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___y_1853_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1891_, lean_object* v_e_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1891_, v_e_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec_ref(v_d_1891_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1899_, lean_object* v_d_1900_, lean_object* v_e_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1900_, v_e_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1908_, lean_object* v_d_1909_, lean_object* v_e_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1908_, v_d_1909_, v_e_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec_ref(v_d_1909_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1917_, lean_object* v_e_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1917_, v_e_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1933_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_snd_1929_; lean_object* v___x_1931_; 
v_snd_1929_ = lean_ctor_get(v_a_1925_, 1);
lean_inc(v_snd_1929_);
lean_dec(v_a_1925_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v_snd_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_snd_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1924_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1924_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1942_, lean_object* v_e_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1942_, v_e_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec_ref(v_d_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1950_, lean_object* v_d_1951_, lean_object* v_e_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1951_, v_e_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_d_1960_, lean_object* v_e_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1959_, v_d_1960_, v_e_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec_ref(v_d_1960_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1968_, lean_object* v_k_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_k_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; 
switch(lean_obj_tag(v_k_1969_))
{
case 4:
{
lean_object* v_a_1997_; lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2009_; 
v_a_1997_ = lean_ctor_get(v_k_1969_, 0);
v_a_1998_ = lean_ctor_get(v_k_1969_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_k_1969_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2000_ = v_k_1969_;
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_inc(v_a_1997_);
lean_dec(v_k_1969_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_zero_2002_; uint8_t v_isZero_2003_; 
v_zero_2002_ = lean_unsigned_to_nat(0u);
v_isZero_2003_ = lean_nat_dec_eq(v_a_1998_, v_zero_2002_);
if (v_isZero_2003_ == 0)
{
lean_object* v_one_2004_; lean_object* v_n_2005_; lean_object* v___x_2007_; 
v_one_2004_ = lean_unsigned_to_nat(1u);
v_n_2005_ = lean_nat_sub(v_a_1998_, v_one_2004_);
lean_dec(v_a_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v_n_2005_);
v___x_2007_ = v___x_2000_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_1997_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_n_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
v_k_1980_ = v___x_2007_;
v___y_1981_ = v_a_1970_;
v___y_1982_ = v_a_1971_;
v___y_1983_ = v_a_1972_;
v___y_1984_ = v_a_1973_;
goto v___jp_1979_;
}
}
else
{
lean_del_object(v___x_2000_);
lean_dec(v_a_1998_);
lean_dec(v_a_1997_);
goto v___jp_1975_;
}
}
}
case 3:
{
lean_object* v_a_2010_; lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2022_; 
v_a_2010_ = lean_ctor_get(v_k_1969_, 0);
v_a_2011_ = lean_ctor_get(v_k_1969_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_k_1969_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2013_ = v_k_1969_;
v_isShared_2014_ = v_isSharedCheck_2022_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
lean_dec(v_k_1969_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2022_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_zero_2015_; uint8_t v_isZero_2016_; 
v_zero_2015_ = lean_unsigned_to_nat(0u);
v_isZero_2016_ = lean_nat_dec_eq(v_a_2011_, v_zero_2015_);
if (v_isZero_2016_ == 0)
{
lean_object* v_one_2017_; lean_object* v_n_2018_; lean_object* v___x_2020_; 
v_one_2017_ = lean_unsigned_to_nat(1u);
v_n_2018_ = lean_nat_sub(v_a_2011_, v_one_2017_);
lean_dec(v_a_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_n_2018_);
v___x_2020_ = v___x_2013_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2010_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_n_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
v_k_1980_ = v___x_2020_;
v___y_1981_ = v_a_1970_;
v___y_1982_ = v_a_1971_;
v___y_1983_ = v_a_1972_;
v___y_1984_ = v_a_1973_;
goto v___jp_1979_;
}
}
else
{
lean_del_object(v___x_2013_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
goto v___jp_1975_;
}
}
}
case 6:
{
lean_object* v_a_2023_; lean_object* v_a_2024_; lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2036_; 
v_a_2023_ = lean_ctor_get(v_k_1969_, 0);
v_a_2024_ = lean_ctor_get(v_k_1969_, 1);
v_a_2025_ = lean_ctor_get(v_k_1969_, 2);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_k_1969_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2027_ = v_k_1969_;
v_isShared_2028_ = v_isSharedCheck_2036_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_inc(v_a_2024_);
lean_inc(v_a_2023_);
lean_dec(v_k_1969_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2036_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_zero_2029_; uint8_t v_isZero_2030_; 
v_zero_2029_ = lean_unsigned_to_nat(0u);
v_isZero_2030_ = lean_nat_dec_eq(v_a_2025_, v_zero_2029_);
if (v_isZero_2030_ == 0)
{
lean_object* v_one_2031_; lean_object* v_n_2032_; lean_object* v___x_2034_; 
v_one_2031_ = lean_unsigned_to_nat(1u);
v_n_2032_ = lean_nat_sub(v_a_2025_, v_one_2031_);
lean_dec(v_a_2025_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 2, v_n_2032_);
v___x_2034_ = v___x_2027_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2023_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_a_2024_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_n_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
v_k_1980_ = v___x_2034_;
v___y_1981_ = v_a_1970_;
v___y_1982_ = v_a_1971_;
v___y_1983_ = v_a_1972_;
v___y_1984_ = v_a_1973_;
goto v___jp_1979_;
}
}
else
{
lean_del_object(v___x_2027_);
lean_dec(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec(v_a_2023_);
goto v___jp_1975_;
}
}
}
default: 
{
lean_dec(v_k_1969_);
goto v___jp_1975_;
}
}
v___jp_1975_:
{
uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = 0;
v___x_1977_ = lean_box(v___x_1976_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
v___jp_1979_:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1968_, v_k_1980_);
if (lean_obj_tag(v___x_1985_) == 0)
{
v_k_1969_ = v_k_1980_;
v_a_1970_ = v___y_1981_;
v_a_1971_ = v___y_1982_;
v_a_1972_ = v___y_1983_;
v_a_1973_ = v___y_1984_;
goto _start;
}
else
{
lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_k_1980_);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1985_, 0);
lean_dec(v_unused_1996_);
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
else
{
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = 1;
v___x_1991_ = lean_box(v___x_1990_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1991_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_2037_, lean_object* v_k_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2037_, v_k_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_d_2037_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_2045_, lean_object* v_d_2046_, lean_object* v_k_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2046_, v_k_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_2054_, lean_object* v_d_2055_, lean_object* v_k_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_2054_, v_d_2055_, v_k_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec_ref(v_d_2055_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_2063_, size_t v_sz_2064_, size_t v_i_2065_, lean_object* v_bs_2066_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_usize_dec_lt(v_i_2065_, v_sz_2064_);
if (v___x_2067_ == 0)
{
lean_dec(v_numExtra_2063_);
return v_bs_2066_;
}
else
{
lean_object* v_v_2068_; lean_object* v___x_2069_; lean_object* v_bs_x27_2070_; lean_object* v___x_2071_; size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
v_v_2068_ = lean_array_uget(v_bs_2066_, v_i_2065_);
v___x_2069_ = lean_unsigned_to_nat(0u);
v_bs_x27_2070_ = lean_array_uset(v_bs_2066_, v_i_2065_, v___x_2069_);
lean_inc(v_numExtra_2063_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v_v_2068_);
lean_ctor_set(v___x_2071_, 1, v_numExtra_2063_);
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_add(v_i_2065_, v___x_2072_);
v___x_2074_ = lean_array_uset(v_bs_x27_2070_, v_i_2065_, v___x_2071_);
v_i_2065_ = v___x_2073_;
v_bs_2066_ = v___x_2074_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_2076_, lean_object* v_sz_2077_, lean_object* v_i_2078_, lean_object* v_bs_2079_){
_start:
{
size_t v_sz_boxed_2080_; size_t v_i_boxed_2081_; lean_object* v_res_2082_; 
v_sz_boxed_2080_ = lean_unbox_usize(v_sz_2077_);
lean_dec(v_sz_2077_);
v_i_boxed_2081_ = lean_unbox_usize(v_i_2078_);
lean_dec(v_i_2078_);
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2076_, v_sz_boxed_2080_, v_i_boxed_2081_, v_bs_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_2083_, lean_object* v_e_2084_, lean_object* v_numExtra_2085_, lean_object* v_result_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___x_2092_; 
lean_inc_ref(v_e_2084_);
v___x_2092_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2083_, v_e_2084_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2110_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2110_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2110_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_snd_2097_; size_t v_sz_2098_; size_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_snd_2097_ = lean_ctor_get(v_a_2093_, 1);
lean_inc(v_snd_2097_);
lean_dec(v_a_2093_);
v_sz_2098_ = lean_array_size(v_snd_2097_);
v___x_2099_ = ((size_t)0ULL);
lean_inc(v_numExtra_2085_);
v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2085_, v_sz_2098_, v___x_2099_, v_snd_2097_);
v___x_2101_ = l_Array_append___redArg(v_result_2086_, v___x_2100_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = l_Lean_Expr_isApp(v_e_2084_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2104_; 
lean_dec(v_numExtra_2085_);
lean_dec_ref(v_e_2084_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2101_);
v___x_2104_ = v___x_2095_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2101_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_del_object(v___x_2095_);
v___x_2106_ = l_Lean_Expr_appFn_x21(v_e_2084_);
lean_dec_ref(v_e_2084_);
v___x_2107_ = lean_unsigned_to_nat(1u);
v___x_2108_ = lean_nat_add(v_numExtra_2085_, v___x_2107_);
lean_dec(v_numExtra_2085_);
v_e_2084_ = v___x_2106_;
v_numExtra_2085_ = v___x_2108_;
v_result_2086_ = v___x_2101_;
goto _start;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_result_2086_);
lean_dec(v_numExtra_2085_);
lean_dec_ref(v_e_2084_);
v_a_2111_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2092_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2092_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2119_, lean_object* v_e_2120_, lean_object* v_numExtra_2121_, lean_object* v_result_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2119_, v_e_2120_, v_numExtra_2121_, v_result_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_d_2119_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2129_, lean_object* v_d_2130_, lean_object* v_e_2131_, lean_object* v_numExtra_2132_, lean_object* v_result_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2130_, v_e_2131_, v_numExtra_2132_, v_result_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2140_, lean_object* v_d_2141_, lean_object* v_e_2142_, lean_object* v_numExtra_2143_, lean_object* v_result_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2140_, v_d_2141_, v_e_2142_, v_numExtra_2143_, v_result_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec_ref(v_d_2141_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2151_, lean_object* v_numExtra_2152_, size_t v_sz_2153_, size_t v_i_2154_, lean_object* v_bs_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2152_, v_sz_2153_, v_i_2154_, v_bs_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2157_, lean_object* v_numExtra_2158_, lean_object* v_sz_2159_, lean_object* v_i_2160_, lean_object* v_bs_2161_){
_start:
{
size_t v_sz_boxed_2162_; size_t v_i_boxed_2163_; lean_object* v_res_2164_; 
v_sz_boxed_2162_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2157_, v_numExtra_2158_, v_sz_boxed_2162_, v_i_boxed_2163_, v_bs_2161_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2165_, size_t v_i_2166_, lean_object* v_bs_2167_){
_start:
{
uint8_t v___x_2168_; 
v___x_2168_ = lean_usize_dec_lt(v_i_2166_, v_sz_2165_);
if (v___x_2168_ == 0)
{
return v_bs_2167_;
}
else
{
lean_object* v_v_2169_; lean_object* v___x_2170_; lean_object* v_bs_x27_2171_; lean_object* v___x_2172_; size_t v___x_2173_; size_t v___x_2174_; lean_object* v___x_2175_; 
v_v_2169_ = lean_array_uget(v_bs_2167_, v_i_2166_);
v___x_2170_ = lean_unsigned_to_nat(0u);
v_bs_x27_2171_ = lean_array_uset(v_bs_2167_, v_i_2166_, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_v_2169_);
lean_ctor_set(v___x_2172_, 1, v___x_2170_);
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_add(v_i_2166_, v___x_2173_);
v___x_2175_ = lean_array_uset(v_bs_x27_2171_, v_i_2166_, v___x_2172_);
v_i_2166_ = v___x_2174_;
v_bs_2167_ = v___x_2175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_bs_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2180_, v_i_boxed_2181_, v_bs_2179_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2183_, lean_object* v_e_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; 
lean_inc_ref(v_e_2184_);
v___x_2190_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2183_, v_e_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2225_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2225_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2225_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_fst_2195_; lean_object* v_snd_2196_; size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_fst_2195_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_fst_2195_);
v_snd_2196_ = lean_ctor_get(v_a_2191_, 1);
lean_inc(v_snd_2196_);
lean_dec(v_a_2191_);
v_sz_2197_ = lean_array_size(v_snd_2196_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2197_, v___x_2198_, v_snd_2196_);
v___x_2200_ = l_Lean_Expr_isApp(v_e_2184_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2202_; 
lean_dec(v_fst_2195_);
lean_dec_ref(v_e_2184_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2199_);
v___x_2202_ = v___x_2193_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2199_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
else
{
lean_object* v___x_2204_; 
lean_del_object(v___x_2193_);
v___x_2204_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2183_, v_fst_2195_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2216_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2216_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2216_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_unbox(v_a_2205_);
lean_dec(v_a_2205_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2211_; 
lean_dec_ref(v_e_2184_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2199_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2199_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_del_object(v___x_2207_);
v___x_2213_ = l_Lean_Expr_appFn_x21(v_e_2184_);
lean_dec_ref(v_e_2184_);
v___x_2214_ = lean_unsigned_to_nat(1u);
v___x_2215_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2183_, v___x_2213_, v___x_2214_, v___x_2199_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
return v___x_2215_;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v___x_2199_);
lean_dec_ref(v_e_2184_);
v_a_2217_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2204_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2204_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_e_2184_);
v_a_2226_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2190_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2190_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2234_, lean_object* v_e_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2234_, v_e_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec_ref(v_d_2234_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2242_, lean_object* v_d_2243_, lean_object* v_e_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2243_, v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_d_2252_, lean_object* v_e_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2251_, v_d_2252_, v_e_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec_ref(v_d_2252_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2260_, size_t v_sz_2261_, size_t v_i_2262_, lean_object* v_bs_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2261_, v_i_2262_, v_bs_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2265_, lean_object* v_sz_2266_, lean_object* v_i_2267_, lean_object* v_bs_2268_){
_start:
{
size_t v_sz_boxed_2269_; size_t v_i_boxed_2270_; lean_object* v_res_2271_; 
v_sz_boxed_2269_ = lean_unbox_usize(v_sz_2266_);
lean_dec(v_sz_2266_);
v_i_boxed_2270_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_res_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2265_, v_sz_boxed_2269_, v_i_boxed_2270_, v_bs_2268_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
uint8_t v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = 1;
v___x_2279_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2272_, v___x_2278_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2303_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2303_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2303_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___y_2286_; lean_object* v___x_2291_; 
v___x_2284_ = l_Lean_Expr_getAppNumArgs(v_a_2280_);
v___x_2291_ = l_Lean_Expr_getAppFn(v_a_2280_);
lean_dec(v_a_2280_);
switch(lean_obj_tag(v___x_2291_))
{
case 9:
{
lean_object* v_a_2292_; lean_object* v___x_2293_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc_ref(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_a_2292_);
v___y_2286_ = v___x_2293_;
goto v___jp_2285_;
}
case 1:
{
lean_object* v_fvarId_2294_; lean_object* v___x_2295_; 
v_fvarId_2294_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_fvarId_2294_);
lean_dec_ref_known(v___x_2291_, 1);
lean_inc(v___x_2284_);
v___x_2295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_fvarId_2294_);
lean_ctor_set(v___x_2295_, 1, v___x_2284_);
v___y_2286_ = v___x_2295_;
goto v___jp_2285_;
}
case 11:
{
lean_object* v_typeName_2296_; lean_object* v_idx_2297_; lean_object* v___x_2298_; 
v_typeName_2296_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_typeName_2296_);
v_idx_2297_ = lean_ctor_get(v___x_2291_, 1);
lean_inc(v_idx_2297_);
lean_dec_ref_known(v___x_2291_, 3);
lean_inc(v___x_2284_);
v___x_2298_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2298_, 0, v_typeName_2296_);
lean_ctor_set(v___x_2298_, 1, v_idx_2297_);
lean_ctor_set(v___x_2298_, 2, v___x_2284_);
v___y_2286_ = v___x_2298_;
goto v___jp_2285_;
}
case 7:
{
lean_object* v___x_2299_; 
lean_dec_ref_known(v___x_2291_, 3);
v___x_2299_ = lean_box(5);
v___y_2286_ = v___x_2299_;
goto v___jp_2285_;
}
case 4:
{
lean_object* v_declName_2300_; lean_object* v___x_2301_; 
v_declName_2300_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_declName_2300_);
lean_dec_ref_known(v___x_2291_, 2);
lean_inc(v___x_2284_);
v___x_2301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_declName_2300_);
lean_ctor_set(v___x_2301_, 1, v___x_2284_);
v___y_2286_ = v___x_2301_;
goto v___jp_2285_;
}
default: 
{
lean_object* v___x_2302_; 
lean_dec_ref(v___x_2291_);
v___x_2302_ = lean_box(1);
v___y_2286_ = v___x_2302_;
goto v___jp_2285_;
}
}
v___jp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___y_2286_);
lean_ctor_set(v___x_2287_, 1, v___x_2284_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2287_);
v___x_2289_ = v___x_2282_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
v_a_2304_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2279_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2279_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2319_, lean_object* v_result_2320_){
_start:
{
lean_object* v___y_2322_; lean_object* v_val_2323_; lean_object* v___y_2334_; lean_object* v_val_2339_; 
if (lean_obj_tag(v_trie_2319_) == 3)
{
lean_object* v_v_2342_; lean_object* v___x_2343_; 
v_v_2342_ = lean_ctor_get(v_trie_2319_, 2);
lean_inc(v_v_2342_);
lean_dec_ref_known(v_trie_2319_, 3);
v___x_2343_ = lean_array_push(v_result_2320_, v_v_2342_);
return v___x_2343_;
}
else
{
switch(lean_obj_tag(v_trie_2319_))
{
case 2:
{
lean_object* v___x_2344_; 
lean_inc_ref(v_trie_2319_);
v___x_2344_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2319_);
v_val_2339_ = v___x_2344_;
goto v___jp_2338_;
}
case 3:
{
lean_object* v___x_2345_; 
lean_inc_ref(v_trie_2319_);
v___x_2345_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2319_);
v_val_2339_ = v___x_2345_;
goto v___jp_2338_;
}
default: 
{
lean_inc_ref(v_trie_2319_);
v_val_2339_ = v_trie_2319_;
goto v___jp_2338_;
}
}
}
v___jp_2321_:
{
if (lean_obj_tag(v_val_2323_) == 0)
{
lean_object* v_child_2324_; 
v_child_2324_ = lean_ctor_get(v_val_2323_, 1);
lean_inc_ref(v_child_2324_);
lean_dec_ref_known(v_val_2323_, 2);
v_trie_2319_ = v_child_2324_;
v_result_2320_ = v___y_2322_;
goto _start;
}
else
{
lean_object* v_children_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_children_2326_ = lean_ctor_get(v_val_2323_, 1);
lean_inc_ref(v_children_2326_);
lean_dec_ref_known(v_val_2323_, 2);
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = lean_array_get_size(v_children_2326_);
v___x_2329_ = lean_nat_dec_lt(v___x_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec_ref(v_children_2326_);
return v___y_2322_;
}
else
{
size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = lean_usize_of_nat(v___x_2328_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2326_, v___x_2330_, v___x_2331_, v___y_2322_);
lean_dec_ref(v_children_2326_);
return v___x_2332_;
}
}
}
v___jp_2333_:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Array_append___redArg(v_result_2320_, v___y_2334_);
lean_dec_ref(v___y_2334_);
switch(lean_obj_tag(v_trie_2319_))
{
case 2:
{
lean_object* v___x_2336_; 
v___x_2336_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2319_);
v___y_2322_ = v___x_2335_;
v_val_2323_ = v___x_2336_;
goto v___jp_2321_;
}
case 3:
{
lean_object* v___x_2337_; 
v___x_2337_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_trie_2319_);
v___y_2322_ = v___x_2335_;
v_val_2323_ = v___x_2337_;
goto v___jp_2321_;
}
default: 
{
v___y_2322_ = v___x_2335_;
v_val_2323_ = v_trie_2319_;
goto v___jp_2321_;
}
}
}
v___jp_2338_:
{
if (lean_obj_tag(v_val_2339_) == 0)
{
lean_object* v___x_2340_; 
lean_dec_ref_known(v_val_2339_, 2);
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_2334_ = v___x_2340_;
goto v___jp_2333_;
}
else
{
lean_object* v_vs_2341_; 
v_vs_2341_ = lean_ctor_get(v_val_2339_, 0);
lean_inc_ref(v_vs_2341_);
lean_dec_ref_known(v_val_2339_, 2);
v___y_2334_ = v_vs_2341_;
goto v___jp_2333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2346_, size_t v_i_2347_, size_t v_stop_2348_, lean_object* v_b_2349_){
_start:
{
uint8_t v___x_2350_; 
v___x_2350_ = lean_usize_dec_eq(v_i_2347_, v_stop_2348_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; lean_object* v_snd_2352_; lean_object* v___x_2353_; size_t v___x_2354_; size_t v___x_2355_; 
v___x_2351_ = lean_array_uget_borrowed(v_as_2346_, v_i_2347_);
v_snd_2352_ = lean_ctor_get(v___x_2351_, 1);
lean_inc(v_snd_2352_);
v___x_2353_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2352_, v_b_2349_);
v___x_2354_ = ((size_t)1ULL);
v___x_2355_ = lean_usize_add(v_i_2347_, v___x_2354_);
v_i_2347_ = v___x_2355_;
v_b_2349_ = v___x_2353_;
goto _start;
}
else
{
return v_b_2349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2357_, lean_object* v_i_2358_, lean_object* v_stop_2359_, lean_object* v_b_2360_){
_start:
{
size_t v_i_boxed_2361_; size_t v_stop_boxed_2362_; lean_object* v_res_2363_; 
v_i_boxed_2361_ = lean_unbox_usize(v_i_2358_);
lean_dec(v_i_2358_);
v_stop_boxed_2362_ = lean_unbox_usize(v_stop_2359_);
lean_dec(v_stop_2359_);
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2357_, v_i_boxed_2361_, v_stop_boxed_2362_, v_b_2360_);
lean_dec_ref(v_as_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2364_, lean_object* v_trie_2365_, lean_object* v_result_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2365_, v_result_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2368_, lean_object* v_as_2369_, size_t v_i_2370_, size_t v_stop_2371_, lean_object* v_b_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2369_, v_i_2370_, v_stop_2371_, v_b_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2374_, lean_object* v_as_2375_, lean_object* v_i_2376_, lean_object* v_stop_2377_, lean_object* v_b_2378_){
_start:
{
size_t v_i_boxed_2379_; size_t v_stop_boxed_2380_; lean_object* v_res_2381_; 
v_i_boxed_2379_ = lean_unbox_usize(v_i_2376_);
lean_dec(v_i_2376_);
v_stop_boxed_2380_ = lean_unbox_usize(v_stop_2377_);
lean_dec(v_stop_2377_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2374_, v_as_2375_, v_i_boxed_2379_, v_stop_boxed_2380_, v_b_2378_);
lean_dec_ref(v_as_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2382_, lean_object* v_k_2383_, lean_object* v_result_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2382_, v_k_2383_);
if (lean_obj_tag(v___x_2385_) == 0)
{
return v_result_2384_;
}
else
{
lean_object* v_val_2386_; lean_object* v___x_2387_; 
v_val_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_val_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2386_, v_result_2384_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2388_, lean_object* v_k_2389_, lean_object* v_result_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2388_, v_k_2389_, v_result_2390_);
lean_dec(v_k_2389_);
lean_dec_ref(v_d_2388_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2392_, lean_object* v_d_2393_, lean_object* v_k_2394_, lean_object* v_result_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2393_, v_k_2394_, v_result_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2397_, lean_object* v_d_2398_, lean_object* v_k_2399_, lean_object* v_result_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2397_, v_d_2398_, v_k_2399_, v_result_2400_);
lean_dec(v_k_2399_);
lean_dec_ref(v_d_2398_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(lean_object* v_e_2402_, lean_object* v_result_2403_, lean_object* v_d_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2402_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2428_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2428_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2428_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2427_; 
v_fst_2415_ = lean_ctor_get(v_a_2411_, 0);
v_snd_2416_ = lean_ctor_get(v_a_2411_, 1);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_a_2411_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2418_ = v_a_2411_;
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snd_2416_);
lean_inc(v_fst_2415_);
lean_dec(v_a_2411_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2427_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2404_, v_fst_2415_, v_result_2403_);
lean_dec(v_fst_2415_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_snd_2416_);
v___x_2422_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2424_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2422_);
v___x_2424_ = v___x_2413_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v_result_2403_);
v_a_2429_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2410_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2410_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0___boxed(lean_object* v_e_2437_, lean_object* v_result_2438_, lean_object* v_d_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2437_, v_result_2438_, v_d_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v_d_2439_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2446_, lean_object* v_e_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v___y_2454_; lean_object* v___x_2471_; uint8_t v_transparency_2472_; lean_object* v_result_2473_; uint8_t v___x_2474_; uint8_t v___x_2475_; 
v___x_2471_ = l_Lean_Meta_Context_config(v_a_2448_);
v_transparency_2472_ = lean_ctor_get_uint8(v___x_2471_, 9);
lean_dec_ref(v___x_2471_);
v_result_2473_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2446_);
v___x_2474_ = 2;
v___x_2475_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2472_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v_keyedConfig_2476_; uint8_t v_trackZetaDelta_2477_; lean_object* v_zetaDeltaSet_2478_; lean_object* v_lctx_2479_; lean_object* v_localInstances_2480_; lean_object* v_defEqCtx_x3f_2481_; lean_object* v_synthPendingDepth_2482_; lean_object* v_customCanUnfoldPredicate_x3f_2483_; uint8_t v_univApprox_2484_; uint8_t v_inTypeClassResolution_2485_; uint8_t v_cacheInferType_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_keyedConfig_2476_ = lean_ctor_get(v_a_2448_, 0);
v_trackZetaDelta_2477_ = lean_ctor_get_uint8(v_a_2448_, sizeof(void*)*7);
v_zetaDeltaSet_2478_ = lean_ctor_get(v_a_2448_, 1);
v_lctx_2479_ = lean_ctor_get(v_a_2448_, 2);
v_localInstances_2480_ = lean_ctor_get(v_a_2448_, 3);
v_defEqCtx_x3f_2481_ = lean_ctor_get(v_a_2448_, 4);
v_synthPendingDepth_2482_ = lean_ctor_get(v_a_2448_, 5);
v_customCanUnfoldPredicate_x3f_2483_ = lean_ctor_get(v_a_2448_, 6);
v_univApprox_2484_ = lean_ctor_get_uint8(v_a_2448_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2485_ = lean_ctor_get_uint8(v_a_2448_, sizeof(void*)*7 + 2);
v_cacheInferType_2486_ = lean_ctor_get_uint8(v_a_2448_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2476_);
v___x_2487_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2474_, v_keyedConfig_2476_);
lean_inc(v_customCanUnfoldPredicate_x3f_2483_);
lean_inc(v_synthPendingDepth_2482_);
lean_inc(v_defEqCtx_x3f_2481_);
lean_inc_ref(v_localInstances_2480_);
lean_inc_ref(v_lctx_2479_);
lean_inc(v_zetaDeltaSet_2478_);
v___x_2488_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v_zetaDeltaSet_2478_);
lean_ctor_set(v___x_2488_, 2, v_lctx_2479_);
lean_ctor_set(v___x_2488_, 3, v_localInstances_2480_);
lean_ctor_set(v___x_2488_, 4, v_defEqCtx_x3f_2481_);
lean_ctor_set(v___x_2488_, 5, v_synthPendingDepth_2482_);
lean_ctor_set(v___x_2488_, 6, v_customCanUnfoldPredicate_x3f_2483_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*7, v_trackZetaDelta_2477_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*7 + 1, v_univApprox_2484_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2485_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*7 + 3, v_cacheInferType_2486_);
v___x_2489_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2447_, v_result_2473_, v_d_2446_, v___x_2488_, v_a_2449_, v_a_2450_, v_a_2451_);
lean_dec_ref_known(v___x_2488_, 7);
v___y_2454_ = v___x_2489_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___lam__0(v_e_2447_, v_result_2473_, v_d_2446_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
v___y_2454_ = v___x_2490_;
goto v___jp_2453_;
}
v___jp_2453_:
{
if (lean_obj_tag(v___y_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
v_a_2455_ = lean_ctor_get(v___y_2454_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___y_2454_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___y_2454_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___y_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v_a_2463_ = lean_ctor_get(v___y_2454_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___y_2454_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___y_2454_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___y_2454_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2491_, lean_object* v_e_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2491_, v_e_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec_ref(v_d_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2499_, lean_object* v_d_2500_, lean_object* v_e_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2500_, v_e_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_d_2509_, lean_object* v_e_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2508_, v_d_2509_, v_e_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_d_2509_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(lean_object* v_skip_2517_, lean_object* v_todo_2518_, lean_object* v_ks_2519_, lean_object* v_i_2520_, lean_object* v_v_2521_, lean_object* v_result_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = lean_array_get_size(v_ks_2519_);
v___x_2529_ = lean_nat_dec_lt(v_i_2520_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
lean_dec(v_i_2520_);
v___x_2530_ = lean_unsigned_to_nat(0u);
v___x_2531_ = lean_nat_dec_eq(v_skip_2517_, v___x_2530_);
lean_dec(v_skip_2517_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
lean_dec(v_v_2521_);
lean_dec_ref(v_todo_2518_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_result_2522_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = lean_array_get_size(v_todo_2518_);
lean_dec_ref(v_todo_2518_);
v___x_2534_ = lean_nat_dec_eq(v___x_2533_, v___x_2530_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec(v_v_2521_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_result_2522_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_array_push(v_result_2522_, v_v_2521_);
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
}
else
{
lean_object* v_key_2538_; lean_object* v_zero_2539_; uint8_t v_isZero_2540_; 
v_key_2538_ = lean_array_fget_borrowed(v_ks_2519_, v_i_2520_);
v_zero_2539_ = lean_unsigned_to_nat(0u);
v_isZero_2540_ = lean_nat_dec_eq(v_skip_2517_, v_zero_2539_);
if (v_isZero_2540_ == 1)
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
lean_dec(v_skip_2517_);
v___x_2541_ = lean_array_get_size(v_todo_2518_);
v___x_2542_ = lean_nat_dec_eq(v___x_2541_, v_zero_2539_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_e_2546_; lean_object* v_todo_2547_; lean_object* v___x_2548_; 
v___x_2543_ = l_Lean_instInhabitedExpr;
v___x_2544_ = lean_unsigned_to_nat(1u);
v___x_2545_ = lean_nat_sub(v___x_2541_, v___x_2544_);
v_e_2546_ = lean_array_get(v___x_2543_, v_todo_2518_, v___x_2545_);
lean_dec(v___x_2545_);
v_todo_2547_ = lean_array_pop(v_todo_2518_);
v___x_2548_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2546_, v___x_2542_, v___x_2542_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2576_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2576_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2576_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_fst_2553_; lean_object* v_snd_2554_; lean_object* v_result_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; 
v_fst_2553_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_fst_2553_);
v_snd_2554_ = lean_ctor_get(v_a_2549_, 1);
lean_inc(v_snd_2554_);
lean_dec(v_a_2549_);
if (lean_obj_tag(v_fst_2553_) == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec(v_snd_2554_);
lean_del_object(v___x_2551_);
v___x_2568_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2538_);
v___x_2569_ = lean_nat_add(v_i_2520_, v___x_2544_);
lean_dec(v_i_2520_);
v_skip_2517_ = v___x_2568_;
v_todo_2518_ = v_todo_2547_;
v_i_2520_ = v___x_2569_;
goto _start;
}
else
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = lean_box(0);
v___x_2572_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2538_, v___x_2571_);
if (v___x_2572_ == 0)
{
v_result_2556_ = v_result_2522_;
v___y_2557_ = v_a_2523_;
v___y_2558_ = v_a_2524_;
v___y_2559_ = v_a_2525_;
v___y_2560_ = v_a_2526_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_nat_add(v_i_2520_, v___x_2544_);
lean_inc(v_v_2521_);
lean_inc_ref(v_todo_2547_);
v___x_2574_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_zero_2539_, v_todo_2547_, v_ks_2519_, v___x_2573_, v_v_2521_, v_result_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v_result_2556_ = v_a_2575_;
v___y_2557_ = v_a_2523_;
v___y_2558_ = v_a_2524_;
v___y_2559_ = v_a_2525_;
v___y_2560_ = v_a_2526_;
goto v___jp_2555_;
}
else
{
lean_dec(v_snd_2554_);
lean_dec(v_fst_2553_);
lean_del_object(v___x_2551_);
lean_dec_ref(v_todo_2547_);
lean_dec(v_v_2521_);
lean_dec(v_i_2520_);
return v___x_2574_;
}
}
}
v___jp_2555_:
{
uint8_t v___x_2561_; 
v___x_2561_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2538_, v_fst_2553_);
lean_dec(v_fst_2553_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2563_; 
lean_dec(v_snd_2554_);
lean_dec_ref(v_todo_2547_);
lean_dec(v_v_2521_);
lean_dec(v_i_2520_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_result_2556_);
v___x_2563_ = v___x_2551_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_result_2556_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_del_object(v___x_2551_);
v___x_2565_ = l_Array_append___redArg(v_todo_2547_, v_snd_2554_);
lean_dec(v_snd_2554_);
v___x_2566_ = lean_nat_add(v_i_2520_, v___x_2544_);
lean_dec(v_i_2520_);
v_skip_2517_ = v_zero_2539_;
v_todo_2518_ = v___x_2565_;
v_i_2520_ = v___x_2566_;
v_result_2522_ = v_result_2556_;
v_a_2523_ = v___y_2557_;
v_a_2524_ = v___y_2558_;
v_a_2525_ = v___y_2559_;
v_a_2526_ = v___y_2560_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_todo_2547_);
lean_dec_ref(v_result_2522_);
lean_dec(v_v_2521_);
lean_dec(v_i_2520_);
v_a_2577_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2548_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2548_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v___x_2585_; 
lean_dec(v_v_2521_);
lean_dec(v_i_2520_);
lean_dec_ref(v_todo_2518_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_result_2522_);
return v___x_2585_;
}
}
else
{
lean_object* v_one_2586_; lean_object* v_n_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_one_2586_ = lean_unsigned_to_nat(1u);
v_n_2587_ = lean_nat_sub(v_skip_2517_, v_one_2586_);
lean_dec(v_skip_2517_);
v___x_2588_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2538_);
v___x_2589_ = lean_nat_add(v_n_2587_, v___x_2588_);
lean_dec(v___x_2588_);
lean_dec(v_n_2587_);
v___x_2590_ = lean_nat_add(v_i_2520_, v_one_2586_);
lean_dec(v_i_2520_);
v_skip_2517_ = v___x_2589_;
v_i_2520_ = v___x_2590_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg___boxed(lean_object* v_skip_2592_, lean_object* v_todo_2593_, lean_object* v_ks_2594_, lean_object* v_i_2595_, lean_object* v_v_2596_, lean_object* v_result_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_skip_2592_, v_todo_2593_, v_ks_2594_, v_i_2595_, v_v_2596_, v_result_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec_ref(v_ks_2594_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix(lean_object* v_00_u03b1_2604_, lean_object* v_skip_2605_, lean_object* v_todo_2606_, lean_object* v_ks_2607_, lean_object* v_i_2608_, lean_object* v_v_2609_, lean_object* v_result_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_skip_2605_, v_todo_2606_, v_ks_2607_, v_i_2608_, v_v_2609_, v_result_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___boxed(lean_object* v_00_u03b1_2617_, lean_object* v_skip_2618_, lean_object* v_todo_2619_, lean_object* v_ks_2620_, lean_object* v_i_2621_, lean_object* v_v_2622_, lean_object* v_result_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix(v_00_u03b1_2617_, v_skip_2618_, v_todo_2619_, v_ks_2620_, v_i_2621_, v_v_2622_, v_result_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec_ref(v_ks_2620_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2630_, lean_object* v_as_2631_, size_t v_i_2632_, size_t v_stop_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_usize_dec_eq(v_i_2632_, v_stop_2633_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v_fst_2642_; lean_object* v_snd_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2641_ = lean_array_uget_borrowed(v_as_2631_, v_i_2632_);
v_fst_2642_ = lean_ctor_get(v___x_2641_, 0);
v_snd_2643_ = lean_ctor_get(v___x_2641_, 1);
v___x_2644_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2642_);
lean_inc(v_snd_2643_);
lean_inc_ref(v_todo_2630_);
v___x_2645_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2644_, v_todo_2630_, v_snd_2643_, v_b_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; size_t v___x_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v___x_2647_ = ((size_t)1ULL);
v___x_2648_ = lean_usize_add(v_i_2632_, v___x_2647_);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(v_todo_2630_, v_as_2631_, v___x_2648_, v_stop_2633_, v_a_2646_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2649_;
}
else
{
lean_dec_ref(v_todo_2630_);
return v___x_2645_;
}
}
else
{
lean_object* v___x_2650_; 
lean_dec_ref(v_todo_2630_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_b_2634_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(lean_object* v_n_2651_, lean_object* v_todo_2652_, lean_object* v_as_2653_, size_t v_i_2654_, size_t v_stop_2655_, lean_object* v_b_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_usize_dec_eq(v_i_2654_, v_stop_2655_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v_fst_2664_; lean_object* v_snd_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2663_ = lean_array_uget_borrowed(v_as_2653_, v_i_2654_);
v_fst_2664_ = lean_ctor_get(v___x_2663_, 0);
v_snd_2665_ = lean_ctor_get(v___x_2663_, 1);
v___x_2666_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2664_);
v___x_2667_ = lean_nat_add(v_n_2651_, v___x_2666_);
lean_dec(v___x_2666_);
lean_inc(v_snd_2665_);
lean_inc_ref(v_todo_2652_);
v___x_2668_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2667_, v_todo_2652_, v_snd_2665_, v_b_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; size_t v___x_2670_; size_t v___x_2671_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = ((size_t)1ULL);
v___x_2671_ = lean_usize_add(v_i_2654_, v___x_2670_);
v_i_2654_ = v___x_2671_;
v_b_2656_ = v_a_2669_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2652_);
return v___x_2668_;
}
}
else
{
lean_object* v___x_2673_; 
lean_dec_ref(v_todo_2652_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_b_2656_);
return v___x_2673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2674_, lean_object* v_todo_2675_, lean_object* v_as_2676_, size_t v_i_2677_, size_t v_stop_2678_, lean_object* v_b_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v___x_2685_; 
v___x_2685_ = lean_usize_dec_eq(v_i_2677_, v_stop_2678_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v_fst_2687_; lean_object* v_snd_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2686_ = lean_array_uget_borrowed(v_as_2676_, v_i_2677_);
v_fst_2687_ = lean_ctor_get(v___x_2686_, 0);
v_snd_2688_ = lean_ctor_get(v___x_2686_, 1);
v___x_2689_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2687_);
v___x_2690_ = lean_nat_add(v_n_2674_, v___x_2689_);
lean_dec(v___x_2689_);
lean_inc(v_snd_2688_);
lean_inc_ref(v_todo_2675_);
v___x_2691_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2690_, v_todo_2675_, v_snd_2688_, v_b_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; size_t v___x_2693_; size_t v___x_2694_; lean_object* v___x_2695_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2693_ = ((size_t)1ULL);
v___x_2694_ = lean_usize_add(v_i_2677_, v___x_2693_);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(v_n_2674_, v_todo_2675_, v_as_2676_, v___x_2694_, v_stop_2678_, v_a_2692_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2695_;
}
else
{
lean_dec_ref(v_todo_2675_);
return v___x_2691_;
}
}
else
{
lean_object* v___x_2696_; 
lean_dec_ref(v_todo_2675_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_b_2679_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2697_, lean_object* v_todo_2698_, lean_object* v_c_2699_, lean_object* v_result_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v___y_2707_; lean_object* v_val_2711_; 
if (lean_obj_tag(v_c_2699_) == 3)
{
lean_object* v_keys_2714_; lean_object* v_i_2715_; lean_object* v_v_2716_; lean_object* v___x_2717_; 
v_keys_2714_ = lean_ctor_get(v_c_2699_, 0);
lean_inc_ref(v_keys_2714_);
v_i_2715_ = lean_ctor_get(v_c_2699_, 1);
lean_inc(v_i_2715_);
v_v_2716_ = lean_ctor_get(v_c_2699_, 2);
lean_inc(v_v_2716_);
lean_dec_ref_known(v_c_2699_, 3);
v___x_2717_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_processSuffix___redArg(v_skip_2697_, v_todo_2698_, v_keys_2714_, v_i_2715_, v_v_2716_, v_result_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
lean_dec_ref(v_keys_2714_);
return v___x_2717_;
}
else
{
lean_object* v_zero_2718_; uint8_t v_isZero_2719_; 
v_zero_2718_ = lean_unsigned_to_nat(0u);
v_isZero_2719_ = lean_nat_dec_eq(v_skip_2697_, v_zero_2718_);
if (v_isZero_2719_ == 1)
{
lean_object* v___x_2720_; lean_object* v___y_2722_; lean_object* v_val_2723_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v_val_2743_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v_val_2756_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v_result_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v_val_2798_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v_val_2806_; uint8_t v___x_2819_; 
lean_dec(v_skip_2697_);
v___x_2720_ = lean_array_get_size(v_todo_2698_);
v___x_2819_ = lean_nat_dec_eq(v___x_2720_, v_zero_2718_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v_val_2845_; 
v___x_2820_ = l_Lean_instInhabitedExpr;
switch(lean_obj_tag(v_c_2699_))
{
case 2:
{
lean_object* v___x_2850_; 
lean_inc_ref(v_c_2699_);
v___x_2850_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v_val_2845_ = v___x_2850_;
goto v___jp_2844_;
}
case 3:
{
lean_object* v___x_2851_; 
lean_inc_ref(v_c_2699_);
v___x_2851_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v_val_2845_ = v___x_2851_;
goto v___jp_2844_;
}
default: 
{
lean_inc_ref(v_c_2699_);
v_val_2845_ = v_c_2699_;
goto v___jp_2844_;
}
}
v___jp_2821_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v_e_2824_; lean_object* v_todo_2825_; lean_object* v___x_2826_; 
v___x_2822_ = lean_unsigned_to_nat(1u);
v___x_2823_ = lean_nat_sub(v___x_2720_, v___x_2822_);
v_e_2824_ = lean_array_get(v___x_2820_, v_todo_2698_, v___x_2823_);
lean_dec(v___x_2823_);
v_todo_2825_ = lean_array_pop(v_todo_2698_);
v___x_2826_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2824_, v___x_2819_, v___x_2819_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v_fst_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v_fst_2828_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_fst_2828_);
if (lean_obj_tag(v_fst_2828_) == 0)
{
lean_dec(v_a_2827_);
switch(lean_obj_tag(v_c_2699_))
{
case 2:
{
lean_object* v___x_2829_; 
v___x_2829_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v___y_2722_ = v_todo_2825_;
v_val_2723_ = v___x_2829_;
goto v___jp_2721_;
}
case 3:
{
lean_object* v___x_2830_; 
v___x_2830_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v___y_2722_ = v_todo_2825_;
v_val_2723_ = v___x_2830_;
goto v___jp_2721_;
}
default: 
{
v___y_2722_ = v_todo_2825_;
v_val_2723_ = v_c_2699_;
goto v___jp_2721_;
}
}
}
else
{
switch(lean_obj_tag(v_c_2699_))
{
case 2:
{
lean_object* v_snd_2831_; lean_object* v___x_2832_; 
v_snd_2831_ = lean_ctor_get(v_a_2827_, 1);
lean_inc(v_snd_2831_);
lean_dec(v_a_2827_);
lean_inc_ref(v_c_2699_);
v___x_2832_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v___y_2802_ = v_fst_2828_;
v___y_2803_ = v_snd_2831_;
v___y_2804_ = v___x_2822_;
v___y_2805_ = v_todo_2825_;
v_val_2806_ = v___x_2832_;
goto v___jp_2801_;
}
case 3:
{
lean_object* v_snd_2833_; lean_object* v___x_2834_; 
v_snd_2833_ = lean_ctor_get(v_a_2827_, 1);
lean_inc(v_snd_2833_);
lean_dec(v_a_2827_);
lean_inc_ref(v_c_2699_);
v___x_2834_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v___y_2802_ = v_fst_2828_;
v___y_2803_ = v_snd_2833_;
v___y_2804_ = v___x_2822_;
v___y_2805_ = v_todo_2825_;
v_val_2806_ = v___x_2834_;
goto v___jp_2801_;
}
default: 
{
lean_object* v_snd_2835_; 
v_snd_2835_ = lean_ctor_get(v_a_2827_, 1);
lean_inc(v_snd_2835_);
lean_dec(v_a_2827_);
lean_inc_ref(v_c_2699_);
v___y_2802_ = v_fst_2828_;
v___y_2803_ = v_snd_2835_;
v___y_2804_ = v___x_2822_;
v___y_2805_ = v_todo_2825_;
v_val_2806_ = v_c_2699_;
goto v___jp_2801_;
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref(v_todo_2825_);
lean_dec_ref(v_result_2700_);
lean_dec_ref(v_c_2699_);
v_a_2836_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2826_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2826_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
v___jp_2844_:
{
if (lean_obj_tag(v_val_2845_) == 0)
{
lean_dec_ref_known(v_val_2845_, 2);
goto v___jp_2821_;
}
else
{
lean_object* v_children_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v_children_2846_ = lean_ctor_get(v_val_2845_, 1);
lean_inc_ref(v_children_2846_);
lean_dec_ref_known(v_val_2845_, 2);
v___x_2847_ = lean_array_get_size(v_children_2846_);
lean_dec_ref(v_children_2846_);
v___x_2848_ = lean_nat_dec_eq(v___x_2847_, v_zero_2718_);
if (v___x_2848_ == 0)
{
goto v___jp_2821_;
}
else
{
lean_object* v___x_2849_; 
lean_dec_ref(v_c_2699_);
lean_dec_ref(v_todo_2698_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v_result_2700_);
return v___x_2849_;
}
}
}
}
else
{
lean_dec_ref(v_todo_2698_);
switch(lean_obj_tag(v_c_2699_))
{
case 2:
{
lean_object* v___x_2852_; 
v___x_2852_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v_val_2711_ = v___x_2852_;
goto v___jp_2710_;
}
case 3:
{
lean_object* v___x_2853_; 
v___x_2853_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v_val_2711_ = v___x_2853_;
goto v___jp_2710_;
}
default: 
{
v_val_2711_ = v_c_2699_;
goto v___jp_2710_;
}
}
}
v___jp_2721_:
{
if (lean_obj_tag(v_val_2723_) == 0)
{
lean_object* v_key_2724_; lean_object* v_child_2725_; lean_object* v___x_2726_; 
v_key_2724_ = lean_ctor_get(v_val_2723_, 0);
lean_inc(v_key_2724_);
v_child_2725_ = lean_ctor_get(v_val_2723_, 1);
lean_inc_ref(v_child_2725_);
lean_dec_ref_known(v_val_2723_, 2);
v___x_2726_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2724_);
lean_dec(v_key_2724_);
v_skip_2697_ = v___x_2726_;
v_todo_2698_ = v___y_2722_;
v_c_2699_ = v_child_2725_;
goto _start;
}
else
{
lean_object* v_children_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_children_2728_ = lean_ctor_get(v_val_2723_, 1);
lean_inc_ref(v_children_2728_);
lean_dec_ref_known(v_val_2723_, 2);
v___x_2729_ = lean_array_get_size(v_children_2728_);
v___x_2730_ = lean_nat_dec_lt(v_zero_2718_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec_ref(v_children_2728_);
lean_dec_ref(v___y_2722_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_result_2700_);
return v___x_2731_;
}
else
{
size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = ((size_t)0ULL);
v___x_2733_ = lean_usize_of_nat(v___x_2729_);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v___y_2722_, v_children_2728_, v___x_2732_, v___x_2733_, v_result_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
lean_dec_ref(v_children_2728_);
return v___x_2734_;
}
}
}
v___jp_2735_:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Array_append___redArg(v___y_2742_, v___y_2737_);
lean_dec_ref(v___y_2737_);
v_skip_2697_ = v_zero_2718_;
v_todo_2698_ = v___x_2744_;
v_c_2699_ = v_val_2743_;
v_result_2700_ = v___y_2741_;
v_a_2701_ = v___y_2736_;
v_a_2702_ = v___y_2739_;
v_a_2703_ = v___y_2740_;
v_a_2704_ = v___y_2738_;
goto _start;
}
v___jp_2746_:
{
if (lean_obj_tag(v_val_2756_) == 0)
{
lean_object* v_key_2757_; lean_object* v_child_2758_; uint8_t v___x_2759_; 
v_key_2757_ = lean_ctor_get(v_val_2756_, 0);
lean_inc(v_key_2757_);
v_child_2758_ = lean_ctor_get(v_val_2756_, 1);
lean_inc_ref(v_child_2758_);
lean_dec_ref_known(v_val_2756_, 2);
v___x_2759_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2757_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec(v_key_2757_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v_child_2758_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2749_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___y_2755_);
return v___x_2760_;
}
else
{
v___y_2736_ = v___y_2747_;
v___y_2737_ = v___y_2749_;
v___y_2738_ = v___y_2750_;
v___y_2739_ = v___y_2752_;
v___y_2740_ = v___y_2753_;
v___y_2741_ = v___y_2755_;
v___y_2742_ = v___y_2754_;
v_val_2743_ = v_child_2758_;
goto v___jp_2735_;
}
}
else
{
lean_object* v_children_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2779_; 
v_children_2761_ = lean_ctor_get(v_val_2756_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_val_2756_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_val_2756_, 0);
lean_dec(v_unused_2780_);
v___x_2763_ = v_val_2756_;
v_isShared_2764_ = v_isSharedCheck_2779_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_children_2761_);
lean_dec(v_val_2756_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2779_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = lean_array_get_size(v_children_2761_);
v___x_2766_ = lean_nat_dec_lt(v_zero_2718_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
lean_del_object(v___x_2763_);
lean_dec_ref(v_children_2761_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___y_2755_);
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = lean_nat_sub(v___x_2765_, v___y_2751_);
v___x_2769_ = lean_nat_dec_le(v_zero_2718_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_dec(v___x_2768_);
lean_del_object(v___x_2763_);
lean_dec_ref(v_children_2761_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___y_2755_);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0));
if (v_isShared_2764_ == 0)
{
lean_ctor_set_tag(v___x_2763_, 0);
lean_ctor_set(v___x_2763_, 1, v___x_2771_);
lean_ctor_set(v___x_2763_, 0, v___y_2748_);
v___x_2773_ = v___x_2763_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___y_2748_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__1___redArg(v_children_2761_, v___x_2773_, v_zero_2718_, v___x_2768_);
lean_dec_ref(v___x_2773_);
lean_dec_ref(v_children_2761_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2775_; 
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2749_);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___y_2755_);
return v___x_2775_;
}
else
{
lean_object* v_val_2776_; lean_object* v_snd_2777_; 
v_val_2776_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v___x_2774_, 1);
v_snd_2777_ = lean_ctor_get(v_val_2776_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_val_2776_);
v___y_2736_ = v___y_2747_;
v___y_2737_ = v___y_2749_;
v___y_2738_ = v___y_2750_;
v___y_2739_ = v___y_2752_;
v___y_2740_ = v___y_2753_;
v___y_2741_ = v___y_2755_;
v___y_2742_ = v___y_2754_;
v_val_2743_ = v_snd_2777_;
goto v___jp_2735_;
}
}
}
}
}
}
}
v___jp_2781_:
{
switch(lean_obj_tag(v_c_2699_))
{
case 2:
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v___y_2747_ = v___y_2787_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___y_2790_;
v___y_2751_ = v___y_2784_;
v___y_2752_ = v___y_2788_;
v___y_2753_ = v___y_2789_;
v___y_2754_ = v___y_2785_;
v___y_2755_ = v_result_2786_;
v_val_2756_ = v___x_2791_;
goto v___jp_2746_;
}
case 3:
{
lean_object* v___x_2792_; 
v___x_2792_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v___y_2747_ = v___y_2787_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___y_2790_;
v___y_2751_ = v___y_2784_;
v___y_2752_ = v___y_2788_;
v___y_2753_ = v___y_2789_;
v___y_2754_ = v___y_2785_;
v___y_2755_ = v_result_2786_;
v_val_2756_ = v___x_2792_;
goto v___jp_2746_;
}
default: 
{
v___y_2747_ = v___y_2787_;
v___y_2748_ = v___y_2782_;
v___y_2749_ = v___y_2783_;
v___y_2750_ = v___y_2790_;
v___y_2751_ = v___y_2784_;
v___y_2752_ = v___y_2788_;
v___y_2753_ = v___y_2789_;
v___y_2754_ = v___y_2785_;
v___y_2755_ = v_result_2786_;
v_val_2756_ = v_c_2699_;
goto v___jp_2746_;
}
}
}
v___jp_2793_:
{
lean_object* v___x_2799_; 
lean_inc_ref(v___y_2797_);
v___x_2799_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2718_, v___y_2797_, v_val_2798_, v_result_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2782_ = v___y_2794_;
v___y_2783_ = v___y_2795_;
v___y_2784_ = v___y_2796_;
v___y_2785_ = v___y_2797_;
v_result_2786_ = v_a_2800_;
v___y_2787_ = v_a_2701_;
v___y_2788_ = v_a_2702_;
v___y_2789_ = v_a_2703_;
v___y_2790_ = v_a_2704_;
goto v___jp_2781_;
}
else
{
lean_dec_ref(v___y_2797_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v_c_2699_);
return v___x_2799_;
}
}
v___jp_2801_:
{
if (lean_obj_tag(v_val_2806_) == 0)
{
lean_object* v_key_2807_; lean_object* v_child_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v_key_2807_ = lean_ctor_get(v_val_2806_, 0);
lean_inc(v_key_2807_);
v_child_2808_ = lean_ctor_get(v_val_2806_, 1);
lean_inc_ref(v_child_2808_);
lean_dec_ref_known(v_val_2806_, 2);
v___x_2809_ = lean_box(0);
v___x_2810_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_2807_, v___x_2809_);
lean_dec(v_key_2807_);
if (v___x_2810_ == 0)
{
lean_dec_ref(v_child_2808_);
v___y_2782_ = v___y_2802_;
v___y_2783_ = v___y_2803_;
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v_result_2786_ = v_result_2700_;
v___y_2787_ = v_a_2701_;
v___y_2788_ = v_a_2702_;
v___y_2789_ = v_a_2703_;
v___y_2790_ = v_a_2704_;
goto v___jp_2781_;
}
else
{
v___y_2794_ = v___y_2802_;
v___y_2795_ = v___y_2803_;
v___y_2796_ = v___y_2804_;
v___y_2797_ = v___y_2805_;
v_val_2798_ = v_child_2808_;
goto v___jp_2793_;
}
}
else
{
lean_object* v_children_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_children_2811_ = lean_ctor_get(v_val_2806_, 1);
lean_inc_ref(v_children_2811_);
lean_dec_ref_known(v_val_2806_, 2);
v___x_2812_ = lean_array_get_size(v_children_2811_);
v___x_2813_ = lean_nat_dec_lt(v_zero_2718_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_dec_ref(v_children_2811_);
v___y_2782_ = v___y_2802_;
v___y_2783_ = v___y_2803_;
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v_result_2786_ = v_result_2700_;
v___y_2787_ = v_a_2701_;
v___y_2788_ = v_a_2702_;
v___y_2789_ = v_a_2703_;
v___y_2790_ = v_a_2704_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2814_; lean_object* v_fst_2815_; lean_object* v_snd_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2814_ = lean_array_fget(v_children_2811_, v_zero_2718_);
lean_dec_ref(v_children_2811_);
v_fst_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_fst_2815_);
v_snd_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_snd_2816_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v___x_2818_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2815_, v___x_2817_);
lean_dec(v_fst_2815_);
if (v___x_2818_ == 0)
{
lean_dec(v_snd_2816_);
v___y_2782_ = v___y_2802_;
v___y_2783_ = v___y_2803_;
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v_result_2786_ = v_result_2700_;
v___y_2787_ = v_a_2701_;
v___y_2788_ = v_a_2702_;
v___y_2789_ = v_a_2703_;
v___y_2790_ = v_a_2704_;
goto v___jp_2781_;
}
else
{
v___y_2794_ = v___y_2802_;
v___y_2795_ = v___y_2803_;
v___y_2796_ = v___y_2804_;
v___y_2797_ = v___y_2805_;
v_val_2798_ = v_snd_2816_;
goto v___jp_2793_;
}
}
}
}
}
else
{
lean_object* v_one_2854_; lean_object* v_n_2855_; lean_object* v_val_2857_; 
v_one_2854_ = lean_unsigned_to_nat(1u);
v_n_2855_ = lean_nat_sub(v_skip_2697_, v_one_2854_);
lean_dec(v_skip_2697_);
switch(lean_obj_tag(v_c_2699_))
{
case 2:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v_val_2857_ = v___x_2870_;
goto v___jp_2856_;
}
case 3:
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_2699_);
v_val_2857_ = v___x_2871_;
goto v___jp_2856_;
}
default: 
{
v_val_2857_ = v_c_2699_;
goto v___jp_2856_;
}
}
v___jp_2856_:
{
if (lean_obj_tag(v_val_2857_) == 0)
{
lean_object* v_key_2858_; lean_object* v_child_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_key_2858_ = lean_ctor_get(v_val_2857_, 0);
lean_inc(v_key_2858_);
v_child_2859_ = lean_ctor_get(v_val_2857_, 1);
lean_inc_ref(v_child_2859_);
lean_dec_ref_known(v_val_2857_, 2);
v___x_2860_ = l_Lean_Meta_DiscrTree_Key_arity(v_key_2858_);
lean_dec(v_key_2858_);
v___x_2861_ = lean_nat_add(v_n_2855_, v___x_2860_);
lean_dec(v___x_2860_);
lean_dec(v_n_2855_);
v_skip_2697_ = v___x_2861_;
v_c_2699_ = v_child_2859_;
goto _start;
}
else
{
lean_object* v_children_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v_children_2863_ = lean_ctor_get(v_val_2857_, 1);
lean_inc_ref(v_children_2863_);
lean_dec_ref_known(v_val_2857_, 2);
v___x_2864_ = lean_array_get_size(v_children_2863_);
v___x_2865_ = lean_nat_dec_lt(v_zero_2718_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec_ref(v_children_2863_);
lean_dec(v_n_2855_);
lean_dec_ref(v_todo_2698_);
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_result_2700_);
return v___x_2866_;
}
else
{
size_t v___x_2867_; size_t v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = ((size_t)0ULL);
v___x_2868_ = lean_usize_of_nat(v___x_2864_);
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2855_, v_todo_2698_, v_children_2863_, v___x_2867_, v___x_2868_, v_result_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_);
lean_dec_ref(v_children_2863_);
lean_dec(v_n_2855_);
return v___x_2869_;
}
}
}
}
}
v___jp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = l_Array_append___redArg(v_result_2700_, v___y_2707_);
lean_dec_ref(v___y_2707_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
v___jp_2710_:
{
if (lean_obj_tag(v_val_2711_) == 0)
{
lean_object* v___x_2712_; 
lean_dec_ref_known(v_val_2711_, 2);
v___x_2712_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___y_2707_ = v___x_2712_;
goto v___jp_2706_;
}
else
{
lean_object* v_vs_2713_; 
v_vs_2713_ = lean_ctor_get(v_val_2711_, 0);
lean_inc_ref(v_vs_2713_);
lean_dec_ref_known(v_val_2711_, 2);
v___y_2707_ = v_vs_2713_;
goto v___jp_2706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(lean_object* v_todo_2872_, lean_object* v_as_2873_, size_t v_i_2874_, size_t v_stop_2875_, lean_object* v_b_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
uint8_t v___x_2882_; 
v___x_2882_ = lean_usize_dec_eq(v_i_2874_, v_stop_2875_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2883_ = lean_array_uget_borrowed(v_as_2873_, v_i_2874_);
v_fst_2884_ = lean_ctor_get(v___x_2883_, 0);
v_snd_2885_ = lean_ctor_get(v___x_2883_, 1);
v___x_2886_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2884_);
lean_inc(v_snd_2885_);
lean_inc_ref(v_todo_2872_);
v___x_2887_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2886_, v_todo_2872_, v_snd_2885_, v_b_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; size_t v___x_2889_; size_t v___x_2890_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_add(v_i_2874_, v___x_2889_);
v_i_2874_ = v___x_2890_;
v_b_2876_ = v_a_2888_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2872_);
return v___x_2887_;
}
}
else
{
lean_object* v___x_2892_; 
lean_dec_ref(v_todo_2872_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_b_2876_);
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg___boxed(lean_object* v_todo_2893_, lean_object* v_as_2894_, lean_object* v_i_2895_, lean_object* v_stop_2896_, lean_object* v_b_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
size_t v_i_boxed_2903_; size_t v_stop_boxed_2904_; lean_object* v_res_2905_; 
v_i_boxed_2903_ = lean_unbox_usize(v_i_2895_);
lean_dec(v_i_2895_);
v_stop_boxed_2904_ = lean_unbox_usize(v_stop_2896_);
lean_dec(v_stop_2896_);
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(v_todo_2893_, v_as_2894_, v_i_boxed_2903_, v_stop_boxed_2904_, v_b_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v_as_2894_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2906_, lean_object* v_as_2907_, lean_object* v_i_2908_, lean_object* v_stop_2909_, lean_object* v_b_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
size_t v_i_boxed_2916_; size_t v_stop_boxed_2917_; lean_object* v_res_2918_; 
v_i_boxed_2916_ = lean_unbox_usize(v_i_2908_);
lean_dec(v_i_2908_);
v_stop_boxed_2917_ = lean_unbox_usize(v_stop_2909_);
lean_dec(v_stop_2909_);
v_res_2918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2906_, v_as_2907_, v_i_boxed_2916_, v_stop_boxed_2917_, v_b_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec_ref(v_as_2907_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg___boxed(lean_object* v_n_2919_, lean_object* v_todo_2920_, lean_object* v_as_2921_, lean_object* v_i_2922_, lean_object* v_stop_2923_, lean_object* v_b_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
size_t v_i_boxed_2930_; size_t v_stop_boxed_2931_; lean_object* v_res_2932_; 
v_i_boxed_2930_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_stop_boxed_2931_ = lean_unbox_usize(v_stop_2923_);
lean_dec(v_stop_2923_);
v_res_2932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(v_n_2919_, v_todo_2920_, v_as_2921_, v_i_boxed_2930_, v_stop_boxed_2931_, v_b_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec_ref(v_as_2921_);
lean_dec(v_n_2919_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2933_, lean_object* v_todo_2934_, lean_object* v_as_2935_, lean_object* v_i_2936_, lean_object* v_stop_2937_, lean_object* v_b_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
size_t v_i_boxed_2944_; size_t v_stop_boxed_2945_; lean_object* v_res_2946_; 
v_i_boxed_2944_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_stop_boxed_2945_ = lean_unbox_usize(v_stop_2937_);
lean_dec(v_stop_2937_);
v_res_2946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2933_, v_todo_2934_, v_as_2935_, v_i_boxed_2944_, v_stop_boxed_2945_, v_b_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec_ref(v_as_2935_);
lean_dec(v_n_2933_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2947_, lean_object* v_todo_2948_, lean_object* v_c_2949_, lean_object* v_result_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2947_, v_todo_2948_, v_c_2949_, v_result_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2957_, lean_object* v_skip_2958_, lean_object* v_todo_2959_, lean_object* v_c_2960_, lean_object* v_result_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2958_, v_todo_2959_, v_c_2960_, v_result_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2968_, lean_object* v_skip_2969_, lean_object* v_todo_2970_, lean_object* v_c_2971_, lean_object* v_result_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2968_, v_skip_2969_, v_todo_2970_, v_c_2971_, v_result_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2979_, lean_object* v_todo_2980_, lean_object* v_as_2981_, size_t v_i_2982_, size_t v_stop_2983_, lean_object* v_b_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2980_, v_as_2981_, v_i_2982_, v_stop_2983_, v_b_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2991_, lean_object* v_todo_2992_, lean_object* v_as_2993_, lean_object* v_i_2994_, lean_object* v_stop_2995_, lean_object* v_b_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
size_t v_i_boxed_3002_; size_t v_stop_boxed_3003_; lean_object* v_res_3004_; 
v_i_boxed_3002_ = lean_unbox_usize(v_i_2994_);
lean_dec(v_i_2994_);
v_stop_boxed_3003_ = lean_unbox_usize(v_stop_2995_);
lean_dec(v_stop_2995_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2991_, v_todo_2992_, v_as_2993_, v_i_boxed_3002_, v_stop_boxed_3003_, v_b_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v_as_2993_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_3005_, lean_object* v_n_3006_, lean_object* v_todo_3007_, lean_object* v_as_3008_, size_t v_i_3009_, size_t v_stop_3010_, lean_object* v_b_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_3006_, v_todo_3007_, v_as_3008_, v_i_3009_, v_stop_3010_, v_b_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_n_3019_, lean_object* v_todo_3020_, lean_object* v_as_3021_, lean_object* v_i_3022_, lean_object* v_stop_3023_, lean_object* v_b_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
size_t v_i_boxed_3030_; size_t v_stop_boxed_3031_; lean_object* v_res_3032_; 
v_i_boxed_3030_ = lean_unbox_usize(v_i_3022_);
lean_dec(v_i_3022_);
v_stop_boxed_3031_ = lean_unbox_usize(v_stop_3023_);
lean_dec(v_stop_3023_);
v_res_3032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_3018_, v_n_3019_, v_todo_3020_, v_as_3021_, v_i_boxed_3030_, v_stop_boxed_3031_, v_b_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v_as_3021_);
lean_dec(v_n_3019_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0(lean_object* v_00_u03b1_3033_, lean_object* v_todo_3034_, lean_object* v_as_3035_, size_t v_i_3036_, size_t v_stop_3037_, lean_object* v_b_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___redArg(v_todo_3034_, v_as_3035_, v_i_3036_, v_stop_3037_, v_b_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3045_, lean_object* v_todo_3046_, lean_object* v_as_3047_, lean_object* v_i_3048_, lean_object* v_stop_3049_, lean_object* v_b_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
size_t v_i_boxed_3056_; size_t v_stop_boxed_3057_; lean_object* v_res_3058_; 
v_i_boxed_3056_ = lean_unbox_usize(v_i_3048_);
lean_dec(v_i_3048_);
v_stop_boxed_3057_ = lean_unbox_usize(v_stop_3049_);
lean_dec(v_stop_3049_);
v_res_3058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0_spec__0(v_00_u03b1_3045_, v_todo_3046_, v_as_3047_, v_i_boxed_3056_, v_stop_boxed_3057_, v_b_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v_as_3047_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2(lean_object* v_00_u03b1_3059_, lean_object* v_n_3060_, lean_object* v_todo_3061_, lean_object* v_as_3062_, size_t v_i_3063_, size_t v_stop_3064_, lean_object* v_b_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___redArg(v_n_3060_, v_todo_3061_, v_as_3062_, v_i_3063_, v_stop_3064_, v_b_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3072_, lean_object* v_n_3073_, lean_object* v_todo_3074_, lean_object* v_as_3075_, lean_object* v_i_3076_, lean_object* v_stop_3077_, lean_object* v_b_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
size_t v_i_boxed_3084_; size_t v_stop_boxed_3085_; lean_object* v_res_3086_; 
v_i_boxed_3084_ = lean_unbox_usize(v_i_3076_);
lean_dec(v_i_3076_);
v_stop_boxed_3085_ = lean_unbox_usize(v_stop_3077_);
lean_dec(v_stop_3077_);
v_res_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1_spec__2(v_00_u03b1_3072_, v_n_3073_, v_todo_3074_, v_as_3075_, v_i_boxed_3084_, v_stop_boxed_3085_, v_b_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec_ref(v_as_3075_);
lean_dec(v_n_3073_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_3087_, lean_object* v_k_3088_, lean_object* v_c_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_3088_);
v___x_3096_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_3097_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_3095_, v___x_3096_, v_c_3089_, v_result_3087_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_3098_, lean_object* v_k_3099_, lean_object* v_c_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_3098_, v_k_3099_, v_c_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v_k_3099_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_3107_, lean_object* v_keys_3108_, lean_object* v_vals_3109_, lean_object* v_i_3110_, lean_object* v_acc_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3117_ = lean_array_get_size(v_keys_3108_);
v___x_3118_ = lean_nat_dec_lt(v_i_3110_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
lean_dec(v_i_3110_);
lean_dec_ref(v_f_3107_);
v___x_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3119_, 0, v_acc_3111_);
return v___x_3119_;
}
else
{
lean_object* v_k_3120_; lean_object* v_v_3121_; lean_object* v___x_3122_; 
v_k_3120_ = lean_array_fget_borrowed(v_keys_3108_, v_i_3110_);
v_v_3121_ = lean_array_fget_borrowed(v_vals_3109_, v_i_3110_);
lean_inc_ref(v_f_3107_);
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
lean_inc(v___y_3113_);
lean_inc_ref(v___y_3112_);
lean_inc(v_v_3121_);
lean_inc(v_k_3120_);
v___x_3122_ = lean_apply_8(v_f_3107_, v_acc_3111_, v_k_3120_, v_v_3121_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, lean_box(0));
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_add(v_i_3110_, v___x_3124_);
lean_dec(v_i_3110_);
v_i_3110_ = v___x_3125_;
v_acc_3111_ = v_a_3123_;
goto _start;
}
else
{
lean_dec(v_i_3110_);
lean_dec_ref(v_f_3107_);
return v___x_3122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_3127_, lean_object* v_keys_3128_, lean_object* v_vals_3129_, lean_object* v_i_3130_, lean_object* v_acc_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3127_, v_keys_3128_, v_vals_3129_, v_i_3130_, v_acc_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v_vals_3129_);
lean_dec_ref(v_keys_3128_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3138_, lean_object* v_as_3139_, size_t v_i_3140_, size_t v_stop_3141_, lean_object* v_b_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_a_3149_; lean_object* v___y_3154_; uint8_t v___x_3156_; 
v___x_3156_ = lean_usize_dec_eq(v_i_3140_, v_stop_3141_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_array_uget_borrowed(v_as_3139_, v_i_3140_);
switch(lean_obj_tag(v___x_3157_))
{
case 0:
{
lean_object* v_key_3158_; lean_object* v_val_3159_; lean_object* v___x_3160_; 
v_key_3158_ = lean_ctor_get(v___x_3157_, 0);
v_val_3159_ = lean_ctor_get(v___x_3157_, 1);
lean_inc_ref(v_f_3138_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
lean_inc(v_val_3159_);
lean_inc(v_key_3158_);
v___x_3160_ = lean_apply_8(v_f_3138_, v_b_3142_, v_key_3158_, v_val_3159_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, lean_box(0));
v___y_3154_ = v___x_3160_;
goto v___jp_3153_;
}
case 1:
{
lean_object* v_node_3161_; lean_object* v___x_3162_; 
v_node_3161_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_node_3161_);
lean_inc_ref(v_f_3138_);
v___x_3162_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3138_, v_node_3161_, v_b_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
v___y_3154_ = v___x_3162_;
goto v___jp_3153_;
}
default: 
{
v_a_3149_ = v_b_3142_;
goto v___jp_3148_;
}
}
}
else
{
lean_object* v___x_3163_; 
lean_dec_ref(v_f_3138_);
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_b_3142_);
return v___x_3163_;
}
v___jp_3148_:
{
size_t v___x_3150_; size_t v___x_3151_; 
v___x_3150_ = ((size_t)1ULL);
v___x_3151_ = lean_usize_add(v_i_3140_, v___x_3150_);
v_i_3140_ = v___x_3151_;
v_b_3142_ = v_a_3149_;
goto _start;
}
v___jp_3153_:
{
if (lean_obj_tag(v___y_3154_) == 0)
{
lean_object* v_a_3155_; 
v_a_3155_ = lean_ctor_get(v___y_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___y_3154_, 1);
v_a_3149_ = v_a_3155_;
goto v___jp_3148_;
}
else
{
lean_dec_ref(v_f_3138_);
return v___y_3154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_3164_, lean_object* v_x_3165_, lean_object* v_x_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
if (lean_obj_tag(v_x_3165_) == 0)
{
lean_object* v_es_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3185_; 
v_es_3172_ = lean_ctor_get(v_x_3165_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_x_3165_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3174_ = v_x_3165_;
v_isShared_3175_ = v_isSharedCheck_3185_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_es_3172_);
lean_dec(v_x_3165_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3185_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3176_ = lean_unsigned_to_nat(0u);
v___x_3177_ = lean_array_get_size(v_es_3172_);
v___x_3178_ = lean_nat_dec_lt(v___x_3176_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3180_; 
lean_dec_ref(v_es_3172_);
lean_dec_ref(v_f_3164_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v_x_3166_);
v___x_3180_ = v___x_3174_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_x_3166_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
else
{
size_t v___x_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
lean_del_object(v___x_3174_);
v___x_3182_ = ((size_t)0ULL);
v___x_3183_ = lean_usize_of_nat(v___x_3177_);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3164_, v_es_3172_, v___x_3182_, v___x_3183_, v_x_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec_ref(v_es_3172_);
return v___x_3184_;
}
}
}
else
{
lean_object* v_ks_3186_; lean_object* v_vs_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v_ks_3186_ = lean_ctor_get(v_x_3165_, 0);
lean_inc_ref(v_ks_3186_);
v_vs_3187_ = lean_ctor_get(v_x_3165_, 1);
lean_inc_ref(v_vs_3187_);
lean_dec_ref_known(v_x_3165_, 2);
v___x_3188_ = lean_unsigned_to_nat(0u);
v___x_3189_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3164_, v_ks_3186_, v_vs_3187_, v___x_3188_, v_x_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec_ref(v_vs_3187_);
lean_dec_ref(v_ks_3186_);
return v___x_3189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_3190_, lean_object* v_x_3191_, lean_object* v_x_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3190_, v_x_3191_, v_x_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3199_, lean_object* v_as_3200_, lean_object* v_i_3201_, lean_object* v_stop_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
size_t v_i_boxed_3209_; size_t v_stop_boxed_3210_; lean_object* v_res_3211_; 
v_i_boxed_3209_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_stop_boxed_3210_ = lean_unbox_usize(v_stop_3202_);
lean_dec(v_stop_3202_);
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3199_, v_as_3200_, v_i_boxed_3209_, v_stop_boxed_3210_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec_ref(v_as_3200_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(lean_object* v_e_3212_, uint8_t v___x_3213_, lean_object* v___f_3214_, lean_object* v_d_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = 0;
v___x_3222_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_3212_, v___x_3221_, v___x_3213_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3239_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3239_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3239_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v_fst_3227_; 
v_fst_3227_ = lean_ctor_get(v_a_3223_, 0);
lean_inc(v_fst_3227_);
if (lean_obj_tag(v_fst_3227_) == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_del_object(v___x_3225_);
lean_dec(v_a_3223_);
v___x_3228_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___closed__0));
v___x_3229_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_3214_, v_d_3215_, v___x_3228_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3229_;
}
else
{
lean_object* v_snd_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec_ref(v___f_3214_);
v_snd_3230_ = lean_ctor_get(v_a_3223_, 1);
lean_inc(v_snd_3230_);
lean_dec(v_a_3223_);
v___x_3231_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_3215_);
v___x_3232_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_3215_, v_fst_3227_);
lean_dec(v_fst_3227_);
lean_dec_ref(v_d_3215_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v___x_3234_; 
lean_dec(v_snd_3230_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3231_);
v___x_3234_ = v___x_3225_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3231_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
else
{
lean_object* v_val_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_del_object(v___x_3225_);
v_val_3236_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3237_ = lean_unsigned_to_nat(0u);
v___x_3238_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_3237_, v_snd_3230_, v_val_3236_, v___x_3231_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v_d_3215_);
lean_dec_ref(v___f_3214_);
v_a_3240_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3222_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3222_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1___boxed(lean_object* v_e_3248_, lean_object* v___x_3249_, lean_object* v___f_3250_, lean_object* v_d_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v___x_1524__boxed_3257_; lean_object* v_res_3258_; 
v___x_1524__boxed_3257_ = lean_unbox(v___x_3249_);
v_res_3258_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_3248_, v___x_1524__boxed_3257_, v___f_3250_, v_d_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_3260_, lean_object* v_e_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___y_3268_; lean_object* v___x_3285_; uint8_t v_transparency_3286_; lean_object* v___f_3287_; uint8_t v___x_3288_; uint8_t v___x_3289_; uint8_t v___x_3290_; 
v___x_3285_ = l_Lean_Meta_Context_config(v_a_3262_);
v_transparency_3286_ = lean_ctor_get_uint8(v___x_3285_, 9);
lean_dec_ref(v___x_3285_);
v___f_3287_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_3288_ = 1;
v___x_3289_ = 2;
v___x_3290_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3286_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v_keyedConfig_3291_; uint8_t v_trackZetaDelta_3292_; lean_object* v_zetaDeltaSet_3293_; lean_object* v_lctx_3294_; lean_object* v_localInstances_3295_; lean_object* v_defEqCtx_x3f_3296_; lean_object* v_synthPendingDepth_3297_; lean_object* v_customCanUnfoldPredicate_x3f_3298_; uint8_t v_univApprox_3299_; uint8_t v_inTypeClassResolution_3300_; uint8_t v_cacheInferType_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_keyedConfig_3291_ = lean_ctor_get(v_a_3262_, 0);
v_trackZetaDelta_3292_ = lean_ctor_get_uint8(v_a_3262_, sizeof(void*)*7);
v_zetaDeltaSet_3293_ = lean_ctor_get(v_a_3262_, 1);
v_lctx_3294_ = lean_ctor_get(v_a_3262_, 2);
v_localInstances_3295_ = lean_ctor_get(v_a_3262_, 3);
v_defEqCtx_x3f_3296_ = lean_ctor_get(v_a_3262_, 4);
v_synthPendingDepth_3297_ = lean_ctor_get(v_a_3262_, 5);
v_customCanUnfoldPredicate_x3f_3298_ = lean_ctor_get(v_a_3262_, 6);
v_univApprox_3299_ = lean_ctor_get_uint8(v_a_3262_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3300_ = lean_ctor_get_uint8(v_a_3262_, sizeof(void*)*7 + 2);
v_cacheInferType_3301_ = lean_ctor_get_uint8(v_a_3262_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3291_);
v___x_3302_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3289_, v_keyedConfig_3291_);
lean_inc(v_customCanUnfoldPredicate_x3f_3298_);
lean_inc(v_synthPendingDepth_3297_);
lean_inc(v_defEqCtx_x3f_3296_);
lean_inc_ref(v_localInstances_3295_);
lean_inc_ref(v_lctx_3294_);
lean_inc(v_zetaDeltaSet_3293_);
v___x_3303_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v_zetaDeltaSet_3293_);
lean_ctor_set(v___x_3303_, 2, v_lctx_3294_);
lean_ctor_set(v___x_3303_, 3, v_localInstances_3295_);
lean_ctor_set(v___x_3303_, 4, v_defEqCtx_x3f_3296_);
lean_ctor_set(v___x_3303_, 5, v_synthPendingDepth_3297_);
lean_ctor_set(v___x_3303_, 6, v_customCanUnfoldPredicate_x3f_3298_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*7, v_trackZetaDelta_3292_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*7 + 1, v_univApprox_3299_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3300_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*7 + 3, v_cacheInferType_3301_);
v___x_3304_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_3261_, v___x_3288_, v___f_3287_, v_d_3260_, v___x_3303_, v_a_3263_, v_a_3264_, v_a_3265_);
lean_dec_ref_known(v___x_3303_, 7);
v___y_3268_ = v___x_3304_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__1(v_e_3261_, v___x_3288_, v___f_3287_, v_d_3260_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
v___y_3268_ = v___x_3305_;
goto v___jp_3267_;
}
v___jp_3267_:
{
if (lean_obj_tag(v___y_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
v_a_3269_ = lean_ctor_get(v___y_3268_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___y_3268_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___y_3268_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___y_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v_a_3277_ = lean_ctor_get(v___y_3268_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___y_3268_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___y_3268_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___y_3268_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_3306_, lean_object* v_e_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_3306_, v_e_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_3314_, lean_object* v_d_3315_, lean_object* v_e_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_3315_, v_e_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_3323_, lean_object* v_d_3324_, lean_object* v_e_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_3323_, v_d_3324_, v_e_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_3332_, lean_object* v_f_3333_, lean_object* v_init_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3333_, v_map_3332_, v_init_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_3341_, lean_object* v_f_3342_, lean_object* v_init_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_3341_, v_f_3342_, v_init_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_3350_, lean_object* v_00_u03b2_3351_, lean_object* v_map_3352_, lean_object* v_f_3353_, lean_object* v_init_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3353_, v_map_3352_, v_init_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_3361_, lean_object* v_00_u03b2_3362_, lean_object* v_map_3363_, lean_object* v_f_3364_, lean_object* v_init_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_3361_, v_00_u03b2_3362_, v_map_3363_, v_f_3364_, v_init_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_3372_, lean_object* v_00_u03b1_3373_, lean_object* v_00_u03b2_3374_, lean_object* v_f_3375_, lean_object* v_x_3376_, lean_object* v_x_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_3375_, v_x_3376_, v_x_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3384_, lean_object* v_00_u03b1_3385_, lean_object* v_00_u03b2_3386_, lean_object* v_f_3387_, lean_object* v_x_3388_, lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_3384_, v_00_u03b1_3385_, v_00_u03b2_3386_, v_f_3387_, v_x_3388_, v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3396_, lean_object* v_00_u03b2_3397_, lean_object* v_00_u03c3_3398_, lean_object* v_f_3399_, lean_object* v_as_3400_, size_t v_i_3401_, size_t v_stop_3402_, lean_object* v_b_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3399_, v_as_3400_, v_i_3401_, v_stop_3402_, v_b_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3410_, lean_object* v_00_u03b2_3411_, lean_object* v_00_u03c3_3412_, lean_object* v_f_3413_, lean_object* v_as_3414_, lean_object* v_i_3415_, lean_object* v_stop_3416_, lean_object* v_b_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
size_t v_i_boxed_3423_; size_t v_stop_boxed_3424_; lean_object* v_res_3425_; 
v_i_boxed_3423_ = lean_unbox_usize(v_i_3415_);
lean_dec(v_i_3415_);
v_stop_boxed_3424_ = lean_unbox_usize(v_stop_3416_);
lean_dec(v_stop_3416_);
v_res_3425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_3410_, v_00_u03b2_3411_, v_00_u03c3_3412_, v_f_3413_, v_as_3414_, v_i_boxed_3423_, v_stop_boxed_3424_, v_b_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v_as_3414_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_3426_, lean_object* v_00_u03b1_3427_, lean_object* v_00_u03b2_3428_, lean_object* v_f_3429_, lean_object* v_keys_3430_, lean_object* v_vals_3431_, lean_object* v_heq_3432_, lean_object* v_i_3433_, lean_object* v_acc_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3429_, v_keys_3430_, v_vals_3431_, v_i_3433_, v_acc_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_3441_, lean_object* v_00_u03b1_3442_, lean_object* v_00_u03b2_3443_, lean_object* v_f_3444_, lean_object* v_keys_3445_, lean_object* v_vals_3446_, lean_object* v_heq_3447_, lean_object* v_i_3448_, lean_object* v_acc_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_3441_, v_00_u03b1_3442_, v_00_u03b2_3443_, v_f_3444_, v_keys_3445_, v_vals_3446_, v_heq_3447_, v_i_3448_, v_acc_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_vals_3446_);
lean_dec_ref(v_keys_3445_);
return v_res_3455_;
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
