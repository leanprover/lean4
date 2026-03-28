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
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_is_class(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object*, lean_object*);
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
lean_dec_ref(v_x_64_);
v___x_73_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(v_arg_72_, v_x_63_, v_infos_62_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; uint8_t v___x_75_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_a_74_);
lean_dec_ref(v___x_73_);
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
lean_object* v_fName_123_; uint8_t v___y_125_; uint8_t v___y_138_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_fName_123_ = l_Lean_Expr_constName_x21(v_f_121_);
lean_dec_ref(v_f_121_);
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_147_ = lean_name_eq(v_fName_123_, v___x_146_);
if (v___x_147_ == 0)
{
v___y_138_ = v___x_147_;
goto v___jp_137_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = l_Lean_Expr_getAppNumArgs(v_e_118_);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_dec_eq(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
v___y_138_ = v___x_150_;
goto v___jp_137_;
}
v___jp_124_:
{
if (v___y_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2));
v___x_127_ = lean_name_eq(v_fName_123_, v___x_126_);
lean_dec(v_fName_123_);
if (v___x_127_ == 0)
{
lean_dec_ref(v_e_118_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
return v___x_120_;
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = l_Lean_Expr_getAppNumArgs(v_e_118_);
lean_dec_ref(v_e_118_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_nat_dec_eq(v___x_128_, v___x_129_);
lean_dec(v___x_128_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
return v___x_120_;
}
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_fName_123_);
v___x_131_ = lean_unsigned_to_nat(1u);
v___x_132_ = l_Lean_Expr_getAppNumArgs(v_e_118_);
v___x_133_ = lean_nat_sub(v___x_132_, v___x_131_);
lean_dec(v___x_132_);
v___x_134_ = lean_nat_sub(v___x_133_, v___x_131_);
lean_dec(v___x_133_);
v___x_135_ = l_Lean_Expr_getRevArg_x21(v_e_118_, v___x_134_);
lean_dec_ref(v_e_118_);
v_e_118_ = v___x_135_;
goto _start;
}
}
v___jp_137_:
{
if (v___y_138_ == 0)
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5));
v___x_140_ = lean_name_eq(v_fName_123_, v___x_139_);
if (v___x_140_ == 0)
{
v___y_125_ = v___x_140_;
goto v___jp_124_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = l_Lean_Expr_getAppNumArgs(v_e_118_);
v___x_142_ = lean_unsigned_to_nat(3u);
v___x_143_ = lean_nat_dec_eq(v___x_141_, v___x_142_);
lean_dec(v___x_141_);
v___y_125_ = v___x_143_;
goto v___jp_124_;
}
}
else
{
lean_object* v___x_144_; 
lean_dec(v_fName_123_);
v___x_144_ = l_Lean_Expr_appArg_x21(v_e_118_);
lean_dec_ref(v_e_118_);
v_e_118_ = v___x_144_;
goto _start;
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
lean_dec_ref(v_f_161_);
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
lean_dec_ref(v_f_161_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(lean_object* v_e_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___boxed(lean_object* v_e_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v_e_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(lean_object* v_fName_273_, lean_object* v_e_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
uint8_t v___y_281_; uint8_t v___y_311_; uint8_t v___y_336_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6));
v___x_347_ = lean_name_eq(v_fName_273_, v___x_346_);
if (v___x_347_ == 0)
{
v___y_336_ = v___x_347_;
goto v___jp_335_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_348_ = l_Lean_Expr_getAppNumArgs(v_e_274_);
v___x_349_ = lean_unsigned_to_nat(2u);
v___x_350_ = lean_nat_dec_eq(v___x_348_, v___x_349_);
lean_dec(v___x_348_);
v___y_336_ = v___x_350_;
goto v___jp_335_;
}
v___jp_280_:
{
if (v___y_281_ == 0)
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7));
v___x_283_ = lean_name_eq(v_fName_273_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_box(v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_286_ = l_Lean_Expr_getAppNumArgs(v_e_274_);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = l_Lean_Expr_getAppNumArgs(v_e_274_);
v___x_293_ = lean_nat_sub(v___x_292_, v___x_291_);
lean_dec(v___x_292_);
v___x_294_ = lean_nat_sub(v___x_293_, v___x_291_);
lean_dec(v___x_293_);
v___x_295_ = l_Lean_Expr_getRevArg_x21(v_e_274_, v___x_294_);
v___x_296_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_295_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; uint8_t v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
v___x_298_ = lean_unbox(v_a_297_);
lean_dec(v_a_297_);
if (v___x_298_ == 0)
{
return v___x_296_;
}
else
{
lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_308_; 
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_296_, 0);
lean_dec(v_unused_309_);
v___x_300_ = v___x_296_;
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
else
{
lean_dec(v___x_296_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_302_ = l_Lean_Expr_appArg_x21(v_e_274_);
v___x_303_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_302_);
v___x_304_ = lean_box(v___x_303_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_304_);
v___x_306_ = v___x_300_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
else
{
return v___x_296_;
}
}
}
v___jp_310_:
{
if (v___y_311_ == 0)
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2));
v___x_313_ = lean_name_eq(v_fName_273_, v___x_312_);
if (v___x_313_ == 0)
{
v___y_281_ = v___x_313_;
goto v___jp_280_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = l_Lean_Expr_getAppNumArgs(v_e_274_);
v___x_315_ = lean_unsigned_to_nat(6u);
v___x_316_ = lean_nat_dec_eq(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
v___y_281_ = v___x_316_;
goto v___jp_280_;
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = l_Lean_Expr_getAppNumArgs(v_e_274_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_sub(v___x_317_, v___x_318_);
lean_dec(v___x_317_);
v___x_320_ = l_Lean_Expr_getRevArg_x21(v_e_274_, v___x_319_);
v___x_321_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(v___x_320_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; uint8_t v___x_323_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
v___x_323_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
if (v___x_323_ == 0)
{
return v___x_321_;
}
else
{
lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_333_; 
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___x_321_, 0);
lean_dec(v_unused_334_);
v___x_325_ = v___x_321_;
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
else
{
lean_dec(v___x_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_327_ = l_Lean_Expr_appArg_x21(v_e_274_);
v___x_328_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_327_);
v___x_329_ = lean_box(v___x_328_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_329_);
v___x_331_ = v___x_325_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
return v___x_321_;
}
}
}
v___jp_335_:
{
if (v___y_336_ == 0)
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5));
v___x_338_ = lean_name_eq(v_fName_273_, v___x_337_);
if (v___x_338_ == 0)
{
v___y_311_ = v___x_338_;
goto v___jp_310_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = l_Lean_Expr_getAppNumArgs(v_e_274_);
v___x_340_ = lean_unsigned_to_nat(4u);
v___x_341_ = lean_nat_dec_eq(v___x_339_, v___x_340_);
lean_dec(v___x_339_);
v___y_311_ = v___x_341_;
goto v___jp_310_;
}
}
else
{
lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = l_Lean_Expr_appArg_x21(v_e_274_);
v___x_343_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v___x_342_);
v___x_344_ = lean_box(v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___boxed(lean_object* v_fName_351_, lean_object* v_e_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_351_, v_e_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec_ref(v_e_352_);
lean_dec(v_fName_351_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(lean_object* v_fName_359_, lean_object* v_e_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_fName_359_, v_e_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(lean_object* v_fName_367_, lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(v_fName_367_, v_e_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec_ref(v_e_368_);
lean_dec(v_fName_367_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object* v_e_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_whnfCore(v_e_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; uint8_t v___x_383_; lean_object* v___x_384_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_n(v_a_382_, 2);
lean_dec_ref(v___x_381_);
v___x_383_ = 0;
v___x_384_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_382_, v___x_383_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_397_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_397_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
if (lean_obj_tag(v_a_385_) == 0)
{
lean_object* v___x_389_; 
lean_inc(v_a_382_);
v___x_389_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_382_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_391_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_a_382_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_382_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
else
{
lean_object* v_val_393_; 
lean_del_object(v___x_387_);
lean_dec(v_a_382_);
v_val_393_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_393_);
lean_dec_ref(v___x_389_);
v_e_375_ = v_val_393_;
goto _start;
}
}
else
{
lean_object* v_val_395_; 
lean_del_object(v___x_387_);
lean_dec(v_a_382_);
v_val_395_ = lean_ctor_get(v_a_385_, 0);
lean_inc(v_val_395_);
lean_dec_ref(v_a_385_);
v_e_375_ = v_val_395_;
goto _start;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_a_382_);
v_a_398_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_384_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_384_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_DiscrTree_reduce(v_e_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_412_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(lean_object* v_fn_413_){
_start:
{
switch(lean_obj_tag(v_fn_413_))
{
case 9:
{
uint8_t v___x_414_; 
v___x_414_ = 0;
return v___x_414_;
}
case 4:
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
case 1:
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
case 11:
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
case 7:
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
default: 
{
uint8_t v___x_419_; 
v___x_419_ = 1;
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey___boxed(lean_object* v_fn_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v_fn_420_);
lean_dec_ref(v_fn_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(lean_object* v_e_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_whnfCore(v_e_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; uint8_t v___x_431_; lean_object* v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_n(v_a_430_, 2);
lean_dec_ref(v___x_429_);
v___x_431_ = 0;
v___x_432_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_430_, v___x_431_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_447_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_447_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_447_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_447_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
if (lean_obj_tag(v_a_433_) == 0)
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_a_430_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_430_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v_val_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_val_440_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_val_440_);
lean_dec_ref(v_a_433_);
v___x_441_ = l_Lean_Expr_getAppFn(v_val_440_);
v___x_442_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v___x_441_);
lean_dec_ref(v___x_441_);
if (v___x_442_ == 0)
{
lean_del_object(v___x_435_);
lean_dec(v_a_430_);
v_e_423_ = v_val_440_;
goto _start;
}
else
{
lean_object* v___x_445_; 
lean_dec(v_val_440_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_a_430_);
v___x_445_ = v___x_435_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_430_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_a_430_);
v_a_448_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_432_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_432_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object* v_e_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
v___x_471_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
return v___x_469_;
}
else
{
lean_object* v_val_472_; 
lean_dec_ref(v___x_469_);
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref(v___x_471_);
v_e_463_ = v_val_472_;
goto _start;
}
}
else
{
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object* v_e_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object* v_e_481_, uint8_t v_root_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
if (v_root_482_ == 0)
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_DiscrTree_reduce(v_e_481_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_481_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduceDT___boxed(lean_object* v_e_490_, lean_object* v_root_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
uint8_t v_root_boxed_497_; lean_object* v_res_498_; 
v_root_boxed_497_ = lean_unbox(v_root_491_);
v_res_498_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_490_, v_root_boxed_497_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(lean_object* v_n_499_, lean_object* v_todo_500_){
_start:
{
lean_object* v_zero_501_; uint8_t v_isZero_502_; 
v_zero_501_ = lean_unsigned_to_nat(0u);
v_isZero_502_ = lean_nat_dec_eq(v_n_499_, v_zero_501_);
if (v_isZero_502_ == 1)
{
lean_dec(v_n_499_);
return v_todo_500_;
}
else
{
lean_object* v_one_503_; lean_object* v_n_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_one_503_ = lean_unsigned_to_nat(1u);
v_n_504_ = lean_nat_sub(v_n_499_, v_one_503_);
lean_dec(v_n_499_);
v___x_505_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
v___x_506_ = lean_array_push(v_todo_500_, v___x_505_);
v_n_499_ = v_n_504_;
v_todo_500_ = v___x_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(uint8_t v_root_508_, lean_object* v_todo_509_, lean_object* v_e_510_, uint8_t v_noIndexAtArgs_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___y_518_; lean_object* v_todo_519_; uint8_t v___x_522_; 
v___x_522_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_510_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_510_, v_root_508_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_653_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_653_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_653_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_653_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_v_529_; lean_object* v___x_535_; lean_object* v_k_537_; lean_object* v_nargs_538_; lean_object* v_todo_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; 
v___x_535_ = l_Lean_Expr_getAppFn(v_a_524_);
switch(lean_obj_tag(v___x_535_))
{
case 9:
{
lean_object* v_a_568_; 
lean_dec(v_a_524_);
v_a_568_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_a_568_);
lean_dec_ref(v___x_535_);
v_v_529_ = v_a_568_;
goto v___jp_528_;
}
case 4:
{
lean_object* v_declName_569_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; 
v_declName_569_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_declName_569_);
if (v_root_508_ == 0)
{
lean_object* v___x_577_; 
lean_inc(v_a_524_);
v___x_577_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_524_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; 
lean_dec(v_declName_569_);
lean_dec_ref(v___x_535_);
lean_dec(v_a_524_);
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref(v___x_577_);
v_v_529_ = v_val_578_;
goto v___jp_528_;
}
else
{
lean_object* v___x_579_; 
lean_dec(v___x_577_);
lean_del_object(v___x_526_);
v___x_579_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_declName_569_, v_a_524_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_590_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_590_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_590_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_590_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
uint8_t v___x_584_; 
v___x_584_ = lean_unbox(v_a_580_);
lean_dec(v_a_580_);
if (v___x_584_ == 0)
{
lean_del_object(v___x_582_);
v___y_571_ = v_a_512_;
v___y_572_ = v_a_513_;
v___y_573_ = v_a_514_;
v___y_574_ = v_a_515_;
goto v___jp_570_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec(v_declName_569_);
lean_dec_ref(v___x_535_);
lean_dec(v_a_524_);
v___x_585_ = lean_box(0);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_todo_509_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_586_);
v___x_588_ = v___x_582_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v_declName_569_);
lean_dec_ref(v___x_535_);
lean_dec(v_a_524_);
lean_dec_ref(v_todo_509_);
v_a_591_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_579_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_579_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
else
{
lean_del_object(v___x_526_);
v___y_571_ = v_a_512_;
v___y_572_ = v_a_513_;
v___y_573_ = v_a_514_;
v___y_574_ = v_a_515_;
goto v___jp_570_;
}
v___jp_570_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = l_Lean_Expr_getAppNumArgs(v_a_524_);
lean_inc(v___x_575_);
v___x_576_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_576_, 0, v_declName_569_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v_k_537_ = v___x_576_;
v_nargs_538_ = v___x_575_;
v_todo_539_ = v_todo_509_;
v___y_540_ = v___y_571_;
v___y_541_ = v___y_572_;
v___y_542_ = v___y_573_;
v___y_543_ = v___y_574_;
goto v___jp_536_;
}
}
case 11:
{
lean_object* v_typeName_599_; lean_object* v_idx_600_; lean_object* v_struct_601_; lean_object* v___x_602_; lean_object* v___y_604_; lean_object* v_env_608_; uint8_t v___x_609_; 
lean_del_object(v___x_526_);
v_typeName_599_ = lean_ctor_get(v___x_535_, 0);
lean_inc_n(v_typeName_599_, 2);
v_idx_600_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_idx_600_);
v_struct_601_ = lean_ctor_get(v___x_535_, 2);
lean_inc_ref(v_struct_601_);
v___x_602_ = lean_st_ref_get(v_a_515_);
v_env_608_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_env_608_);
lean_dec(v___x_602_);
v___x_609_ = lean_is_class(v_env_608_, v_typeName_599_);
if (v___x_609_ == 0)
{
v___y_604_ = v_struct_601_;
goto v___jp_603_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_601_);
v___y_604_ = v___x_610_;
goto v___jp_603_;
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_Expr_getAppNumArgs(v_a_524_);
lean_inc(v___x_605_);
v___x_606_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_606_, 0, v_typeName_599_);
lean_ctor_set(v___x_606_, 1, v_idx_600_);
lean_ctor_set(v___x_606_, 2, v___x_605_);
v___x_607_ = lean_array_push(v_todo_509_, v___y_604_);
v_k_537_ = v___x_606_;
v_nargs_538_ = v___x_605_;
v_todo_539_ = v___x_607_;
v___y_540_ = v_a_512_;
v___y_541_ = v_a_513_;
v___y_542_ = v_a_514_;
v___y_543_ = v_a_515_;
goto v___jp_536_;
}
}
case 1:
{
lean_object* v_fvarId_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_del_object(v___x_526_);
v_fvarId_611_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_fvarId_611_);
v___x_612_ = l_Lean_Expr_getAppNumArgs(v_a_524_);
lean_inc(v___x_612_);
v___x_613_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_613_, 0, v_fvarId_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v_k_537_ = v___x_613_;
v_nargs_538_ = v___x_612_;
v_todo_539_ = v_todo_509_;
v___y_540_ = v_a_512_;
v___y_541_ = v_a_513_;
v___y_542_ = v_a_514_;
v___y_543_ = v_a_515_;
goto v___jp_536_;
}
case 2:
{
lean_object* v_mvarId_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
lean_del_object(v___x_526_);
lean_dec(v_a_524_);
v_mvarId_614_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_mvarId_614_);
lean_dec_ref(v___x_535_);
v___x_615_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId));
v___x_616_ = l_Lean_instBEqMVarId_beq(v_mvarId_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_614_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_633_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_unbox(v_a_618_);
lean_dec(v_a_618_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v_todo_509_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_626_ = v___x_620_;
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
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_box(1);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_todo_509_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_629_);
v___x_631_ = v___x_620_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v_todo_509_);
v_a_634_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_617_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_617_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v_mvarId_614_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_todo_509_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
case 7:
{
lean_object* v_binderType_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_del_object(v___x_526_);
lean_dec(v_a_524_);
v_binderType_645_ = lean_ctor_get(v___x_535_, 1);
lean_inc_ref(v_binderType_645_);
lean_dec_ref(v___x_535_);
v___x_646_ = lean_box(5);
v___x_647_ = lean_array_push(v_todo_509_, v_binderType_645_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
default: 
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref(v___x_535_);
lean_del_object(v___x_526_);
lean_dec(v_a_524_);
v___x_650_ = lean_box(1);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_todo_509_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_530_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_530_, 0, v_v_529_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v_todo_509_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_531_);
v___x_533_ = v___x_526_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
v___jp_536_:
{
lean_object* v___x_544_; 
lean_inc(v_nargs_538_);
v___x_544_ = l_Lean_Meta_getFunInfoNArgs(v___x_535_, v_nargs_538_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
if (v_noIndexAtArgs_511_ == 0)
{
lean_object* v_a_545_; lean_object* v_paramInfo_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref(v___x_544_);
v_paramInfo_546_ = lean_ctor_get(v_a_545_, 0);
lean_inc_ref(v_paramInfo_546_);
lean_dec(v_a_545_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_sub(v_nargs_538_, v___x_547_);
lean_dec(v_nargs_538_);
v___x_549_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(v_paramInfo_546_, v___x_548_, v_a_524_, v_todo_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec_ref(v_paramInfo_546_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_549_);
v___y_518_ = v_k_537_;
v_todo_519_ = v_a_550_;
goto v___jp_517_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec(v_k_537_);
v_a_551_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_549_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_549_);
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
lean_object* v___x_559_; 
lean_dec_ref(v___x_544_);
lean_dec(v_a_524_);
v___x_559_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(v_nargs_538_, v_todo_539_);
v___y_518_ = v_k_537_;
v_todo_519_ = v___x_559_;
goto v___jp_517_;
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v_todo_539_);
lean_dec(v_nargs_538_);
lean_dec(v_k_537_);
lean_dec(v_a_524_);
v_a_560_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_544_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_544_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_todo_509_);
v_a_654_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_523_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_523_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref(v_e_510_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_todo_509_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
v___jp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_518_);
lean_ctor_set(v___x_520_, 1, v_todo_519_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs___boxed(lean_object* v_root_665_, lean_object* v_todo_666_, lean_object* v_e_667_, lean_object* v_noIndexAtArgs_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
uint8_t v_root_boxed_674_; uint8_t v_noIndexAtArgs_boxed_675_; lean_object* v_res_676_; 
v_root_boxed_674_ = lean_unbox(v_root_665_);
v_noIndexAtArgs_boxed_675_ = lean_unbox(v_noIndexAtArgs_668_);
v_res_676_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_boxed_674_, v_todo_666_, v_e_667_, v_noIndexAtArgs_boxed_675_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux(uint8_t v_root_677_, lean_object* v_todo_678_, lean_object* v_keys_679_, uint8_t v_noIndexAtArgs_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_array_get_size(v_todo_678_);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_e_692_; lean_object* v_todo_693_; lean_object* v___x_694_; 
v___x_689_ = l_Lean_instInhabitedExpr;
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v___x_686_, v___x_690_);
v_e_692_ = lean_array_get(v___x_689_, v_todo_678_, v___x_691_);
lean_dec(v___x_691_);
v_todo_693_ = lean_array_pop(v_todo_678_);
v___x_694_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(v_root_677_, v_todo_693_, v_e_692_, v_noIndexAtArgs_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v_fst_696_; lean_object* v_snd_697_; lean_object* v___x_698_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v_fst_696_ = lean_ctor_get(v_a_695_, 0);
lean_inc(v_fst_696_);
v_snd_697_ = lean_ctor_get(v_a_695_, 1);
lean_inc(v_snd_697_);
lean_dec(v_a_695_);
v___x_698_ = lean_array_push(v_keys_679_, v_fst_696_);
v_root_677_ = v___x_688_;
v_todo_678_ = v_snd_697_;
v_keys_679_ = v___x_698_;
goto _start;
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_keys_679_);
v_a_700_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_694_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_694_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec_ref(v_todo_678_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_keys_679_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPathAux___boxed(lean_object* v_root_709_, lean_object* v_todo_710_, lean_object* v_keys_711_, lean_object* v_noIndexAtArgs_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
uint8_t v_root_boxed_718_; uint8_t v_noIndexAtArgs_boxed_719_; lean_object* v_res_720_; 
v_root_boxed_718_ = lean_unbox(v_root_709_);
v_noIndexAtArgs_boxed_719_ = lean_unbox(v_noIndexAtArgs_712_);
v_res_720_ = l_Lean_Meta_DiscrTree_mkPathAux(v_root_boxed_718_, v_todo_710_, v_keys_711_, v_noIndexAtArgs_boxed_719_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_720_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_unsigned_to_nat(8u);
return v___x_721_;
}
}
static uint64_t _init_l_Lean_Meta_DiscrTree_mkPath___closed__0(void){
_start:
{
uint8_t v___x_722_; uint64_t v___x_723_; 
v___x_722_ = 2;
v___x_723_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object* v_e_724_, uint8_t v_noIndexAtArgs_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; uint8_t v_foApprox_732_; uint8_t v_ctxApprox_733_; uint8_t v_quasiPatternApprox_734_; uint8_t v_constApprox_735_; uint8_t v_isDefEqStuckEx_736_; uint8_t v_unificationHints_737_; uint8_t v_proofIrrelevance_738_; uint8_t v_assignSyntheticOpaque_739_; uint8_t v_offsetCnstrs_740_; uint8_t v_etaStruct_741_; uint8_t v_univApprox_742_; uint8_t v_iota_743_; uint8_t v_beta_744_; uint8_t v_proj_745_; uint8_t v_zeta_746_; uint8_t v_zetaDelta_747_; uint8_t v_zetaUnused_748_; uint8_t v_zetaHave_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_780_; 
v___x_731_ = l_Lean_Meta_Context_config(v_a_726_);
v_foApprox_732_ = lean_ctor_get_uint8(v___x_731_, 0);
v_ctxApprox_733_ = lean_ctor_get_uint8(v___x_731_, 1);
v_quasiPatternApprox_734_ = lean_ctor_get_uint8(v___x_731_, 2);
v_constApprox_735_ = lean_ctor_get_uint8(v___x_731_, 3);
v_isDefEqStuckEx_736_ = lean_ctor_get_uint8(v___x_731_, 4);
v_unificationHints_737_ = lean_ctor_get_uint8(v___x_731_, 5);
v_proofIrrelevance_738_ = lean_ctor_get_uint8(v___x_731_, 6);
v_assignSyntheticOpaque_739_ = lean_ctor_get_uint8(v___x_731_, 7);
v_offsetCnstrs_740_ = lean_ctor_get_uint8(v___x_731_, 8);
v_etaStruct_741_ = lean_ctor_get_uint8(v___x_731_, 10);
v_univApprox_742_ = lean_ctor_get_uint8(v___x_731_, 11);
v_iota_743_ = lean_ctor_get_uint8(v___x_731_, 12);
v_beta_744_ = lean_ctor_get_uint8(v___x_731_, 13);
v_proj_745_ = lean_ctor_get_uint8(v___x_731_, 14);
v_zeta_746_ = lean_ctor_get_uint8(v___x_731_, 15);
v_zetaDelta_747_ = lean_ctor_get_uint8(v___x_731_, 16);
v_zetaUnused_748_ = lean_ctor_get_uint8(v___x_731_, 17);
v_zetaHave_749_ = lean_ctor_get_uint8(v___x_731_, 18);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_780_ == 0)
{
v___x_751_ = v___x_731_;
v_isShared_752_ = v_isSharedCheck_780_;
goto v_resetjp_750_;
}
else
{
lean_dec(v___x_731_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_780_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
uint8_t v_trackZetaDelta_753_; lean_object* v_zetaDeltaSet_754_; lean_object* v_lctx_755_; lean_object* v_localInstances_756_; lean_object* v_defEqCtx_x3f_757_; lean_object* v_synthPendingDepth_758_; lean_object* v_canUnfold_x3f_759_; uint8_t v_univApprox_760_; uint8_t v_inTypeClassResolution_761_; uint8_t v_cacheInferType_762_; uint8_t v___x_763_; lean_object* v_config_765_; 
v_trackZetaDelta_753_ = lean_ctor_get_uint8(v_a_726_, sizeof(void*)*7);
v_zetaDeltaSet_754_ = lean_ctor_get(v_a_726_, 1);
v_lctx_755_ = lean_ctor_get(v_a_726_, 2);
v_localInstances_756_ = lean_ctor_get(v_a_726_, 3);
v_defEqCtx_x3f_757_ = lean_ctor_get(v_a_726_, 4);
v_synthPendingDepth_758_ = lean_ctor_get(v_a_726_, 5);
v_canUnfold_x3f_759_ = lean_ctor_get(v_a_726_, 6);
v_univApprox_760_ = lean_ctor_get_uint8(v_a_726_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_761_ = lean_ctor_get_uint8(v_a_726_, sizeof(void*)*7 + 2);
v_cacheInferType_762_ = lean_ctor_get_uint8(v_a_726_, sizeof(void*)*7 + 3);
v___x_763_ = 2;
if (v_isShared_752_ == 0)
{
v_config_765_ = v___x_751_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 0, v_foApprox_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 1, v_ctxApprox_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 2, v_quasiPatternApprox_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 3, v_constApprox_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 4, v_isDefEqStuckEx_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 5, v_unificationHints_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 6, v_proofIrrelevance_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 7, v_assignSyntheticOpaque_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 8, v_offsetCnstrs_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 10, v_etaStruct_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 11, v_univApprox_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 12, v_iota_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 13, v_beta_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 14, v_proj_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 15, v_zeta_746_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 16, v_zetaDelta_747_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 17, v_zetaUnused_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, 18, v_zetaHave_749_);
v_config_765_ = v_reuseFailAlloc_779_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
uint64_t v___x_766_; uint64_t v___x_767_; uint64_t v___x_768_; lean_object* v___x_769_; lean_object* v_todo_770_; uint8_t v___x_771_; lean_object* v___x_772_; uint64_t v___x_773_; uint64_t v___x_774_; uint64_t v_key_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_ctor_set_uint8(v_config_765_, 9, v___x_763_);
v___x_766_ = l_Lean_Meta_Context_configKey(v_a_726_);
v___x_767_ = 2ULL;
v___x_768_ = lean_uint64_shift_right(v___x_766_, v___x_767_);
v___x_769_ = lean_unsigned_to_nat(8u);
v_todo_770_ = lean_mk_empty_array_with_capacity(v___x_769_);
v___x_771_ = 1;
lean_inc_ref(v_todo_770_);
v___x_772_ = lean_array_push(v_todo_770_, v_e_724_);
v___x_773_ = lean_uint64_shift_left(v___x_768_, v___x_767_);
v___x_774_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_775_ = lean_uint64_lor(v___x_773_, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_776_, 0, v_config_765_);
lean_ctor_set_uint64(v___x_776_, sizeof(void*)*1, v_key_775_);
lean_inc(v_canUnfold_x3f_759_);
lean_inc(v_synthPendingDepth_758_);
lean_inc(v_defEqCtx_x3f_757_);
lean_inc_ref(v_localInstances_756_);
lean_inc_ref(v_lctx_755_);
lean_inc(v_zetaDeltaSet_754_);
v___x_777_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v_zetaDeltaSet_754_);
lean_ctor_set(v___x_777_, 2, v_lctx_755_);
lean_ctor_set(v___x_777_, 3, v_localInstances_756_);
lean_ctor_set(v___x_777_, 4, v_defEqCtx_x3f_757_);
lean_ctor_set(v___x_777_, 5, v_synthPendingDepth_758_);
lean_ctor_set(v___x_777_, 6, v_canUnfold_x3f_759_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*7, v_trackZetaDelta_753_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*7 + 1, v_univApprox_760_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*7 + 2, v_inTypeClassResolution_761_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*7 + 3, v_cacheInferType_762_);
v___x_778_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_771_, v___x_772_, v_todo_770_, v_noIndexAtArgs_725_, v___x_777_, v_a_727_, v_a_728_, v_a_729_);
lean_dec_ref(v___x_777_);
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object* v_e_781_, lean_object* v_noIndexAtArgs_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_788_; lean_object* v_res_789_; 
v_noIndexAtArgs_boxed_788_ = lean_unbox(v_noIndexAtArgs_782_);
v_res_789_ = l_Lean_Meta_DiscrTree_mkPath(v_e_781_, v_noIndexAtArgs_boxed_788_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg(lean_object* v_inst_790_, lean_object* v_d_791_, lean_object* v_e_792_, lean_object* v_v_793_, uint8_t v_noIndexAtArgs_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_DiscrTree_mkPath(v_e_792_, v_noIndexAtArgs_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_809_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_790_, v_d_791_, v_a_801_, v_v_793_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_v_793_);
lean_dec_ref(v_d_791_);
lean_dec_ref(v_inst_790_);
v_a_810_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_800_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg___boxed(lean_object* v_inst_818_, lean_object* v_d_819_, lean_object* v_e_820_, lean_object* v_v_821_, lean_object* v_noIndexAtArgs_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_828_; lean_object* v_res_829_; 
v_noIndexAtArgs_boxed_828_ = lean_unbox(v_noIndexAtArgs_822_);
v_res_829_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_818_, v_d_819_, v_e_820_, v_v_821_, v_noIndexAtArgs_boxed_828_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* v_00_u03b1_830_, lean_object* v_inst_831_, lean_object* v_d_832_, lean_object* v_e_833_, lean_object* v_v_834_, uint8_t v_noIndexAtArgs_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_831_, v_d_832_, v_e_833_, v_v_834_, v_noIndexAtArgs_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___boxed(lean_object* v_00_u03b1_842_, lean_object* v_inst_843_, lean_object* v_d_844_, lean_object* v_e_845_, lean_object* v_v_846_, lean_object* v_noIndexAtArgs_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_853_; lean_object* v_res_854_; 
v_noIndexAtArgs_boxed_853_ = lean_unbox(v_noIndexAtArgs_847_);
v_res_854_ = l_Lean_Meta_DiscrTree_insert(v_00_u03b1_842_, v_inst_843_, v_d_844_, v_e_845_, v_v_846_, v_noIndexAtArgs_boxed_853_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_870_ = lean_array_get_size(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_877_ = lean_array_get_size(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(lean_object* v_inst_878_, lean_object* v_d_879_, lean_object* v_e_880_, lean_object* v_v_881_, uint8_t v_noIndexAtArgs_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Meta_DiscrTree_mkPath(v_e_880_, v_noIndexAtArgs_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_913_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_913_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_913_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_913_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_906_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_907_ = lean_array_get_size(v_a_889_);
v___x_908_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7);
v___x_909_ = lean_nat_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
goto v___jp_898_;
}
else
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_911_ = l_Array_isEqvAux___redArg(v_a_889_, v___x_906_, v___x_910_, v___x_907_);
if (v___x_911_ == 0)
{
goto v___jp_898_;
}
else
{
lean_object* v___x_912_; 
lean_del_object(v___x_891_);
lean_dec(v_a_889_);
lean_dec(v_v_881_);
lean_dec_ref(v_inst_878_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_d_879_);
return v___x_912_;
}
}
v___jp_893_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_878_, v_d_879_, v_a_889_, v_v_881_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
v___jp_898_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_899_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_900_ = lean_array_get_size(v_a_889_);
v___x_901_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4);
v___x_902_ = lean_nat_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
goto v___jp_893_;
}
else
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_904_ = l_Array_isEqvAux___redArg(v_a_889_, v___x_899_, v___x_903_, v___x_900_);
if (v___x_904_ == 0)
{
goto v___jp_893_;
}
else
{
lean_object* v___x_905_; 
lean_del_object(v___x_891_);
lean_dec(v_a_889_);
lean_dec(v_v_881_);
lean_dec_ref(v_inst_878_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v_d_879_);
return v___x_905_;
}
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_v_881_);
lean_dec_ref(v_d_879_);
lean_dec_ref(v_inst_878_);
v_a_914_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_888_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_888_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(lean_object* v_inst_922_, lean_object* v_d_923_, lean_object* v_e_924_, lean_object* v_v_925_, lean_object* v_noIndexAtArgs_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_932_; lean_object* v_res_933_; 
v_noIndexAtArgs_boxed_932_ = lean_unbox(v_noIndexAtArgs_926_);
v_res_933_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_922_, v_d_923_, v_e_924_, v_v_925_, v_noIndexAtArgs_boxed_932_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific(lean_object* v_00_u03b1_934_, lean_object* v_inst_935_, lean_object* v_d_936_, lean_object* v_e_937_, lean_object* v_v_938_, uint8_t v_noIndexAtArgs_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_935_, v_d_936_, v_e_937_, v_v_938_, v_noIndexAtArgs_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(lean_object* v_00_u03b1_946_, lean_object* v_inst_947_, lean_object* v_d_948_, lean_object* v_e_949_, lean_object* v_v_950_, lean_object* v_noIndexAtArgs_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_957_; lean_object* v_res_958_; 
v_noIndexAtArgs_boxed_957_ = lean_unbox(v_noIndexAtArgs_951_);
v_res_958_ = l_Lean_Meta_DiscrTree_insertIfSpecific(v_00_u03b1_946_, v_inst_947_, v_d_948_, v_e_949_, v_v_950_, v_noIndexAtArgs_boxed_957_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(lean_object* v_declName_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_env_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_962_ = lean_st_ref_get(v___y_960_);
v_env_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_env_963_);
lean_dec(v___x_962_);
v___x_964_ = l_Lean_isRecCore(v_env_963_, v_declName_959_);
v___x_965_ = lean_box(v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_967_, v___y_968_);
lean_dec(v___y_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(lean_object* v_declName_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_971_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(lean_object* v_declName_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(lean_object* v_a_985_, lean_object* v_b_986_){
_start:
{
lean_object* v_array_988_; lean_object* v_start_989_; lean_object* v_stop_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1007_; 
v_array_988_ = lean_ctor_get(v_a_985_, 0);
v_start_989_ = lean_ctor_get(v_a_985_, 1);
v_stop_990_ = lean_ctor_get(v_a_985_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_a_985_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_992_ = v_a_985_;
v_isShared_993_ = v_isSharedCheck_1007_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_stop_990_);
lean_inc(v_start_989_);
lean_inc(v_array_988_);
lean_dec(v_a_985_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1007_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; 
v___x_994_ = lean_nat_dec_lt(v_start_989_, v_stop_990_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_del_object(v___x_992_);
lean_dec(v_stop_990_);
lean_dec(v_start_989_);
lean_dec_ref(v_array_988_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v_b_986_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_996_ = lean_box(0);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_start_989_, v___x_997_);
lean_inc_ref(v_array_988_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_998_);
v___x_1000_ = v___x_992_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_array_988_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_stop_990_);
v___x_1000_ = v_reuseFailAlloc_1006_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_array_fget(v_array_988_, v_start_989_);
lean_dec(v_start_989_);
lean_dec_ref(v_array_988_);
v___x_1002_ = l_Lean_Expr_hasExprMVar(v___x_1001_);
lean_dec(v___x_1001_);
if (v___x_1002_ == 0)
{
v_a_985_ = v___x_1000_;
v_b_986_ = v___x_996_;
goto _start;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_dec_ref(v___x_1004_);
v_a_985_ = v___x_1000_;
v_b_986_ = v___x_996_;
goto _start;
}
else
{
lean_dec_ref(v___x_1000_);
return v___x_1004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1008_, v_b_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; lean_object* v_env_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1015_ = lean_st_ref_get(v___y_1013_);
v_env_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc_ref(v_env_1016_);
lean_dec(v___x_1015_);
v___x_1017_ = lean_get_reducibility_status(v_env_1016_, v_declName_1012_);
v___x_1018_ = lean_box(v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1020_, v___y_1021_);
lean_dec(v___y_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(lean_object* v_declName_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1046_; 
v___x_1030_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1024_, v___y_1028_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1046_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1046_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_unbox(v_a_1031_);
lean_dec(v_a_1031_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1036_ = 1;
v___x_1037_ = lean_box(v___x_1036_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1037_);
v___x_1039_ = v___x_1033_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
else
{
uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1041_ = 0;
v___x_1042_ = lean_box(v___x_1041_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1042_);
v___x_1044_ = v___x_1033_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0___boxed(lean_object* v_declName_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1(void){
_start:
{
lean_object* v___x_1056_; lean_object* v_dummy_1057_; 
v___x_1056_ = lean_box(0);
v_dummy_1057_ = l_Lean_Expr_sort___override(v___x_1056_);
return v_dummy_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* v_e_1064_, uint8_t v_isMatch_1065_, uint8_t v_root_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1064_, v_root_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1229_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1229_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1229_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___y_1078_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; 
if (v_root_1066_ == 0)
{
lean_object* v___x_1217_; 
lean_inc(v_a_1073_);
v___x_1217_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_1073_);
if (lean_obj_tag(v___x_1217_) == 1)
{
lean_object* v_val_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1228_; 
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_val_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_val_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1228_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 2);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_val_1218_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
}
else
{
lean_dec(v___x_1217_);
v___y_1088_ = v_a_1067_;
v___y_1089_ = v_a_1068_;
v___y_1090_ = v_a_1069_;
v___y_1091_ = v_a_1070_;
goto v___jp_1087_;
}
}
else
{
v___y_1088_ = v_a_1067_;
v___y_1089_ = v_a_1068_;
v___y_1090_ = v_a_1069_;
v___y_1091_ = v_a_1070_;
goto v___jp_1087_;
}
v___jp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1079_ = l_Lean_Expr_getAppNumArgs(v_a_1073_);
lean_inc(v___x_1079_);
v___x_1080_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___y_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_mk_empty_array_with_capacity(v___x_1079_);
lean_dec(v___x_1079_);
v___x_1082_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1073_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1080_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1083_);
v___x_1085_ = v___x_1075_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
v___jp_1087_:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Expr_getAppFn(v_a_1073_);
switch(lean_obj_tag(v___x_1092_))
{
case 9:
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc_ref(v_a_1093_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_a_1093_);
v___x_1095_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
case 4:
{
lean_object* v_declName_1098_; lean_object* v___x_1099_; uint8_t v_isDefEqStuckEx_1100_; 
v_declName_1098_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_declName_1098_);
lean_dec_ref(v___x_1092_);
v___x_1099_ = l_Lean_Meta_Context_config(v___y_1088_);
v_isDefEqStuckEx_1100_ = lean_ctor_get_uint8(v___x_1099_, 4);
lean_dec_ref(v___x_1099_);
if (v_isDefEqStuckEx_1100_ == 0)
{
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Expr_hasExprMVar(v_a_1073_);
if (v___x_1101_ == 0)
{
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1102_; 
lean_inc(v_declName_1098_);
v___x_1102_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1098_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; uint8_t v___x_1104_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = lean_unbox(v_a_1103_);
lean_dec(v_a_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v_env_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_st_ref_get(v___y_1091_);
v_env_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref(v_env_1106_);
lean_dec(v___x_1105_);
v___x_1107_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1106_, v_a_1073_);
if (lean_obj_tag(v___x_1107_) == 1)
{
lean_object* v_val_1108_; lean_object* v_numDiscrs_1109_; lean_object* v_nargs_1110_; lean_object* v_dummy_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_val_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref(v___x_1107_);
v_numDiscrs_1109_ = lean_ctor_get(v_val_1108_, 1);
lean_inc(v_numDiscrs_1109_);
v_nargs_1110_ = l_Lean_Expr_getAppNumArgs(v_a_1073_);
v_dummy_1111_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
lean_inc(v_nargs_1110_);
v___x_1112_ = lean_mk_array(v_nargs_1110_, v_dummy_1111_);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_sub(v_nargs_1110_, v___x_1113_);
lean_dec(v_nargs_1110_);
lean_inc(v_a_1073_);
v___x_1115_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1073_, v___x_1112_, v___x_1114_);
v___x_1116_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1108_);
lean_dec(v_val_1108_);
v___x_1117_ = lean_nat_add(v___x_1116_, v_numDiscrs_1109_);
lean_dec(v_numDiscrs_1109_);
v___x_1118_ = l_Array_toSubarray___redArg(v___x_1115_, v___x_1116_, v___x_1117_);
v___x_1119_ = lean_box(0);
v___x_1120_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_1118_, v___x_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_dec_ref(v___x_1120_);
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1129_; lean_object* v_a_1130_; uint8_t v___x_1131_; 
lean_dec(v___x_1107_);
lean_inc(v_declName_1098_);
v___x_1129_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_1098_, v___y_1091_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = lean_unbox(v_a_1130_);
lean_dec(v_a_1130_);
if (v___x_1131_ == 0)
{
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_dec_ref(v___x_1132_);
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_dec_ref(v___x_1141_);
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1150_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1102_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1102_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_del_object(v___x_1075_);
v_fvarId_1158_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_fvarId_1158_);
lean_dec_ref(v___x_1092_);
v___x_1159_ = l_Lean_Expr_getAppNumArgs(v_a_1073_);
lean_inc(v___x_1159_);
v___x_1160_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_fvarId_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_mk_empty_array_with_capacity(v___x_1159_);
lean_dec(v___x_1159_);
v___x_1162_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1073_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1160_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
case 2:
{
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
if (v_isMatch_1065_ == 0)
{
lean_object* v_mvarId_1165_; lean_object* v___x_1166_; uint8_t v_isDefEqStuckEx_1167_; 
v_mvarId_1165_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_mvarId_1165_);
lean_dec_ref(v___x_1092_);
v___x_1166_ = l_Lean_Meta_Context_config(v___y_1088_);
v_isDefEqStuckEx_1167_ = lean_ctor_get_uint8(v___x_1166_, 4);
lean_dec_ref(v___x_1166_);
if (v_isDefEqStuckEx_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1165_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1182_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1182_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_a_1169_);
lean_dec(v_a_1169_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1174_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1178_);
v___x_1180_ = v___x_1171_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1168_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1168_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec(v_mvarId_1165_);
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec_ref(v___x_1092_);
v___x_1193_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
case 11:
{
lean_object* v_typeName_1195_; lean_object* v_idx_1196_; lean_object* v_struct_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_del_object(v___x_1075_);
v_typeName_1195_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_typeName_1195_);
v_idx_1196_ = lean_ctor_get(v___x_1092_, 1);
lean_inc(v_idx_1196_);
v_struct_1197_ = lean_ctor_get(v___x_1092_, 2);
lean_inc_ref(v_struct_1197_);
lean_dec_ref(v___x_1092_);
v___x_1198_ = l_Lean_Expr_getAppNumArgs(v_a_1073_);
lean_inc(v___x_1198_);
v___x_1199_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1199_, 0, v_typeName_1195_);
lean_ctor_set(v___x_1199_, 1, v_idx_1196_);
lean_ctor_set(v___x_1199_, 2, v___x_1198_);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
v___x_1202_ = lean_array_push(v___x_1201_, v_struct_1197_);
v___x_1203_ = lean_mk_empty_array_with_capacity(v___x_1198_);
lean_dec(v___x_1198_);
v___x_1204_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1073_, v___x_1203_);
v___x_1205_ = l_Array_append___redArg(v___x_1202_, v___x_1204_);
lean_dec_ref(v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1199_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
case 7:
{
lean_object* v_binderType_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_binderType_1208_ = lean_ctor_get(v___x_1092_, 1);
lean_inc_ref(v_binderType_1208_);
lean_dec_ref(v___x_1092_);
v___x_1209_ = lean_box(5);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_mk_empty_array_with_capacity(v___x_1210_);
v___x_1212_ = lean_array_push(v___x_1211_, v_binderType_1208_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1209_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
default: 
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v___x_1092_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v___x_1215_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_a_1230_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1072_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1072_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* v_e_1238_, lean_object* v_isMatch_1239_, lean_object* v_root_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
uint8_t v_isMatch_boxed_1246_; uint8_t v_root_boxed_1247_; lean_object* v_res_1248_; 
v_isMatch_boxed_1246_ = lean_unbox(v_isMatch_1239_);
v_root_boxed_1247_ = lean_unbox(v_root_1240_);
v_res_1248_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1238_, v_isMatch_boxed_1246_, v_root_boxed_1247_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1249_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object* v_inst_1263_, lean_object* v_R_1264_, lean_object* v_a_1265_, lean_object* v_b_1266_, lean_object* v_c_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1265_, v_b_1266_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object* v_inst_1274_, lean_object* v_R_1275_, lean_object* v_a_1276_, lean_object* v_b_1277_, lean_object* v_c_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_1274_, v_R_1275_, v_a_1276_, v_b_1277_, v_c_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* v_e_1285_, uint8_t v_root_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint8_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = 1;
v___x_1293_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1285_, v___x_1292_, v_root_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* v_e_1294_, lean_object* v_root_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
uint8_t v_root_boxed_1301_; lean_object* v_res_1302_; 
v_root_boxed_1301_ = lean_unbox(v_root_1295_);
v_res_1302_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1294_, v_root_boxed_1301_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* v_e_1303_, uint8_t v_root_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
uint8_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = 0;
v___x_1311_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1303_, v___x_1310_, v_root_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* v_e_1312_, lean_object* v_root_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
uint8_t v_root_boxed_1319_; lean_object* v_res_1320_; 
v_root_boxed_1319_ = lean_unbox(v_root_1313_);
v_res_1320_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1312_, v_root_boxed_1319_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1321_, lean_object* v_vals_1322_, lean_object* v_i_1323_, lean_object* v_k_1324_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_array_get_size(v_keys_1321_);
v___x_1326_ = lean_nat_dec_lt(v_i_1323_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec(v_i_1323_);
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
else
{
lean_object* v_k_x27_1328_; uint8_t v___x_1329_; 
v_k_x27_1328_ = lean_array_fget_borrowed(v_keys_1321_, v_i_1323_);
v___x_1329_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1324_, v_k_x27_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = lean_nat_add(v_i_1323_, v___x_1330_);
lean_dec(v_i_1323_);
v_i_1323_ = v___x_1331_;
goto _start;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_array_fget_borrowed(v_vals_1322_, v_i_1323_);
lean_dec(v_i_1323_);
lean_inc(v___x_1333_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1335_, lean_object* v_vals_1336_, lean_object* v_i_1337_, lean_object* v_k_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1335_, v_vals_1336_, v_i_1337_, v_k_1338_);
lean_dec(v_k_1338_);
lean_dec_ref(v_vals_1336_);
lean_dec_ref(v_keys_1335_);
return v_res_1339_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1340_; size_t v___x_1341_; size_t v___x_1342_; 
v___x_1340_ = ((size_t)5ULL);
v___x_1341_ = ((size_t)1ULL);
v___x_1342_ = lean_usize_shift_left(v___x_1341_, v___x_1340_);
return v___x_1342_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1343_; size_t v___x_1344_; size_t v___x_1345_; 
v___x_1343_ = ((size_t)1ULL);
v___x_1344_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0);
v___x_1345_ = lean_usize_sub(v___x_1344_, v___x_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1346_, size_t v_x_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
lean_object* v_es_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1370_; 
v_es_1349_ = lean_ctor_get(v_x_1346_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_x_1346_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1351_ = v_x_1346_;
v_isShared_1352_ = v_isSharedCheck_1370_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_es_1349_);
lean_dec(v_x_1346_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1370_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; lean_object* v_j_1357_; lean_object* v___x_1358_; 
v___x_1353_ = lean_box(2);
v___x_1354_ = ((size_t)5ULL);
v___x_1355_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1);
v___x_1356_ = lean_usize_land(v_x_1347_, v___x_1355_);
v_j_1357_ = lean_usize_to_nat(v___x_1356_);
v___x_1358_ = lean_array_get(v___x_1353_, v_es_1349_, v_j_1357_);
lean_dec(v_j_1357_);
lean_dec_ref(v_es_1349_);
switch(lean_obj_tag(v___x_1358_))
{
case 0:
{
lean_object* v_key_1359_; lean_object* v_val_1360_; uint8_t v___x_1361_; 
v_key_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_key_1359_);
v_val_1360_ = lean_ctor_get(v___x_1358_, 1);
lean_inc(v_val_1360_);
lean_dec_ref(v___x_1358_);
v___x_1361_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1348_, v_key_1359_);
lean_dec(v_key_1359_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec(v_val_1360_);
lean_del_object(v___x_1351_);
v___x_1362_ = lean_box(0);
return v___x_1362_;
}
else
{
lean_object* v___x_1364_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set_tag(v___x_1351_, 1);
lean_ctor_set(v___x_1351_, 0, v_val_1360_);
v___x_1364_ = v___x_1351_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_val_1360_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
case 1:
{
lean_object* v_node_1366_; size_t v___x_1367_; 
lean_del_object(v___x_1351_);
v_node_1366_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_node_1366_);
lean_dec_ref(v___x_1358_);
v___x_1367_ = lean_usize_shift_right(v_x_1347_, v___x_1354_);
v_x_1346_ = v_node_1366_;
v_x_1347_ = v___x_1367_;
goto _start;
}
default: 
{
lean_object* v___x_1369_; 
lean_del_object(v___x_1351_);
v___x_1369_ = lean_box(0);
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_ks_1371_; lean_object* v_vs_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_ks_1371_ = lean_ctor_get(v_x_1346_, 0);
lean_inc_ref(v_ks_1371_);
v_vs_1372_ = lean_ctor_get(v_x_1346_, 1);
lean_inc_ref(v_vs_1372_);
lean_dec_ref(v_x_1346_);
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1371_, v_vs_1372_, v___x_1373_, v_x_1348_);
lean_dec_ref(v_vs_1372_);
lean_dec_ref(v_ks_1371_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_){
_start:
{
size_t v_x_181__boxed_1378_; lean_object* v_res_1379_; 
v_x_181__boxed_1378_ = lean_unbox_usize(v_x_1376_);
lean_dec(v_x_1376_);
v_res_1379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1375_, v_x_181__boxed_1378_, v_x_1377_);
lean_dec(v_x_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1380_, lean_object* v_x_1381_){
_start:
{
uint64_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1381_);
v___x_1383_ = lean_uint64_to_usize(v___x_1382_);
v___x_1384_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1380_, v___x_1383_, v_x_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1385_, v_x_1386_);
lean_dec(v_x_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v_result_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1389_ = lean_unsigned_to_nat(8u);
v_result_1390_ = lean_mk_empty_array_with_capacity(v___x_1389_);
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1388_, v___x_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
return v_result_1390_;
}
else
{
lean_object* v_val_1393_; lean_object* v_vs_1394_; lean_object* v___x_1395_; 
v_val_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_val_1393_);
lean_dec_ref(v___x_1392_);
v_vs_1394_ = lean_ctor_get(v_val_1393_, 0);
lean_inc_ref(v_vs_1394_);
lean_dec(v_val_1393_);
v___x_1395_ = l_Array_append___redArg(v_result_1390_, v_vs_1394_);
lean_dec_ref(v_vs_1394_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1396_, lean_object* v_d_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1400_, v_x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1403_, v_x_1404_, v_x_1405_);
lean_dec(v_x_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, size_t v_x_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1408_, v_x_1409_, v_x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
size_t v_x_281__boxed_1416_; lean_object* v_res_1417_; 
v_x_281__boxed_1416_ = lean_unbox_usize(v_x_1414_);
lean_dec(v_x_1414_);
v_res_1417_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1412_, v_x_1413_, v_x_281__boxed_1416_, v_x_1415_);
lean_dec(v_x_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1418_, lean_object* v_keys_1419_, lean_object* v_vals_1420_, lean_object* v_heq_1421_, lean_object* v_i_1422_, lean_object* v_k_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1419_, v_vals_1420_, v_i_1422_, v_k_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1425_, lean_object* v_keys_1426_, lean_object* v_vals_1427_, lean_object* v_heq_1428_, lean_object* v_i_1429_, lean_object* v_k_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1425_, v_keys_1426_, v_vals_1427_, v_heq_1428_, v_i_1429_, v_k_1430_);
lean_dec(v_k_1430_);
lean_dec_ref(v_vals_1427_);
lean_dec_ref(v_keys_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object* v_a_1432_, lean_object* v_b_1433_){
_start:
{
lean_object* v_fst_1434_; lean_object* v_fst_1435_; uint8_t v___x_1436_; 
v_fst_1434_ = lean_ctor_get(v_a_1432_, 0);
v_fst_1435_ = lean_ctor_get(v_b_1433_, 0);
v___x_1436_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1434_, v_fst_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object* v_a_1437_, lean_object* v_b_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1437_, v_b_1438_);
lean_dec_ref(v_b_1438_);
lean_dec_ref(v_a_1437_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1447_, lean_object* v_k_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_array_get_size(v_cs_1447_);
v___x_1451_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; 
lean_dec(v_k_1448_);
v___x_1452_ = lean_box(0);
return v___x_1452_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_sub(v___x_1450_, v___x_1453_);
v___x_1455_ = lean_nat_dec_le(v___x_1449_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec(v___x_1454_);
lean_dec(v_k_1448_);
v___x_1456_ = lean_box(0);
return v___x_1456_;
}
else
{
lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___f_1457_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1458_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_k_1448_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1461_ = l_Array_binSearchAux___redArg(v___f_1457_, v___x_1460_, v_cs_1447_, v___x_1459_, v___x_1449_, v___x_1454_);
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1462_, lean_object* v_k_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1462_, v_k_1463_);
lean_dec_ref(v_cs_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1465_, lean_object* v_cs_1466_, lean_object* v_k_1467_){
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
v___x_1477_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_k_1467_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1480_ = l_Array_binSearchAux___redArg(v___f_1476_, v___x_1479_, v_cs_1466_, v___x_1478_, v___x_1468_, v___x_1473_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_cs_1482_, lean_object* v_k_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1481_, v_cs_1482_, v_k_1483_);
lean_dec_ref(v_cs_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1485_, lean_object* v_k_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_m_1491_; lean_object* v_a_1492_; uint8_t v___x_1493_; 
v___x_1489_ = lean_nat_add(v_x_1487_, v_x_1488_);
v___x_1490_ = lean_unsigned_to_nat(1u);
v_m_1491_ = lean_nat_shiftr(v___x_1489_, v___x_1490_);
lean_dec(v___x_1489_);
v_a_1492_ = lean_array_fget_borrowed(v_as_1485_, v_m_1491_);
v___x_1493_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1492_, v_k_1486_);
if (v___x_1493_ == 0)
{
uint8_t v___x_1494_; 
lean_dec(v_x_1488_);
v___x_1494_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1486_, v_a_1492_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v_m_1491_);
lean_dec(v_x_1487_);
lean_inc(v_a_1492_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_a_1492_);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = lean_nat_dec_eq(v_m_1491_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = lean_nat_sub(v_m_1491_, v___x_1490_);
lean_dec(v_m_1491_);
v___x_1499_ = lean_nat_dec_lt(v___x_1498_, v_x_1487_);
if (v___x_1499_ == 0)
{
v_x_1488_ = v___x_1498_;
goto _start;
}
else
{
lean_object* v___x_1501_; 
lean_dec(v___x_1498_);
lean_dec(v_x_1487_);
v___x_1501_ = lean_box(0);
return v___x_1501_;
}
}
else
{
lean_object* v___x_1502_; 
lean_dec(v_m_1491_);
lean_dec(v_x_1487_);
v___x_1502_ = lean_box(0);
return v___x_1502_;
}
}
}
else
{
lean_object* v___x_1503_; uint8_t v___x_1504_; 
lean_dec(v_x_1487_);
v___x_1503_ = lean_nat_add(v_m_1491_, v___x_1490_);
lean_dec(v_m_1491_);
v___x_1504_ = lean_nat_dec_le(v___x_1503_, v_x_1488_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
lean_dec(v___x_1503_);
lean_dec(v_x_1488_);
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
else
{
v_x_1487_ = v___x_1503_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1507_, lean_object* v_k_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1507_, v_k_1508_, v_x_1509_, v_x_1510_);
lean_dec_ref(v_k_1508_);
lean_dec_ref(v_as_1507_);
return v_res_1511_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v___x_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1516_, lean_object* v_c_1517_, lean_object* v_result_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_vs_1524_; lean_object* v_children_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_vs_1524_ = lean_ctor_get(v_c_1517_, 0);
lean_inc_ref(v_vs_1524_);
v_children_1525_ = lean_ctor_get(v_c_1517_, 1);
lean_inc_ref(v_children_1525_);
lean_dec_ref(v_c_1517_);
v___x_1526_ = lean_array_get_size(v_todo_1516_);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_nat_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
lean_dec_ref(v_vs_1524_);
v___x_1529_ = lean_array_get_size(v_children_1525_);
v___x_1530_ = lean_nat_dec_eq(v___x_1529_, v___x_1527_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_e_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1531_ = l_Lean_instInhabitedExpr;
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_sub(v___x_1526_, v___x_1532_);
v_e_1534_ = lean_array_get_borrowed(v___x_1531_, v_todo_1516_, v___x_1533_);
lean_dec(v___x_1533_);
v___x_1535_ = 1;
lean_inc(v_e_1534_);
v___x_1536_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1534_, v___x_1535_, v___x_1530_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1574_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1574_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1574_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_fst_1541_; lean_object* v_snd_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_first_1545_; lean_object* v_fst_1546_; lean_object* v_snd_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1573_; 
v_fst_1541_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_fst_1541_);
v_snd_1542_ = lean_ctor_get(v_a_1537_, 1);
lean_inc(v_snd_1542_);
lean_dec(v_a_1537_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v_first_1545_ = lean_array_get(v___x_1544_, v_children_1525_, v___x_1527_);
v_fst_1546_ = lean_ctor_get(v_first_1545_, 0);
v_snd_1547_ = lean_ctor_get(v_first_1545_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_first_1545_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1549_ = v_first_1545_;
v_isShared_1550_ = v_isSharedCheck_1573_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_snd_1547_);
lean_inc(v_fst_1546_);
lean_dec(v_first_1545_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1573_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_todo_1551_; lean_object* v___y_1553_; lean_object* v_a_1554_; uint8_t v___x_1567_; 
v_todo_1551_ = lean_array_pop(v_todo_1516_);
v___x_1567_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1546_, v___x_1543_);
lean_dec(v_fst_1546_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1569_; 
lean_dec(v_snd_1547_);
lean_inc_ref(v_result_1518_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v_result_1518_);
v___x_1569_ = v___x_1539_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_result_1518_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v___y_1553_ = v___x_1569_;
v_a_1554_ = v_result_1518_;
goto v___jp_1552_;
}
}
else
{
lean_object* v___x_1571_; 
lean_del_object(v___x_1539_);
lean_inc_ref(v_todo_1551_);
v___x_1571_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1551_, v_snd_1547_, v_result_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
v___y_1553_ = v___x_1571_;
v_a_1554_ = v_a_1572_;
goto v___jp_1552_;
}
else
{
lean_dec_ref(v_todo_1551_);
lean_del_object(v___x_1549_);
lean_dec(v_snd_1542_);
lean_dec(v_fst_1541_);
lean_dec_ref(v_children_1525_);
return v___x_1571_;
}
}
v___jp_1552_:
{
if (lean_obj_tag(v_fst_1541_) == 0)
{
lean_dec_ref(v_a_1554_);
lean_dec_ref(v_todo_1551_);
lean_del_object(v___x_1549_);
lean_dec(v_snd_1542_);
lean_dec_ref(v_children_1525_);
return v___y_1553_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_nat_dec_lt(v___x_1527_, v___x_1529_);
if (v___x_1555_ == 0)
{
lean_dec_ref(v_a_1554_);
lean_dec_ref(v_todo_1551_);
lean_del_object(v___x_1549_);
lean_dec(v_snd_1542_);
lean_dec(v_fst_1541_);
lean_dec_ref(v_children_1525_);
return v___y_1553_;
}
else
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = lean_nat_sub(v___x_1529_, v___x_1532_);
v___x_1557_ = lean_nat_dec_le(v___x_1527_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec(v___x_1556_);
lean_dec_ref(v_a_1554_);
lean_dec_ref(v_todo_1551_);
lean_del_object(v___x_1549_);
lean_dec(v_snd_1542_);
lean_dec(v_fst_1541_);
lean_dec_ref(v_children_1525_);
return v___y_1553_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v___x_1558_);
lean_ctor_set(v___x_1549_, 0, v_fst_1541_);
v___x_1560_ = v___x_1549_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_fst_1541_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1525_, v___x_1560_, v___x_1527_, v___x_1556_);
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_children_1525_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_dec_ref(v_a_1554_);
lean_dec_ref(v_todo_1551_);
lean_dec(v_snd_1542_);
return v___y_1553_;
}
else
{
lean_object* v_val_1562_; lean_object* v_snd_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v___y_1553_);
v_val_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_val_1562_);
lean_dec_ref(v___x_1561_);
v_snd_1563_ = lean_ctor_get(v_val_1562_, 1);
lean_inc(v_snd_1563_);
lean_dec(v_val_1562_);
v___x_1564_ = l_Array_append___redArg(v_todo_1551_, v_snd_1542_);
lean_dec(v_snd_1542_);
v_todo_1516_ = v___x_1564_;
v_c_1517_ = v_snd_1563_;
v_result_1518_ = v_a_1554_;
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
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_children_1525_);
lean_dec_ref(v_result_1518_);
lean_dec_ref(v_todo_1516_);
v_a_1575_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1536_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1536_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v___x_1583_; 
lean_dec_ref(v_children_1525_);
lean_dec_ref(v_todo_1516_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_result_1518_);
return v___x_1583_;
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec_ref(v_children_1525_);
lean_dec_ref(v_todo_1516_);
v___x_1584_ = l_Array_append___redArg(v_result_1518_, v_vs_1524_);
lean_dec_ref(v_vs_1524_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1586_, lean_object* v_c_1587_, lean_object* v_result_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1586_, v_c_1587_, v_result_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1595_, lean_object* v_todo_1596_, lean_object* v_c_1597_, lean_object* v_result_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1596_, v_c_1597_, v_result_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_todo_1606_, lean_object* v_c_1607_, lean_object* v_result_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1605_, v_todo_1606_, v_c_1607_, v_result_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1615_, lean_object* v_as_1616_, lean_object* v_k_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1616_, v_k_1617_, v_x_1618_, v_x_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_as_1623_, lean_object* v_k_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1622_, v_as_1623_, v_k_1624_, v_x_1625_, v_x_1626_, v_x_1627_);
lean_dec_ref(v_k_1624_);
lean_dec_ref(v_as_1623_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1629_, lean_object* v_k_1630_, lean_object* v_args_1631_, lean_object* v_result_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1629_, v_k_1630_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v_args_1631_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_result_1632_);
return v___x_1639_;
}
else
{
lean_object* v_val_1640_; lean_object* v___x_1641_; 
v_val_1640_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1640_);
lean_dec_ref(v___x_1638_);
v___x_1641_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1631_, v_val_1640_, v_result_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1642_, lean_object* v_k_1643_, lean_object* v_args_1644_, lean_object* v_result_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1642_, v_k_1643_, v_args_1644_, v_result_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_k_1643_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1652_, lean_object* v_d_1653_, lean_object* v_k_1654_, lean_object* v_args_1655_, lean_object* v_result_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1653_, v_k_1654_, v_args_1655_, v_result_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_d_1664_, lean_object* v_k_1665_, lean_object* v_args_1666_, lean_object* v_result_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1663_, v_d_1664_, v_k_1665_, v_args_1666_, v_result_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_k_1665_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1674_, lean_object* v_e_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; uint8_t v_foApprox_1682_; uint8_t v_ctxApprox_1683_; uint8_t v_quasiPatternApprox_1684_; uint8_t v_constApprox_1685_; uint8_t v_isDefEqStuckEx_1686_; uint8_t v_unificationHints_1687_; uint8_t v_proofIrrelevance_1688_; uint8_t v_assignSyntheticOpaque_1689_; uint8_t v_offsetCnstrs_1690_; uint8_t v_etaStruct_1691_; uint8_t v_univApprox_1692_; uint8_t v_iota_1693_; uint8_t v_beta_1694_; uint8_t v_proj_1695_; uint8_t v_zeta_1696_; uint8_t v_zetaDelta_1697_; uint8_t v_zetaUnused_1698_; uint8_t v_zetaHave_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1773_; 
v___x_1681_ = l_Lean_Meta_Context_config(v_a_1676_);
v_foApprox_1682_ = lean_ctor_get_uint8(v___x_1681_, 0);
v_ctxApprox_1683_ = lean_ctor_get_uint8(v___x_1681_, 1);
v_quasiPatternApprox_1684_ = lean_ctor_get_uint8(v___x_1681_, 2);
v_constApprox_1685_ = lean_ctor_get_uint8(v___x_1681_, 3);
v_isDefEqStuckEx_1686_ = lean_ctor_get_uint8(v___x_1681_, 4);
v_unificationHints_1687_ = lean_ctor_get_uint8(v___x_1681_, 5);
v_proofIrrelevance_1688_ = lean_ctor_get_uint8(v___x_1681_, 6);
v_assignSyntheticOpaque_1689_ = lean_ctor_get_uint8(v___x_1681_, 7);
v_offsetCnstrs_1690_ = lean_ctor_get_uint8(v___x_1681_, 8);
v_etaStruct_1691_ = lean_ctor_get_uint8(v___x_1681_, 10);
v_univApprox_1692_ = lean_ctor_get_uint8(v___x_1681_, 11);
v_iota_1693_ = lean_ctor_get_uint8(v___x_1681_, 12);
v_beta_1694_ = lean_ctor_get_uint8(v___x_1681_, 13);
v_proj_1695_ = lean_ctor_get_uint8(v___x_1681_, 14);
v_zeta_1696_ = lean_ctor_get_uint8(v___x_1681_, 15);
v_zetaDelta_1697_ = lean_ctor_get_uint8(v___x_1681_, 16);
v_zetaUnused_1698_ = lean_ctor_get_uint8(v___x_1681_, 17);
v_zetaHave_1699_ = lean_ctor_get_uint8(v___x_1681_, 18);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1701_ = v___x_1681_;
v_isShared_1702_ = v_isSharedCheck_1773_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v___x_1681_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1773_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
uint8_t v_trackZetaDelta_1703_; lean_object* v_zetaDeltaSet_1704_; lean_object* v_lctx_1705_; lean_object* v_localInstances_1706_; lean_object* v_defEqCtx_x3f_1707_; lean_object* v_synthPendingDepth_1708_; lean_object* v_canUnfold_x3f_1709_; uint8_t v_univApprox_1710_; uint8_t v_inTypeClassResolution_1711_; uint8_t v_cacheInferType_1712_; uint8_t v___x_1713_; lean_object* v_config_1715_; 
v_trackZetaDelta_1703_ = lean_ctor_get_uint8(v_a_1676_, sizeof(void*)*7);
v_zetaDeltaSet_1704_ = lean_ctor_get(v_a_1676_, 1);
v_lctx_1705_ = lean_ctor_get(v_a_1676_, 2);
v_localInstances_1706_ = lean_ctor_get(v_a_1676_, 3);
v_defEqCtx_x3f_1707_ = lean_ctor_get(v_a_1676_, 4);
v_synthPendingDepth_1708_ = lean_ctor_get(v_a_1676_, 5);
v_canUnfold_x3f_1709_ = lean_ctor_get(v_a_1676_, 6);
v_univApprox_1710_ = lean_ctor_get_uint8(v_a_1676_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1711_ = lean_ctor_get_uint8(v_a_1676_, sizeof(void*)*7 + 2);
v_cacheInferType_1712_ = lean_ctor_get_uint8(v_a_1676_, sizeof(void*)*7 + 3);
v___x_1713_ = 2;
if (v_isShared_1702_ == 0)
{
v_config_1715_ = v___x_1701_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 0, v_foApprox_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 1, v_ctxApprox_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 2, v_quasiPatternApprox_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 3, v_constApprox_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 4, v_isDefEqStuckEx_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 5, v_unificationHints_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 6, v_proofIrrelevance_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 7, v_assignSyntheticOpaque_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 8, v_offsetCnstrs_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 10, v_etaStruct_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 11, v_univApprox_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 12, v_iota_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 13, v_beta_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 14, v_proj_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 15, v_zeta_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 16, v_zetaDelta_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 17, v_zetaUnused_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, 18, v_zetaHave_1699_);
v_config_1715_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
uint64_t v___x_1716_; uint64_t v___x_1717_; uint64_t v___x_1718_; uint8_t v___x_1719_; uint64_t v___x_1720_; uint64_t v___x_1721_; uint64_t v_key_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_ctor_set_uint8(v_config_1715_, 9, v___x_1713_);
v___x_1716_ = l_Lean_Meta_Context_configKey(v_a_1676_);
v___x_1717_ = 2ULL;
v___x_1718_ = lean_uint64_shift_right(v___x_1716_, v___x_1717_);
v___x_1719_ = 1;
v___x_1720_ = lean_uint64_shift_left(v___x_1718_, v___x_1717_);
v___x_1721_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_1722_ = lean_uint64_lor(v___x_1720_, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1723_, 0, v_config_1715_);
lean_ctor_set_uint64(v___x_1723_, sizeof(void*)*1, v_key_1722_);
lean_inc(v_canUnfold_x3f_1709_);
lean_inc(v_synthPendingDepth_1708_);
lean_inc(v_defEqCtx_x3f_1707_);
lean_inc_ref(v_localInstances_1706_);
lean_inc_ref(v_lctx_1705_);
lean_inc(v_zetaDeltaSet_1704_);
v___x_1724_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v_zetaDeltaSet_1704_);
lean_ctor_set(v___x_1724_, 2, v_lctx_1705_);
lean_ctor_set(v___x_1724_, 3, v_localInstances_1706_);
lean_ctor_set(v___x_1724_, 4, v_defEqCtx_x3f_1707_);
lean_ctor_set(v___x_1724_, 5, v_synthPendingDepth_1708_);
lean_ctor_set(v___x_1724_, 6, v_canUnfold_x3f_1709_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*7, v_trackZetaDelta_1703_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*7 + 1, v_univApprox_1710_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1711_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*7 + 3, v_cacheInferType_1712_);
v___x_1725_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1675_, v___x_1719_, v___x_1719_, v___x_1724_, v_a_1677_, v_a_1678_, v_a_1679_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1763_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1763_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1763_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_fst_1730_; lean_object* v_snd_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1762_; 
v_fst_1730_ = lean_ctor_get(v_a_1726_, 0);
v_snd_1731_ = lean_ctor_get(v_a_1726_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_a_1726_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1733_ = v_a_1726_;
v_isShared_1734_ = v_isSharedCheck_1762_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_snd_1731_);
lean_inc(v_fst_1730_);
lean_dec(v_a_1726_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1762_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_result_1735_; 
lean_inc_ref(v_d_1674_);
v_result_1735_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1674_);
if (lean_obj_tag(v_fst_1730_) == 0)
{
lean_object* v___x_1737_; 
lean_dec(v_snd_1731_);
lean_dec_ref(v___x_1724_);
lean_dec_ref(v_d_1674_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_result_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_fst_1730_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_result_1735_);
v___x_1737_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1739_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1737_);
v___x_1739_ = v___x_1728_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v___x_1742_; 
lean_del_object(v___x_1728_);
v___x_1742_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1674_, v_fst_1730_, v_snd_1731_, v_result_1735_, v___x_1724_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec_ref(v___x_1724_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1753_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1753_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1753_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_a_1743_);
v___x_1748_ = v___x_1733_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_fst_1730_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1750_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1748_);
v___x_1750_ = v___x_1745_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_del_object(v___x_1733_);
lean_dec(v_fst_1730_);
v_a_1754_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1742_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1742_);
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
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v___x_1724_);
lean_dec_ref(v_d_1674_);
v_a_1764_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1725_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1725_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1774_, lean_object* v_e_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1774_, v_e_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1782_, lean_object* v_d_1783_, lean_object* v_e_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1783_, v_e_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1791_, lean_object* v_d_1792_, lean_object* v_e_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1791_, v_d_1792_, v_e_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1800_, lean_object* v_e_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1800_, v_e_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1816_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1816_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_snd_1812_; lean_object* v___x_1814_; 
v_snd_1812_ = lean_ctor_get(v_a_1808_, 1);
lean_inc(v_snd_1812_);
lean_dec(v_a_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v_snd_1812_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_snd_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1807_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1807_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1825_, lean_object* v_e_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1825_, v_e_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1833_, lean_object* v_d_1834_, lean_object* v_e_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1834_, v_e_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1842_, lean_object* v_d_1843_, lean_object* v_e_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1842_, v_d_1843_, v_e_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1851_, lean_object* v_k_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_k_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; 
switch(lean_obj_tag(v_k_1852_))
{
case 4:
{
lean_object* v_a_1880_; lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1892_; 
v_a_1880_ = lean_ctor_get(v_k_1852_, 0);
v_a_1881_ = lean_ctor_get(v_k_1852_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_k_1852_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1883_ = v_k_1852_;
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_inc(v_a_1880_);
lean_dec(v_k_1852_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_zero_1885_; uint8_t v_isZero_1886_; 
v_zero_1885_ = lean_unsigned_to_nat(0u);
v_isZero_1886_ = lean_nat_dec_eq(v_a_1881_, v_zero_1885_);
if (v_isZero_1886_ == 0)
{
lean_object* v_one_1887_; lean_object* v_n_1888_; lean_object* v___x_1890_; 
v_one_1887_ = lean_unsigned_to_nat(1u);
v_n_1888_ = lean_nat_sub(v_a_1881_, v_one_1887_);
lean_dec(v_a_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v_n_1888_);
v___x_1890_ = v___x_1883_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1880_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_n_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
v_k_1863_ = v___x_1890_;
v___y_1864_ = v_a_1853_;
v___y_1865_ = v_a_1854_;
v___y_1866_ = v_a_1855_;
v___y_1867_ = v_a_1856_;
goto v___jp_1862_;
}
}
else
{
lean_del_object(v___x_1883_);
lean_dec(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_d_1851_);
goto v___jp_1858_;
}
}
}
case 3:
{
lean_object* v_a_1893_; lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1905_; 
v_a_1893_ = lean_ctor_get(v_k_1852_, 0);
v_a_1894_ = lean_ctor_get(v_k_1852_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_k_1852_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1896_ = v_k_1852_;
v_isShared_1897_ = v_isSharedCheck_1905_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_inc(v_a_1893_);
lean_dec(v_k_1852_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1905_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_zero_1898_; uint8_t v_isZero_1899_; 
v_zero_1898_ = lean_unsigned_to_nat(0u);
v_isZero_1899_ = lean_nat_dec_eq(v_a_1894_, v_zero_1898_);
if (v_isZero_1899_ == 0)
{
lean_object* v_one_1900_; lean_object* v_n_1901_; lean_object* v___x_1903_; 
v_one_1900_ = lean_unsigned_to_nat(1u);
v_n_1901_ = lean_nat_sub(v_a_1894_, v_one_1900_);
lean_dec(v_a_1894_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v_n_1901_);
v___x_1903_ = v___x_1896_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1893_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_n_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
v_k_1863_ = v___x_1903_;
v___y_1864_ = v_a_1853_;
v___y_1865_ = v_a_1854_;
v___y_1866_ = v_a_1855_;
v___y_1867_ = v_a_1856_;
goto v___jp_1862_;
}
}
else
{
lean_del_object(v___x_1896_);
lean_dec(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_d_1851_);
goto v___jp_1858_;
}
}
}
case 6:
{
lean_object* v_a_1906_; lean_object* v_a_1907_; lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1919_; 
v_a_1906_ = lean_ctor_get(v_k_1852_, 0);
v_a_1907_ = lean_ctor_get(v_k_1852_, 1);
v_a_1908_ = lean_ctor_get(v_k_1852_, 2);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_k_1852_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1910_ = v_k_1852_;
v_isShared_1911_ = v_isSharedCheck_1919_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_inc(v_a_1907_);
lean_inc(v_a_1906_);
lean_dec(v_k_1852_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1919_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_zero_1912_; uint8_t v_isZero_1913_; 
v_zero_1912_ = lean_unsigned_to_nat(0u);
v_isZero_1913_ = lean_nat_dec_eq(v_a_1908_, v_zero_1912_);
if (v_isZero_1913_ == 0)
{
lean_object* v_one_1914_; lean_object* v_n_1915_; lean_object* v___x_1917_; 
v_one_1914_ = lean_unsigned_to_nat(1u);
v_n_1915_ = lean_nat_sub(v_a_1908_, v_one_1914_);
lean_dec(v_a_1908_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 2, v_n_1915_);
v___x_1917_ = v___x_1910_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1906_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_a_1907_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_n_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
v_k_1863_ = v___x_1917_;
v___y_1864_ = v_a_1853_;
v___y_1865_ = v_a_1854_;
v___y_1866_ = v_a_1855_;
v___y_1867_ = v_a_1856_;
goto v___jp_1862_;
}
}
else
{
lean_del_object(v___x_1910_);
lean_dec(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_d_1851_);
goto v___jp_1858_;
}
}
}
default: 
{
lean_dec(v_k_1852_);
lean_dec_ref(v_d_1851_);
goto v___jp_1858_;
}
}
v___jp_1858_:
{
uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = 0;
v___x_1860_ = lean_box(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
v___jp_1862_:
{
lean_object* v___x_1868_; 
lean_inc_ref(v_d_1851_);
v___x_1868_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1851_, v_k_1863_);
if (lean_obj_tag(v___x_1868_) == 0)
{
v_k_1852_ = v_k_1863_;
v_a_1853_ = v___y_1864_;
v_a_1854_ = v___y_1865_;
v_a_1855_ = v___y_1866_;
v_a_1856_ = v___y_1867_;
goto _start;
}
else
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_k_1863_);
lean_dec_ref(v_d_1851_);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1879_);
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1873_ = 1;
v___x_1874_ = lean_box(v___x_1873_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_1920_, lean_object* v_k_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1920_, v_k_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_1928_, lean_object* v_d_1929_, lean_object* v_k_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1929_, v_k_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_1937_, lean_object* v_d_1938_, lean_object* v_k_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_1937_, v_d_1938_, v_k_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_1946_, size_t v_sz_1947_, size_t v_i_1948_, lean_object* v_bs_1949_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_lt(v_i_1948_, v_sz_1947_);
if (v___x_1950_ == 0)
{
lean_dec(v_numExtra_1946_);
return v_bs_1949_;
}
else
{
lean_object* v_v_1951_; lean_object* v___x_1952_; lean_object* v_bs_x27_1953_; lean_object* v___x_1954_; size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v_v_1951_ = lean_array_uget(v_bs_1949_, v_i_1948_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v_bs_x27_1953_ = lean_array_uset(v_bs_1949_, v_i_1948_, v___x_1952_);
lean_inc(v_numExtra_1946_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v_v_1951_);
lean_ctor_set(v___x_1954_, 1, v_numExtra_1946_);
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1948_, v___x_1955_);
v___x_1957_ = lean_array_uset(v_bs_x27_1953_, v_i_1948_, v___x_1954_);
v_i_1948_ = v___x_1956_;
v_bs_1949_ = v___x_1957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_1959_, lean_object* v_sz_1960_, lean_object* v_i_1961_, lean_object* v_bs_1962_){
_start:
{
size_t v_sz_boxed_1963_; size_t v_i_boxed_1964_; lean_object* v_res_1965_; 
v_sz_boxed_1963_ = lean_unbox_usize(v_sz_1960_);
lean_dec(v_sz_1960_);
v_i_boxed_1964_ = lean_unbox_usize(v_i_1961_);
lean_dec(v_i_1961_);
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1959_, v_sz_boxed_1963_, v_i_boxed_1964_, v_bs_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_1966_, lean_object* v_e_1967_, lean_object* v_numExtra_1968_, lean_object* v_result_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; 
lean_inc_ref(v_e_1967_);
lean_inc_ref(v_d_1966_);
v___x_1975_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1966_, v_e_1967_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1993_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1993_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1993_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_snd_1980_; size_t v_sz_1981_; size_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v_snd_1980_ = lean_ctor_get(v_a_1976_, 1);
lean_inc(v_snd_1980_);
lean_dec(v_a_1976_);
v_sz_1981_ = lean_array_size(v_snd_1980_);
v___x_1982_ = ((size_t)0ULL);
lean_inc(v_numExtra_1968_);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1968_, v_sz_1981_, v___x_1982_, v_snd_1980_);
v___x_1984_ = l_Array_append___redArg(v_result_1969_, v___x_1983_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = l_Lean_Expr_isApp(v_e_1967_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1987_; 
lean_dec(v_numExtra_1968_);
lean_dec_ref(v_e_1967_);
lean_dec_ref(v_d_1966_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1984_);
v___x_1987_ = v___x_1978_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1984_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_del_object(v___x_1978_);
v___x_1989_ = l_Lean_Expr_appFn_x21(v_e_1967_);
lean_dec_ref(v_e_1967_);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_add(v_numExtra_1968_, v___x_1990_);
lean_dec(v_numExtra_1968_);
v_e_1967_ = v___x_1989_;
v_numExtra_1968_ = v___x_1991_;
v_result_1969_ = v___x_1984_;
goto _start;
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_result_1969_);
lean_dec(v_numExtra_1968_);
lean_dec_ref(v_e_1967_);
lean_dec_ref(v_d_1966_);
v_a_1994_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1975_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1975_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2002_, lean_object* v_e_2003_, lean_object* v_numExtra_2004_, lean_object* v_result_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2002_, v_e_2003_, v_numExtra_2004_, v_result_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2012_, lean_object* v_d_2013_, lean_object* v_e_2014_, lean_object* v_numExtra_2015_, lean_object* v_result_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2013_, v_e_2014_, v_numExtra_2015_, v_result_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_d_2024_, lean_object* v_e_2025_, lean_object* v_numExtra_2026_, lean_object* v_result_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2023_, v_d_2024_, v_e_2025_, v_numExtra_2026_, v_result_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2034_, lean_object* v_numExtra_2035_, size_t v_sz_2036_, size_t v_i_2037_, lean_object* v_bs_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2035_, v_sz_2036_, v_i_2037_, v_bs_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_numExtra_2041_, lean_object* v_sz_2042_, lean_object* v_i_2043_, lean_object* v_bs_2044_){
_start:
{
size_t v_sz_boxed_2045_; size_t v_i_boxed_2046_; lean_object* v_res_2047_; 
v_sz_boxed_2045_ = lean_unbox_usize(v_sz_2042_);
lean_dec(v_sz_2042_);
v_i_boxed_2046_ = lean_unbox_usize(v_i_2043_);
lean_dec(v_i_2043_);
v_res_2047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2040_, v_numExtra_2041_, v_sz_boxed_2045_, v_i_boxed_2046_, v_bs_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2048_, size_t v_i_2049_, lean_object* v_bs_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2049_, v_sz_2048_);
if (v___x_2051_ == 0)
{
return v_bs_2050_;
}
else
{
lean_object* v_v_2052_; lean_object* v___x_2053_; lean_object* v_bs_x27_2054_; lean_object* v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v_v_2052_ = lean_array_uget(v_bs_2050_, v_i_2049_);
v___x_2053_ = lean_unsigned_to_nat(0u);
v_bs_x27_2054_ = lean_array_uset(v_bs_2050_, v_i_2049_, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_v_2052_);
lean_ctor_set(v___x_2055_, 1, v___x_2053_);
v___x_2056_ = ((size_t)1ULL);
v___x_2057_ = lean_usize_add(v_i_2049_, v___x_2056_);
v___x_2058_ = lean_array_uset(v_bs_x27_2054_, v_i_2049_, v___x_2055_);
v_i_2049_ = v___x_2057_;
v_bs_2050_ = v___x_2058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2060_, lean_object* v_i_2061_, lean_object* v_bs_2062_){
_start:
{
size_t v_sz_boxed_2063_; size_t v_i_boxed_2064_; lean_object* v_res_2065_; 
v_sz_boxed_2063_ = lean_unbox_usize(v_sz_2060_);
lean_dec(v_sz_2060_);
v_i_boxed_2064_ = lean_unbox_usize(v_i_2061_);
lean_dec(v_i_2061_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2063_, v_i_boxed_2064_, v_bs_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2066_, lean_object* v_e_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2073_; 
lean_inc_ref(v_e_2067_);
lean_inc_ref(v_d_2066_);
v___x_2073_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2066_, v_e_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2108_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2108_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2108_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_fst_2078_; lean_object* v_snd_2079_; size_t v_sz_2080_; size_t v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v_fst_2078_ = lean_ctor_get(v_a_2074_, 0);
lean_inc(v_fst_2078_);
v_snd_2079_ = lean_ctor_get(v_a_2074_, 1);
lean_inc(v_snd_2079_);
lean_dec(v_a_2074_);
v_sz_2080_ = lean_array_size(v_snd_2079_);
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2080_, v___x_2081_, v_snd_2079_);
v___x_2083_ = l_Lean_Expr_isApp(v_e_2067_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v_fst_2078_);
lean_dec_ref(v_e_2067_);
lean_dec_ref(v_d_2066_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2082_);
v___x_2085_ = v___x_2076_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2082_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
else
{
lean_object* v___x_2087_; 
lean_del_object(v___x_2076_);
lean_inc_ref(v_d_2066_);
v___x_2087_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2066_, v_fst_2078_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2099_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2099_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2099_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_unbox(v_a_2088_);
lean_dec(v_a_2088_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2094_; 
lean_dec_ref(v_e_2067_);
lean_dec_ref(v_d_2066_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2082_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2082_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_del_object(v___x_2090_);
v___x_2096_ = l_Lean_Expr_appFn_x21(v_e_2067_);
lean_dec_ref(v_e_2067_);
v___x_2097_ = lean_unsigned_to_nat(1u);
v___x_2098_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2066_, v___x_2096_, v___x_2097_, v___x_2082_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2098_;
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v___x_2082_);
lean_dec_ref(v_e_2067_);
lean_dec_ref(v_d_2066_);
v_a_2100_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2087_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2087_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_e_2067_);
lean_dec_ref(v_d_2066_);
v_a_2109_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2073_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2073_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2117_, lean_object* v_e_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2117_, v_e_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2125_, lean_object* v_d_2126_, lean_object* v_e_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2126_, v_e_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_d_2135_, lean_object* v_e_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2134_, v_d_2135_, v_e_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2143_, size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_bs_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2144_, v_i_2145_, v_bs_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_sz_2149_, lean_object* v_i_2150_, lean_object* v_bs_2151_){
_start:
{
size_t v_sz_boxed_2152_; size_t v_i_boxed_2153_; lean_object* v_res_2154_; 
v_sz_boxed_2152_ = lean_unbox_usize(v_sz_2149_);
lean_dec(v_sz_2149_);
v_i_boxed_2153_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2148_, v_sz_boxed_2152_, v_i_boxed_2153_, v_bs_2151_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
uint8_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = 1;
v___x_2162_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2155_, v___x_2161_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2187_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2187_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2187_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v___y_2169_; lean_object* v___x_2174_; 
v___x_2167_ = l_Lean_Expr_getAppNumArgs(v_a_2163_);
v___x_2174_ = l_Lean_Expr_getAppFn(v_a_2163_);
lean_dec(v_a_2163_);
switch(lean_obj_tag(v___x_2174_))
{
case 9:
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc_ref(v_a_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_a_2175_);
v___y_2169_ = v___x_2176_;
goto v___jp_2168_;
}
case 1:
{
lean_object* v_fvarId_2177_; lean_object* v___x_2178_; 
v_fvarId_2177_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_fvarId_2177_);
lean_dec_ref(v___x_2174_);
lean_inc(v___x_2167_);
v___x_2178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_fvarId_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2167_);
v___y_2169_ = v___x_2178_;
goto v___jp_2168_;
}
case 2:
{
lean_object* v___x_2179_; 
lean_dec_ref(v___x_2174_);
v___x_2179_ = lean_box(1);
v___y_2169_ = v___x_2179_;
goto v___jp_2168_;
}
case 11:
{
lean_object* v_typeName_2180_; lean_object* v_idx_2181_; lean_object* v___x_2182_; 
v_typeName_2180_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_typeName_2180_);
v_idx_2181_ = lean_ctor_get(v___x_2174_, 1);
lean_inc(v_idx_2181_);
lean_dec_ref(v___x_2174_);
lean_inc(v___x_2167_);
v___x_2182_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2182_, 0, v_typeName_2180_);
lean_ctor_set(v___x_2182_, 1, v_idx_2181_);
lean_ctor_set(v___x_2182_, 2, v___x_2167_);
v___y_2169_ = v___x_2182_;
goto v___jp_2168_;
}
case 7:
{
lean_object* v___x_2183_; 
lean_dec_ref(v___x_2174_);
v___x_2183_ = lean_box(5);
v___y_2169_ = v___x_2183_;
goto v___jp_2168_;
}
case 4:
{
lean_object* v_declName_2184_; lean_object* v___x_2185_; 
v_declName_2184_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_declName_2184_);
lean_dec_ref(v___x_2174_);
lean_inc(v___x_2167_);
v___x_2185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_declName_2184_);
lean_ctor_set(v___x_2185_, 1, v___x_2167_);
v___y_2169_ = v___x_2185_;
goto v___jp_2168_;
}
default: 
{
lean_object* v___x_2186_; 
lean_dec_ref(v___x_2174_);
v___x_2186_ = lean_box(1);
v___y_2169_ = v___x_2186_;
goto v___jp_2168_;
}
}
v___jp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___y_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2167_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2170_);
v___x_2172_ = v___x_2165_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_a_2188_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2162_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2162_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2203_, size_t v_sz_2204_, size_t v_i_2205_, lean_object* v_b_2206_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
if (v___x_2207_ == 0)
{
return v_b_2206_;
}
else
{
lean_object* v_a_2208_; lean_object* v_snd_2209_; lean_object* v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; 
v_a_2208_ = lean_array_uget_borrowed(v_as_2203_, v_i_2205_);
v_snd_2209_ = lean_ctor_get(v_a_2208_, 1);
v___x_2210_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2209_, v_b_2206_);
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2205_, v___x_2211_);
v_i_2205_ = v___x_2212_;
v_b_2206_ = v___x_2210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2214_, lean_object* v_result_2215_){
_start:
{
lean_object* v_vs_2216_; lean_object* v_children_2217_; lean_object* v_result_2218_; size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_vs_2216_ = lean_ctor_get(v_trie_2214_, 0);
v_children_2217_ = lean_ctor_get(v_trie_2214_, 1);
v_result_2218_ = l_Array_append___redArg(v_result_2215_, v_vs_2216_);
v_sz_2219_ = lean_array_size(v_children_2217_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2217_, v_sz_2219_, v___x_2220_, v_result_2218_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2222_, lean_object* v_result_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2222_, v_result_2223_);
lean_dec_ref(v_trie_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2225_, lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_b_2228_){
_start:
{
size_t v_sz_boxed_2229_; size_t v_i_boxed_2230_; lean_object* v_res_2231_; 
v_sz_boxed_2229_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2225_, v_sz_boxed_2229_, v_i_boxed_2230_, v_b_2228_);
lean_dec_ref(v_as_2225_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2232_, lean_object* v_trie_2233_, lean_object* v_result_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2233_, v_result_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_trie_2237_, lean_object* v_result_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2236_, v_trie_2237_, v_result_2238_);
lean_dec_ref(v_trie_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2240_, lean_object* v_as_2241_, size_t v_sz_2242_, size_t v_i_2243_, lean_object* v_b_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2241_, v_sz_2242_, v_i_2243_, v_b_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_as_2247_, lean_object* v_sz_2248_, lean_object* v_i_2249_, lean_object* v_b_2250_){
_start:
{
size_t v_sz_boxed_2251_; size_t v_i_boxed_2252_; lean_object* v_res_2253_; 
v_sz_boxed_2251_ = lean_unbox_usize(v_sz_2248_);
lean_dec(v_sz_2248_);
v_i_boxed_2252_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2246_, v_as_2247_, v_sz_boxed_2251_, v_i_boxed_2252_, v_b_2250_);
lean_dec_ref(v_as_2247_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2254_, lean_object* v_k_2255_, lean_object* v_result_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2254_, v_k_2255_);
if (lean_obj_tag(v___x_2257_) == 0)
{
return v_result_2256_;
}
else
{
lean_object* v_val_2258_; lean_object* v___x_2259_; 
v_val_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_val_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2258_, v_result_2256_);
lean_dec(v_val_2258_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2260_, lean_object* v_k_2261_, lean_object* v_result_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2260_, v_k_2261_, v_result_2262_);
lean_dec(v_k_2261_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2264_, lean_object* v_d_2265_, lean_object* v_k_2266_, lean_object* v_result_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2265_, v_k_2266_, v_result_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_d_2270_, lean_object* v_k_2271_, lean_object* v_result_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2269_, v_d_2270_, v_k_2271_, v_result_2272_);
lean_dec(v_k_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2274_, lean_object* v_e_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2281_; uint8_t v_foApprox_2282_; uint8_t v_ctxApprox_2283_; uint8_t v_quasiPatternApprox_2284_; uint8_t v_constApprox_2285_; uint8_t v_isDefEqStuckEx_2286_; uint8_t v_unificationHints_2287_; uint8_t v_proofIrrelevance_2288_; uint8_t v_assignSyntheticOpaque_2289_; uint8_t v_offsetCnstrs_2290_; uint8_t v_etaStruct_2291_; uint8_t v_univApprox_2292_; uint8_t v_iota_2293_; uint8_t v_beta_2294_; uint8_t v_proj_2295_; uint8_t v_zeta_2296_; uint8_t v_zetaDelta_2297_; uint8_t v_zetaUnused_2298_; uint8_t v_zetaHave_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2353_; 
v___x_2281_ = l_Lean_Meta_Context_config(v_a_2276_);
v_foApprox_2282_ = lean_ctor_get_uint8(v___x_2281_, 0);
v_ctxApprox_2283_ = lean_ctor_get_uint8(v___x_2281_, 1);
v_quasiPatternApprox_2284_ = lean_ctor_get_uint8(v___x_2281_, 2);
v_constApprox_2285_ = lean_ctor_get_uint8(v___x_2281_, 3);
v_isDefEqStuckEx_2286_ = lean_ctor_get_uint8(v___x_2281_, 4);
v_unificationHints_2287_ = lean_ctor_get_uint8(v___x_2281_, 5);
v_proofIrrelevance_2288_ = lean_ctor_get_uint8(v___x_2281_, 6);
v_assignSyntheticOpaque_2289_ = lean_ctor_get_uint8(v___x_2281_, 7);
v_offsetCnstrs_2290_ = lean_ctor_get_uint8(v___x_2281_, 8);
v_etaStruct_2291_ = lean_ctor_get_uint8(v___x_2281_, 10);
v_univApprox_2292_ = lean_ctor_get_uint8(v___x_2281_, 11);
v_iota_2293_ = lean_ctor_get_uint8(v___x_2281_, 12);
v_beta_2294_ = lean_ctor_get_uint8(v___x_2281_, 13);
v_proj_2295_ = lean_ctor_get_uint8(v___x_2281_, 14);
v_zeta_2296_ = lean_ctor_get_uint8(v___x_2281_, 15);
v_zetaDelta_2297_ = lean_ctor_get_uint8(v___x_2281_, 16);
v_zetaUnused_2298_ = lean_ctor_get_uint8(v___x_2281_, 17);
v_zetaHave_2299_ = lean_ctor_get_uint8(v___x_2281_, 18);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2301_ = v___x_2281_;
v_isShared_2302_ = v_isSharedCheck_2353_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v___x_2281_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2353_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
uint8_t v_trackZetaDelta_2303_; lean_object* v_zetaDeltaSet_2304_; lean_object* v_lctx_2305_; lean_object* v_localInstances_2306_; lean_object* v_defEqCtx_x3f_2307_; lean_object* v_synthPendingDepth_2308_; lean_object* v_canUnfold_x3f_2309_; uint8_t v_univApprox_2310_; uint8_t v_inTypeClassResolution_2311_; uint8_t v_cacheInferType_2312_; uint8_t v___x_2313_; lean_object* v_config_2315_; 
v_trackZetaDelta_2303_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*7);
v_zetaDeltaSet_2304_ = lean_ctor_get(v_a_2276_, 1);
v_lctx_2305_ = lean_ctor_get(v_a_2276_, 2);
v_localInstances_2306_ = lean_ctor_get(v_a_2276_, 3);
v_defEqCtx_x3f_2307_ = lean_ctor_get(v_a_2276_, 4);
v_synthPendingDepth_2308_ = lean_ctor_get(v_a_2276_, 5);
v_canUnfold_x3f_2309_ = lean_ctor_get(v_a_2276_, 6);
v_univApprox_2310_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2311_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*7 + 2);
v_cacheInferType_2312_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*7 + 3);
v___x_2313_ = 2;
if (v_isShared_2302_ == 0)
{
v_config_2315_ = v___x_2301_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 0, v_foApprox_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 1, v_ctxApprox_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 2, v_quasiPatternApprox_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 3, v_constApprox_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 4, v_isDefEqStuckEx_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 5, v_unificationHints_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 6, v_proofIrrelevance_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 7, v_assignSyntheticOpaque_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 8, v_offsetCnstrs_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 10, v_etaStruct_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 11, v_univApprox_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 12, v_iota_2293_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 13, v_beta_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 14, v_proj_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 15, v_zeta_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 16, v_zetaDelta_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 17, v_zetaUnused_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2352_, 18, v_zetaHave_2299_);
v_config_2315_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
uint64_t v___x_2316_; uint64_t v___x_2317_; uint64_t v___x_2318_; uint64_t v___x_2319_; uint64_t v___x_2320_; uint64_t v_key_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_ctor_set_uint8(v_config_2315_, 9, v___x_2313_);
v___x_2316_ = l_Lean_Meta_Context_configKey(v_a_2276_);
v___x_2317_ = 2ULL;
v___x_2318_ = lean_uint64_shift_right(v___x_2316_, v___x_2317_);
v___x_2319_ = lean_uint64_shift_left(v___x_2318_, v___x_2317_);
v___x_2320_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2321_ = lean_uint64_lor(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2322_, 0, v_config_2315_);
lean_ctor_set_uint64(v___x_2322_, sizeof(void*)*1, v_key_2321_);
lean_inc(v_canUnfold_x3f_2309_);
lean_inc(v_synthPendingDepth_2308_);
lean_inc(v_defEqCtx_x3f_2307_);
lean_inc_ref(v_localInstances_2306_);
lean_inc_ref(v_lctx_2305_);
lean_inc(v_zetaDeltaSet_2304_);
v___x_2323_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v_zetaDeltaSet_2304_);
lean_ctor_set(v___x_2323_, 2, v_lctx_2305_);
lean_ctor_set(v___x_2323_, 3, v_localInstances_2306_);
lean_ctor_set(v___x_2323_, 4, v_defEqCtx_x3f_2307_);
lean_ctor_set(v___x_2323_, 5, v_synthPendingDepth_2308_);
lean_ctor_set(v___x_2323_, 6, v_canUnfold_x3f_2309_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*7, v_trackZetaDelta_2303_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*7 + 1, v_univApprox_2310_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2311_);
lean_ctor_set_uint8(v___x_2323_, sizeof(void*)*7 + 3, v_cacheInferType_2312_);
v___x_2324_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2275_, v___x_2323_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v___x_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2343_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2343_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2343_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_fst_2329_; lean_object* v_snd_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2342_; 
v_fst_2329_ = lean_ctor_get(v_a_2325_, 0);
v_snd_2330_ = lean_ctor_get(v_a_2325_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_a_2325_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2332_ = v_a_2325_;
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_snd_2330_);
lean_inc(v_fst_2329_);
lean_dec(v_a_2325_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v_result_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_inc_ref(v_d_2274_);
v_result_2334_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2274_);
v___x_2335_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2274_, v_fst_2329_, v_result_2334_);
lean_dec(v_fst_2329_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_snd_2330_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2337_);
v___x_2339_ = v___x_2327_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v_d_2274_);
v_a_2344_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2324_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2324_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2354_, lean_object* v_e_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2354_, v_e_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2362_, lean_object* v_d_2363_, lean_object* v_e_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2363_, v_e_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2371_, lean_object* v_d_2372_, lean_object* v_e_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2371_, v_d_2372_, v_e_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2380_, lean_object* v_todo_2381_, lean_object* v_as_2382_, size_t v_i_2383_, size_t v_stop_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_usize_dec_eq(v_i_2383_, v_stop_2384_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v_fst_2393_; lean_object* v_snd_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2392_ = lean_array_uget_borrowed(v_as_2382_, v_i_2383_);
v_fst_2393_ = lean_ctor_get(v___x_2392_, 0);
v_snd_2394_ = lean_ctor_get(v___x_2392_, 1);
v___x_2395_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2393_);
v___x_2396_ = lean_nat_add(v_n_2380_, v___x_2395_);
lean_dec(v___x_2395_);
lean_inc(v_snd_2394_);
lean_inc_ref(v_todo_2381_);
v___x_2397_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2396_, v_todo_2381_, v_snd_2394_, v_b_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; size_t v___x_2399_; size_t v___x_2400_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = lean_usize_add(v_i_2383_, v___x_2399_);
v_i_2383_ = v___x_2400_;
v_b_2385_ = v_a_2398_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2381_);
return v___x_2397_;
}
}
else
{
lean_object* v___x_2402_; 
lean_dec_ref(v_todo_2381_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v_b_2385_);
return v___x_2402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2403_, lean_object* v_todo_2404_, lean_object* v_c_2405_, lean_object* v_result_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_zero_2412_; uint8_t v_isZero_2413_; 
v_zero_2412_ = lean_unsigned_to_nat(0u);
v_isZero_2413_ = lean_nat_dec_eq(v_skip_2403_, v_zero_2412_);
if (v_isZero_2413_ == 1)
{
lean_object* v_vs_2414_; lean_object* v_children_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
lean_dec(v_skip_2403_);
v_vs_2414_ = lean_ctor_get(v_c_2405_, 0);
lean_inc_ref(v_vs_2414_);
v_children_2415_ = lean_ctor_get(v_c_2405_, 1);
lean_inc_ref(v_children_2415_);
lean_dec_ref(v_c_2405_);
v___x_2416_ = lean_array_get_size(v_todo_2404_);
v___x_2417_ = lean_nat_dec_eq(v___x_2416_, v_zero_2412_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
lean_dec_ref(v_vs_2414_);
v___x_2418_ = lean_array_get_size(v_children_2415_);
v___x_2419_ = lean_nat_dec_eq(v___x_2418_, v_zero_2412_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v_e_2423_; lean_object* v___x_2424_; 
v___x_2420_ = l_Lean_instInhabitedExpr;
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = lean_nat_sub(v___x_2416_, v___x_2421_);
v_e_2423_ = lean_array_get_borrowed(v___x_2420_, v_todo_2404_, v___x_2422_);
lean_dec(v___x_2422_);
lean_inc(v_e_2423_);
v___x_2424_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2423_, v___x_2419_, v___x_2419_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2476_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2476_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2476_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2475_; 
v_fst_2429_ = lean_ctor_get(v_a_2425_, 0);
v_snd_2430_ = lean_ctor_get(v_a_2425_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2432_ = v_a_2425_;
v_isShared_2433_ = v_isSharedCheck_2475_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_snd_2430_);
lean_inc(v_fst_2429_);
lean_dec(v_a_2425_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2475_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_todo_2434_; lean_object* v___y_2436_; lean_object* v_a_2437_; 
v_todo_2434_ = lean_array_pop(v_todo_2404_);
if (lean_obj_tag(v_fst_2429_) == 0)
{
uint8_t v___x_2450_; 
lean_del_object(v___x_2432_);
lean_dec(v_snd_2430_);
v___x_2450_ = lean_nat_dec_lt(v_zero_2412_, v___x_2418_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2452_; 
lean_dec_ref(v_todo_2434_);
lean_dec_ref(v_children_2415_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_result_2406_);
v___x_2452_ = v___x_2427_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_result_2406_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
else
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_nat_dec_le(v___x_2418_, v___x_2418_);
if (v___x_2454_ == 0)
{
if (v___x_2450_ == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref(v_todo_2434_);
lean_dec_ref(v_children_2415_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_result_2406_);
v___x_2456_ = v___x_2427_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_result_2406_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
else
{
size_t v___x_2458_; size_t v___x_2459_; lean_object* v___x_2460_; 
lean_del_object(v___x_2427_);
v___x_2458_ = ((size_t)0ULL);
v___x_2459_ = lean_usize_of_nat(v___x_2418_);
v___x_2460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2434_, v_children_2415_, v___x_2458_, v___x_2459_, v_result_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec_ref(v_children_2415_);
return v___x_2460_;
}
}
else
{
size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; 
lean_del_object(v___x_2427_);
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = lean_usize_of_nat(v___x_2418_);
v___x_2463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2434_, v_children_2415_, v___x_2461_, v___x_2462_, v_result_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec_ref(v_children_2415_);
return v___x_2463_;
}
}
}
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; uint8_t v___x_2469_; 
v___x_2464_ = lean_box(0);
v___x_2465_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_2466_ = lean_array_get_borrowed(v___x_2465_, v_children_2415_, v_zero_2412_);
v_fst_2467_ = lean_ctor_get(v___x_2466_, 0);
v_snd_2468_ = lean_ctor_get(v___x_2466_, 1);
v___x_2469_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2467_, v___x_2464_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2471_; 
lean_inc_ref(v_result_2406_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_result_2406_);
v___x_2471_ = v___x_2427_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_result_2406_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
v___y_2436_ = v___x_2471_;
v_a_2437_ = v_result_2406_;
goto v___jp_2435_;
}
}
else
{
lean_object* v___x_2473_; 
lean_del_object(v___x_2427_);
lean_inc(v_snd_2468_);
lean_inc_ref(v_todo_2434_);
v___x_2473_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2412_, v_todo_2434_, v_snd_2468_, v_result_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
v___y_2436_ = v___x_2473_;
v_a_2437_ = v_a_2474_;
goto v___jp_2435_;
}
else
{
lean_dec_ref(v_todo_2434_);
lean_del_object(v___x_2432_);
lean_dec(v_snd_2430_);
lean_dec(v_fst_2429_);
lean_dec_ref(v_children_2415_);
return v___x_2473_;
}
}
}
v___jp_2435_:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_nat_dec_lt(v_zero_2412_, v___x_2418_);
if (v___x_2438_ == 0)
{
lean_dec_ref(v_a_2437_);
lean_dec_ref(v_todo_2434_);
lean_del_object(v___x_2432_);
lean_dec(v_snd_2430_);
lean_dec(v_fst_2429_);
lean_dec_ref(v_children_2415_);
return v___y_2436_;
}
else
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = lean_nat_sub(v___x_2418_, v___x_2421_);
v___x_2440_ = lean_nat_dec_le(v_zero_2412_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_dec(v___x_2439_);
lean_dec_ref(v_a_2437_);
lean_dec_ref(v_todo_2434_);
lean_del_object(v___x_2432_);
lean_dec(v_snd_2430_);
lean_dec(v_fst_2429_);
lean_dec_ref(v_children_2415_);
return v___y_2436_;
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___x_2441_);
v___x_2443_ = v___x_2432_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_fst_2429_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_2415_, v___x_2443_, v_zero_2412_, v___x_2439_);
lean_dec_ref(v___x_2443_);
lean_dec_ref(v_children_2415_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_dec_ref(v_a_2437_);
lean_dec_ref(v_todo_2434_);
lean_dec(v_snd_2430_);
return v___y_2436_;
}
else
{
lean_object* v_val_2445_; lean_object* v_snd_2446_; lean_object* v___x_2447_; 
lean_dec_ref(v___y_2436_);
v_val_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_val_2445_);
lean_dec_ref(v___x_2444_);
v_snd_2446_ = lean_ctor_get(v_val_2445_, 1);
lean_inc(v_snd_2446_);
lean_dec(v_val_2445_);
v___x_2447_ = l_Array_append___redArg(v_todo_2434_, v_snd_2430_);
lean_dec(v_snd_2430_);
v_skip_2403_ = v_zero_2412_;
v_todo_2404_ = v___x_2447_;
v_c_2405_ = v_snd_2446_;
v_result_2406_ = v_a_2437_;
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
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_children_2415_);
lean_dec_ref(v_result_2406_);
lean_dec_ref(v_todo_2404_);
v_a_2477_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2424_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2424_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v___x_2485_; 
lean_dec_ref(v_children_2415_);
lean_dec_ref(v_todo_2404_);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_result_2406_);
return v___x_2485_;
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec_ref(v_children_2415_);
lean_dec_ref(v_todo_2404_);
v___x_2486_ = l_Array_append___redArg(v_result_2406_, v_vs_2414_);
lean_dec_ref(v_vs_2414_);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
return v___x_2487_;
}
}
else
{
lean_object* v_children_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v_children_2488_ = lean_ctor_get(v_c_2405_, 1);
lean_inc_ref(v_children_2488_);
lean_dec_ref(v_c_2405_);
v___x_2489_ = lean_array_get_size(v_children_2488_);
v___x_2490_ = lean_nat_dec_eq(v___x_2489_, v_zero_2412_);
if (v___x_2490_ == 0)
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_nat_dec_lt(v_zero_2412_, v___x_2489_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref(v_children_2488_);
lean_dec_ref(v_todo_2404_);
lean_dec(v_skip_2403_);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_result_2406_);
return v___x_2492_;
}
else
{
lean_object* v_one_2493_; lean_object* v_n_2494_; uint8_t v___x_2495_; 
v_one_2493_ = lean_unsigned_to_nat(1u);
v_n_2494_ = lean_nat_sub(v_skip_2403_, v_one_2493_);
lean_dec(v_skip_2403_);
v___x_2495_ = lean_nat_dec_le(v___x_2489_, v___x_2489_);
if (v___x_2495_ == 0)
{
if (v___x_2491_ == 0)
{
lean_object* v___x_2496_; 
lean_dec(v_n_2494_);
lean_dec_ref(v_children_2488_);
lean_dec_ref(v_todo_2404_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_result_2406_);
return v___x_2496_;
}
else
{
size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = ((size_t)0ULL);
v___x_2498_ = lean_usize_of_nat(v___x_2489_);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2494_, v_todo_2404_, v_children_2488_, v___x_2497_, v___x_2498_, v_result_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec_ref(v_children_2488_);
lean_dec(v_n_2494_);
return v___x_2499_;
}
}
else
{
size_t v___x_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = ((size_t)0ULL);
v___x_2501_ = lean_usize_of_nat(v___x_2489_);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2494_, v_todo_2404_, v_children_2488_, v___x_2500_, v___x_2501_, v_result_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec_ref(v_children_2488_);
lean_dec(v_n_2494_);
return v___x_2502_;
}
}
}
else
{
lean_object* v___x_2503_; 
lean_dec_ref(v_children_2488_);
lean_dec_ref(v_todo_2404_);
lean_dec(v_skip_2403_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_result_2406_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2504_, lean_object* v_as_2505_, size_t v_i_2506_, size_t v_stop_2507_, lean_object* v_b_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_eq(v_i_2506_, v_stop_2507_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v_fst_2516_; lean_object* v_snd_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2515_ = lean_array_uget_borrowed(v_as_2505_, v_i_2506_);
v_fst_2516_ = lean_ctor_get(v___x_2515_, 0);
v_snd_2517_ = lean_ctor_get(v___x_2515_, 1);
v___x_2518_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2516_);
lean_inc(v_snd_2517_);
lean_inc_ref(v_todo_2504_);
v___x_2519_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2518_, v_todo_2504_, v_snd_2517_, v_b_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; size_t v___x_2521_; size_t v___x_2522_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref(v___x_2519_);
v___x_2521_ = ((size_t)1ULL);
v___x_2522_ = lean_usize_add(v_i_2506_, v___x_2521_);
v_i_2506_ = v___x_2522_;
v_b_2508_ = v_a_2520_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2504_);
return v___x_2519_;
}
}
else
{
lean_object* v___x_2524_; 
lean_dec_ref(v_todo_2504_);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_b_2508_);
return v___x_2524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2525_, lean_object* v_as_2526_, lean_object* v_i_2527_, lean_object* v_stop_2528_, lean_object* v_b_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
size_t v_i_boxed_2535_; size_t v_stop_boxed_2536_; lean_object* v_res_2537_; 
v_i_boxed_2535_ = lean_unbox_usize(v_i_2527_);
lean_dec(v_i_2527_);
v_stop_boxed_2536_ = lean_unbox_usize(v_stop_2528_);
lean_dec(v_stop_2528_);
v_res_2537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2525_, v_as_2526_, v_i_boxed_2535_, v_stop_boxed_2536_, v_b_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_as_2526_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2538_, lean_object* v_todo_2539_, lean_object* v_as_2540_, lean_object* v_i_2541_, lean_object* v_stop_2542_, lean_object* v_b_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
size_t v_i_boxed_2549_; size_t v_stop_boxed_2550_; lean_object* v_res_2551_; 
v_i_boxed_2549_ = lean_unbox_usize(v_i_2541_);
lean_dec(v_i_2541_);
v_stop_boxed_2550_ = lean_unbox_usize(v_stop_2542_);
lean_dec(v_stop_2542_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2538_, v_todo_2539_, v_as_2540_, v_i_boxed_2549_, v_stop_boxed_2550_, v_b_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v_as_2540_);
lean_dec(v_n_2538_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2552_, lean_object* v_todo_2553_, lean_object* v_c_2554_, lean_object* v_result_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2552_, v_todo_2553_, v_c_2554_, v_result_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2562_, lean_object* v_skip_2563_, lean_object* v_todo_2564_, lean_object* v_c_2565_, lean_object* v_result_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2563_, v_todo_2564_, v_c_2565_, v_result_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_skip_2574_, lean_object* v_todo_2575_, lean_object* v_c_2576_, lean_object* v_result_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2573_, v_skip_2574_, v_todo_2575_, v_c_2576_, v_result_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2584_, lean_object* v_todo_2585_, lean_object* v_as_2586_, size_t v_i_2587_, size_t v_stop_2588_, lean_object* v_b_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2585_, v_as_2586_, v_i_2587_, v_stop_2588_, v_b_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2596_, lean_object* v_todo_2597_, lean_object* v_as_2598_, lean_object* v_i_2599_, lean_object* v_stop_2600_, lean_object* v_b_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
size_t v_i_boxed_2607_; size_t v_stop_boxed_2608_; lean_object* v_res_2609_; 
v_i_boxed_2607_ = lean_unbox_usize(v_i_2599_);
lean_dec(v_i_2599_);
v_stop_boxed_2608_ = lean_unbox_usize(v_stop_2600_);
lean_dec(v_stop_2600_);
v_res_2609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2596_, v_todo_2597_, v_as_2598_, v_i_boxed_2607_, v_stop_boxed_2608_, v_b_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec_ref(v_as_2598_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2610_, lean_object* v_n_2611_, lean_object* v_todo_2612_, lean_object* v_as_2613_, size_t v_i_2614_, size_t v_stop_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2611_, v_todo_2612_, v_as_2613_, v_i_2614_, v_stop_2615_, v_b_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2623_, lean_object* v_n_2624_, lean_object* v_todo_2625_, lean_object* v_as_2626_, lean_object* v_i_2627_, lean_object* v_stop_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
size_t v_i_boxed_2635_; size_t v_stop_boxed_2636_; lean_object* v_res_2637_; 
v_i_boxed_2635_ = lean_unbox_usize(v_i_2627_);
lean_dec(v_i_2627_);
v_stop_boxed_2636_ = lean_unbox_usize(v_stop_2628_);
lean_dec(v_stop_2628_);
v_res_2637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2623_, v_n_2624_, v_todo_2625_, v_as_2626_, v_i_boxed_2635_, v_stop_boxed_2636_, v_b_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v_as_2626_);
lean_dec(v_n_2624_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2638_, lean_object* v_k_2639_, lean_object* v_c_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2639_);
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2648_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2646_, v___x_2647_, v_c_2640_, v_result_2638_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2649_, lean_object* v_k_2650_, lean_object* v_c_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2649_, v_k_2650_, v_c_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v_k_2650_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2658_, lean_object* v_keys_2659_, lean_object* v_vals_2660_, lean_object* v_i_2661_, lean_object* v_acc_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = lean_array_get_size(v_keys_2659_);
v___x_2669_ = lean_nat_dec_lt(v_i_2661_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec(v_i_2661_);
lean_dec_ref(v_f_2658_);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_acc_2662_);
return v___x_2670_;
}
else
{
lean_object* v_k_2671_; lean_object* v_v_2672_; lean_object* v___x_2673_; 
v_k_2671_ = lean_array_fget_borrowed(v_keys_2659_, v_i_2661_);
v_v_2672_ = lean_array_fget_borrowed(v_vals_2660_, v_i_2661_);
lean_inc_ref(v_f_2658_);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
lean_inc(v_v_2672_);
lean_inc(v_k_2671_);
v___x_2673_ = lean_apply_8(v_f_2658_, v_acc_2662_, v_k_2671_, v_v_2672_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, lean_box(0));
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref(v___x_2673_);
v___x_2675_ = lean_unsigned_to_nat(1u);
v___x_2676_ = lean_nat_add(v_i_2661_, v___x_2675_);
lean_dec(v_i_2661_);
v_i_2661_ = v___x_2676_;
v_acc_2662_ = v_a_2674_;
goto _start;
}
else
{
lean_dec(v_i_2661_);
lean_dec_ref(v_f_2658_);
return v___x_2673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2678_, lean_object* v_keys_2679_, lean_object* v_vals_2680_, lean_object* v_i_2681_, lean_object* v_acc_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2678_, v_keys_2679_, v_vals_2680_, v_i_2681_, v_acc_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec_ref(v_vals_2680_);
lean_dec_ref(v_keys_2679_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
if (lean_obj_tag(v_x_2690_) == 0)
{
lean_object* v_es_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2717_; 
v_es_2697_ = lean_ctor_get(v_x_2690_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_x_2690_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2699_ = v_x_2690_;
v_isShared_2700_ = v_isSharedCheck_2717_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_es_2697_);
lean_dec(v_x_2690_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2717_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_array_get_size(v_es_2697_);
v___x_2703_ = lean_nat_dec_lt(v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2705_; 
lean_dec_ref(v_es_2697_);
lean_dec_ref(v_f_2689_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v_x_2691_);
v___x_2705_ = v___x_2699_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_x_2691_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
else
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_nat_dec_le(v___x_2702_, v___x_2702_);
if (v___x_2707_ == 0)
{
if (v___x_2703_ == 0)
{
lean_object* v___x_2709_; 
lean_dec_ref(v_es_2697_);
lean_dec_ref(v_f_2689_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v_x_2691_);
v___x_2709_ = v___x_2699_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_x_2691_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
else
{
size_t v___x_2711_; size_t v___x_2712_; lean_object* v___x_2713_; 
lean_del_object(v___x_2699_);
v___x_2711_ = ((size_t)0ULL);
v___x_2712_ = lean_usize_of_nat(v___x_2702_);
v___x_2713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2689_, v_es_2697_, v___x_2711_, v___x_2712_, v_x_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec_ref(v_es_2697_);
return v___x_2713_;
}
}
else
{
size_t v___x_2714_; size_t v___x_2715_; lean_object* v___x_2716_; 
lean_del_object(v___x_2699_);
v___x_2714_ = ((size_t)0ULL);
v___x_2715_ = lean_usize_of_nat(v___x_2702_);
v___x_2716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2689_, v_es_2697_, v___x_2714_, v___x_2715_, v_x_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec_ref(v_es_2697_);
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_ks_2718_; lean_object* v_vs_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_ks_2718_ = lean_ctor_get(v_x_2690_, 0);
lean_inc_ref(v_ks_2718_);
v_vs_2719_ = lean_ctor_get(v_x_2690_, 1);
lean_inc_ref(v_vs_2719_);
lean_dec_ref(v_x_2690_);
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2689_, v_ks_2718_, v_vs_2719_, v___x_2720_, v_x_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec_ref(v_vs_2719_);
lean_dec_ref(v_ks_2718_);
return v___x_2721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2722_, lean_object* v_as_2723_, size_t v_i_2724_, size_t v_stop_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_a_2733_; lean_object* v___y_2738_; uint8_t v___x_2740_; 
v___x_2740_ = lean_usize_dec_eq(v_i_2724_, v_stop_2725_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_array_uget_borrowed(v_as_2723_, v_i_2724_);
switch(lean_obj_tag(v___x_2741_))
{
case 0:
{
lean_object* v_key_2742_; lean_object* v_val_2743_; lean_object* v___x_2744_; 
v_key_2742_ = lean_ctor_get(v___x_2741_, 0);
v_val_2743_ = lean_ctor_get(v___x_2741_, 1);
lean_inc_ref(v_f_2722_);
lean_inc(v___y_2730_);
lean_inc_ref(v___y_2729_);
lean_inc(v___y_2728_);
lean_inc_ref(v___y_2727_);
lean_inc(v_val_2743_);
lean_inc(v_key_2742_);
v___x_2744_ = lean_apply_8(v_f_2722_, v_b_2726_, v_key_2742_, v_val_2743_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, lean_box(0));
v___y_2738_ = v___x_2744_;
goto v___jp_2737_;
}
case 1:
{
lean_object* v_node_2745_; lean_object* v___x_2746_; 
v_node_2745_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_node_2745_);
lean_inc_ref(v_f_2722_);
v___x_2746_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2722_, v_node_2745_, v_b_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
v___y_2738_ = v___x_2746_;
goto v___jp_2737_;
}
default: 
{
v_a_2733_ = v_b_2726_;
goto v___jp_2732_;
}
}
}
else
{
lean_object* v___x_2747_; 
lean_dec_ref(v_f_2722_);
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_b_2726_);
return v___x_2747_;
}
v___jp_2732_:
{
size_t v___x_2734_; size_t v___x_2735_; 
v___x_2734_ = ((size_t)1ULL);
v___x_2735_ = lean_usize_add(v_i_2724_, v___x_2734_);
v_i_2724_ = v___x_2735_;
v_b_2726_ = v_a_2733_;
goto _start;
}
v___jp_2737_:
{
if (lean_obj_tag(v___y_2738_) == 0)
{
lean_object* v_a_2739_; 
v_a_2739_ = lean_ctor_get(v___y_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref(v___y_2738_);
v_a_2733_ = v_a_2739_;
goto v___jp_2732_;
}
else
{
lean_dec_ref(v_f_2722_);
return v___y_2738_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2748_, lean_object* v_as_2749_, lean_object* v_i_2750_, lean_object* v_stop_2751_, lean_object* v_b_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
size_t v_i_boxed_2758_; size_t v_stop_boxed_2759_; lean_object* v_res_2760_; 
v_i_boxed_2758_ = lean_unbox_usize(v_i_2750_);
lean_dec(v_i_2750_);
v_stop_boxed_2759_ = lean_unbox_usize(v_stop_2751_);
lean_dec(v_stop_2751_);
v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2748_, v_as_2749_, v_i_boxed_2758_, v_stop_boxed_2759_, v_b_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v_as_2749_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2761_, v_x_2762_, v_x_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2771_, lean_object* v_e_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2778_; uint8_t v_foApprox_2779_; uint8_t v_ctxApprox_2780_; uint8_t v_quasiPatternApprox_2781_; uint8_t v_constApprox_2782_; uint8_t v_isDefEqStuckEx_2783_; uint8_t v_unificationHints_2784_; uint8_t v_proofIrrelevance_2785_; uint8_t v_assignSyntheticOpaque_2786_; uint8_t v_offsetCnstrs_2787_; uint8_t v_etaStruct_2788_; uint8_t v_univApprox_2789_; uint8_t v_iota_2790_; uint8_t v_beta_2791_; uint8_t v_proj_2792_; uint8_t v_zeta_2793_; uint8_t v_zetaDelta_2794_; uint8_t v_zetaUnused_2795_; uint8_t v_zetaHave_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2851_; 
v___x_2778_ = l_Lean_Meta_Context_config(v_a_2773_);
v_foApprox_2779_ = lean_ctor_get_uint8(v___x_2778_, 0);
v_ctxApprox_2780_ = lean_ctor_get_uint8(v___x_2778_, 1);
v_quasiPatternApprox_2781_ = lean_ctor_get_uint8(v___x_2778_, 2);
v_constApprox_2782_ = lean_ctor_get_uint8(v___x_2778_, 3);
v_isDefEqStuckEx_2783_ = lean_ctor_get_uint8(v___x_2778_, 4);
v_unificationHints_2784_ = lean_ctor_get_uint8(v___x_2778_, 5);
v_proofIrrelevance_2785_ = lean_ctor_get_uint8(v___x_2778_, 6);
v_assignSyntheticOpaque_2786_ = lean_ctor_get_uint8(v___x_2778_, 7);
v_offsetCnstrs_2787_ = lean_ctor_get_uint8(v___x_2778_, 8);
v_etaStruct_2788_ = lean_ctor_get_uint8(v___x_2778_, 10);
v_univApprox_2789_ = lean_ctor_get_uint8(v___x_2778_, 11);
v_iota_2790_ = lean_ctor_get_uint8(v___x_2778_, 12);
v_beta_2791_ = lean_ctor_get_uint8(v___x_2778_, 13);
v_proj_2792_ = lean_ctor_get_uint8(v___x_2778_, 14);
v_zeta_2793_ = lean_ctor_get_uint8(v___x_2778_, 15);
v_zetaDelta_2794_ = lean_ctor_get_uint8(v___x_2778_, 16);
v_zetaUnused_2795_ = lean_ctor_get_uint8(v___x_2778_, 17);
v_zetaHave_2796_ = lean_ctor_get_uint8(v___x_2778_, 18);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2798_ = v___x_2778_;
v_isShared_2799_ = v_isSharedCheck_2851_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v___x_2778_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2851_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
uint8_t v_trackZetaDelta_2800_; lean_object* v_zetaDeltaSet_2801_; lean_object* v_lctx_2802_; lean_object* v_localInstances_2803_; lean_object* v_defEqCtx_x3f_2804_; lean_object* v_synthPendingDepth_2805_; lean_object* v_canUnfold_x3f_2806_; uint8_t v_univApprox_2807_; uint8_t v_inTypeClassResolution_2808_; uint8_t v_cacheInferType_2809_; uint8_t v___x_2810_; lean_object* v_config_2812_; 
v_trackZetaDelta_2800_ = lean_ctor_get_uint8(v_a_2773_, sizeof(void*)*7);
v_zetaDeltaSet_2801_ = lean_ctor_get(v_a_2773_, 1);
v_lctx_2802_ = lean_ctor_get(v_a_2773_, 2);
v_localInstances_2803_ = lean_ctor_get(v_a_2773_, 3);
v_defEqCtx_x3f_2804_ = lean_ctor_get(v_a_2773_, 4);
v_synthPendingDepth_2805_ = lean_ctor_get(v_a_2773_, 5);
v_canUnfold_x3f_2806_ = lean_ctor_get(v_a_2773_, 6);
v_univApprox_2807_ = lean_ctor_get_uint8(v_a_2773_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2808_ = lean_ctor_get_uint8(v_a_2773_, sizeof(void*)*7 + 2);
v_cacheInferType_2809_ = lean_ctor_get_uint8(v_a_2773_, sizeof(void*)*7 + 3);
v___x_2810_ = 2;
if (v_isShared_2799_ == 0)
{
v_config_2812_ = v___x_2798_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 0, v_foApprox_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 1, v_ctxApprox_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 2, v_quasiPatternApprox_2781_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 3, v_constApprox_2782_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 4, v_isDefEqStuckEx_2783_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 5, v_unificationHints_2784_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 6, v_proofIrrelevance_2785_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 7, v_assignSyntheticOpaque_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 8, v_offsetCnstrs_2787_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 10, v_etaStruct_2788_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 11, v_univApprox_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 12, v_iota_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 13, v_beta_2791_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 14, v_proj_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 15, v_zeta_2793_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 16, v_zetaDelta_2794_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 17, v_zetaUnused_2795_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, 18, v_zetaHave_2796_);
v_config_2812_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
uint64_t v___x_2813_; uint64_t v___x_2814_; uint64_t v___x_2815_; uint8_t v___x_2816_; uint64_t v___x_2817_; uint64_t v___x_2818_; uint64_t v_key_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; 
lean_ctor_set_uint8(v_config_2812_, 9, v___x_2810_);
v___x_2813_ = l_Lean_Meta_Context_configKey(v_a_2773_);
v___x_2814_ = 2ULL;
v___x_2815_ = lean_uint64_shift_right(v___x_2813_, v___x_2814_);
v___x_2816_ = 1;
v___x_2817_ = lean_uint64_shift_left(v___x_2815_, v___x_2814_);
v___x_2818_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2819_ = lean_uint64_lor(v___x_2817_, v___x_2818_);
v___x_2820_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2820_, 0, v_config_2812_);
lean_ctor_set_uint64(v___x_2820_, sizeof(void*)*1, v_key_2819_);
lean_inc(v_canUnfold_x3f_2806_);
lean_inc(v_synthPendingDepth_2805_);
lean_inc(v_defEqCtx_x3f_2804_);
lean_inc_ref(v_localInstances_2803_);
lean_inc_ref(v_lctx_2802_);
lean_inc(v_zetaDeltaSet_2801_);
v___x_2821_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v_zetaDeltaSet_2801_);
lean_ctor_set(v___x_2821_, 2, v_lctx_2802_);
lean_ctor_set(v___x_2821_, 3, v_localInstances_2803_);
lean_ctor_set(v___x_2821_, 4, v_defEqCtx_x3f_2804_);
lean_ctor_set(v___x_2821_, 5, v_synthPendingDepth_2805_);
lean_ctor_set(v___x_2821_, 6, v_canUnfold_x3f_2806_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7, v_trackZetaDelta_2800_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 1, v_univApprox_2807_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2808_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*7 + 3, v_cacheInferType_2809_);
v___x_2822_ = 0;
v___x_2823_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2772_, v___x_2822_, v___x_2816_, v___x_2821_, v_a_2774_, v_a_2775_, v_a_2776_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2841_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2841_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2841_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v_fst_2828_; 
v_fst_2828_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_fst_2828_);
if (lean_obj_tag(v_fst_2828_) == 0)
{
lean_object* v___f_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2826_);
lean_dec(v_a_2824_);
v___f_2829_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2830_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_2831_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2829_, v_d_2771_, v___x_2830_, v___x_2821_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec_ref(v___x_2821_);
return v___x_2831_;
}
else
{
lean_object* v_snd_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_snd_2832_ = lean_ctor_get(v_a_2824_, 1);
lean_inc(v_snd_2832_);
lean_dec(v_a_2824_);
lean_inc_ref(v_d_2771_);
v___x_2833_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2771_);
v___x_2834_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2771_, v_fst_2828_);
lean_dec(v_fst_2828_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2836_; 
lean_dec(v_snd_2832_);
lean_dec_ref(v___x_2821_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2833_);
v___x_2836_ = v___x_2826_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2833_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
else
{
lean_object* v_val_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
lean_del_object(v___x_2826_);
v_val_2838_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_val_2838_);
lean_dec_ref(v___x_2834_);
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2839_, v_snd_2832_, v_val_2838_, v___x_2833_, v___x_2821_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec_ref(v___x_2821_);
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_d_2771_);
v_a_2842_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2823_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2823_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_2852_, lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2852_, v_e_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_2860_, lean_object* v_d_2861_, lean_object* v_e_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2861_, v_e_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_2869_, lean_object* v_d_2870_, lean_object* v_e_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_2869_, v_d_2870_, v_e_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_2878_, lean_object* v_f_2879_, lean_object* v_init_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2879_, v_map_2878_, v_init_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_2887_, lean_object* v_f_2888_, lean_object* v_init_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_2887_, v_f_2888_, v_init_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_2896_, lean_object* v_00_u03b2_2897_, lean_object* v_map_2898_, lean_object* v_f_2899_, lean_object* v_init_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2899_, v_map_2898_, v_init_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_2907_, lean_object* v_00_u03b2_2908_, lean_object* v_map_2909_, lean_object* v_f_2910_, lean_object* v_init_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_2907_, v_00_u03b2_2908_, v_map_2909_, v_f_2910_, v_init_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_2918_, lean_object* v_00_u03b1_2919_, lean_object* v_00_u03b2_2920_, lean_object* v_f_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2921_, v_x_2922_, v_x_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2930_, lean_object* v_00_u03b1_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_f_2933_, lean_object* v_x_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_2930_, v_00_u03b1_2931_, v_00_u03b2_2932_, v_f_2933_, v_x_2934_, v_x_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2942_, lean_object* v_00_u03b2_2943_, lean_object* v_00_u03c3_2944_, lean_object* v_f_2945_, lean_object* v_as_2946_, size_t v_i_2947_, size_t v_stop_2948_, lean_object* v_b_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2945_, v_as_2946_, v_i_2947_, v_stop_2948_, v_b_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_00_u03b2_2957_, lean_object* v_00_u03c3_2958_, lean_object* v_f_2959_, lean_object* v_as_2960_, lean_object* v_i_2961_, lean_object* v_stop_2962_, lean_object* v_b_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
size_t v_i_boxed_2969_; size_t v_stop_boxed_2970_; lean_object* v_res_2971_; 
v_i_boxed_2969_ = lean_unbox_usize(v_i_2961_);
lean_dec(v_i_2961_);
v_stop_boxed_2970_ = lean_unbox_usize(v_stop_2962_);
lean_dec(v_stop_2962_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_2956_, v_00_u03b2_2957_, v_00_u03c3_2958_, v_f_2959_, v_as_2960_, v_i_boxed_2969_, v_stop_boxed_2970_, v_b_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v_as_2960_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2972_, lean_object* v_00_u03b1_2973_, lean_object* v_00_u03b2_2974_, lean_object* v_f_2975_, lean_object* v_keys_2976_, lean_object* v_vals_2977_, lean_object* v_heq_2978_, lean_object* v_i_2979_, lean_object* v_acc_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2975_, v_keys_2976_, v_vals_2977_, v_i_2979_, v_acc_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2987_, lean_object* v_00_u03b1_2988_, lean_object* v_00_u03b2_2989_, lean_object* v_f_2990_, lean_object* v_keys_2991_, lean_object* v_vals_2992_, lean_object* v_heq_2993_, lean_object* v_i_2994_, lean_object* v_acc_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_2987_, v_00_u03b1_2988_, v_00_u03b2_2989_, v_f_2990_, v_keys_2991_, v_vals_2992_, v_heq_2993_, v_i_2994_, v_acc_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v_vals_2992_);
lean_dec_ref(v_keys_2991_);
return v_res_3001_;
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
