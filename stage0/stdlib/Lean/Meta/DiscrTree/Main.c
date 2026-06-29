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
lean_dec_ref_known(v___x_381_, 1);
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
lean_dec_ref_known(v___x_389_, 1);
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
lean_dec_ref_known(v_a_385_, 1);
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
lean_dec_ref_known(v___x_429_, 1);
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
lean_dec_ref_known(v_a_433_, 1);
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
lean_dec_ref_known(v___x_469_, 1);
v_val_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref_known(v___x_471_, 1);
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
lean_dec_ref_known(v___x_535_, 1);
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
lean_dec_ref_known(v___x_535_, 2);
lean_dec(v_a_524_);
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v___x_577_, 1);
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
lean_dec_ref_known(v___x_535_, 2);
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
lean_dec_ref_known(v___x_535_, 2);
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
lean_dec_ref_known(v___x_535_, 1);
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
lean_dec_ref_known(v___x_535_, 3);
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
lean_dec_ref_known(v___x_544_, 1);
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
lean_dec_ref_known(v___x_549_, 1);
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
lean_dec_ref_known(v___x_544_, 1);
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
lean_dec_ref_known(v___x_694_, 1);
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
v___x_767_ = 3ULL;
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
lean_dec_ref_known(v___x_777_, 7);
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
lean_dec_ref_known(v___x_1004_, 1);
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
lean_dec_ref_known(v___x_1092_, 1);
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
lean_dec_ref_known(v___x_1092_, 2);
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
lean_dec_ref_known(v___x_1102_, 1);
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
lean_dec_ref_known(v___x_1107_, 1);
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
lean_dec_ref_known(v___x_1120_, 1);
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
lean_dec_ref_known(v___x_1132_, 1);
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
lean_dec_ref_known(v___x_1141_, 1);
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
lean_dec_ref_known(v___x_1092_, 1);
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
lean_dec_ref_known(v___x_1092_, 1);
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
lean_dec_ref_known(v___x_1092_, 1);
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
lean_dec_ref_known(v___x_1092_, 3);
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
lean_dec_ref_known(v___x_1092_, 3);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1340_, size_t v_x_1341_, lean_object* v_x_1342_){
_start:
{
if (lean_obj_tag(v_x_1340_) == 0)
{
lean_object* v_es_1343_; lean_object* v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; lean_object* v_j_1347_; lean_object* v___x_1348_; 
v_es_1343_ = lean_ctor_get(v_x_1340_, 0);
v___x_1344_ = lean_box(2);
v___x_1345_ = ((size_t)31ULL);
v___x_1346_ = lean_usize_land(v_x_1341_, v___x_1345_);
v_j_1347_ = lean_usize_to_nat(v___x_1346_);
v___x_1348_ = lean_array_get_borrowed(v___x_1344_, v_es_1343_, v_j_1347_);
lean_dec(v_j_1347_);
switch(lean_obj_tag(v___x_1348_))
{
case 0:
{
lean_object* v_key_1349_; lean_object* v_val_1350_; uint8_t v___x_1351_; 
v_key_1349_ = lean_ctor_get(v___x_1348_, 0);
v_val_1350_ = lean_ctor_get(v___x_1348_, 1);
v___x_1351_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1342_, v_key_1349_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; 
lean_inc(v_val_1350_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_val_1350_);
return v___x_1353_;
}
}
case 1:
{
lean_object* v_node_1354_; size_t v___x_1355_; size_t v___x_1356_; 
v_node_1354_ = lean_ctor_get(v___x_1348_, 0);
v___x_1355_ = ((size_t)5ULL);
v___x_1356_ = lean_usize_shift_right(v_x_1341_, v___x_1355_);
v_x_1340_ = v_node_1354_;
v_x_1341_ = v___x_1356_;
goto _start;
}
default: 
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_box(0);
return v___x_1358_;
}
}
}
else
{
lean_object* v_ks_1359_; lean_object* v_vs_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_ks_1359_ = lean_ctor_get(v_x_1340_, 0);
v_vs_1360_ = lean_ctor_get(v_x_1340_, 1);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1359_, v_vs_1360_, v___x_1361_, v_x_1342_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
size_t v_x_165__boxed_1366_; lean_object* v_res_1367_; 
v_x_165__boxed_1366_ = lean_unbox_usize(v_x_1364_);
lean_dec(v_x_1364_);
v_res_1367_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1363_, v_x_165__boxed_1366_, v_x_1365_);
lean_dec(v_x_1365_);
lean_dec_ref(v_x_1363_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
uint64_t v___x_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v___x_1370_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1369_);
v___x_1371_ = lean_uint64_to_usize(v___x_1370_);
v___x_1372_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1368_, v___x_1371_, v_x_1369_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1373_, v_x_1374_);
lean_dec(v_x_1374_);
lean_dec_ref(v_x_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1376_){
_start:
{
lean_object* v___x_1377_; lean_object* v_result_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1377_ = lean_unsigned_to_nat(8u);
v_result_1378_ = lean_mk_empty_array_with_capacity(v___x_1377_);
v___x_1379_ = lean_box(0);
v___x_1380_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1376_, v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
return v_result_1378_;
}
else
{
lean_object* v_val_1381_; lean_object* v_vs_1382_; lean_object* v___x_1383_; 
v_val_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_vs_1382_ = lean_ctor_get(v_val_1381_, 0);
lean_inc_ref(v_vs_1382_);
lean_dec(v_val_1381_);
v___x_1383_ = l_Array_append___redArg(v_result_1378_, v_vs_1382_);
lean_dec_ref(v_vs_1382_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___boxed(lean_object* v_d_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1384_);
lean_dec_ref(v_d_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1386_, lean_object* v_d_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_1389_, lean_object* v_d_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(v_00_u03b1_1389_, v_d_1390_);
lean_dec_ref(v_d_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1393_, v_x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1396_, v_x_1397_, v_x_1398_);
lean_dec(v_x_1398_);
lean_dec_ref(v_x_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1400_, lean_object* v_x_1401_, size_t v_x_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1401_, v_x_1402_, v_x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
size_t v_x_247__boxed_1409_; lean_object* v_res_1410_; 
v_x_247__boxed_1409_ = lean_unbox_usize(v_x_1407_);
lean_dec(v_x_1407_);
v_res_1410_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1405_, v_x_1406_, v_x_247__boxed_1409_, v_x_1408_);
lean_dec(v_x_1408_);
lean_dec_ref(v_x_1406_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1411_, lean_object* v_keys_1412_, lean_object* v_vals_1413_, lean_object* v_heq_1414_, lean_object* v_i_1415_, lean_object* v_k_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1412_, v_vals_1413_, v_i_1415_, v_k_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1418_, lean_object* v_keys_1419_, lean_object* v_vals_1420_, lean_object* v_heq_1421_, lean_object* v_i_1422_, lean_object* v_k_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1418_, v_keys_1419_, v_vals_1420_, v_heq_1421_, v_i_1422_, v_k_1423_);
lean_dec(v_k_1423_);
lean_dec_ref(v_vals_1420_);
lean_dec_ref(v_keys_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object* v_a_1425_, lean_object* v_b_1426_){
_start:
{
lean_object* v_fst_1427_; lean_object* v_fst_1428_; uint8_t v___x_1429_; 
v_fst_1427_ = lean_ctor_get(v_a_1425_, 0);
v_fst_1428_ = lean_ctor_get(v_b_1426_, 0);
v___x_1429_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1427_, v_fst_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object* v_a_1430_, lean_object* v_b_1431_){
_start:
{
uint8_t v_res_1432_; lean_object* v_r_1433_; 
v_res_1432_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1430_, v_b_1431_);
lean_dec_ref(v_b_1431_);
lean_dec_ref(v_a_1430_);
v_r_1433_ = lean_box(v_res_1432_);
return v_r_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1440_, lean_object* v_k_1441_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_array_get_size(v_cs_1440_);
v___x_1444_ = lean_nat_dec_lt(v___x_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_k_1441_);
v___x_1445_ = lean_box(0);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_sub(v___x_1443_, v___x_1446_);
v___x_1448_ = lean_nat_dec_le(v___x_1442_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v___x_1447_);
lean_dec(v_k_1441_);
v___x_1449_ = lean_box(0);
return v___x_1449_;
}
else
{
lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___f_1450_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1451_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_k_1441_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1454_ = l_Array_binSearchAux___redArg(v___f_1450_, v___x_1453_, v_cs_1440_, v___x_1452_, v___x_1442_, v___x_1447_);
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1455_, lean_object* v_k_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1455_, v_k_1456_);
lean_dec_ref(v_cs_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1458_, lean_object* v_cs_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_get_size(v_cs_1459_);
v___x_1463_ = lean_nat_dec_lt(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
lean_dec(v_k_1460_);
v___x_1464_ = lean_box(0);
return v___x_1464_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_sub(v___x_1462_, v___x_1465_);
v___x_1467_ = lean_nat_dec_le(v___x_1461_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec(v___x_1466_);
lean_dec(v_k_1460_);
v___x_1468_ = lean_box(0);
return v___x_1468_;
}
else
{
lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___f_1469_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1470_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_k_1460_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1473_ = l_Array_binSearchAux___redArg(v___f_1469_, v___x_1472_, v_cs_1459_, v___x_1471_, v___x_1461_, v___x_1466_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_cs_1475_, lean_object* v_k_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1474_, v_cs_1475_, v_k_1476_);
lean_dec_ref(v_cs_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1478_, lean_object* v_k_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_m_1484_; lean_object* v_a_1485_; uint8_t v___x_1486_; 
v___x_1482_ = lean_nat_add(v_x_1480_, v_x_1481_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v_m_1484_ = lean_nat_shiftr(v___x_1482_, v___x_1483_);
lean_dec(v___x_1482_);
v_a_1485_ = lean_array_fget_borrowed(v_as_1478_, v_m_1484_);
v___x_1486_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1485_, v_k_1479_);
if (v___x_1486_ == 0)
{
uint8_t v___x_1487_; 
lean_dec(v_x_1481_);
v___x_1487_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1479_, v_a_1485_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
lean_dec(v_m_1484_);
lean_dec(v_x_1480_);
lean_inc(v_a_1485_);
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_a_1485_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_nat_dec_eq(v_m_1484_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_nat_sub(v_m_1484_, v___x_1483_);
lean_dec(v_m_1484_);
v___x_1492_ = lean_nat_dec_lt(v___x_1491_, v_x_1480_);
if (v___x_1492_ == 0)
{
v_x_1481_ = v___x_1491_;
goto _start;
}
else
{
lean_object* v___x_1494_; 
lean_dec(v___x_1491_);
lean_dec(v_x_1480_);
v___x_1494_ = lean_box(0);
return v___x_1494_;
}
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_m_1484_);
lean_dec(v_x_1480_);
v___x_1495_ = lean_box(0);
return v___x_1495_;
}
}
}
else
{
lean_object* v___x_1496_; uint8_t v___x_1497_; 
lean_dec(v_x_1480_);
v___x_1496_ = lean_nat_add(v_m_1484_, v___x_1483_);
lean_dec(v_m_1484_);
v___x_1497_ = lean_nat_dec_le(v___x_1496_, v_x_1481_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
lean_dec(v___x_1496_);
lean_dec(v_x_1481_);
v___x_1498_ = lean_box(0);
return v___x_1498_;
}
else
{
v_x_1480_ = v___x_1496_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1500_, lean_object* v_k_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1500_, v_k_1501_, v_x_1502_, v_x_1503_);
lean_dec_ref(v_k_1501_);
lean_dec_ref(v_as_1500_);
return v_res_1504_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1507_ = lean_box(0);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v___x_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1509_, lean_object* v_c_1510_, lean_object* v_result_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_vs_1517_; lean_object* v_children_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_vs_1517_ = lean_ctor_get(v_c_1510_, 0);
lean_inc_ref(v_vs_1517_);
v_children_1518_ = lean_ctor_get(v_c_1510_, 1);
lean_inc_ref(v_children_1518_);
lean_dec_ref(v_c_1510_);
v___x_1519_ = lean_array_get_size(v_todo_1509_);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = lean_nat_dec_eq(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
lean_dec_ref(v_vs_1517_);
v___x_1522_ = lean_array_get_size(v_children_1518_);
v___x_1523_ = lean_nat_dec_eq(v___x_1522_, v___x_1520_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_e_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1524_ = l_Lean_instInhabitedExpr;
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_sub(v___x_1519_, v___x_1525_);
v_e_1527_ = lean_array_get_borrowed(v___x_1524_, v_todo_1509_, v___x_1526_);
lean_dec(v___x_1526_);
v___x_1528_ = 1;
lean_inc(v_e_1527_);
v___x_1529_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1527_, v___x_1528_, v___x_1523_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1567_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1567_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1567_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_fst_1534_; lean_object* v_snd_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_first_1538_; lean_object* v_fst_1539_; lean_object* v_snd_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1566_; 
v_fst_1534_ = lean_ctor_get(v_a_1530_, 0);
lean_inc(v_fst_1534_);
v_snd_1535_ = lean_ctor_get(v_a_1530_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_a_1530_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v_first_1538_ = lean_array_get(v___x_1537_, v_children_1518_, v___x_1520_);
v_fst_1539_ = lean_ctor_get(v_first_1538_, 0);
v_snd_1540_ = lean_ctor_get(v_first_1538_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_first_1538_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1542_ = v_first_1538_;
v_isShared_1543_ = v_isSharedCheck_1566_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_snd_1540_);
lean_inc(v_fst_1539_);
lean_dec(v_first_1538_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1566_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_todo_1544_; lean_object* v___y_1546_; lean_object* v_a_1547_; uint8_t v___x_1560_; 
v_todo_1544_ = lean_array_pop(v_todo_1509_);
v___x_1560_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1539_, v___x_1536_);
lean_dec(v_fst_1539_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1562_; 
lean_dec(v_snd_1540_);
lean_inc_ref(v_result_1511_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_result_1511_);
v___x_1562_ = v___x_1532_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_result_1511_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
v___y_1546_ = v___x_1562_;
v_a_1547_ = v_result_1511_;
goto v___jp_1545_;
}
}
else
{
lean_object* v___x_1564_; 
lean_del_object(v___x_1532_);
lean_inc_ref(v_todo_1544_);
v___x_1564_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1544_, v_snd_1540_, v_result_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
v___y_1546_ = v___x_1564_;
v_a_1547_ = v_a_1565_;
goto v___jp_1545_;
}
else
{
lean_dec_ref(v_todo_1544_);
lean_del_object(v___x_1542_);
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
lean_dec_ref(v_children_1518_);
return v___x_1564_;
}
}
v___jp_1545_:
{
if (lean_obj_tag(v_fst_1534_) == 0)
{
lean_dec_ref(v_a_1547_);
lean_dec_ref(v_todo_1544_);
lean_del_object(v___x_1542_);
lean_dec(v_snd_1535_);
lean_dec_ref(v_children_1518_);
return v___y_1546_;
}
else
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_nat_dec_lt(v___x_1520_, v___x_1522_);
if (v___x_1548_ == 0)
{
lean_dec_ref(v_a_1547_);
lean_dec_ref(v_todo_1544_);
lean_del_object(v___x_1542_);
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
lean_dec_ref(v_children_1518_);
return v___y_1546_;
}
else
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_nat_sub(v___x_1522_, v___x_1525_);
v___x_1550_ = lean_nat_dec_le(v___x_1520_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec(v___x_1549_);
lean_dec_ref(v_a_1547_);
lean_dec_ref(v_todo_1544_);
lean_del_object(v___x_1542_);
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
lean_dec_ref(v_children_1518_);
return v___y_1546_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v___x_1551_);
lean_ctor_set(v___x_1542_, 0, v_fst_1534_);
v___x_1553_ = v___x_1542_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_fst_1534_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1518_, v___x_1553_, v___x_1520_, v___x_1549_);
lean_dec_ref(v___x_1553_);
lean_dec_ref(v_children_1518_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref(v_a_1547_);
lean_dec_ref(v_todo_1544_);
lean_dec(v_snd_1535_);
return v___y_1546_;
}
else
{
lean_object* v_val_1555_; lean_object* v_snd_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v___y_1546_);
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v_snd_1556_ = lean_ctor_get(v_val_1555_, 1);
lean_inc(v_snd_1556_);
lean_dec(v_val_1555_);
v___x_1557_ = l_Array_append___redArg(v_todo_1544_, v_snd_1535_);
lean_dec(v_snd_1535_);
v_todo_1509_ = v___x_1557_;
v_c_1510_ = v_snd_1556_;
v_result_1511_ = v_a_1547_;
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
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_children_1518_);
lean_dec_ref(v_result_1511_);
lean_dec_ref(v_todo_1509_);
v_a_1568_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1529_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1529_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_object* v___x_1576_; 
lean_dec_ref(v_children_1518_);
lean_dec_ref(v_todo_1509_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_result_1511_);
return v___x_1576_;
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref(v_children_1518_);
lean_dec_ref(v_todo_1509_);
v___x_1577_ = l_Array_append___redArg(v_result_1511_, v_vs_1517_);
lean_dec_ref(v_vs_1517_);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1579_, lean_object* v_c_1580_, lean_object* v_result_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1579_, v_c_1580_, v_result_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1588_, lean_object* v_todo_1589_, lean_object* v_c_1590_, lean_object* v_result_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1589_, v_c_1590_, v_result_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_todo_1599_, lean_object* v_c_1600_, lean_object* v_result_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1598_, v_todo_1599_, v_c_1600_, v_result_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1608_, lean_object* v_as_1609_, lean_object* v_k_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1609_, v_k_1610_, v_x_1611_, v_x_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1615_, lean_object* v_as_1616_, lean_object* v_k_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1615_, v_as_1616_, v_k_1617_, v_x_1618_, v_x_1619_, v_x_1620_);
lean_dec_ref(v_k_1617_);
lean_dec_ref(v_as_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1622_, lean_object* v_k_1623_, lean_object* v_args_1624_, lean_object* v_result_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1622_, v_k_1623_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v_args_1624_);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_result_1625_);
return v___x_1632_;
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1634_; 
v_val_1633_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1634_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1624_, v_val_1633_, v_result_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1635_, lean_object* v_k_1636_, lean_object* v_args_1637_, lean_object* v_result_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1635_, v_k_1636_, v_args_1637_, v_result_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_k_1636_);
lean_dec_ref(v_d_1635_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1645_, lean_object* v_d_1646_, lean_object* v_k_1647_, lean_object* v_args_1648_, lean_object* v_result_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1646_, v_k_1647_, v_args_1648_, v_result_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1656_, lean_object* v_d_1657_, lean_object* v_k_1658_, lean_object* v_args_1659_, lean_object* v_result_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1656_, v_d_1657_, v_k_1658_, v_args_1659_, v_result_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_k_1658_);
lean_dec_ref(v_d_1657_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1667_, lean_object* v_e_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v___x_1674_; uint8_t v_foApprox_1675_; uint8_t v_ctxApprox_1676_; uint8_t v_quasiPatternApprox_1677_; uint8_t v_constApprox_1678_; uint8_t v_isDefEqStuckEx_1679_; uint8_t v_unificationHints_1680_; uint8_t v_proofIrrelevance_1681_; uint8_t v_assignSyntheticOpaque_1682_; uint8_t v_offsetCnstrs_1683_; uint8_t v_etaStruct_1684_; uint8_t v_univApprox_1685_; uint8_t v_iota_1686_; uint8_t v_beta_1687_; uint8_t v_proj_1688_; uint8_t v_zeta_1689_; uint8_t v_zetaDelta_1690_; uint8_t v_zetaUnused_1691_; uint8_t v_zetaHave_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1766_; 
v___x_1674_ = l_Lean_Meta_Context_config(v_a_1669_);
v_foApprox_1675_ = lean_ctor_get_uint8(v___x_1674_, 0);
v_ctxApprox_1676_ = lean_ctor_get_uint8(v___x_1674_, 1);
v_quasiPatternApprox_1677_ = lean_ctor_get_uint8(v___x_1674_, 2);
v_constApprox_1678_ = lean_ctor_get_uint8(v___x_1674_, 3);
v_isDefEqStuckEx_1679_ = lean_ctor_get_uint8(v___x_1674_, 4);
v_unificationHints_1680_ = lean_ctor_get_uint8(v___x_1674_, 5);
v_proofIrrelevance_1681_ = lean_ctor_get_uint8(v___x_1674_, 6);
v_assignSyntheticOpaque_1682_ = lean_ctor_get_uint8(v___x_1674_, 7);
v_offsetCnstrs_1683_ = lean_ctor_get_uint8(v___x_1674_, 8);
v_etaStruct_1684_ = lean_ctor_get_uint8(v___x_1674_, 10);
v_univApprox_1685_ = lean_ctor_get_uint8(v___x_1674_, 11);
v_iota_1686_ = lean_ctor_get_uint8(v___x_1674_, 12);
v_beta_1687_ = lean_ctor_get_uint8(v___x_1674_, 13);
v_proj_1688_ = lean_ctor_get_uint8(v___x_1674_, 14);
v_zeta_1689_ = lean_ctor_get_uint8(v___x_1674_, 15);
v_zetaDelta_1690_ = lean_ctor_get_uint8(v___x_1674_, 16);
v_zetaUnused_1691_ = lean_ctor_get_uint8(v___x_1674_, 17);
v_zetaHave_1692_ = lean_ctor_get_uint8(v___x_1674_, 18);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1694_ = v___x_1674_;
v_isShared_1695_ = v_isSharedCheck_1766_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v___x_1674_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1766_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint8_t v_trackZetaDelta_1696_; lean_object* v_zetaDeltaSet_1697_; lean_object* v_lctx_1698_; lean_object* v_localInstances_1699_; lean_object* v_defEqCtx_x3f_1700_; lean_object* v_synthPendingDepth_1701_; lean_object* v_canUnfold_x3f_1702_; uint8_t v_univApprox_1703_; uint8_t v_inTypeClassResolution_1704_; uint8_t v_cacheInferType_1705_; uint8_t v___x_1706_; lean_object* v_config_1708_; 
v_trackZetaDelta_1696_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7);
v_zetaDeltaSet_1697_ = lean_ctor_get(v_a_1669_, 1);
v_lctx_1698_ = lean_ctor_get(v_a_1669_, 2);
v_localInstances_1699_ = lean_ctor_get(v_a_1669_, 3);
v_defEqCtx_x3f_1700_ = lean_ctor_get(v_a_1669_, 4);
v_synthPendingDepth_1701_ = lean_ctor_get(v_a_1669_, 5);
v_canUnfold_x3f_1702_ = lean_ctor_get(v_a_1669_, 6);
v_univApprox_1703_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1704_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7 + 2);
v_cacheInferType_1705_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*7 + 3);
v___x_1706_ = 2;
if (v_isShared_1695_ == 0)
{
v_config_1708_ = v___x_1694_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 0, v_foApprox_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 1, v_ctxApprox_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 2, v_quasiPatternApprox_1677_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 3, v_constApprox_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 4, v_isDefEqStuckEx_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 5, v_unificationHints_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 6, v_proofIrrelevance_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 7, v_assignSyntheticOpaque_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 8, v_offsetCnstrs_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 10, v_etaStruct_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 11, v_univApprox_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 12, v_iota_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 13, v_beta_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 14, v_proj_1688_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 15, v_zeta_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 16, v_zetaDelta_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 17, v_zetaUnused_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, 18, v_zetaHave_1692_);
v_config_1708_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
uint64_t v___x_1709_; uint64_t v___x_1710_; uint64_t v___x_1711_; uint8_t v___x_1712_; uint64_t v___x_1713_; uint64_t v___x_1714_; uint64_t v_key_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_ctor_set_uint8(v_config_1708_, 9, v___x_1706_);
v___x_1709_ = l_Lean_Meta_Context_configKey(v_a_1669_);
v___x_1710_ = 3ULL;
v___x_1711_ = lean_uint64_shift_right(v___x_1709_, v___x_1710_);
v___x_1712_ = 1;
v___x_1713_ = lean_uint64_shift_left(v___x_1711_, v___x_1710_);
v___x_1714_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_1715_ = lean_uint64_lor(v___x_1713_, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1716_, 0, v_config_1708_);
lean_ctor_set_uint64(v___x_1716_, sizeof(void*)*1, v_key_1715_);
lean_inc(v_canUnfold_x3f_1702_);
lean_inc(v_synthPendingDepth_1701_);
lean_inc(v_defEqCtx_x3f_1700_);
lean_inc_ref(v_localInstances_1699_);
lean_inc_ref(v_lctx_1698_);
lean_inc(v_zetaDeltaSet_1697_);
v___x_1717_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v_zetaDeltaSet_1697_);
lean_ctor_set(v___x_1717_, 2, v_lctx_1698_);
lean_ctor_set(v___x_1717_, 3, v_localInstances_1699_);
lean_ctor_set(v___x_1717_, 4, v_defEqCtx_x3f_1700_);
lean_ctor_set(v___x_1717_, 5, v_synthPendingDepth_1701_);
lean_ctor_set(v___x_1717_, 6, v_canUnfold_x3f_1702_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*7, v_trackZetaDelta_1696_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*7 + 1, v_univApprox_1703_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1704_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*7 + 3, v_cacheInferType_1705_);
v___x_1718_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1668_, v___x_1712_, v___x_1712_, v___x_1717_, v_a_1670_, v_a_1671_, v_a_1672_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1756_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1756_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1756_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1755_; 
v_fst_1723_ = lean_ctor_get(v_a_1719_, 0);
v_snd_1724_ = lean_ctor_get(v_a_1719_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_a_1719_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1726_ = v_a_1719_;
v_isShared_1727_ = v_isSharedCheck_1755_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
lean_dec(v_a_1719_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1755_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_result_1728_; 
v_result_1728_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1667_);
if (lean_obj_tag(v_fst_1723_) == 0)
{
lean_object* v___x_1730_; 
lean_dec(v_snd_1724_);
lean_dec_ref_known(v___x_1717_, 7);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_result_1728_);
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_result_1728_);
v___x_1730_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1730_);
v___x_1732_ = v___x_1721_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v___x_1735_; 
lean_del_object(v___x_1721_);
v___x_1735_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1667_, v_fst_1723_, v_snd_1724_, v_result_1728_, v___x_1717_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec_ref_known(v___x_1717_, 7);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1746_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v_a_1736_);
v___x_1741_ = v___x_1726_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_del_object(v___x_1726_);
lean_dec(v_fst_1723_);
v_a_1747_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1735_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1735_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref_known(v___x_1717_, 7);
v_a_1757_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1718_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1718_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1767_, lean_object* v_e_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1767_, v_e_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_d_1767_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1775_, lean_object* v_d_1776_, lean_object* v_e_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1776_, v_e_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1784_, lean_object* v_d_1785_, lean_object* v_e_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1784_, v_d_1785_, v_e_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec_ref(v_d_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1793_, lean_object* v_e_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1793_, v_e_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1809_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_snd_1805_; lean_object* v___x_1807_; 
v_snd_1805_ = lean_ctor_get(v_a_1801_, 1);
lean_inc(v_snd_1805_);
lean_dec(v_a_1801_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_snd_1805_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_snd_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1800_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1800_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1818_, lean_object* v_e_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1818_, v_e_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec_ref(v_d_1818_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1826_, lean_object* v_d_1827_, lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1827_, v_e_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_d_1836_, lean_object* v_e_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1835_, v_d_1836_, v_e_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec_ref(v_d_1836_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1844_, lean_object* v_k_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_k_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; 
switch(lean_obj_tag(v_k_1845_))
{
case 4:
{
lean_object* v_a_1873_; lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1885_; 
v_a_1873_ = lean_ctor_get(v_k_1845_, 0);
v_a_1874_ = lean_ctor_get(v_k_1845_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_k_1845_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1876_ = v_k_1845_;
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_inc(v_a_1873_);
lean_dec(v_k_1845_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_zero_1878_; uint8_t v_isZero_1879_; 
v_zero_1878_ = lean_unsigned_to_nat(0u);
v_isZero_1879_ = lean_nat_dec_eq(v_a_1874_, v_zero_1878_);
if (v_isZero_1879_ == 0)
{
lean_object* v_one_1880_; lean_object* v_n_1881_; lean_object* v___x_1883_; 
v_one_1880_ = lean_unsigned_to_nat(1u);
v_n_1881_ = lean_nat_sub(v_a_1874_, v_one_1880_);
lean_dec(v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v_n_1881_);
v___x_1883_ = v___x_1876_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1873_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_n_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
v_k_1856_ = v___x_1883_;
v___y_1857_ = v_a_1846_;
v___y_1858_ = v_a_1847_;
v___y_1859_ = v_a_1848_;
v___y_1860_ = v_a_1849_;
goto v___jp_1855_;
}
}
else
{
lean_del_object(v___x_1876_);
lean_dec(v_a_1874_);
lean_dec(v_a_1873_);
goto v___jp_1851_;
}
}
}
case 3:
{
lean_object* v_a_1886_; lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1898_; 
v_a_1886_ = lean_ctor_get(v_k_1845_, 0);
v_a_1887_ = lean_ctor_get(v_k_1845_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_k_1845_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1889_ = v_k_1845_;
v_isShared_1890_ = v_isSharedCheck_1898_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_inc(v_a_1886_);
lean_dec(v_k_1845_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1898_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_zero_1891_; uint8_t v_isZero_1892_; 
v_zero_1891_ = lean_unsigned_to_nat(0u);
v_isZero_1892_ = lean_nat_dec_eq(v_a_1887_, v_zero_1891_);
if (v_isZero_1892_ == 0)
{
lean_object* v_one_1893_; lean_object* v_n_1894_; lean_object* v___x_1896_; 
v_one_1893_ = lean_unsigned_to_nat(1u);
v_n_1894_ = lean_nat_sub(v_a_1887_, v_one_1893_);
lean_dec(v_a_1887_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v_n_1894_);
v___x_1896_ = v___x_1889_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1886_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_n_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
v_k_1856_ = v___x_1896_;
v___y_1857_ = v_a_1846_;
v___y_1858_ = v_a_1847_;
v___y_1859_ = v_a_1848_;
v___y_1860_ = v_a_1849_;
goto v___jp_1855_;
}
}
else
{
lean_del_object(v___x_1889_);
lean_dec(v_a_1887_);
lean_dec(v_a_1886_);
goto v___jp_1851_;
}
}
}
case 6:
{
lean_object* v_a_1899_; lean_object* v_a_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1912_; 
v_a_1899_ = lean_ctor_get(v_k_1845_, 0);
v_a_1900_ = lean_ctor_get(v_k_1845_, 1);
v_a_1901_ = lean_ctor_get(v_k_1845_, 2);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_k_1845_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1903_ = v_k_1845_;
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_inc(v_a_1900_);
lean_inc(v_a_1899_);
lean_dec(v_k_1845_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_zero_1905_; uint8_t v_isZero_1906_; 
v_zero_1905_ = lean_unsigned_to_nat(0u);
v_isZero_1906_ = lean_nat_dec_eq(v_a_1901_, v_zero_1905_);
if (v_isZero_1906_ == 0)
{
lean_object* v_one_1907_; lean_object* v_n_1908_; lean_object* v___x_1910_; 
v_one_1907_ = lean_unsigned_to_nat(1u);
v_n_1908_ = lean_nat_sub(v_a_1901_, v_one_1907_);
lean_dec(v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 2, v_n_1908_);
v___x_1910_ = v___x_1903_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1899_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_a_1900_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_n_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
v_k_1856_ = v___x_1910_;
v___y_1857_ = v_a_1846_;
v___y_1858_ = v_a_1847_;
v___y_1859_ = v_a_1848_;
v___y_1860_ = v_a_1849_;
goto v___jp_1855_;
}
}
else
{
lean_del_object(v___x_1903_);
lean_dec(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec(v_a_1899_);
goto v___jp_1851_;
}
}
}
default: 
{
lean_dec(v_k_1845_);
goto v___jp_1851_;
}
}
v___jp_1851_:
{
uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = 0;
v___x_1853_ = lean_box(v___x_1852_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
v___jp_1855_:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1844_, v_k_1856_);
if (lean_obj_tag(v___x_1861_) == 0)
{
v_k_1845_ = v_k_1856_;
v_a_1846_ = v___y_1857_;
v_a_1847_ = v___y_1858_;
v_a_1848_ = v___y_1859_;
v_a_1849_ = v___y_1860_;
goto _start;
}
else
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_k_1856_);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v___x_1861_, 0);
lean_dec(v_unused_1872_);
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1871_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1871_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1866_ = 1;
v___x_1867_ = lean_box(v___x_1866_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1867_);
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_1913_, lean_object* v_k_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1913_, v_k_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec_ref(v_d_1913_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_1921_, lean_object* v_d_1922_, lean_object* v_k_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1922_, v_k_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_1930_, lean_object* v_d_1931_, lean_object* v_k_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_1930_, v_d_1931_, v_k_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec_ref(v_d_1931_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_1939_, size_t v_sz_1940_, size_t v_i_1941_, lean_object* v_bs_1942_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_lt(v_i_1941_, v_sz_1940_);
if (v___x_1943_ == 0)
{
lean_dec(v_numExtra_1939_);
return v_bs_1942_;
}
else
{
lean_object* v_v_1944_; lean_object* v___x_1945_; lean_object* v_bs_x27_1946_; lean_object* v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
v_v_1944_ = lean_array_uget(v_bs_1942_, v_i_1941_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v_bs_x27_1946_ = lean_array_uset(v_bs_1942_, v_i_1941_, v___x_1945_);
lean_inc(v_numExtra_1939_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v_v_1944_);
lean_ctor_set(v___x_1947_, 1, v_numExtra_1939_);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_add(v_i_1941_, v___x_1948_);
v___x_1950_ = lean_array_uset(v_bs_x27_1946_, v_i_1941_, v___x_1947_);
v_i_1941_ = v___x_1949_;
v_bs_1942_ = v___x_1950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_1952_, lean_object* v_sz_1953_, lean_object* v_i_1954_, lean_object* v_bs_1955_){
_start:
{
size_t v_sz_boxed_1956_; size_t v_i_boxed_1957_; lean_object* v_res_1958_; 
v_sz_boxed_1956_ = lean_unbox_usize(v_sz_1953_);
lean_dec(v_sz_1953_);
v_i_boxed_1957_ = lean_unbox_usize(v_i_1954_);
lean_dec(v_i_1954_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1952_, v_sz_boxed_1956_, v_i_boxed_1957_, v_bs_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_1959_, lean_object* v_e_1960_, lean_object* v_numExtra_1961_, lean_object* v_result_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v___x_1968_; 
lean_inc_ref(v_e_1960_);
v___x_1968_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1959_, v_e_1960_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1986_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1986_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1986_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_snd_1973_; size_t v_sz_1974_; size_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_snd_1973_ = lean_ctor_get(v_a_1969_, 1);
lean_inc(v_snd_1973_);
lean_dec(v_a_1969_);
v_sz_1974_ = lean_array_size(v_snd_1973_);
v___x_1975_ = ((size_t)0ULL);
lean_inc(v_numExtra_1961_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1961_, v_sz_1974_, v___x_1975_, v_snd_1973_);
v___x_1977_ = l_Array_append___redArg(v_result_1962_, v___x_1976_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = l_Lean_Expr_isApp(v_e_1960_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1980_; 
lean_dec(v_numExtra_1961_);
lean_dec_ref(v_e_1960_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1977_);
v___x_1980_ = v___x_1971_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1977_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_del_object(v___x_1971_);
v___x_1982_ = l_Lean_Expr_appFn_x21(v_e_1960_);
lean_dec_ref(v_e_1960_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_add(v_numExtra_1961_, v___x_1983_);
lean_dec(v_numExtra_1961_);
v_e_1960_ = v___x_1982_;
v_numExtra_1961_ = v___x_1984_;
v_result_1962_ = v___x_1977_;
goto _start;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_result_1962_);
lean_dec(v_numExtra_1961_);
lean_dec_ref(v_e_1960_);
v_a_1987_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1968_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1968_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_1995_, lean_object* v_e_1996_, lean_object* v_numExtra_1997_, lean_object* v_result_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_1995_, v_e_1996_, v_numExtra_1997_, v_result_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec_ref(v_d_1995_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2005_, lean_object* v_d_2006_, lean_object* v_e_2007_, lean_object* v_numExtra_2008_, lean_object* v_result_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2006_, v_e_2007_, v_numExtra_2008_, v_result_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2016_, lean_object* v_d_2017_, lean_object* v_e_2018_, lean_object* v_numExtra_2019_, lean_object* v_result_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2016_, v_d_2017_, v_e_2018_, v_numExtra_2019_, v_result_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec_ref(v_d_2017_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2027_, lean_object* v_numExtra_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_bs_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2028_, v_sz_2029_, v_i_2030_, v_bs_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2033_, lean_object* v_numExtra_2034_, lean_object* v_sz_2035_, lean_object* v_i_2036_, lean_object* v_bs_2037_){
_start:
{
size_t v_sz_boxed_2038_; size_t v_i_boxed_2039_; lean_object* v_res_2040_; 
v_sz_boxed_2038_ = lean_unbox_usize(v_sz_2035_);
lean_dec(v_sz_2035_);
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_res_2040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2033_, v_numExtra_2034_, v_sz_boxed_2038_, v_i_boxed_2039_, v_bs_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2041_, size_t v_i_2042_, lean_object* v_bs_2043_){
_start:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_usize_dec_lt(v_i_2042_, v_sz_2041_);
if (v___x_2044_ == 0)
{
return v_bs_2043_;
}
else
{
lean_object* v_v_2045_; lean_object* v___x_2046_; lean_object* v_bs_x27_2047_; lean_object* v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
v_v_2045_ = lean_array_uget(v_bs_2043_, v_i_2042_);
v___x_2046_ = lean_unsigned_to_nat(0u);
v_bs_x27_2047_ = lean_array_uset(v_bs_2043_, v_i_2042_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_v_2045_);
lean_ctor_set(v___x_2048_, 1, v___x_2046_);
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2042_, v___x_2049_);
v___x_2051_ = lean_array_uset(v_bs_x27_2047_, v_i_2042_, v___x_2048_);
v_i_2042_ = v___x_2050_;
v_bs_2043_ = v___x_2051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2053_, lean_object* v_i_2054_, lean_object* v_bs_2055_){
_start:
{
size_t v_sz_boxed_2056_; size_t v_i_boxed_2057_; lean_object* v_res_2058_; 
v_sz_boxed_2056_ = lean_unbox_usize(v_sz_2053_);
lean_dec(v_sz_2053_);
v_i_boxed_2057_ = lean_unbox_usize(v_i_2054_);
lean_dec(v_i_2054_);
v_res_2058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2056_, v_i_boxed_2057_, v_bs_2055_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2059_, lean_object* v_e_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; 
lean_inc_ref(v_e_2060_);
v___x_2066_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2059_, v_e_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2101_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2101_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2101_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_fst_2071_; lean_object* v_snd_2072_; size_t v_sz_2073_; size_t v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_fst_2071_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_fst_2071_);
v_snd_2072_ = lean_ctor_get(v_a_2067_, 1);
lean_inc(v_snd_2072_);
lean_dec(v_a_2067_);
v_sz_2073_ = lean_array_size(v_snd_2072_);
v___x_2074_ = ((size_t)0ULL);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2073_, v___x_2074_, v_snd_2072_);
v___x_2076_ = l_Lean_Expr_isApp(v_e_2060_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v_fst_2071_);
lean_dec_ref(v_e_2060_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2075_);
v___x_2078_ = v___x_2069_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2075_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
else
{
lean_object* v___x_2080_; 
lean_del_object(v___x_2069_);
v___x_2080_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2059_, v_fst_2071_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2092_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2092_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_unbox(v_a_2081_);
lean_dec(v_a_2081_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2087_; 
lean_dec_ref(v_e_2060_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2075_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2075_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_del_object(v___x_2083_);
v___x_2089_ = l_Lean_Expr_appFn_x21(v_e_2060_);
lean_dec_ref(v_e_2060_);
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2059_, v___x_2089_, v___x_2090_, v___x_2075_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
return v___x_2091_;
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_e_2060_);
v_a_2093_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2080_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2080_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
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
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v_e_2060_);
v_a_2102_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2066_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2066_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2110_, lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2110_, v_e_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec_ref(v_d_2110_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2118_, lean_object* v_d_2119_, lean_object* v_e_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2119_, v_e_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_d_2128_, lean_object* v_e_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2127_, v_d_2128_, v_e_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec_ref(v_d_2128_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2136_, size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_bs_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2137_, v_i_2138_, v_bs_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_sz_2142_, lean_object* v_i_2143_, lean_object* v_bs_2144_){
_start:
{
size_t v_sz_boxed_2145_; size_t v_i_boxed_2146_; lean_object* v_res_2147_; 
v_sz_boxed_2145_ = lean_unbox_usize(v_sz_2142_);
lean_dec(v_sz_2142_);
v_i_boxed_2146_ = lean_unbox_usize(v_i_2143_);
lean_dec(v_i_2143_);
v_res_2147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2141_, v_sz_boxed_2145_, v_i_boxed_2146_, v_bs_2144_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
uint8_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = 1;
v___x_2155_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2148_, v___x_2154_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2180_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2180_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2180_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___y_2162_; lean_object* v___x_2167_; 
v___x_2160_ = l_Lean_Expr_getAppNumArgs(v_a_2156_);
v___x_2167_ = l_Lean_Expr_getAppFn(v_a_2156_);
lean_dec(v_a_2156_);
switch(lean_obj_tag(v___x_2167_))
{
case 9:
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_ref(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_a_2168_);
v___y_2162_ = v___x_2169_;
goto v___jp_2161_;
}
case 1:
{
lean_object* v_fvarId_2170_; lean_object* v___x_2171_; 
v_fvarId_2170_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_fvarId_2170_);
lean_dec_ref_known(v___x_2167_, 1);
lean_inc(v___x_2160_);
v___x_2171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_fvarId_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2160_);
v___y_2162_ = v___x_2171_;
goto v___jp_2161_;
}
case 2:
{
lean_object* v___x_2172_; 
lean_dec_ref_known(v___x_2167_, 1);
v___x_2172_ = lean_box(1);
v___y_2162_ = v___x_2172_;
goto v___jp_2161_;
}
case 11:
{
lean_object* v_typeName_2173_; lean_object* v_idx_2174_; lean_object* v___x_2175_; 
v_typeName_2173_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_typeName_2173_);
v_idx_2174_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_idx_2174_);
lean_dec_ref_known(v___x_2167_, 3);
lean_inc(v___x_2160_);
v___x_2175_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2175_, 0, v_typeName_2173_);
lean_ctor_set(v___x_2175_, 1, v_idx_2174_);
lean_ctor_set(v___x_2175_, 2, v___x_2160_);
v___y_2162_ = v___x_2175_;
goto v___jp_2161_;
}
case 7:
{
lean_object* v___x_2176_; 
lean_dec_ref_known(v___x_2167_, 3);
v___x_2176_ = lean_box(5);
v___y_2162_ = v___x_2176_;
goto v___jp_2161_;
}
case 4:
{
lean_object* v_declName_2177_; lean_object* v___x_2178_; 
v_declName_2177_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_declName_2177_);
lean_dec_ref_known(v___x_2167_, 2);
lean_inc(v___x_2160_);
v___x_2178_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_declName_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2160_);
v___y_2162_ = v___x_2178_;
goto v___jp_2161_;
}
default: 
{
lean_object* v___x_2179_; 
lean_dec_ref(v___x_2167_);
v___x_2179_ = lean_box(1);
v___y_2162_ = v___x_2179_;
goto v___jp_2161_;
}
}
v___jp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___y_2162_);
lean_ctor_set(v___x_2163_, 1, v___x_2160_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2163_);
v___x_2165_ = v___x_2158_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_a_2181_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2155_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2155_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2196_, size_t v_sz_2197_, size_t v_i_2198_, lean_object* v_b_2199_){
_start:
{
uint8_t v___x_2200_; 
v___x_2200_ = lean_usize_dec_lt(v_i_2198_, v_sz_2197_);
if (v___x_2200_ == 0)
{
return v_b_2199_;
}
else
{
lean_object* v_a_2201_; lean_object* v_snd_2202_; lean_object* v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; 
v_a_2201_ = lean_array_uget_borrowed(v_as_2196_, v_i_2198_);
v_snd_2202_ = lean_ctor_get(v_a_2201_, 1);
v___x_2203_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2202_, v_b_2199_);
v___x_2204_ = ((size_t)1ULL);
v___x_2205_ = lean_usize_add(v_i_2198_, v___x_2204_);
v_i_2198_ = v___x_2205_;
v_b_2199_ = v___x_2203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2207_, lean_object* v_result_2208_){
_start:
{
lean_object* v_vs_2209_; lean_object* v_children_2210_; lean_object* v_result_2211_; size_t v_sz_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v_vs_2209_ = lean_ctor_get(v_trie_2207_, 0);
v_children_2210_ = lean_ctor_get(v_trie_2207_, 1);
v_result_2211_ = l_Array_append___redArg(v_result_2208_, v_vs_2209_);
v_sz_2212_ = lean_array_size(v_children_2210_);
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2210_, v_sz_2212_, v___x_2213_, v_result_2211_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2215_, lean_object* v_result_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2215_, v_result_2216_);
lean_dec_ref(v_trie_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2218_, lean_object* v_sz_2219_, lean_object* v_i_2220_, lean_object* v_b_2221_){
_start:
{
size_t v_sz_boxed_2222_; size_t v_i_boxed_2223_; lean_object* v_res_2224_; 
v_sz_boxed_2222_ = lean_unbox_usize(v_sz_2219_);
lean_dec(v_sz_2219_);
v_i_boxed_2223_ = lean_unbox_usize(v_i_2220_);
lean_dec(v_i_2220_);
v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2218_, v_sz_boxed_2222_, v_i_boxed_2223_, v_b_2221_);
lean_dec_ref(v_as_2218_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2225_, lean_object* v_trie_2226_, lean_object* v_result_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2226_, v_result_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2229_, lean_object* v_trie_2230_, lean_object* v_result_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2229_, v_trie_2230_, v_result_2231_);
lean_dec_ref(v_trie_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2233_, lean_object* v_as_2234_, size_t v_sz_2235_, size_t v_i_2236_, lean_object* v_b_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2234_, v_sz_2235_, v_i_2236_, v_b_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_as_2240_, lean_object* v_sz_2241_, lean_object* v_i_2242_, lean_object* v_b_2243_){
_start:
{
size_t v_sz_boxed_2244_; size_t v_i_boxed_2245_; lean_object* v_res_2246_; 
v_sz_boxed_2244_ = lean_unbox_usize(v_sz_2241_);
lean_dec(v_sz_2241_);
v_i_boxed_2245_ = lean_unbox_usize(v_i_2242_);
lean_dec(v_i_2242_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2239_, v_as_2240_, v_sz_boxed_2244_, v_i_boxed_2245_, v_b_2243_);
lean_dec_ref(v_as_2240_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2247_, lean_object* v_k_2248_, lean_object* v_result_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2247_, v_k_2248_);
if (lean_obj_tag(v___x_2250_) == 0)
{
return v_result_2249_;
}
else
{
lean_object* v_val_2251_; lean_object* v___x_2252_; 
v_val_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_val_2251_);
lean_dec_ref_known(v___x_2250_, 1);
v___x_2252_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2251_, v_result_2249_);
lean_dec(v_val_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2253_, lean_object* v_k_2254_, lean_object* v_result_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2253_, v_k_2254_, v_result_2255_);
lean_dec(v_k_2254_);
lean_dec_ref(v_d_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2257_, lean_object* v_d_2258_, lean_object* v_k_2259_, lean_object* v_result_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2258_, v_k_2259_, v_result_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2262_, lean_object* v_d_2263_, lean_object* v_k_2264_, lean_object* v_result_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2262_, v_d_2263_, v_k_2264_, v_result_2265_);
lean_dec(v_k_2264_);
lean_dec_ref(v_d_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2267_, lean_object* v_e_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2274_; uint8_t v_foApprox_2275_; uint8_t v_ctxApprox_2276_; uint8_t v_quasiPatternApprox_2277_; uint8_t v_constApprox_2278_; uint8_t v_isDefEqStuckEx_2279_; uint8_t v_unificationHints_2280_; uint8_t v_proofIrrelevance_2281_; uint8_t v_assignSyntheticOpaque_2282_; uint8_t v_offsetCnstrs_2283_; uint8_t v_etaStruct_2284_; uint8_t v_univApprox_2285_; uint8_t v_iota_2286_; uint8_t v_beta_2287_; uint8_t v_proj_2288_; uint8_t v_zeta_2289_; uint8_t v_zetaDelta_2290_; uint8_t v_zetaUnused_2291_; uint8_t v_zetaHave_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2346_; 
v___x_2274_ = l_Lean_Meta_Context_config(v_a_2269_);
v_foApprox_2275_ = lean_ctor_get_uint8(v___x_2274_, 0);
v_ctxApprox_2276_ = lean_ctor_get_uint8(v___x_2274_, 1);
v_quasiPatternApprox_2277_ = lean_ctor_get_uint8(v___x_2274_, 2);
v_constApprox_2278_ = lean_ctor_get_uint8(v___x_2274_, 3);
v_isDefEqStuckEx_2279_ = lean_ctor_get_uint8(v___x_2274_, 4);
v_unificationHints_2280_ = lean_ctor_get_uint8(v___x_2274_, 5);
v_proofIrrelevance_2281_ = lean_ctor_get_uint8(v___x_2274_, 6);
v_assignSyntheticOpaque_2282_ = lean_ctor_get_uint8(v___x_2274_, 7);
v_offsetCnstrs_2283_ = lean_ctor_get_uint8(v___x_2274_, 8);
v_etaStruct_2284_ = lean_ctor_get_uint8(v___x_2274_, 10);
v_univApprox_2285_ = lean_ctor_get_uint8(v___x_2274_, 11);
v_iota_2286_ = lean_ctor_get_uint8(v___x_2274_, 12);
v_beta_2287_ = lean_ctor_get_uint8(v___x_2274_, 13);
v_proj_2288_ = lean_ctor_get_uint8(v___x_2274_, 14);
v_zeta_2289_ = lean_ctor_get_uint8(v___x_2274_, 15);
v_zetaDelta_2290_ = lean_ctor_get_uint8(v___x_2274_, 16);
v_zetaUnused_2291_ = lean_ctor_get_uint8(v___x_2274_, 17);
v_zetaHave_2292_ = lean_ctor_get_uint8(v___x_2274_, 18);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2294_ = v___x_2274_;
v_isShared_2295_ = v_isSharedCheck_2346_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v___x_2274_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2346_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
uint8_t v_trackZetaDelta_2296_; lean_object* v_zetaDeltaSet_2297_; lean_object* v_lctx_2298_; lean_object* v_localInstances_2299_; lean_object* v_defEqCtx_x3f_2300_; lean_object* v_synthPendingDepth_2301_; lean_object* v_canUnfold_x3f_2302_; uint8_t v_univApprox_2303_; uint8_t v_inTypeClassResolution_2304_; uint8_t v_cacheInferType_2305_; uint8_t v___x_2306_; lean_object* v_config_2308_; 
v_trackZetaDelta_2296_ = lean_ctor_get_uint8(v_a_2269_, sizeof(void*)*7);
v_zetaDeltaSet_2297_ = lean_ctor_get(v_a_2269_, 1);
v_lctx_2298_ = lean_ctor_get(v_a_2269_, 2);
v_localInstances_2299_ = lean_ctor_get(v_a_2269_, 3);
v_defEqCtx_x3f_2300_ = lean_ctor_get(v_a_2269_, 4);
v_synthPendingDepth_2301_ = lean_ctor_get(v_a_2269_, 5);
v_canUnfold_x3f_2302_ = lean_ctor_get(v_a_2269_, 6);
v_univApprox_2303_ = lean_ctor_get_uint8(v_a_2269_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2304_ = lean_ctor_get_uint8(v_a_2269_, sizeof(void*)*7 + 2);
v_cacheInferType_2305_ = lean_ctor_get_uint8(v_a_2269_, sizeof(void*)*7 + 3);
v___x_2306_ = 2;
if (v_isShared_2295_ == 0)
{
v_config_2308_ = v___x_2294_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 0, v_foApprox_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 1, v_ctxApprox_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 2, v_quasiPatternApprox_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 3, v_constApprox_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 4, v_isDefEqStuckEx_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 5, v_unificationHints_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 6, v_proofIrrelevance_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 7, v_assignSyntheticOpaque_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 8, v_offsetCnstrs_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 10, v_etaStruct_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 11, v_univApprox_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 12, v_iota_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 13, v_beta_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 14, v_proj_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 15, v_zeta_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 16, v_zetaDelta_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 17, v_zetaUnused_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, 18, v_zetaHave_2292_);
v_config_2308_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
uint64_t v___x_2309_; uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v_key_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_ctor_set_uint8(v_config_2308_, 9, v___x_2306_);
v___x_2309_ = l_Lean_Meta_Context_configKey(v_a_2269_);
v___x_2310_ = 3ULL;
v___x_2311_ = lean_uint64_shift_right(v___x_2309_, v___x_2310_);
v___x_2312_ = lean_uint64_shift_left(v___x_2311_, v___x_2310_);
v___x_2313_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2314_ = lean_uint64_lor(v___x_2312_, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2315_, 0, v_config_2308_);
lean_ctor_set_uint64(v___x_2315_, sizeof(void*)*1, v_key_2314_);
lean_inc(v_canUnfold_x3f_2302_);
lean_inc(v_synthPendingDepth_2301_);
lean_inc(v_defEqCtx_x3f_2300_);
lean_inc_ref(v_localInstances_2299_);
lean_inc_ref(v_lctx_2298_);
lean_inc(v_zetaDeltaSet_2297_);
v___x_2316_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v_zetaDeltaSet_2297_);
lean_ctor_set(v___x_2316_, 2, v_lctx_2298_);
lean_ctor_set(v___x_2316_, 3, v_localInstances_2299_);
lean_ctor_set(v___x_2316_, 4, v_defEqCtx_x3f_2300_);
lean_ctor_set(v___x_2316_, 5, v_synthPendingDepth_2301_);
lean_ctor_set(v___x_2316_, 6, v_canUnfold_x3f_2302_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*7, v_trackZetaDelta_2296_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*7 + 1, v_univApprox_2303_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2304_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*7 + 3, v_cacheInferType_2305_);
v___x_2317_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2268_, v___x_2316_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec_ref_known(v___x_2316_, 7);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2336_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2336_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2336_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_fst_2322_; lean_object* v_snd_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2335_; 
v_fst_2322_ = lean_ctor_get(v_a_2318_, 0);
v_snd_2323_ = lean_ctor_get(v_a_2318_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_a_2318_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2325_ = v_a_2318_;
v_isShared_2326_ = v_isSharedCheck_2335_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_snd_2323_);
lean_inc(v_fst_2322_);
lean_dec(v_a_2318_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2335_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_result_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v_result_2327_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2267_);
v___x_2328_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2267_, v_fst_2322_, v_result_2327_);
lean_dec(v_fst_2322_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_snd_2323_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2330_);
v___x_2332_ = v___x_2320_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_a_2337_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2317_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2317_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2347_, lean_object* v_e_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2347_, v_e_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec_ref(v_d_2347_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2355_, lean_object* v_d_2356_, lean_object* v_e_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2356_, v_e_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2364_, lean_object* v_d_2365_, lean_object* v_e_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2364_, v_d_2365_, v_e_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec_ref(v_d_2365_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2373_, lean_object* v_todo_2374_, lean_object* v_as_2375_, size_t v_i_2376_, size_t v_stop_2377_, lean_object* v_b_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
uint8_t v___x_2384_; 
v___x_2384_ = lean_usize_dec_eq(v_i_2376_, v_stop_2377_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v_fst_2386_; lean_object* v_snd_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2385_ = lean_array_uget_borrowed(v_as_2375_, v_i_2376_);
v_fst_2386_ = lean_ctor_get(v___x_2385_, 0);
v_snd_2387_ = lean_ctor_get(v___x_2385_, 1);
v___x_2388_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2386_);
v___x_2389_ = lean_nat_add(v_n_2373_, v___x_2388_);
lean_dec(v___x_2388_);
lean_inc(v_snd_2387_);
lean_inc_ref(v_todo_2374_);
v___x_2390_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2389_, v_todo_2374_, v_snd_2387_, v_b_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; size_t v___x_2392_; size_t v___x_2393_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = ((size_t)1ULL);
v___x_2393_ = lean_usize_add(v_i_2376_, v___x_2392_);
v_i_2376_ = v___x_2393_;
v_b_2378_ = v_a_2391_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2374_);
return v___x_2390_;
}
}
else
{
lean_object* v___x_2395_; 
lean_dec_ref(v_todo_2374_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v_b_2378_);
return v___x_2395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2396_, lean_object* v_todo_2397_, lean_object* v_c_2398_, lean_object* v_result_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_zero_2405_; uint8_t v_isZero_2406_; 
v_zero_2405_ = lean_unsigned_to_nat(0u);
v_isZero_2406_ = lean_nat_dec_eq(v_skip_2396_, v_zero_2405_);
if (v_isZero_2406_ == 1)
{
lean_object* v_vs_2407_; lean_object* v_children_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
lean_dec(v_skip_2396_);
v_vs_2407_ = lean_ctor_get(v_c_2398_, 0);
lean_inc_ref(v_vs_2407_);
v_children_2408_ = lean_ctor_get(v_c_2398_, 1);
lean_inc_ref(v_children_2408_);
lean_dec_ref(v_c_2398_);
v___x_2409_ = lean_array_get_size(v_todo_2397_);
v___x_2410_ = lean_nat_dec_eq(v___x_2409_, v_zero_2405_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
lean_dec_ref(v_vs_2407_);
v___x_2411_ = lean_array_get_size(v_children_2408_);
v___x_2412_ = lean_nat_dec_eq(v___x_2411_, v_zero_2405_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_e_2416_; lean_object* v___x_2417_; 
v___x_2413_ = l_Lean_instInhabitedExpr;
v___x_2414_ = lean_unsigned_to_nat(1u);
v___x_2415_ = lean_nat_sub(v___x_2409_, v___x_2414_);
v_e_2416_ = lean_array_get_borrowed(v___x_2413_, v_todo_2397_, v___x_2415_);
lean_dec(v___x_2415_);
lean_inc(v_e_2416_);
v___x_2417_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2416_, v___x_2412_, v___x_2412_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2469_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2469_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2469_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_fst_2422_; lean_object* v_snd_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2468_; 
v_fst_2422_ = lean_ctor_get(v_a_2418_, 0);
v_snd_2423_ = lean_ctor_get(v_a_2418_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_a_2418_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2425_ = v_a_2418_;
v_isShared_2426_ = v_isSharedCheck_2468_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_snd_2423_);
lean_inc(v_fst_2422_);
lean_dec(v_a_2418_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2468_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_todo_2427_; lean_object* v___y_2429_; lean_object* v_a_2430_; 
v_todo_2427_ = lean_array_pop(v_todo_2397_);
if (lean_obj_tag(v_fst_2422_) == 0)
{
uint8_t v___x_2443_; 
lean_del_object(v___x_2425_);
lean_dec(v_snd_2423_);
v___x_2443_ = lean_nat_dec_lt(v_zero_2405_, v___x_2411_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2445_; 
lean_dec_ref(v_todo_2427_);
lean_dec_ref(v_children_2408_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v_result_2399_);
v___x_2445_ = v___x_2420_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_result_2399_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
else
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_nat_dec_le(v___x_2411_, v___x_2411_);
if (v___x_2447_ == 0)
{
if (v___x_2443_ == 0)
{
lean_object* v___x_2449_; 
lean_dec_ref(v_todo_2427_);
lean_dec_ref(v_children_2408_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v_result_2399_);
v___x_2449_ = v___x_2420_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_result_2399_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
else
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
lean_del_object(v___x_2420_);
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = lean_usize_of_nat(v___x_2411_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2427_, v_children_2408_, v___x_2451_, v___x_2452_, v_result_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec_ref(v_children_2408_);
return v___x_2453_;
}
}
else
{
size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; 
lean_del_object(v___x_2420_);
v___x_2454_ = ((size_t)0ULL);
v___x_2455_ = lean_usize_of_nat(v___x_2411_);
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2427_, v_children_2408_, v___x_2454_, v___x_2455_, v_result_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec_ref(v_children_2408_);
return v___x_2456_;
}
}
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_fst_2460_; lean_object* v_snd_2461_; uint8_t v___x_2462_; 
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_2459_ = lean_array_get_borrowed(v___x_2458_, v_children_2408_, v_zero_2405_);
v_fst_2460_ = lean_ctor_get(v___x_2459_, 0);
v_snd_2461_ = lean_ctor_get(v___x_2459_, 1);
v___x_2462_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2460_, v___x_2457_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2464_; 
lean_inc_ref(v_result_2399_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v_result_2399_);
v___x_2464_ = v___x_2420_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_result_2399_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
v___y_2429_ = v___x_2464_;
v_a_2430_ = v_result_2399_;
goto v___jp_2428_;
}
}
else
{
lean_object* v___x_2466_; 
lean_del_object(v___x_2420_);
lean_inc(v_snd_2461_);
lean_inc_ref(v_todo_2427_);
v___x_2466_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2405_, v_todo_2427_, v_snd_2461_, v_result_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
v___y_2429_ = v___x_2466_;
v_a_2430_ = v_a_2467_;
goto v___jp_2428_;
}
else
{
lean_dec_ref(v_todo_2427_);
lean_del_object(v___x_2425_);
lean_dec(v_snd_2423_);
lean_dec(v_fst_2422_);
lean_dec_ref(v_children_2408_);
return v___x_2466_;
}
}
}
v___jp_2428_:
{
uint8_t v___x_2431_; 
v___x_2431_ = lean_nat_dec_lt(v_zero_2405_, v___x_2411_);
if (v___x_2431_ == 0)
{
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_todo_2427_);
lean_del_object(v___x_2425_);
lean_dec(v_snd_2423_);
lean_dec(v_fst_2422_);
lean_dec_ref(v_children_2408_);
return v___y_2429_;
}
else
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = lean_nat_sub(v___x_2411_, v___x_2414_);
v___x_2433_ = lean_nat_dec_le(v_zero_2405_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_dec(v___x_2432_);
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_todo_2427_);
lean_del_object(v___x_2425_);
lean_dec(v_snd_2423_);
lean_dec(v_fst_2422_);
lean_dec_ref(v_children_2408_);
return v___y_2429_;
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2));
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v___x_2434_);
v___x_2436_ = v___x_2425_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_fst_2422_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_2408_, v___x_2436_, v_zero_2405_, v___x_2432_);
lean_dec_ref(v___x_2436_);
lean_dec_ref(v_children_2408_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_dec_ref(v_a_2430_);
lean_dec_ref(v_todo_2427_);
lean_dec(v_snd_2423_);
return v___y_2429_;
}
else
{
lean_object* v_val_2438_; lean_object* v_snd_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v___y_2429_);
v_val_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_val_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v_snd_2439_ = lean_ctor_get(v_val_2438_, 1);
lean_inc(v_snd_2439_);
lean_dec(v_val_2438_);
v___x_2440_ = l_Array_append___redArg(v_todo_2427_, v_snd_2423_);
lean_dec(v_snd_2423_);
v_skip_2396_ = v_zero_2405_;
v_todo_2397_ = v___x_2440_;
v_c_2398_ = v_snd_2439_;
v_result_2399_ = v_a_2430_;
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
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v_children_2408_);
lean_dec_ref(v_result_2399_);
lean_dec_ref(v_todo_2397_);
v_a_2470_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2417_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2417_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v___x_2478_; 
lean_dec_ref(v_children_2408_);
lean_dec_ref(v_todo_2397_);
v___x_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_result_2399_);
return v___x_2478_;
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec_ref(v_children_2408_);
lean_dec_ref(v_todo_2397_);
v___x_2479_ = l_Array_append___redArg(v_result_2399_, v_vs_2407_);
lean_dec_ref(v_vs_2407_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
else
{
lean_object* v_children_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_children_2481_ = lean_ctor_get(v_c_2398_, 1);
lean_inc_ref(v_children_2481_);
lean_dec_ref(v_c_2398_);
v___x_2482_ = lean_array_get_size(v_children_2481_);
v___x_2483_ = lean_nat_dec_eq(v___x_2482_, v_zero_2405_);
if (v___x_2483_ == 0)
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_nat_dec_lt(v_zero_2405_, v___x_2482_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
lean_dec_ref(v_children_2481_);
lean_dec_ref(v_todo_2397_);
lean_dec(v_skip_2396_);
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_result_2399_);
return v___x_2485_;
}
else
{
lean_object* v_one_2486_; lean_object* v_n_2487_; uint8_t v___x_2488_; 
v_one_2486_ = lean_unsigned_to_nat(1u);
v_n_2487_ = lean_nat_sub(v_skip_2396_, v_one_2486_);
lean_dec(v_skip_2396_);
v___x_2488_ = lean_nat_dec_le(v___x_2482_, v___x_2482_);
if (v___x_2488_ == 0)
{
if (v___x_2484_ == 0)
{
lean_object* v___x_2489_; 
lean_dec(v_n_2487_);
lean_dec_ref(v_children_2481_);
lean_dec_ref(v_todo_2397_);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_result_2399_);
return v___x_2489_;
}
else
{
size_t v___x_2490_; size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = lean_usize_of_nat(v___x_2482_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2487_, v_todo_2397_, v_children_2481_, v___x_2490_, v___x_2491_, v_result_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec_ref(v_children_2481_);
lean_dec(v_n_2487_);
return v___x_2492_;
}
}
else
{
size_t v___x_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = ((size_t)0ULL);
v___x_2494_ = lean_usize_of_nat(v___x_2482_);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2487_, v_todo_2397_, v_children_2481_, v___x_2493_, v___x_2494_, v_result_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec_ref(v_children_2481_);
lean_dec(v_n_2487_);
return v___x_2495_;
}
}
}
else
{
lean_object* v___x_2496_; 
lean_dec_ref(v_children_2481_);
lean_dec_ref(v_todo_2397_);
lean_dec(v_skip_2396_);
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_result_2399_);
return v___x_2496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2497_, lean_object* v_as_2498_, size_t v_i_2499_, size_t v_stop_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_usize_dec_eq(v_i_2499_, v_stop_2500_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v_fst_2509_; lean_object* v_snd_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2508_ = lean_array_uget_borrowed(v_as_2498_, v_i_2499_);
v_fst_2509_ = lean_ctor_get(v___x_2508_, 0);
v_snd_2510_ = lean_ctor_get(v___x_2508_, 1);
v___x_2511_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2509_);
lean_inc(v_snd_2510_);
lean_inc_ref(v_todo_2497_);
v___x_2512_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2511_, v_todo_2497_, v_snd_2510_, v_b_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; size_t v___x_2514_; size_t v___x_2515_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = ((size_t)1ULL);
v___x_2515_ = lean_usize_add(v_i_2499_, v___x_2514_);
v_i_2499_ = v___x_2515_;
v_b_2501_ = v_a_2513_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2497_);
return v___x_2512_;
}
}
else
{
lean_object* v___x_2517_; 
lean_dec_ref(v_todo_2497_);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_b_2501_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2518_, lean_object* v_as_2519_, lean_object* v_i_2520_, lean_object* v_stop_2521_, lean_object* v_b_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
size_t v_i_boxed_2528_; size_t v_stop_boxed_2529_; lean_object* v_res_2530_; 
v_i_boxed_2528_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_stop_boxed_2529_ = lean_unbox_usize(v_stop_2521_);
lean_dec(v_stop_2521_);
v_res_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2518_, v_as_2519_, v_i_boxed_2528_, v_stop_boxed_2529_, v_b_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v_as_2519_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2531_, lean_object* v_todo_2532_, lean_object* v_as_2533_, lean_object* v_i_2534_, lean_object* v_stop_2535_, lean_object* v_b_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
size_t v_i_boxed_2542_; size_t v_stop_boxed_2543_; lean_object* v_res_2544_; 
v_i_boxed_2542_ = lean_unbox_usize(v_i_2534_);
lean_dec(v_i_2534_);
v_stop_boxed_2543_ = lean_unbox_usize(v_stop_2535_);
lean_dec(v_stop_2535_);
v_res_2544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2531_, v_todo_2532_, v_as_2533_, v_i_boxed_2542_, v_stop_boxed_2543_, v_b_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec_ref(v_as_2533_);
lean_dec(v_n_2531_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2545_, lean_object* v_todo_2546_, lean_object* v_c_2547_, lean_object* v_result_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2545_, v_todo_2546_, v_c_2547_, v_result_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2555_, lean_object* v_skip_2556_, lean_object* v_todo_2557_, lean_object* v_c_2558_, lean_object* v_result_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2556_, v_todo_2557_, v_c_2558_, v_result_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2566_, lean_object* v_skip_2567_, lean_object* v_todo_2568_, lean_object* v_c_2569_, lean_object* v_result_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2566_, v_skip_2567_, v_todo_2568_, v_c_2569_, v_result_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2577_, lean_object* v_todo_2578_, lean_object* v_as_2579_, size_t v_i_2580_, size_t v_stop_2581_, lean_object* v_b_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2578_, v_as_2579_, v_i_2580_, v_stop_2581_, v_b_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2589_, lean_object* v_todo_2590_, lean_object* v_as_2591_, lean_object* v_i_2592_, lean_object* v_stop_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
size_t v_i_boxed_2600_; size_t v_stop_boxed_2601_; lean_object* v_res_2602_; 
v_i_boxed_2600_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_stop_boxed_2601_ = lean_unbox_usize(v_stop_2593_);
lean_dec(v_stop_2593_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2589_, v_todo_2590_, v_as_2591_, v_i_boxed_2600_, v_stop_boxed_2601_, v_b_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec_ref(v_as_2591_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2603_, lean_object* v_n_2604_, lean_object* v_todo_2605_, lean_object* v_as_2606_, size_t v_i_2607_, size_t v_stop_2608_, lean_object* v_b_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2604_, v_todo_2605_, v_as_2606_, v_i_2607_, v_stop_2608_, v_b_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_n_2617_, lean_object* v_todo_2618_, lean_object* v_as_2619_, lean_object* v_i_2620_, lean_object* v_stop_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
size_t v_i_boxed_2628_; size_t v_stop_boxed_2629_; lean_object* v_res_2630_; 
v_i_boxed_2628_ = lean_unbox_usize(v_i_2620_);
lean_dec(v_i_2620_);
v_stop_boxed_2629_ = lean_unbox_usize(v_stop_2621_);
lean_dec(v_stop_2621_);
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2616_, v_n_2617_, v_todo_2618_, v_as_2619_, v_i_boxed_2628_, v_stop_boxed_2629_, v_b_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v_as_2619_);
lean_dec(v_n_2617_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2631_, lean_object* v_k_2632_, lean_object* v_c_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2632_);
v___x_2640_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2641_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2639_, v___x_2640_, v_c_2633_, v_result_2631_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2642_, lean_object* v_k_2643_, lean_object* v_c_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2642_, v_k_2643_, v_c_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v_k_2643_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2651_, lean_object* v_keys_2652_, lean_object* v_vals_2653_, lean_object* v_i_2654_, lean_object* v_acc_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_array_get_size(v_keys_2652_);
v___x_2662_ = lean_nat_dec_lt(v_i_2654_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
lean_dec(v_i_2654_);
lean_dec_ref(v_f_2651_);
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_acc_2655_);
return v___x_2663_;
}
else
{
lean_object* v_k_2664_; lean_object* v_v_2665_; lean_object* v___x_2666_; 
v_k_2664_ = lean_array_fget_borrowed(v_keys_2652_, v_i_2654_);
v_v_2665_ = lean_array_fget_borrowed(v_vals_2653_, v_i_2654_);
lean_inc_ref(v_f_2651_);
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v_v_2665_);
lean_inc(v_k_2664_);
v___x_2666_ = lean_apply_8(v_f_2651_, v_acc_2655_, v_k_2664_, v_v_2665_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_nat_add(v_i_2654_, v___x_2668_);
lean_dec(v_i_2654_);
v_i_2654_ = v___x_2669_;
v_acc_2655_ = v_a_2667_;
goto _start;
}
else
{
lean_dec(v_i_2654_);
lean_dec_ref(v_f_2651_);
return v___x_2666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2671_, lean_object* v_keys_2672_, lean_object* v_vals_2673_, lean_object* v_i_2674_, lean_object* v_acc_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2671_, v_keys_2672_, v_vals_2673_, v_i_2674_, v_acc_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec_ref(v_vals_2673_);
lean_dec_ref(v_keys_2672_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
if (lean_obj_tag(v_x_2683_) == 0)
{
lean_object* v_es_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2710_; 
v_es_2690_ = lean_ctor_get(v_x_2683_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_x_2683_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2692_ = v_x_2683_;
v_isShared_2693_ = v_isSharedCheck_2710_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_es_2690_);
lean_dec(v_x_2683_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2710_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_array_get_size(v_es_2690_);
v___x_2696_ = lean_nat_dec_lt(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2698_; 
lean_dec_ref(v_es_2690_);
lean_dec_ref(v_f_2682_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_x_2684_);
v___x_2698_ = v___x_2692_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_x_2684_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
else
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_nat_dec_le(v___x_2695_, v___x_2695_);
if (v___x_2700_ == 0)
{
if (v___x_2696_ == 0)
{
lean_object* v___x_2702_; 
lean_dec_ref(v_es_2690_);
lean_dec_ref(v_f_2682_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_x_2684_);
v___x_2702_ = v___x_2692_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_x_2684_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
else
{
size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2692_);
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = lean_usize_of_nat(v___x_2695_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2682_, v_es_2690_, v___x_2704_, v___x_2705_, v_x_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v_es_2690_);
return v___x_2706_;
}
}
else
{
size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; 
lean_del_object(v___x_2692_);
v___x_2707_ = ((size_t)0ULL);
v___x_2708_ = lean_usize_of_nat(v___x_2695_);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2682_, v_es_2690_, v___x_2707_, v___x_2708_, v_x_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v_es_2690_);
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_ks_2711_; lean_object* v_vs_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_ks_2711_ = lean_ctor_get(v_x_2683_, 0);
lean_inc_ref(v_ks_2711_);
v_vs_2712_ = lean_ctor_get(v_x_2683_, 1);
lean_inc_ref(v_vs_2712_);
lean_dec_ref_known(v_x_2683_, 2);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2682_, v_ks_2711_, v_vs_2712_, v___x_2713_, v_x_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v_vs_2712_);
lean_dec_ref(v_ks_2711_);
return v___x_2714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2715_, lean_object* v_as_2716_, size_t v_i_2717_, size_t v_stop_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_a_2726_; lean_object* v___y_2731_; uint8_t v___x_2733_; 
v___x_2733_ = lean_usize_dec_eq(v_i_2717_, v_stop_2718_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_array_uget_borrowed(v_as_2716_, v_i_2717_);
switch(lean_obj_tag(v___x_2734_))
{
case 0:
{
lean_object* v_key_2735_; lean_object* v_val_2736_; lean_object* v___x_2737_; 
v_key_2735_ = lean_ctor_get(v___x_2734_, 0);
v_val_2736_ = lean_ctor_get(v___x_2734_, 1);
lean_inc_ref(v_f_2715_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
lean_inc(v_val_2736_);
lean_inc(v_key_2735_);
v___x_2737_ = lean_apply_8(v_f_2715_, v_b_2719_, v_key_2735_, v_val_2736_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, lean_box(0));
v___y_2731_ = v___x_2737_;
goto v___jp_2730_;
}
case 1:
{
lean_object* v_node_2738_; lean_object* v___x_2739_; 
v_node_2738_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_node_2738_);
lean_inc_ref(v_f_2715_);
v___x_2739_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2715_, v_node_2738_, v_b_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
v___y_2731_ = v___x_2739_;
goto v___jp_2730_;
}
default: 
{
v_a_2726_ = v_b_2719_;
goto v___jp_2725_;
}
}
}
else
{
lean_object* v___x_2740_; 
lean_dec_ref(v_f_2715_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_b_2719_);
return v___x_2740_;
}
v___jp_2725_:
{
size_t v___x_2727_; size_t v___x_2728_; 
v___x_2727_ = ((size_t)1ULL);
v___x_2728_ = lean_usize_add(v_i_2717_, v___x_2727_);
v_i_2717_ = v___x_2728_;
v_b_2719_ = v_a_2726_;
goto _start;
}
v___jp_2730_:
{
if (lean_obj_tag(v___y_2731_) == 0)
{
lean_object* v_a_2732_; 
v_a_2732_ = lean_ctor_get(v___y_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___y_2731_, 1);
v_a_2726_ = v_a_2732_;
goto v___jp_2725_;
}
else
{
lean_dec_ref(v_f_2715_);
return v___y_2731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2741_, lean_object* v_as_2742_, lean_object* v_i_2743_, lean_object* v_stop_2744_, lean_object* v_b_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
size_t v_i_boxed_2751_; size_t v_stop_boxed_2752_; lean_object* v_res_2753_; 
v_i_boxed_2751_ = lean_unbox_usize(v_i_2743_);
lean_dec(v_i_2743_);
v_stop_boxed_2752_ = lean_unbox_usize(v_stop_2744_);
lean_dec(v_stop_2744_);
v_res_2753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2741_, v_as_2742_, v_i_boxed_2751_, v_stop_boxed_2752_, v_b_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec_ref(v_as_2742_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2754_, v_x_2755_, v_x_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2764_, lean_object* v_e_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___x_2771_; uint8_t v_foApprox_2772_; uint8_t v_ctxApprox_2773_; uint8_t v_quasiPatternApprox_2774_; uint8_t v_constApprox_2775_; uint8_t v_isDefEqStuckEx_2776_; uint8_t v_unificationHints_2777_; uint8_t v_proofIrrelevance_2778_; uint8_t v_assignSyntheticOpaque_2779_; uint8_t v_offsetCnstrs_2780_; uint8_t v_etaStruct_2781_; uint8_t v_univApprox_2782_; uint8_t v_iota_2783_; uint8_t v_beta_2784_; uint8_t v_proj_2785_; uint8_t v_zeta_2786_; uint8_t v_zetaDelta_2787_; uint8_t v_zetaUnused_2788_; uint8_t v_zetaHave_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2844_; 
v___x_2771_ = l_Lean_Meta_Context_config(v_a_2766_);
v_foApprox_2772_ = lean_ctor_get_uint8(v___x_2771_, 0);
v_ctxApprox_2773_ = lean_ctor_get_uint8(v___x_2771_, 1);
v_quasiPatternApprox_2774_ = lean_ctor_get_uint8(v___x_2771_, 2);
v_constApprox_2775_ = lean_ctor_get_uint8(v___x_2771_, 3);
v_isDefEqStuckEx_2776_ = lean_ctor_get_uint8(v___x_2771_, 4);
v_unificationHints_2777_ = lean_ctor_get_uint8(v___x_2771_, 5);
v_proofIrrelevance_2778_ = lean_ctor_get_uint8(v___x_2771_, 6);
v_assignSyntheticOpaque_2779_ = lean_ctor_get_uint8(v___x_2771_, 7);
v_offsetCnstrs_2780_ = lean_ctor_get_uint8(v___x_2771_, 8);
v_etaStruct_2781_ = lean_ctor_get_uint8(v___x_2771_, 10);
v_univApprox_2782_ = lean_ctor_get_uint8(v___x_2771_, 11);
v_iota_2783_ = lean_ctor_get_uint8(v___x_2771_, 12);
v_beta_2784_ = lean_ctor_get_uint8(v___x_2771_, 13);
v_proj_2785_ = lean_ctor_get_uint8(v___x_2771_, 14);
v_zeta_2786_ = lean_ctor_get_uint8(v___x_2771_, 15);
v_zetaDelta_2787_ = lean_ctor_get_uint8(v___x_2771_, 16);
v_zetaUnused_2788_ = lean_ctor_get_uint8(v___x_2771_, 17);
v_zetaHave_2789_ = lean_ctor_get_uint8(v___x_2771_, 18);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2791_ = v___x_2771_;
v_isShared_2792_ = v_isSharedCheck_2844_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v___x_2771_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2844_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
uint8_t v_trackZetaDelta_2793_; lean_object* v_zetaDeltaSet_2794_; lean_object* v_lctx_2795_; lean_object* v_localInstances_2796_; lean_object* v_defEqCtx_x3f_2797_; lean_object* v_synthPendingDepth_2798_; lean_object* v_canUnfold_x3f_2799_; uint8_t v_univApprox_2800_; uint8_t v_inTypeClassResolution_2801_; uint8_t v_cacheInferType_2802_; uint8_t v___x_2803_; lean_object* v_config_2805_; 
v_trackZetaDelta_2793_ = lean_ctor_get_uint8(v_a_2766_, sizeof(void*)*7);
v_zetaDeltaSet_2794_ = lean_ctor_get(v_a_2766_, 1);
v_lctx_2795_ = lean_ctor_get(v_a_2766_, 2);
v_localInstances_2796_ = lean_ctor_get(v_a_2766_, 3);
v_defEqCtx_x3f_2797_ = lean_ctor_get(v_a_2766_, 4);
v_synthPendingDepth_2798_ = lean_ctor_get(v_a_2766_, 5);
v_canUnfold_x3f_2799_ = lean_ctor_get(v_a_2766_, 6);
v_univApprox_2800_ = lean_ctor_get_uint8(v_a_2766_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2801_ = lean_ctor_get_uint8(v_a_2766_, sizeof(void*)*7 + 2);
v_cacheInferType_2802_ = lean_ctor_get_uint8(v_a_2766_, sizeof(void*)*7 + 3);
v___x_2803_ = 2;
if (v_isShared_2792_ == 0)
{
v_config_2805_ = v___x_2791_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 0, v_foApprox_2772_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 1, v_ctxApprox_2773_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 2, v_quasiPatternApprox_2774_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 3, v_constApprox_2775_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 4, v_isDefEqStuckEx_2776_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 5, v_unificationHints_2777_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 6, v_proofIrrelevance_2778_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 7, v_assignSyntheticOpaque_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 8, v_offsetCnstrs_2780_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 10, v_etaStruct_2781_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 11, v_univApprox_2782_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 12, v_iota_2783_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 13, v_beta_2784_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 14, v_proj_2785_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 15, v_zeta_2786_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 16, v_zetaDelta_2787_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 17, v_zetaUnused_2788_);
lean_ctor_set_uint8(v_reuseFailAlloc_2843_, 18, v_zetaHave_2789_);
v_config_2805_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
uint64_t v___x_2806_; uint64_t v___x_2807_; uint64_t v___x_2808_; uint8_t v___x_2809_; uint64_t v___x_2810_; uint64_t v___x_2811_; uint64_t v_key_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; 
lean_ctor_set_uint8(v_config_2805_, 9, v___x_2803_);
v___x_2806_ = l_Lean_Meta_Context_configKey(v_a_2766_);
v___x_2807_ = 3ULL;
v___x_2808_ = lean_uint64_shift_right(v___x_2806_, v___x_2807_);
v___x_2809_ = 1;
v___x_2810_ = lean_uint64_shift_left(v___x_2808_, v___x_2807_);
v___x_2811_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2812_ = lean_uint64_lor(v___x_2810_, v___x_2811_);
v___x_2813_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2813_, 0, v_config_2805_);
lean_ctor_set_uint64(v___x_2813_, sizeof(void*)*1, v_key_2812_);
lean_inc(v_canUnfold_x3f_2799_);
lean_inc(v_synthPendingDepth_2798_);
lean_inc(v_defEqCtx_x3f_2797_);
lean_inc_ref(v_localInstances_2796_);
lean_inc_ref(v_lctx_2795_);
lean_inc(v_zetaDeltaSet_2794_);
v___x_2814_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v_zetaDeltaSet_2794_);
lean_ctor_set(v___x_2814_, 2, v_lctx_2795_);
lean_ctor_set(v___x_2814_, 3, v_localInstances_2796_);
lean_ctor_set(v___x_2814_, 4, v_defEqCtx_x3f_2797_);
lean_ctor_set(v___x_2814_, 5, v_synthPendingDepth_2798_);
lean_ctor_set(v___x_2814_, 6, v_canUnfold_x3f_2799_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*7, v_trackZetaDelta_2793_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*7 + 1, v_univApprox_2800_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2801_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*7 + 3, v_cacheInferType_2802_);
v___x_2815_ = 0;
v___x_2816_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2765_, v___x_2815_, v___x_2809_, v___x_2814_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2834_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2819_ = v___x_2816_;
v_isShared_2820_ = v_isSharedCheck_2834_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2834_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v_fst_2821_; 
v_fst_2821_ = lean_ctor_get(v_a_2817_, 0);
lean_inc(v_fst_2821_);
if (lean_obj_tag(v_fst_2821_) == 0)
{
lean_object* v___f_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_del_object(v___x_2819_);
lean_dec(v_a_2817_);
v___f_2822_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_2824_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2822_, v_d_2764_, v___x_2823_, v___x_2814_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec_ref_known(v___x_2814_, 7);
return v___x_2824_;
}
else
{
lean_object* v_snd_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_snd_2825_ = lean_ctor_get(v_a_2817_, 1);
lean_inc(v_snd_2825_);
lean_dec(v_a_2817_);
v___x_2826_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2764_);
v___x_2827_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2764_, v_fst_2821_);
lean_dec(v_fst_2821_);
lean_dec_ref(v_d_2764_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2829_; 
lean_dec(v_snd_2825_);
lean_dec_ref_known(v___x_2814_, 7);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2826_);
v___x_2829_ = v___x_2819_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2826_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
else
{
lean_object* v_val_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2819_);
v_val_2831_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2832_, v_snd_2825_, v_val_2831_, v___x_2826_, v___x_2814_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec_ref_known(v___x_2814_, 7);
return v___x_2833_;
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref_known(v___x_2814_, 7);
lean_dec_ref(v_d_2764_);
v_a_2835_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2816_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2816_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_2845_, lean_object* v_e_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2845_, v_e_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_2853_, lean_object* v_d_2854_, lean_object* v_e_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2854_, v_e_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_2862_, lean_object* v_d_2863_, lean_object* v_e_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_2862_, v_d_2863_, v_e_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_2871_, lean_object* v_f_2872_, lean_object* v_init_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2872_, v_map_2871_, v_init_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_2880_, lean_object* v_f_2881_, lean_object* v_init_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_2880_, v_f_2881_, v_init_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_2889_, lean_object* v_00_u03b2_2890_, lean_object* v_map_2891_, lean_object* v_f_2892_, lean_object* v_init_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2892_, v_map_2891_, v_init_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_2900_, lean_object* v_00_u03b2_2901_, lean_object* v_map_2902_, lean_object* v_f_2903_, lean_object* v_init_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_2900_, v_00_u03b2_2901_, v_map_2902_, v_f_2903_, v_init_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_2911_, lean_object* v_00_u03b1_2912_, lean_object* v_00_u03b2_2913_, lean_object* v_f_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2914_, v_x_2915_, v_x_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2923_, lean_object* v_00_u03b1_2924_, lean_object* v_00_u03b2_2925_, lean_object* v_f_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_2923_, v_00_u03b1_2924_, v_00_u03b2_2925_, v_f_2926_, v_x_2927_, v_x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_00_u03c3_2937_, lean_object* v_f_2938_, lean_object* v_as_2939_, size_t v_i_2940_, size_t v_stop_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2938_, v_as_2939_, v_i_2940_, v_stop_2941_, v_b_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_00_u03b2_2950_, lean_object* v_00_u03c3_2951_, lean_object* v_f_2952_, lean_object* v_as_2953_, lean_object* v_i_2954_, lean_object* v_stop_2955_, lean_object* v_b_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
size_t v_i_boxed_2962_; size_t v_stop_boxed_2963_; lean_object* v_res_2964_; 
v_i_boxed_2962_ = lean_unbox_usize(v_i_2954_);
lean_dec(v_i_2954_);
v_stop_boxed_2963_ = lean_unbox_usize(v_stop_2955_);
lean_dec(v_stop_2955_);
v_res_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_2949_, v_00_u03b2_2950_, v_00_u03c3_2951_, v_f_2952_, v_as_2953_, v_i_boxed_2962_, v_stop_boxed_2963_, v_b_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v_as_2953_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2965_, lean_object* v_00_u03b1_2966_, lean_object* v_00_u03b2_2967_, lean_object* v_f_2968_, lean_object* v_keys_2969_, lean_object* v_vals_2970_, lean_object* v_heq_2971_, lean_object* v_i_2972_, lean_object* v_acc_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2968_, v_keys_2969_, v_vals_2970_, v_i_2972_, v_acc_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_2980_, lean_object* v_00_u03b1_2981_, lean_object* v_00_u03b2_2982_, lean_object* v_f_2983_, lean_object* v_keys_2984_, lean_object* v_vals_2985_, lean_object* v_heq_2986_, lean_object* v_i_2987_, lean_object* v_acc_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_2980_, v_00_u03b1_2981_, v_00_u03b2_2982_, v_f_2983_, v_keys_2984_, v_vals_2985_, v_heq_2986_, v_i_2987_, v_acc_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_vals_2985_);
lean_dec_ref(v_keys_2984_);
return v_res_2994_;
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
