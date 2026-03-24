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
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2;
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
lean_inc_ref(v_arg_72_);
lean_dec_ref(v_x_64_);
lean_inc_ref(v_arg_72_);
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
lean_inc(v_a_382_);
lean_dec_ref(v___x_381_);
v___x_383_ = 0;
lean_inc(v_a_382_);
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
lean_inc(v_a_430_);
lean_dec_ref(v___x_429_);
v___x_431_ = 0;
lean_inc(v_a_430_);
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
lean_inc(v_typeName_599_);
v_idx_600_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_idx_600_);
v_struct_601_ = lean_ctor_get(v___x_535_, 2);
lean_inc_ref(v_struct_601_);
v___x_602_ = lean_st_ref_get(v_a_515_);
v_env_608_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_env_608_);
lean_dec(v___x_602_);
lean_inc(v_typeName_599_);
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
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1253_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1253_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1253_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___y_1078_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; 
if (v_root_1066_ == 0)
{
lean_object* v___x_1241_; 
lean_inc(v_a_1073_);
v___x_1241_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_1073_);
if (lean_obj_tag(v___x_1241_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1252_; 
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_val_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 2);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_val_1242_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
}
else
{
lean_dec(v___x_1241_);
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
lean_object* v_declName_1098_; lean_object* v___x_1099_; 
v_declName_1098_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_declName_1098_);
lean_dec_ref(v___x_1092_);
v___x_1099_ = l_Lean_Meta_getConfig___redArg(v___y_1088_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; uint8_t v_isDefEqStuckEx_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v___x_1099_);
v_isDefEqStuckEx_1101_ = lean_ctor_get_uint8(v_a_1100_, 4);
lean_dec(v_a_1100_);
if (v_isDefEqStuckEx_1101_ == 0)
{
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
uint8_t v___x_1102_; 
v___x_1102_ = l_Lean_Expr_hasExprMVar(v_a_1073_);
if (v___x_1102_ == 0)
{
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1103_; 
lean_inc(v_declName_1098_);
v___x_1103_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1098_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; uint8_t v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = lean_unbox(v_a_1104_);
lean_dec(v_a_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v_env_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_st_ref_get(v___y_1091_);
v_env_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc_ref(v_env_1107_);
lean_dec(v___x_1106_);
v___x_1108_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1107_, v_a_1073_);
if (lean_obj_tag(v___x_1108_) == 1)
{
lean_object* v_val_1109_; lean_object* v_numDiscrs_1110_; lean_object* v_nargs_1111_; lean_object* v_dummy_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_val_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref(v___x_1108_);
v_numDiscrs_1110_ = lean_ctor_get(v_val_1109_, 1);
lean_inc(v_numDiscrs_1110_);
v_nargs_1111_ = l_Lean_Expr_getAppNumArgs(v_a_1073_);
v_dummy_1112_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
lean_inc(v_nargs_1111_);
v___x_1113_ = lean_mk_array(v_nargs_1111_, v_dummy_1112_);
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_sub(v_nargs_1111_, v___x_1114_);
lean_dec(v_nargs_1111_);
lean_inc(v_a_1073_);
v___x_1116_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1073_, v___x_1113_, v___x_1115_);
v___x_1117_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1109_);
lean_dec(v_val_1109_);
v___x_1118_ = lean_nat_add(v___x_1117_, v_numDiscrs_1110_);
lean_dec(v_numDiscrs_1110_);
v___x_1119_ = l_Array_toSubarray___redArg(v___x_1116_, v___x_1117_, v___x_1118_);
v___x_1120_ = lean_box(0);
v___x_1121_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_1119_, v___x_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_dec_ref(v___x_1121_);
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
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
else
{
lean_object* v___x_1130_; lean_object* v_a_1131_; uint8_t v___x_1132_; 
lean_dec(v___x_1108_);
lean_inc(v_declName_1098_);
v___x_1130_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_1098_, v___y_1091_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = lean_unbox(v_a_1131_);
lean_dec(v_a_1131_);
if (v___x_1132_ == 0)
{
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref(v___x_1133_);
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
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
}
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref(v___x_1142_);
v___y_1078_ = v_declName_1098_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1151_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1103_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1103_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_declName_1098_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_a_1159_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1099_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1099_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_del_object(v___x_1075_);
v_fvarId_1167_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_fvarId_1167_);
lean_dec_ref(v___x_1092_);
v___x_1168_ = l_Lean_Expr_getAppNumArgs(v_a_1073_);
lean_inc(v___x_1168_);
v___x_1169_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_fvarId_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_mk_empty_array_with_capacity(v___x_1168_);
lean_dec(v___x_1168_);
v___x_1171_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1073_, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
case 2:
{
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
if (v_isMatch_1065_ == 0)
{
lean_object* v_mvarId_1174_; lean_object* v___x_1175_; 
v_mvarId_1174_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_mvarId_1174_);
lean_dec_ref(v___x_1092_);
v___x_1175_ = l_Lean_Meta_getConfig___redArg(v___y_1088_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1208_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1208_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1208_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
uint8_t v_isDefEqStuckEx_1180_; 
v_isDefEqStuckEx_1180_ = lean_ctor_get_uint8(v_a_1176_, 4);
lean_dec(v_a_1176_);
if (v_isDefEqStuckEx_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_del_object(v___x_1178_);
v___x_1181_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1174_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
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
lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_dec(v_mvarId_1174_);
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1204_);
v___x_1206_ = v___x_1178_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_mvarId_1174_);
v_a_1209_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1175_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1175_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v___x_1092_);
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
case 11:
{
lean_object* v_typeName_1219_; lean_object* v_idx_1220_; lean_object* v_struct_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_del_object(v___x_1075_);
v_typeName_1219_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_typeName_1219_);
v_idx_1220_ = lean_ctor_get(v___x_1092_, 1);
lean_inc(v_idx_1220_);
v_struct_1221_ = lean_ctor_get(v___x_1092_, 2);
lean_inc_ref(v_struct_1221_);
lean_dec_ref(v___x_1092_);
v___x_1222_ = l_Lean_Expr_getAppNumArgs(v_a_1073_);
lean_inc(v___x_1222_);
v___x_1223_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1223_, 0, v_typeName_1219_);
lean_ctor_set(v___x_1223_, 1, v_idx_1220_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_mk_empty_array_with_capacity(v___x_1224_);
v___x_1226_ = lean_array_push(v___x_1225_, v_struct_1221_);
v___x_1227_ = lean_mk_empty_array_with_capacity(v___x_1222_);
lean_dec(v___x_1222_);
v___x_1228_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1073_, v___x_1227_);
v___x_1229_ = l_Array_append___redArg(v___x_1226_, v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1223_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
case 7:
{
lean_object* v_binderType_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v_binderType_1232_ = lean_ctor_get(v___x_1092_, 1);
lean_inc_ref(v_binderType_1232_);
lean_dec_ref(v___x_1092_);
v___x_1233_ = lean_box(5);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_mk_empty_array_with_capacity(v___x_1234_);
v___x_1236_ = lean_array_push(v___x_1235_, v_binderType_1232_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1233_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
default: 
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v___x_1092_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_a_1254_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1072_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1072_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* v_e_1262_, lean_object* v_isMatch_1263_, lean_object* v_root_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
uint8_t v_isMatch_boxed_1270_; uint8_t v_root_boxed_1271_; lean_object* v_res_1272_; 
v_isMatch_boxed_1270_ = lean_unbox(v_isMatch_1263_);
v_root_boxed_1271_ = lean_unbox(v_root_1264_);
v_res_1272_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1262_, v_isMatch_boxed_1270_, v_root_boxed_1271_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1273_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object* v_inst_1287_, lean_object* v_R_1288_, lean_object* v_a_1289_, lean_object* v_b_1290_, lean_object* v_c_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1289_, v_b_1290_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object* v_inst_1298_, lean_object* v_R_1299_, lean_object* v_a_1300_, lean_object* v_b_1301_, lean_object* v_c_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_1298_, v_R_1299_, v_a_1300_, v_b_1301_, v_c_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* v_e_1309_, uint8_t v_root_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
uint8_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = 1;
v___x_1317_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1309_, v___x_1316_, v_root_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* v_e_1318_, lean_object* v_root_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
uint8_t v_root_boxed_1325_; lean_object* v_res_1326_; 
v_root_boxed_1325_ = lean_unbox(v_root_1319_);
v_res_1326_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1318_, v_root_boxed_1325_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* v_e_1327_, uint8_t v_root_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
uint8_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = 0;
v___x_1335_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1327_, v___x_1334_, v_root_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* v_e_1336_, lean_object* v_root_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
uint8_t v_root_boxed_1343_; lean_object* v_res_1344_; 
v_root_boxed_1343_ = lean_unbox(v_root_1337_);
v_res_1344_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1336_, v_root_boxed_1343_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1345_, lean_object* v_vals_1346_, lean_object* v_i_1347_, lean_object* v_k_1348_){
_start:
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = lean_array_get_size(v_keys_1345_);
v___x_1350_ = lean_nat_dec_lt(v_i_1347_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_dec(v_i_1347_);
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
else
{
lean_object* v_k_x27_1352_; uint8_t v___x_1353_; 
v_k_x27_1352_ = lean_array_fget_borrowed(v_keys_1345_, v_i_1347_);
v___x_1353_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1348_, v_k_x27_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_nat_add(v_i_1347_, v___x_1354_);
lean_dec(v_i_1347_);
v_i_1347_ = v___x_1355_;
goto _start;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_array_fget_borrowed(v_vals_1346_, v_i_1347_);
lean_dec(v_i_1347_);
lean_inc(v___x_1357_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1359_, lean_object* v_vals_1360_, lean_object* v_i_1361_, lean_object* v_k_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1359_, v_vals_1360_, v_i_1361_, v_k_1362_);
lean_dec(v_k_1362_);
lean_dec_ref(v_vals_1360_);
lean_dec_ref(v_keys_1359_);
return v_res_1363_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; 
v___x_1364_ = ((size_t)5ULL);
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_shift_left(v___x_1365_, v___x_1364_);
return v___x_1366_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; 
v___x_1367_ = ((size_t)1ULL);
v___x_1368_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0);
v___x_1369_ = lean_usize_sub(v___x_1368_, v___x_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1370_, size_t v_x_1371_, lean_object* v_x_1372_){
_start:
{
if (lean_obj_tag(v_x_1370_) == 0)
{
lean_object* v_es_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1394_; 
v_es_1373_ = lean_ctor_get(v_x_1370_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_x_1370_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1375_ = v_x_1370_;
v_isShared_1376_ = v_isSharedCheck_1394_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_es_1373_);
lean_dec(v_x_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1394_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; lean_object* v_j_1381_; lean_object* v___x_1382_; 
v___x_1377_ = lean_box(2);
v___x_1378_ = ((size_t)5ULL);
v___x_1379_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1);
v___x_1380_ = lean_usize_land(v_x_1371_, v___x_1379_);
v_j_1381_ = lean_usize_to_nat(v___x_1380_);
v___x_1382_ = lean_array_get(v___x_1377_, v_es_1373_, v_j_1381_);
lean_dec(v_j_1381_);
lean_dec_ref(v_es_1373_);
switch(lean_obj_tag(v___x_1382_))
{
case 0:
{
lean_object* v_key_1383_; lean_object* v_val_1384_; uint8_t v___x_1385_; 
v_key_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_key_1383_);
v_val_1384_ = lean_ctor_get(v___x_1382_, 1);
lean_inc(v_val_1384_);
lean_dec_ref(v___x_1382_);
v___x_1385_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1372_, v_key_1383_);
lean_dec(v_key_1383_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec(v_val_1384_);
lean_del_object(v___x_1375_);
v___x_1386_ = lean_box(0);
return v___x_1386_;
}
else
{
lean_object* v___x_1388_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 1);
lean_ctor_set(v___x_1375_, 0, v_val_1384_);
v___x_1388_ = v___x_1375_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_val_1384_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
case 1:
{
lean_object* v_node_1390_; size_t v___x_1391_; 
lean_del_object(v___x_1375_);
v_node_1390_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_node_1390_);
lean_dec_ref(v___x_1382_);
v___x_1391_ = lean_usize_shift_right(v_x_1371_, v___x_1378_);
v_x_1370_ = v_node_1390_;
v_x_1371_ = v___x_1391_;
goto _start;
}
default: 
{
lean_object* v___x_1393_; 
lean_del_object(v___x_1375_);
v___x_1393_ = lean_box(0);
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_ks_1395_; lean_object* v_vs_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_ks_1395_ = lean_ctor_get(v_x_1370_, 0);
lean_inc_ref(v_ks_1395_);
v_vs_1396_ = lean_ctor_get(v_x_1370_, 1);
lean_inc_ref(v_vs_1396_);
lean_dec_ref(v_x_1370_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1395_, v_vs_1396_, v___x_1397_, v_x_1372_);
lean_dec_ref(v_vs_1396_);
lean_dec_ref(v_ks_1395_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
size_t v_x_181__boxed_1402_; lean_object* v_res_1403_; 
v_x_181__boxed_1402_ = lean_unbox_usize(v_x_1400_);
lean_dec(v_x_1400_);
v_res_1403_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1399_, v_x_181__boxed_1402_, v_x_1401_);
lean_dec(v_x_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
uint64_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1405_);
v___x_1407_ = lean_uint64_to_usize(v___x_1406_);
v___x_1408_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1404_, v___x_1407_, v_x_1405_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1409_, v_x_1410_);
lean_dec(v_x_1410_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v_result_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1413_ = lean_unsigned_to_nat(8u);
v_result_1414_ = lean_mk_empty_array_with_capacity(v___x_1413_);
v___x_1415_ = lean_box(0);
v___x_1416_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1412_, v___x_1415_);
if (lean_obj_tag(v___x_1416_) == 0)
{
return v_result_1414_;
}
else
{
lean_object* v_val_1417_; lean_object* v_vs_1418_; lean_object* v___x_1419_; 
v_val_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_val_1417_);
lean_dec_ref(v___x_1416_);
v_vs_1418_ = lean_ctor_get(v_val_1417_, 0);
lean_inc_ref(v_vs_1418_);
lean_dec(v_val_1417_);
v___x_1419_ = l_Array_append___redArg(v_result_1414_, v_vs_1418_);
lean_dec_ref(v_vs_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1420_, lean_object* v_d_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1424_, v_x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1427_, v_x_1428_, v_x_1429_);
lean_dec(v_x_1429_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1431_, lean_object* v_x_1432_, size_t v_x_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1432_, v_x_1433_, v_x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_){
_start:
{
size_t v_x_281__boxed_1440_; lean_object* v_res_1441_; 
v_x_281__boxed_1440_ = lean_unbox_usize(v_x_1438_);
lean_dec(v_x_1438_);
v_res_1441_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1436_, v_x_1437_, v_x_281__boxed_1440_, v_x_1439_);
lean_dec(v_x_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1442_, lean_object* v_keys_1443_, lean_object* v_vals_1444_, lean_object* v_heq_1445_, lean_object* v_i_1446_, lean_object* v_k_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1443_, v_vals_1444_, v_i_1446_, v_k_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1449_, lean_object* v_keys_1450_, lean_object* v_vals_1451_, lean_object* v_heq_1452_, lean_object* v_i_1453_, lean_object* v_k_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1449_, v_keys_1450_, v_vals_1451_, v_heq_1452_, v_i_1453_, v_k_1454_);
lean_dec(v_k_1454_);
lean_dec_ref(v_vals_1451_);
lean_dec_ref(v_keys_1450_);
return v_res_1455_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object* v_a_1456_, lean_object* v_b_1457_){
_start:
{
lean_object* v_fst_1458_; lean_object* v_fst_1459_; uint8_t v___x_1460_; 
v_fst_1458_ = lean_ctor_get(v_a_1456_, 0);
v_fst_1459_ = lean_ctor_get(v_b_1457_, 0);
v___x_1460_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1458_, v_fst_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object* v_a_1461_, lean_object* v_b_1462_){
_start:
{
uint8_t v_res_1463_; lean_object* v_r_1464_; 
v_res_1463_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1461_, v_b_1462_);
lean_dec_ref(v_b_1462_);
lean_dec_ref(v_a_1461_);
v_r_1464_ = lean_box(v_res_1463_);
return v_r_1464_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1471_, lean_object* v_k_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_array_get_size(v_cs_1471_);
v___x_1475_ = lean_nat_dec_lt(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_dec(v_k_1472_);
v___x_1476_ = lean_box(0);
return v___x_1476_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_sub(v___x_1474_, v___x_1477_);
v___x_1479_ = lean_nat_dec_le(v___x_1473_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_dec(v___x_1478_);
lean_dec(v_k_1472_);
v___x_1480_ = lean_box(0);
return v___x_1480_;
}
else
{
lean_object* v___f_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___f_1481_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1482_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_k_1472_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1485_ = l_Array_binSearchAux___redArg(v___f_1481_, v___x_1484_, v_cs_1471_, v___x_1483_, v___x_1473_, v___x_1478_);
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1486_, lean_object* v_k_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1486_, v_k_1487_);
lean_dec_ref(v_cs_1486_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1489_, lean_object* v_cs_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_array_get_size(v_cs_1490_);
v___x_1494_ = lean_nat_dec_lt(v___x_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v_k_1491_);
v___x_1495_ = lean_box(0);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_sub(v___x_1493_, v___x_1496_);
v___x_1498_ = lean_nat_dec_le(v___x_1492_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v___x_1497_);
lean_dec(v_k_1491_);
v___x_1499_ = lean_box(0);
return v___x_1499_;
}
else
{
lean_object* v___f_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___f_1500_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1501_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_k_1491_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1504_ = l_Array_binSearchAux___redArg(v___f_1500_, v___x_1503_, v_cs_1490_, v___x_1502_, v___x_1492_, v___x_1497_);
return v___x_1504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_cs_1506_, lean_object* v_k_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1505_, v_cs_1506_, v_k_1507_);
lean_dec_ref(v_cs_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1509_, lean_object* v_k_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_m_1515_; lean_object* v_a_1516_; uint8_t v___x_1517_; 
v___x_1513_ = lean_nat_add(v_x_1511_, v_x_1512_);
v___x_1514_ = lean_unsigned_to_nat(1u);
v_m_1515_ = lean_nat_shiftr(v___x_1513_, v___x_1514_);
lean_dec(v___x_1513_);
v_a_1516_ = lean_array_fget_borrowed(v_as_1509_, v_m_1515_);
v___x_1517_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1516_, v_k_1510_);
if (v___x_1517_ == 0)
{
uint8_t v___x_1518_; 
lean_dec(v_x_1512_);
v___x_1518_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1510_, v_a_1516_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_dec(v_m_1515_);
lean_dec(v_x_1511_);
lean_inc(v_a_1516_);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_a_1516_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = lean_nat_dec_eq(v_m_1515_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = lean_nat_sub(v_m_1515_, v___x_1514_);
lean_dec(v_m_1515_);
v___x_1523_ = lean_nat_dec_lt(v___x_1522_, v_x_1511_);
if (v___x_1523_ == 0)
{
v_x_1512_ = v___x_1522_;
goto _start;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v___x_1522_);
lean_dec(v_x_1511_);
v___x_1525_ = lean_box(0);
return v___x_1525_;
}
}
else
{
lean_object* v___x_1526_; 
lean_dec(v_m_1515_);
lean_dec(v_x_1511_);
v___x_1526_ = lean_box(0);
return v___x_1526_;
}
}
}
else
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
lean_dec(v_x_1511_);
v___x_1527_ = lean_nat_add(v_m_1515_, v___x_1514_);
lean_dec(v_m_1515_);
v___x_1528_ = lean_nat_dec_le(v___x_1527_, v_x_1512_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec(v___x_1527_);
lean_dec(v_x_1512_);
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
else
{
v_x_1511_ = v___x_1527_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1531_, lean_object* v_k_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1531_, v_k_1532_, v_x_1533_, v_x_1534_);
lean_dec_ref(v_k_1532_);
lean_dec_ref(v_as_1531_);
return v_res_1535_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1540_, lean_object* v_c_1541_, lean_object* v_result_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_vs_1548_; lean_object* v_children_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_vs_1548_ = lean_ctor_get(v_c_1541_, 0);
lean_inc_ref(v_vs_1548_);
v_children_1549_ = lean_ctor_get(v_c_1541_, 1);
lean_inc_ref(v_children_1549_);
lean_dec_ref(v_c_1541_);
v___x_1550_ = lean_array_get_size(v_todo_1540_);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = lean_nat_dec_eq(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
lean_dec_ref(v_vs_1548_);
v___x_1553_ = lean_array_get_size(v_children_1549_);
v___x_1554_ = lean_nat_dec_eq(v___x_1553_, v___x_1551_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_e_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1555_ = l_Lean_instInhabitedExpr;
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_sub(v___x_1550_, v___x_1556_);
v_e_1558_ = lean_array_get_borrowed(v___x_1555_, v_todo_1540_, v___x_1557_);
lean_dec(v___x_1557_);
v___x_1559_ = 1;
lean_inc(v_e_1558_);
v___x_1560_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1558_, v___x_1559_, v___x_1554_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1598_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1598_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1598_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v_first_1569_; lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1597_; 
v_fst_1565_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_fst_1565_);
v_snd_1566_ = lean_ctor_get(v_a_1561_, 1);
lean_inc(v_snd_1566_);
lean_dec(v_a_1561_);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v_first_1569_ = lean_array_get(v___x_1568_, v_children_1549_, v___x_1551_);
v_fst_1570_ = lean_ctor_get(v_first_1569_, 0);
v_snd_1571_ = lean_ctor_get(v_first_1569_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_first_1569_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1573_ = v_first_1569_;
v_isShared_1574_ = v_isSharedCheck_1597_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_snd_1571_);
lean_inc(v_fst_1570_);
lean_dec(v_first_1569_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1597_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_todo_1575_; lean_object* v___y_1577_; lean_object* v_a_1578_; uint8_t v___x_1591_; 
v_todo_1575_ = lean_array_pop(v_todo_1540_);
v___x_1591_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1570_, v___x_1567_);
lean_dec(v_fst_1570_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1593_; 
lean_dec(v_snd_1571_);
lean_inc_ref(v_result_1542_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v_result_1542_);
v___x_1593_ = v___x_1563_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_result_1542_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
v___y_1577_ = v___x_1593_;
v_a_1578_ = v_result_1542_;
goto v___jp_1576_;
}
}
else
{
lean_object* v___x_1595_; 
lean_del_object(v___x_1563_);
lean_inc_ref(v_todo_1575_);
v___x_1595_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1575_, v_snd_1571_, v_result_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
v___y_1577_ = v___x_1595_;
v_a_1578_ = v_a_1596_;
goto v___jp_1576_;
}
else
{
lean_dec_ref(v_todo_1575_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1565_);
lean_dec_ref(v_children_1549_);
return v___x_1595_;
}
}
v___jp_1576_:
{
if (lean_obj_tag(v_fst_1565_) == 0)
{
lean_dec_ref(v_a_1578_);
lean_dec_ref(v_todo_1575_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1566_);
lean_dec_ref(v_children_1549_);
return v___y_1577_;
}
else
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_nat_dec_lt(v___x_1551_, v___x_1553_);
if (v___x_1579_ == 0)
{
lean_dec_ref(v_a_1578_);
lean_dec_ref(v_todo_1575_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1565_);
lean_dec_ref(v_children_1549_);
return v___y_1577_;
}
else
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = lean_nat_sub(v___x_1553_, v___x_1556_);
v___x_1581_ = lean_nat_dec_le(v___x_1551_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_dec(v___x_1580_);
lean_dec_ref(v_a_1578_);
lean_dec_ref(v_todo_1575_);
lean_del_object(v___x_1573_);
lean_dec(v_snd_1566_);
lean_dec(v_fst_1565_);
lean_dec_ref(v_children_1549_);
return v___y_1577_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1582_);
lean_ctor_set(v___x_1573_, 0, v_fst_1565_);
v___x_1584_ = v___x_1573_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_fst_1565_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1549_, v___x_1584_, v___x_1551_, v___x_1580_);
lean_dec_ref(v___x_1584_);
lean_dec_ref(v_children_1549_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_dec_ref(v_a_1578_);
lean_dec_ref(v_todo_1575_);
lean_dec(v_snd_1566_);
return v___y_1577_;
}
else
{
lean_object* v_val_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; 
lean_dec_ref(v___y_1577_);
v_val_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_val_1586_);
lean_dec_ref(v___x_1585_);
v_snd_1587_ = lean_ctor_get(v_val_1586_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_val_1586_);
v___x_1588_ = l_Array_append___redArg(v_todo_1575_, v_snd_1566_);
lean_dec(v_snd_1566_);
v_todo_1540_ = v___x_1588_;
v_c_1541_ = v_snd_1587_;
v_result_1542_ = v_a_1578_;
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
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v_children_1549_);
lean_dec_ref(v_result_1542_);
lean_dec_ref(v_todo_1540_);
v_a_1599_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1560_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1560_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v___x_1607_; 
lean_dec_ref(v_children_1549_);
lean_dec_ref(v_todo_1540_);
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_result_1542_);
return v___x_1607_;
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v_children_1549_);
lean_dec_ref(v_todo_1540_);
v___x_1608_ = l_Array_append___redArg(v_result_1542_, v_vs_1548_);
lean_dec_ref(v_vs_1548_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1610_, lean_object* v_c_1611_, lean_object* v_result_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1610_, v_c_1611_, v_result_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1619_, lean_object* v_todo_1620_, lean_object* v_c_1621_, lean_object* v_result_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1620_, v_c_1621_, v_result_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1629_, lean_object* v_todo_1630_, lean_object* v_c_1631_, lean_object* v_result_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1629_, v_todo_1630_, v_c_1631_, v_result_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1639_, lean_object* v_as_1640_, lean_object* v_k_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1640_, v_k_1641_, v_x_1642_, v_x_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1646_, lean_object* v_as_1647_, lean_object* v_k_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1646_, v_as_1647_, v_k_1648_, v_x_1649_, v_x_1650_, v_x_1651_);
lean_dec_ref(v_k_1648_);
lean_dec_ref(v_as_1647_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1653_, lean_object* v_k_1654_, lean_object* v_args_1655_, lean_object* v_result_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1653_, v_k_1654_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref(v_args_1655_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_result_1656_);
return v___x_1663_;
}
else
{
lean_object* v_val_1664_; lean_object* v___x_1665_; 
v_val_1664_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1664_);
lean_dec_ref(v___x_1662_);
v___x_1665_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1655_, v_val_1664_, v_result_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1666_, lean_object* v_k_1667_, lean_object* v_args_1668_, lean_object* v_result_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1666_, v_k_1667_, v_args_1668_, v_result_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_k_1667_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1676_, lean_object* v_d_1677_, lean_object* v_k_1678_, lean_object* v_args_1679_, lean_object* v_result_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1677_, v_k_1678_, v_args_1679_, v_result_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1687_, lean_object* v_d_1688_, lean_object* v_k_1689_, lean_object* v_args_1690_, lean_object* v_result_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1687_, v_d_1688_, v_k_1689_, v_args_1690_, v_result_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_k_1689_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1698_, lean_object* v_e_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; uint8_t v_foApprox_1706_; uint8_t v_ctxApprox_1707_; uint8_t v_quasiPatternApprox_1708_; uint8_t v_constApprox_1709_; uint8_t v_isDefEqStuckEx_1710_; uint8_t v_unificationHints_1711_; uint8_t v_proofIrrelevance_1712_; uint8_t v_assignSyntheticOpaque_1713_; uint8_t v_offsetCnstrs_1714_; uint8_t v_etaStruct_1715_; uint8_t v_univApprox_1716_; uint8_t v_iota_1717_; uint8_t v_beta_1718_; uint8_t v_proj_1719_; uint8_t v_zeta_1720_; uint8_t v_zetaDelta_1721_; uint8_t v_zetaUnused_1722_; uint8_t v_zetaHave_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1797_; 
v___x_1705_ = l_Lean_Meta_Context_config(v_a_1700_);
v_foApprox_1706_ = lean_ctor_get_uint8(v___x_1705_, 0);
v_ctxApprox_1707_ = lean_ctor_get_uint8(v___x_1705_, 1);
v_quasiPatternApprox_1708_ = lean_ctor_get_uint8(v___x_1705_, 2);
v_constApprox_1709_ = lean_ctor_get_uint8(v___x_1705_, 3);
v_isDefEqStuckEx_1710_ = lean_ctor_get_uint8(v___x_1705_, 4);
v_unificationHints_1711_ = lean_ctor_get_uint8(v___x_1705_, 5);
v_proofIrrelevance_1712_ = lean_ctor_get_uint8(v___x_1705_, 6);
v_assignSyntheticOpaque_1713_ = lean_ctor_get_uint8(v___x_1705_, 7);
v_offsetCnstrs_1714_ = lean_ctor_get_uint8(v___x_1705_, 8);
v_etaStruct_1715_ = lean_ctor_get_uint8(v___x_1705_, 10);
v_univApprox_1716_ = lean_ctor_get_uint8(v___x_1705_, 11);
v_iota_1717_ = lean_ctor_get_uint8(v___x_1705_, 12);
v_beta_1718_ = lean_ctor_get_uint8(v___x_1705_, 13);
v_proj_1719_ = lean_ctor_get_uint8(v___x_1705_, 14);
v_zeta_1720_ = lean_ctor_get_uint8(v___x_1705_, 15);
v_zetaDelta_1721_ = lean_ctor_get_uint8(v___x_1705_, 16);
v_zetaUnused_1722_ = lean_ctor_get_uint8(v___x_1705_, 17);
v_zetaHave_1723_ = lean_ctor_get_uint8(v___x_1705_, 18);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1725_ = v___x_1705_;
v_isShared_1726_ = v_isSharedCheck_1797_;
goto v_resetjp_1724_;
}
else
{
lean_dec(v___x_1705_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1797_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v_trackZetaDelta_1727_; lean_object* v_zetaDeltaSet_1728_; lean_object* v_lctx_1729_; lean_object* v_localInstances_1730_; lean_object* v_defEqCtx_x3f_1731_; lean_object* v_synthPendingDepth_1732_; lean_object* v_canUnfold_x3f_1733_; uint8_t v_univApprox_1734_; uint8_t v_inTypeClassResolution_1735_; uint8_t v_cacheInferType_1736_; uint8_t v___x_1737_; lean_object* v_config_1739_; 
v_trackZetaDelta_1727_ = lean_ctor_get_uint8(v_a_1700_, sizeof(void*)*7);
v_zetaDeltaSet_1728_ = lean_ctor_get(v_a_1700_, 1);
v_lctx_1729_ = lean_ctor_get(v_a_1700_, 2);
v_localInstances_1730_ = lean_ctor_get(v_a_1700_, 3);
v_defEqCtx_x3f_1731_ = lean_ctor_get(v_a_1700_, 4);
v_synthPendingDepth_1732_ = lean_ctor_get(v_a_1700_, 5);
v_canUnfold_x3f_1733_ = lean_ctor_get(v_a_1700_, 6);
v_univApprox_1734_ = lean_ctor_get_uint8(v_a_1700_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1735_ = lean_ctor_get_uint8(v_a_1700_, sizeof(void*)*7 + 2);
v_cacheInferType_1736_ = lean_ctor_get_uint8(v_a_1700_, sizeof(void*)*7 + 3);
v___x_1737_ = 2;
if (v_isShared_1726_ == 0)
{
v_config_1739_ = v___x_1725_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 0, v_foApprox_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 1, v_ctxApprox_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 2, v_quasiPatternApprox_1708_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 3, v_constApprox_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 4, v_isDefEqStuckEx_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 5, v_unificationHints_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 6, v_proofIrrelevance_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 7, v_assignSyntheticOpaque_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 8, v_offsetCnstrs_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 10, v_etaStruct_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 11, v_univApprox_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 12, v_iota_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 13, v_beta_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 14, v_proj_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 15, v_zeta_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 16, v_zetaDelta_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 17, v_zetaUnused_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, 18, v_zetaHave_1723_);
v_config_1739_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
uint64_t v___x_1740_; uint64_t v___x_1741_; uint64_t v___x_1742_; uint8_t v___x_1743_; uint64_t v___x_1744_; uint64_t v___x_1745_; uint64_t v_key_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_ctor_set_uint8(v_config_1739_, 9, v___x_1737_);
v___x_1740_ = l_Lean_Meta_Context_configKey(v_a_1700_);
v___x_1741_ = 2ULL;
v___x_1742_ = lean_uint64_shift_right(v___x_1740_, v___x_1741_);
v___x_1743_ = 1;
v___x_1744_ = lean_uint64_shift_left(v___x_1742_, v___x_1741_);
v___x_1745_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_1746_ = lean_uint64_lor(v___x_1744_, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1747_, 0, v_config_1739_);
lean_ctor_set_uint64(v___x_1747_, sizeof(void*)*1, v_key_1746_);
lean_inc(v_canUnfold_x3f_1733_);
lean_inc(v_synthPendingDepth_1732_);
lean_inc(v_defEqCtx_x3f_1731_);
lean_inc_ref(v_localInstances_1730_);
lean_inc_ref(v_lctx_1729_);
lean_inc(v_zetaDeltaSet_1728_);
v___x_1748_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_zetaDeltaSet_1728_);
lean_ctor_set(v___x_1748_, 2, v_lctx_1729_);
lean_ctor_set(v___x_1748_, 3, v_localInstances_1730_);
lean_ctor_set(v___x_1748_, 4, v_defEqCtx_x3f_1731_);
lean_ctor_set(v___x_1748_, 5, v_synthPendingDepth_1732_);
lean_ctor_set(v___x_1748_, 6, v_canUnfold_x3f_1733_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*7, v_trackZetaDelta_1727_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*7 + 1, v_univApprox_1734_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1735_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*7 + 3, v_cacheInferType_1736_);
v___x_1749_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1699_, v___x_1743_, v___x_1743_, v___x_1748_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1787_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1787_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1787_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_fst_1754_; lean_object* v_snd_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1786_; 
v_fst_1754_ = lean_ctor_get(v_a_1750_, 0);
v_snd_1755_ = lean_ctor_get(v_a_1750_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_a_1750_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1757_ = v_a_1750_;
v_isShared_1758_ = v_isSharedCheck_1786_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_snd_1755_);
lean_inc(v_fst_1754_);
lean_dec(v_a_1750_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1786_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_result_1759_; 
lean_inc_ref(v_d_1698_);
v_result_1759_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1698_);
if (lean_obj_tag(v_fst_1754_) == 0)
{
lean_object* v___x_1761_; 
lean_dec(v_snd_1755_);
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_d_1698_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v_result_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_fst_1754_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_result_1759_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1761_);
v___x_1763_ = v___x_1752_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
lean_object* v___x_1766_; 
lean_del_object(v___x_1752_);
v___x_1766_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1698_, v_fst_1754_, v_snd_1755_, v_result_1759_, v___x_1748_, v_a_1701_, v_a_1702_, v_a_1703_);
lean_dec_ref(v___x_1748_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1777_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v_a_1767_);
v___x_1772_ = v___x_1757_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_fst_1754_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1772_);
v___x_1774_ = v___x_1769_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_del_object(v___x_1757_);
lean_dec(v_fst_1754_);
v_a_1778_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1766_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1766_);
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
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v___x_1748_);
lean_dec_ref(v_d_1698_);
v_a_1788_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1749_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1749_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1798_, lean_object* v_e_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1798_, v_e_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1806_, lean_object* v_d_1807_, lean_object* v_e_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1807_, v_e_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_d_1816_, lean_object* v_e_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1815_, v_d_1816_, v_e_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1824_, lean_object* v_e_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1824_, v_e_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1840_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_snd_1836_; lean_object* v___x_1838_; 
v_snd_1836_ = lean_ctor_get(v_a_1832_, 1);
lean_inc(v_snd_1836_);
lean_dec(v_a_1832_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_snd_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_snd_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1831_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1831_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1849_, lean_object* v_e_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1849_, v_e_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1857_, lean_object* v_d_1858_, lean_object* v_e_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1858_, v_e_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_d_1867_, lean_object* v_e_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1866_, v_d_1867_, v_e_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1875_, lean_object* v_k_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_k_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; 
switch(lean_obj_tag(v_k_1876_))
{
case 4:
{
lean_object* v_a_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1916_; 
v_a_1904_ = lean_ctor_get(v_k_1876_, 0);
v_a_1905_ = lean_ctor_get(v_k_1876_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_k_1876_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1907_ = v_k_1876_;
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_inc(v_a_1904_);
lean_dec(v_k_1876_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_zero_1909_; uint8_t v_isZero_1910_; 
v_zero_1909_ = lean_unsigned_to_nat(0u);
v_isZero_1910_ = lean_nat_dec_eq(v_a_1905_, v_zero_1909_);
if (v_isZero_1910_ == 0)
{
lean_object* v_one_1911_; lean_object* v_n_1912_; lean_object* v___x_1914_; 
v_one_1911_ = lean_unsigned_to_nat(1u);
v_n_1912_ = lean_nat_sub(v_a_1905_, v_one_1911_);
lean_dec(v_a_1905_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v_n_1912_);
v___x_1914_ = v___x_1907_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1904_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_n_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
v_k_1887_ = v___x_1914_;
v___y_1888_ = v_a_1877_;
v___y_1889_ = v_a_1878_;
v___y_1890_ = v_a_1879_;
v___y_1891_ = v_a_1880_;
goto v___jp_1886_;
}
}
else
{
lean_del_object(v___x_1907_);
lean_dec(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_d_1875_);
goto v___jp_1882_;
}
}
}
case 3:
{
lean_object* v_a_1917_; lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1929_; 
v_a_1917_ = lean_ctor_get(v_k_1876_, 0);
v_a_1918_ = lean_ctor_get(v_k_1876_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_k_1876_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1920_ = v_k_1876_;
v_isShared_1921_ = v_isSharedCheck_1929_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_inc(v_a_1917_);
lean_dec(v_k_1876_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1929_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_zero_1922_; uint8_t v_isZero_1923_; 
v_zero_1922_ = lean_unsigned_to_nat(0u);
v_isZero_1923_ = lean_nat_dec_eq(v_a_1918_, v_zero_1922_);
if (v_isZero_1923_ == 0)
{
lean_object* v_one_1924_; lean_object* v_n_1925_; lean_object* v___x_1927_; 
v_one_1924_ = lean_unsigned_to_nat(1u);
v_n_1925_ = lean_nat_sub(v_a_1918_, v_one_1924_);
lean_dec(v_a_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v_n_1925_);
v___x_1927_ = v___x_1920_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1917_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_n_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v_k_1887_ = v___x_1927_;
v___y_1888_ = v_a_1877_;
v___y_1889_ = v_a_1878_;
v___y_1890_ = v_a_1879_;
v___y_1891_ = v_a_1880_;
goto v___jp_1886_;
}
}
else
{
lean_del_object(v___x_1920_);
lean_dec(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_d_1875_);
goto v___jp_1882_;
}
}
}
case 6:
{
lean_object* v_a_1930_; lean_object* v_a_1931_; lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1943_; 
v_a_1930_ = lean_ctor_get(v_k_1876_, 0);
v_a_1931_ = lean_ctor_get(v_k_1876_, 1);
v_a_1932_ = lean_ctor_get(v_k_1876_, 2);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_k_1876_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1934_ = v_k_1876_;
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_inc(v_a_1931_);
lean_inc(v_a_1930_);
lean_dec(v_k_1876_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_zero_1936_; uint8_t v_isZero_1937_; 
v_zero_1936_ = lean_unsigned_to_nat(0u);
v_isZero_1937_ = lean_nat_dec_eq(v_a_1932_, v_zero_1936_);
if (v_isZero_1937_ == 0)
{
lean_object* v_one_1938_; lean_object* v_n_1939_; lean_object* v___x_1941_; 
v_one_1938_ = lean_unsigned_to_nat(1u);
v_n_1939_ = lean_nat_sub(v_a_1932_, v_one_1938_);
lean_dec(v_a_1932_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 2, v_n_1939_);
v___x_1941_ = v___x_1934_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1930_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_a_1931_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_n_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
v_k_1887_ = v___x_1941_;
v___y_1888_ = v_a_1877_;
v___y_1889_ = v_a_1878_;
v___y_1890_ = v_a_1879_;
v___y_1891_ = v_a_1880_;
goto v___jp_1886_;
}
}
else
{
lean_del_object(v___x_1934_);
lean_dec(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_d_1875_);
goto v___jp_1882_;
}
}
}
default: 
{
lean_dec(v_k_1876_);
lean_dec_ref(v_d_1875_);
goto v___jp_1882_;
}
}
v___jp_1882_:
{
uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = 0;
v___x_1884_ = lean_box(v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
v___jp_1886_:
{
lean_object* v___x_1892_; 
lean_inc_ref(v_d_1875_);
v___x_1892_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1875_, v_k_1887_);
if (lean_obj_tag(v___x_1892_) == 0)
{
v_k_1876_ = v_k_1887_;
v_a_1877_ = v___y_1888_;
v_a_1878_ = v___y_1889_;
v_a_1879_ = v___y_1890_;
v_a_1880_ = v___y_1891_;
goto _start;
}
else
{
lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_k_1887_);
lean_dec_ref(v_d_1875_);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1892_, 0);
lean_dec(v_unused_1903_);
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
else
{
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
uint8_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1897_ = 1;
v___x_1898_ = lean_box(v___x_1897_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_1944_, lean_object* v_k_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1944_, v_k_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_1952_, lean_object* v_d_1953_, lean_object* v_k_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1953_, v_k_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_d_1962_, lean_object* v_k_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_1961_, v_d_1962_, v_k_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_1970_, size_t v_sz_1971_, size_t v_i_1972_, lean_object* v_bs_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_lt(v_i_1972_, v_sz_1971_);
if (v___x_1974_ == 0)
{
lean_dec(v_numExtra_1970_);
return v_bs_1973_;
}
else
{
lean_object* v_v_1975_; lean_object* v___x_1976_; lean_object* v_bs_x27_1977_; lean_object* v___x_1978_; size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v_v_1975_ = lean_array_uget(v_bs_1973_, v_i_1972_);
v___x_1976_ = lean_unsigned_to_nat(0u);
v_bs_x27_1977_ = lean_array_uset(v_bs_1973_, v_i_1972_, v___x_1976_);
lean_inc(v_numExtra_1970_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v_v_1975_);
lean_ctor_set(v___x_1978_, 1, v_numExtra_1970_);
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_add(v_i_1972_, v___x_1979_);
v___x_1981_ = lean_array_uset(v_bs_x27_1977_, v_i_1972_, v___x_1978_);
v_i_1972_ = v___x_1980_;
v_bs_1973_ = v___x_1981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_1983_, lean_object* v_sz_1984_, lean_object* v_i_1985_, lean_object* v_bs_1986_){
_start:
{
size_t v_sz_boxed_1987_; size_t v_i_boxed_1988_; lean_object* v_res_1989_; 
v_sz_boxed_1987_ = lean_unbox_usize(v_sz_1984_);
lean_dec(v_sz_1984_);
v_i_boxed_1988_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1983_, v_sz_boxed_1987_, v_i_boxed_1988_, v_bs_1986_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_1990_, lean_object* v_e_1991_, lean_object* v_numExtra_1992_, lean_object* v_result_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___x_1999_; 
lean_inc_ref(v_e_1991_);
lean_inc_ref(v_d_1990_);
v___x_1999_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1990_, v_e_1991_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2017_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2017_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2017_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_snd_2004_; size_t v_sz_2005_; size_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_snd_2004_ = lean_ctor_get(v_a_2000_, 1);
lean_inc(v_snd_2004_);
lean_dec(v_a_2000_);
v_sz_2005_ = lean_array_size(v_snd_2004_);
v___x_2006_ = ((size_t)0ULL);
lean_inc(v_numExtra_1992_);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_1992_, v_sz_2005_, v___x_2006_, v_snd_2004_);
v___x_2008_ = l_Array_append___redArg(v_result_1993_, v___x_2007_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = l_Lean_Expr_isApp(v_e_1991_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2011_; 
lean_dec(v_numExtra_1992_);
lean_dec_ref(v_e_1991_);
lean_dec_ref(v_d_1990_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2008_);
v___x_2011_ = v___x_2002_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2008_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_del_object(v___x_2002_);
v___x_2013_ = l_Lean_Expr_appFn_x21(v_e_1991_);
lean_dec_ref(v_e_1991_);
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_nat_add(v_numExtra_1992_, v___x_2014_);
lean_dec(v_numExtra_1992_);
v_e_1991_ = v___x_2013_;
v_numExtra_1992_ = v___x_2015_;
v_result_1993_ = v___x_2008_;
goto _start;
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_result_1993_);
lean_dec(v_numExtra_1992_);
lean_dec_ref(v_e_1991_);
lean_dec_ref(v_d_1990_);
v_a_2018_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1999_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1999_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2026_, lean_object* v_e_2027_, lean_object* v_numExtra_2028_, lean_object* v_result_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2026_, v_e_2027_, v_numExtra_2028_, v_result_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2036_, lean_object* v_d_2037_, lean_object* v_e_2038_, lean_object* v_numExtra_2039_, lean_object* v_result_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2037_, v_e_2038_, v_numExtra_2039_, v_result_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2047_, lean_object* v_d_2048_, lean_object* v_e_2049_, lean_object* v_numExtra_2050_, lean_object* v_result_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2047_, v_d_2048_, v_e_2049_, v_numExtra_2050_, v_result_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2058_, lean_object* v_numExtra_2059_, size_t v_sz_2060_, size_t v_i_2061_, lean_object* v_bs_2062_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2059_, v_sz_2060_, v_i_2061_, v_bs_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2064_, lean_object* v_numExtra_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_bs_2068_){
_start:
{
size_t v_sz_boxed_2069_; size_t v_i_boxed_2070_; lean_object* v_res_2071_; 
v_sz_boxed_2069_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2070_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2064_, v_numExtra_2065_, v_sz_boxed_2069_, v_i_boxed_2070_, v_bs_2068_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2072_, size_t v_i_2073_, lean_object* v_bs_2074_){
_start:
{
uint8_t v___x_2075_; 
v___x_2075_ = lean_usize_dec_lt(v_i_2073_, v_sz_2072_);
if (v___x_2075_ == 0)
{
return v_bs_2074_;
}
else
{
lean_object* v_v_2076_; lean_object* v___x_2077_; lean_object* v_bs_x27_2078_; lean_object* v___x_2079_; size_t v___x_2080_; size_t v___x_2081_; lean_object* v___x_2082_; 
v_v_2076_ = lean_array_uget(v_bs_2074_, v_i_2073_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v_bs_x27_2078_ = lean_array_uset(v_bs_2074_, v_i_2073_, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v_v_2076_);
lean_ctor_set(v___x_2079_, 1, v___x_2077_);
v___x_2080_ = ((size_t)1ULL);
v___x_2081_ = lean_usize_add(v_i_2073_, v___x_2080_);
v___x_2082_ = lean_array_uset(v_bs_x27_2078_, v_i_2073_, v___x_2079_);
v_i_2073_ = v___x_2081_;
v_bs_2074_ = v___x_2082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2084_, lean_object* v_i_2085_, lean_object* v_bs_2086_){
_start:
{
size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2084_);
lean_dec(v_sz_2084_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2085_);
lean_dec(v_i_2085_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2087_, v_i_boxed_2088_, v_bs_2086_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2090_, lean_object* v_e_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2097_; 
lean_inc_ref(v_e_2091_);
lean_inc_ref(v_d_2090_);
v___x_2097_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2090_, v_e_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2132_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2132_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2132_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_fst_2102_; lean_object* v_snd_2103_; size_t v_sz_2104_; size_t v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_fst_2102_ = lean_ctor_get(v_a_2098_, 0);
lean_inc(v_fst_2102_);
v_snd_2103_ = lean_ctor_get(v_a_2098_, 1);
lean_inc(v_snd_2103_);
lean_dec(v_a_2098_);
v_sz_2104_ = lean_array_size(v_snd_2103_);
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2104_, v___x_2105_, v_snd_2103_);
v___x_2107_ = l_Lean_Expr_isApp(v_e_2091_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2109_; 
lean_dec(v_fst_2102_);
lean_dec_ref(v_e_2091_);
lean_dec_ref(v_d_2090_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2106_);
v___x_2109_ = v___x_2100_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2106_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
else
{
lean_object* v___x_2111_; 
lean_del_object(v___x_2100_);
lean_inc_ref(v_d_2090_);
v___x_2111_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2090_, v_fst_2102_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2123_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2123_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2123_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_unbox(v_a_2112_);
lean_dec(v_a_2112_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref(v_e_2091_);
lean_dec_ref(v_d_2090_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2106_);
v___x_2118_ = v___x_2114_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2106_);
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
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_del_object(v___x_2114_);
v___x_2120_ = l_Lean_Expr_appFn_x21(v_e_2091_);
lean_dec_ref(v_e_2091_);
v___x_2121_ = lean_unsigned_to_nat(1u);
v___x_2122_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2090_, v___x_2120_, v___x_2121_, v___x_2106_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
return v___x_2122_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v___x_2106_);
lean_dec_ref(v_e_2091_);
lean_dec_ref(v_d_2090_);
v_a_2124_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2111_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2111_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_e_2091_);
lean_dec_ref(v_d_2090_);
v_a_2133_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2097_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2097_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2141_, lean_object* v_e_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2141_, v_e_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2149_, lean_object* v_d_2150_, lean_object* v_e_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2150_, v_e_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_d_2159_, lean_object* v_e_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2158_, v_d_2159_, v_e_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2167_, size_t v_sz_2168_, size_t v_i_2169_, lean_object* v_bs_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2168_, v_i_2169_, v_bs_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2172_, lean_object* v_sz_2173_, lean_object* v_i_2174_, lean_object* v_bs_2175_){
_start:
{
size_t v_sz_boxed_2176_; size_t v_i_boxed_2177_; lean_object* v_res_2178_; 
v_sz_boxed_2176_ = lean_unbox_usize(v_sz_2173_);
lean_dec(v_sz_2173_);
v_i_boxed_2177_ = lean_unbox_usize(v_i_2174_);
lean_dec(v_i_2174_);
v_res_2178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2172_, v_sz_boxed_2176_, v_i_boxed_2177_, v_bs_2175_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
uint8_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = 1;
v___x_2186_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2179_, v___x_2185_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2211_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2211_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2211_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___y_2193_; lean_object* v___x_2198_; 
v___x_2191_ = l_Lean_Expr_getAppNumArgs(v_a_2187_);
v___x_2198_ = l_Lean_Expr_getAppFn(v_a_2187_);
lean_dec(v_a_2187_);
switch(lean_obj_tag(v___x_2198_))
{
case 9:
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_ref(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_a_2199_);
v___y_2193_ = v___x_2200_;
goto v___jp_2192_;
}
case 1:
{
lean_object* v_fvarId_2201_; lean_object* v___x_2202_; 
v_fvarId_2201_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_fvarId_2201_);
lean_dec_ref(v___x_2198_);
lean_inc(v___x_2191_);
v___x_2202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_fvarId_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2191_);
v___y_2193_ = v___x_2202_;
goto v___jp_2192_;
}
case 2:
{
lean_object* v___x_2203_; 
lean_dec_ref(v___x_2198_);
v___x_2203_ = lean_box(1);
v___y_2193_ = v___x_2203_;
goto v___jp_2192_;
}
case 11:
{
lean_object* v_typeName_2204_; lean_object* v_idx_2205_; lean_object* v___x_2206_; 
v_typeName_2204_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_typeName_2204_);
v_idx_2205_ = lean_ctor_get(v___x_2198_, 1);
lean_inc(v_idx_2205_);
lean_dec_ref(v___x_2198_);
lean_inc(v___x_2191_);
v___x_2206_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2206_, 0, v_typeName_2204_);
lean_ctor_set(v___x_2206_, 1, v_idx_2205_);
lean_ctor_set(v___x_2206_, 2, v___x_2191_);
v___y_2193_ = v___x_2206_;
goto v___jp_2192_;
}
case 7:
{
lean_object* v___x_2207_; 
lean_dec_ref(v___x_2198_);
v___x_2207_ = lean_box(5);
v___y_2193_ = v___x_2207_;
goto v___jp_2192_;
}
case 4:
{
lean_object* v_declName_2208_; lean_object* v___x_2209_; 
v_declName_2208_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_declName_2208_);
lean_dec_ref(v___x_2198_);
lean_inc(v___x_2191_);
v___x_2209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_declName_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2191_);
v___y_2193_ = v___x_2209_;
goto v___jp_2192_;
}
default: 
{
lean_object* v___x_2210_; 
lean_dec_ref(v___x_2198_);
v___x_2210_ = lean_box(1);
v___y_2193_ = v___x_2210_;
goto v___jp_2192_;
}
}
v___jp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___y_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2191_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2194_);
v___x_2196_ = v___x_2189_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2212_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2186_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2186_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2227_, size_t v_sz_2228_, size_t v_i_2229_, lean_object* v_b_2230_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_usize_dec_lt(v_i_2229_, v_sz_2228_);
if (v___x_2231_ == 0)
{
return v_b_2230_;
}
else
{
lean_object* v_a_2232_; lean_object* v_snd_2233_; lean_object* v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; 
v_a_2232_ = lean_array_uget_borrowed(v_as_2227_, v_i_2229_);
v_snd_2233_ = lean_ctor_get(v_a_2232_, 1);
v___x_2234_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2233_, v_b_2230_);
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_add(v_i_2229_, v___x_2235_);
v_i_2229_ = v___x_2236_;
v_b_2230_ = v___x_2234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2238_, lean_object* v_result_2239_){
_start:
{
lean_object* v_vs_2240_; lean_object* v_children_2241_; lean_object* v_result_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v_vs_2240_ = lean_ctor_get(v_trie_2238_, 0);
v_children_2241_ = lean_ctor_get(v_trie_2238_, 1);
v_result_2242_ = l_Array_append___redArg(v_result_2239_, v_vs_2240_);
v_sz_2243_ = lean_array_size(v_children_2241_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2241_, v_sz_2243_, v___x_2244_, v_result_2242_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2246_, lean_object* v_result_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2246_, v_result_2247_);
lean_dec_ref(v_trie_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2249_, lean_object* v_sz_2250_, lean_object* v_i_2251_, lean_object* v_b_2252_){
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2250_);
lean_dec(v_sz_2250_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2249_, v_sz_boxed_2253_, v_i_boxed_2254_, v_b_2252_);
lean_dec_ref(v_as_2249_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2256_, lean_object* v_trie_2257_, lean_object* v_result_2258_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2257_, v_result_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2260_, lean_object* v_trie_2261_, lean_object* v_result_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2260_, v_trie_2261_, v_result_2262_);
lean_dec_ref(v_trie_2261_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2264_, lean_object* v_as_2265_, size_t v_sz_2266_, size_t v_i_2267_, lean_object* v_b_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2265_, v_sz_2266_, v_i_2267_, v_b_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_as_2271_, lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_b_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2270_, v_as_2271_, v_sz_boxed_2275_, v_i_boxed_2276_, v_b_2274_);
lean_dec_ref(v_as_2271_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2278_, lean_object* v_k_2279_, lean_object* v_result_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2278_, v_k_2279_);
if (lean_obj_tag(v___x_2281_) == 0)
{
return v_result_2280_;
}
else
{
lean_object* v_val_2282_; lean_object* v___x_2283_; 
v_val_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_val_2282_);
lean_dec_ref(v___x_2281_);
v___x_2283_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2282_, v_result_2280_);
lean_dec(v_val_2282_);
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2284_, lean_object* v_k_2285_, lean_object* v_result_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2284_, v_k_2285_, v_result_2286_);
lean_dec(v_k_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2288_, lean_object* v_d_2289_, lean_object* v_k_2290_, lean_object* v_result_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2289_, v_k_2290_, v_result_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_d_2294_, lean_object* v_k_2295_, lean_object* v_result_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2293_, v_d_2294_, v_k_2295_, v_result_2296_);
lean_dec(v_k_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2298_, lean_object* v_e_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2305_; uint8_t v_foApprox_2306_; uint8_t v_ctxApprox_2307_; uint8_t v_quasiPatternApprox_2308_; uint8_t v_constApprox_2309_; uint8_t v_isDefEqStuckEx_2310_; uint8_t v_unificationHints_2311_; uint8_t v_proofIrrelevance_2312_; uint8_t v_assignSyntheticOpaque_2313_; uint8_t v_offsetCnstrs_2314_; uint8_t v_etaStruct_2315_; uint8_t v_univApprox_2316_; uint8_t v_iota_2317_; uint8_t v_beta_2318_; uint8_t v_proj_2319_; uint8_t v_zeta_2320_; uint8_t v_zetaDelta_2321_; uint8_t v_zetaUnused_2322_; uint8_t v_zetaHave_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2377_; 
v___x_2305_ = l_Lean_Meta_Context_config(v_a_2300_);
v_foApprox_2306_ = lean_ctor_get_uint8(v___x_2305_, 0);
v_ctxApprox_2307_ = lean_ctor_get_uint8(v___x_2305_, 1);
v_quasiPatternApprox_2308_ = lean_ctor_get_uint8(v___x_2305_, 2);
v_constApprox_2309_ = lean_ctor_get_uint8(v___x_2305_, 3);
v_isDefEqStuckEx_2310_ = lean_ctor_get_uint8(v___x_2305_, 4);
v_unificationHints_2311_ = lean_ctor_get_uint8(v___x_2305_, 5);
v_proofIrrelevance_2312_ = lean_ctor_get_uint8(v___x_2305_, 6);
v_assignSyntheticOpaque_2313_ = lean_ctor_get_uint8(v___x_2305_, 7);
v_offsetCnstrs_2314_ = lean_ctor_get_uint8(v___x_2305_, 8);
v_etaStruct_2315_ = lean_ctor_get_uint8(v___x_2305_, 10);
v_univApprox_2316_ = lean_ctor_get_uint8(v___x_2305_, 11);
v_iota_2317_ = lean_ctor_get_uint8(v___x_2305_, 12);
v_beta_2318_ = lean_ctor_get_uint8(v___x_2305_, 13);
v_proj_2319_ = lean_ctor_get_uint8(v___x_2305_, 14);
v_zeta_2320_ = lean_ctor_get_uint8(v___x_2305_, 15);
v_zetaDelta_2321_ = lean_ctor_get_uint8(v___x_2305_, 16);
v_zetaUnused_2322_ = lean_ctor_get_uint8(v___x_2305_, 17);
v_zetaHave_2323_ = lean_ctor_get_uint8(v___x_2305_, 18);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2325_ = v___x_2305_;
v_isShared_2326_ = v_isSharedCheck_2377_;
goto v_resetjp_2324_;
}
else
{
lean_dec(v___x_2305_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2377_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
uint8_t v_trackZetaDelta_2327_; lean_object* v_zetaDeltaSet_2328_; lean_object* v_lctx_2329_; lean_object* v_localInstances_2330_; lean_object* v_defEqCtx_x3f_2331_; lean_object* v_synthPendingDepth_2332_; lean_object* v_canUnfold_x3f_2333_; uint8_t v_univApprox_2334_; uint8_t v_inTypeClassResolution_2335_; uint8_t v_cacheInferType_2336_; uint8_t v___x_2337_; lean_object* v_config_2339_; 
v_trackZetaDelta_2327_ = lean_ctor_get_uint8(v_a_2300_, sizeof(void*)*7);
v_zetaDeltaSet_2328_ = lean_ctor_get(v_a_2300_, 1);
v_lctx_2329_ = lean_ctor_get(v_a_2300_, 2);
v_localInstances_2330_ = lean_ctor_get(v_a_2300_, 3);
v_defEqCtx_x3f_2331_ = lean_ctor_get(v_a_2300_, 4);
v_synthPendingDepth_2332_ = lean_ctor_get(v_a_2300_, 5);
v_canUnfold_x3f_2333_ = lean_ctor_get(v_a_2300_, 6);
v_univApprox_2334_ = lean_ctor_get_uint8(v_a_2300_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2335_ = lean_ctor_get_uint8(v_a_2300_, sizeof(void*)*7 + 2);
v_cacheInferType_2336_ = lean_ctor_get_uint8(v_a_2300_, sizeof(void*)*7 + 3);
v___x_2337_ = 2;
if (v_isShared_2326_ == 0)
{
v_config_2339_ = v___x_2325_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 0, v_foApprox_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 1, v_ctxApprox_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 2, v_quasiPatternApprox_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 3, v_constApprox_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 4, v_isDefEqStuckEx_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 5, v_unificationHints_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 6, v_proofIrrelevance_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 7, v_assignSyntheticOpaque_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 8, v_offsetCnstrs_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 10, v_etaStruct_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 11, v_univApprox_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 12, v_iota_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 13, v_beta_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 14, v_proj_2319_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 15, v_zeta_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 16, v_zetaDelta_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 17, v_zetaUnused_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2376_, 18, v_zetaHave_2323_);
v_config_2339_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
uint64_t v___x_2340_; uint64_t v___x_2341_; uint64_t v___x_2342_; uint64_t v___x_2343_; uint64_t v___x_2344_; uint64_t v_key_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_ctor_set_uint8(v_config_2339_, 9, v___x_2337_);
v___x_2340_ = l_Lean_Meta_Context_configKey(v_a_2300_);
v___x_2341_ = 2ULL;
v___x_2342_ = lean_uint64_shift_right(v___x_2340_, v___x_2341_);
v___x_2343_ = lean_uint64_shift_left(v___x_2342_, v___x_2341_);
v___x_2344_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2345_ = lean_uint64_lor(v___x_2343_, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2346_, 0, v_config_2339_);
lean_ctor_set_uint64(v___x_2346_, sizeof(void*)*1, v_key_2345_);
lean_inc(v_canUnfold_x3f_2333_);
lean_inc(v_synthPendingDepth_2332_);
lean_inc(v_defEqCtx_x3f_2331_);
lean_inc_ref(v_localInstances_2330_);
lean_inc_ref(v_lctx_2329_);
lean_inc(v_zetaDeltaSet_2328_);
v___x_2347_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
lean_ctor_set(v___x_2347_, 1, v_zetaDeltaSet_2328_);
lean_ctor_set(v___x_2347_, 2, v_lctx_2329_);
lean_ctor_set(v___x_2347_, 3, v_localInstances_2330_);
lean_ctor_set(v___x_2347_, 4, v_defEqCtx_x3f_2331_);
lean_ctor_set(v___x_2347_, 5, v_synthPendingDepth_2332_);
lean_ctor_set(v___x_2347_, 6, v_canUnfold_x3f_2333_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*7, v_trackZetaDelta_2327_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*7 + 1, v_univApprox_2334_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2335_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*7 + 3, v_cacheInferType_2336_);
v___x_2348_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2299_, v___x_2347_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec_ref(v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2367_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_fst_2353_; lean_object* v_snd_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2366_; 
v_fst_2353_ = lean_ctor_get(v_a_2349_, 0);
v_snd_2354_ = lean_ctor_get(v_a_2349_, 1);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_a_2349_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2356_ = v_a_2349_;
v_isShared_2357_ = v_isSharedCheck_2366_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_snd_2354_);
lean_inc(v_fst_2353_);
lean_dec(v_a_2349_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2366_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_result_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_inc_ref(v_d_2298_);
v_result_2358_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2298_);
v___x_2359_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2298_, v_fst_2353_, v_result_2358_);
lean_dec(v_fst_2353_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2359_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_snd_2354_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2361_);
v___x_2363_ = v___x_2351_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v_d_2298_);
v_a_2368_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2348_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2348_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2378_, lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2378_, v_e_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2386_, lean_object* v_d_2387_, lean_object* v_e_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2387_, v_e_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_d_2396_, lean_object* v_e_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2395_, v_d_2396_, v_e_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2404_, lean_object* v_todo_2405_, lean_object* v_as_2406_, size_t v_i_2407_, size_t v_stop_2408_, lean_object* v_b_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v___x_2415_; 
v___x_2415_ = lean_usize_dec_eq(v_i_2407_, v_stop_2408_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v_fst_2417_; lean_object* v_snd_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2416_ = lean_array_uget_borrowed(v_as_2406_, v_i_2407_);
v_fst_2417_ = lean_ctor_get(v___x_2416_, 0);
v_snd_2418_ = lean_ctor_get(v___x_2416_, 1);
v___x_2419_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2417_);
v___x_2420_ = lean_nat_add(v_n_2404_, v___x_2419_);
lean_dec(v___x_2419_);
lean_inc(v_snd_2418_);
lean_inc_ref(v_todo_2405_);
v___x_2421_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2420_, v_todo_2405_, v_snd_2418_, v_b_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; size_t v___x_2423_; size_t v___x_2424_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2421_);
v___x_2423_ = ((size_t)1ULL);
v___x_2424_ = lean_usize_add(v_i_2407_, v___x_2423_);
v_i_2407_ = v___x_2424_;
v_b_2409_ = v_a_2422_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2405_);
return v___x_2421_;
}
}
else
{
lean_object* v___x_2426_; 
lean_dec_ref(v_todo_2405_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_b_2409_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2427_, lean_object* v_todo_2428_, lean_object* v_c_2429_, lean_object* v_result_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_zero_2436_; uint8_t v_isZero_2437_; 
v_zero_2436_ = lean_unsigned_to_nat(0u);
v_isZero_2437_ = lean_nat_dec_eq(v_skip_2427_, v_zero_2436_);
if (v_isZero_2437_ == 1)
{
lean_object* v_vs_2438_; lean_object* v_children_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
lean_dec(v_skip_2427_);
v_vs_2438_ = lean_ctor_get(v_c_2429_, 0);
lean_inc_ref(v_vs_2438_);
v_children_2439_ = lean_ctor_get(v_c_2429_, 1);
lean_inc_ref(v_children_2439_);
lean_dec_ref(v_c_2429_);
v___x_2440_ = lean_array_get_size(v_todo_2428_);
v___x_2441_ = lean_nat_dec_eq(v___x_2440_, v_zero_2436_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; uint8_t v___x_2443_; 
lean_dec_ref(v_vs_2438_);
v___x_2442_ = lean_array_get_size(v_children_2439_);
v___x_2443_ = lean_nat_dec_eq(v___x_2442_, v_zero_2436_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_e_2447_; lean_object* v___x_2448_; 
v___x_2444_ = l_Lean_instInhabitedExpr;
v___x_2445_ = lean_unsigned_to_nat(1u);
v___x_2446_ = lean_nat_sub(v___x_2440_, v___x_2445_);
v_e_2447_ = lean_array_get_borrowed(v___x_2444_, v_todo_2428_, v___x_2446_);
lean_dec(v___x_2446_);
lean_inc(v_e_2447_);
v___x_2448_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2447_, v___x_2443_, v___x_2443_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2500_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2500_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2500_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2499_; 
v_fst_2453_ = lean_ctor_get(v_a_2449_, 0);
v_snd_2454_ = lean_ctor_get(v_a_2449_, 1);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_a_2449_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2456_ = v_a_2449_;
v_isShared_2457_ = v_isSharedCheck_2499_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_snd_2454_);
lean_inc(v_fst_2453_);
lean_dec(v_a_2449_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2499_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_todo_2458_; lean_object* v___y_2460_; lean_object* v_a_2461_; 
v_todo_2458_ = lean_array_pop(v_todo_2428_);
if (lean_obj_tag(v_fst_2453_) == 0)
{
uint8_t v___x_2474_; 
lean_del_object(v___x_2456_);
lean_dec(v_snd_2454_);
v___x_2474_ = lean_nat_dec_lt(v_zero_2436_, v___x_2442_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2476_; 
lean_dec_ref(v_todo_2458_);
lean_dec_ref(v_children_2439_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v_result_2430_);
v___x_2476_ = v___x_2451_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_result_2430_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
else
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_le(v___x_2442_, v___x_2442_);
if (v___x_2478_ == 0)
{
if (v___x_2474_ == 0)
{
lean_object* v___x_2480_; 
lean_dec_ref(v_todo_2458_);
lean_dec_ref(v_children_2439_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v_result_2430_);
v___x_2480_ = v___x_2451_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_result_2430_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
else
{
size_t v___x_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
lean_del_object(v___x_2451_);
v___x_2482_ = ((size_t)0ULL);
v___x_2483_ = lean_usize_of_nat(v___x_2442_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2458_, v_children_2439_, v___x_2482_, v___x_2483_, v_result_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v_children_2439_);
return v___x_2484_;
}
}
else
{
size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
lean_del_object(v___x_2451_);
v___x_2485_ = ((size_t)0ULL);
v___x_2486_ = lean_usize_of_nat(v___x_2442_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2458_, v_children_2439_, v___x_2485_, v___x_2486_, v_result_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v_children_2439_);
return v___x_2487_;
}
}
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v_fst_2491_; lean_object* v_snd_2492_; uint8_t v___x_2493_; 
v___x_2488_ = lean_box(0);
v___x_2489_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_2490_ = lean_array_get_borrowed(v___x_2489_, v_children_2439_, v_zero_2436_);
v_fst_2491_ = lean_ctor_get(v___x_2490_, 0);
v_snd_2492_ = lean_ctor_get(v___x_2490_, 1);
v___x_2493_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2491_, v___x_2488_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2495_; 
lean_inc_ref(v_result_2430_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v_result_2430_);
v___x_2495_ = v___x_2451_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_result_2430_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
v___y_2460_ = v___x_2495_;
v_a_2461_ = v_result_2430_;
goto v___jp_2459_;
}
}
else
{
lean_object* v___x_2497_; 
lean_del_object(v___x_2451_);
lean_inc(v_snd_2492_);
lean_inc_ref(v_todo_2458_);
v___x_2497_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2436_, v_todo_2458_, v_snd_2492_, v_result_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
v___y_2460_ = v___x_2497_;
v_a_2461_ = v_a_2498_;
goto v___jp_2459_;
}
else
{
lean_dec_ref(v_todo_2458_);
lean_del_object(v___x_2456_);
lean_dec(v_snd_2454_);
lean_dec(v_fst_2453_);
lean_dec_ref(v_children_2439_);
return v___x_2497_;
}
}
}
v___jp_2459_:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_nat_dec_lt(v_zero_2436_, v___x_2442_);
if (v___x_2462_ == 0)
{
lean_dec_ref(v_a_2461_);
lean_dec_ref(v_todo_2458_);
lean_del_object(v___x_2456_);
lean_dec(v_snd_2454_);
lean_dec(v_fst_2453_);
lean_dec_ref(v_children_2439_);
return v___y_2460_;
}
else
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = lean_nat_sub(v___x_2442_, v___x_2445_);
v___x_2464_ = lean_nat_dec_le(v_zero_2436_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec(v___x_2463_);
lean_dec_ref(v_a_2461_);
lean_dec_ref(v_todo_2458_);
lean_del_object(v___x_2456_);
lean_dec(v_snd_2454_);
lean_dec(v_fst_2453_);
lean_dec_ref(v_children_2439_);
return v___y_2460_;
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v___x_2465_);
v___x_2467_ = v___x_2456_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_fst_2453_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_2439_, v___x_2467_, v_zero_2436_, v___x_2463_);
lean_dec_ref(v___x_2467_);
lean_dec_ref(v_children_2439_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_dec_ref(v_a_2461_);
lean_dec_ref(v_todo_2458_);
lean_dec(v_snd_2454_);
return v___y_2460_;
}
else
{
lean_object* v_val_2469_; lean_object* v_snd_2470_; lean_object* v___x_2471_; 
lean_dec_ref(v___y_2460_);
v_val_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_val_2469_);
lean_dec_ref(v___x_2468_);
v_snd_2470_ = lean_ctor_get(v_val_2469_, 1);
lean_inc(v_snd_2470_);
lean_dec(v_val_2469_);
v___x_2471_ = l_Array_append___redArg(v_todo_2458_, v_snd_2454_);
lean_dec(v_snd_2454_);
v_skip_2427_ = v_zero_2436_;
v_todo_2428_ = v___x_2471_;
v_c_2429_ = v_snd_2470_;
v_result_2430_ = v_a_2461_;
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
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v_children_2439_);
lean_dec_ref(v_result_2430_);
lean_dec_ref(v_todo_2428_);
v_a_2501_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2448_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2448_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v___x_2509_; 
lean_dec_ref(v_children_2439_);
lean_dec_ref(v_todo_2428_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_result_2430_);
return v___x_2509_;
}
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec_ref(v_children_2439_);
lean_dec_ref(v_todo_2428_);
v___x_2510_ = l_Array_append___redArg(v_result_2430_, v_vs_2438_);
lean_dec_ref(v_vs_2438_);
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
return v___x_2511_;
}
}
else
{
lean_object* v_children_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v_children_2512_ = lean_ctor_get(v_c_2429_, 1);
lean_inc_ref(v_children_2512_);
lean_dec_ref(v_c_2429_);
v___x_2513_ = lean_array_get_size(v_children_2512_);
v___x_2514_ = lean_nat_dec_eq(v___x_2513_, v_zero_2436_);
if (v___x_2514_ == 0)
{
uint8_t v___x_2515_; 
v___x_2515_ = lean_nat_dec_lt(v_zero_2436_, v___x_2513_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; 
lean_dec_ref(v_children_2512_);
lean_dec_ref(v_todo_2428_);
lean_dec(v_skip_2427_);
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_result_2430_);
return v___x_2516_;
}
else
{
lean_object* v_one_2517_; lean_object* v_n_2518_; uint8_t v___x_2519_; 
v_one_2517_ = lean_unsigned_to_nat(1u);
v_n_2518_ = lean_nat_sub(v_skip_2427_, v_one_2517_);
lean_dec(v_skip_2427_);
v___x_2519_ = lean_nat_dec_le(v___x_2513_, v___x_2513_);
if (v___x_2519_ == 0)
{
if (v___x_2515_ == 0)
{
lean_object* v___x_2520_; 
lean_dec(v_n_2518_);
lean_dec_ref(v_children_2512_);
lean_dec_ref(v_todo_2428_);
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_result_2430_);
return v___x_2520_;
}
else
{
size_t v___x_2521_; size_t v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = ((size_t)0ULL);
v___x_2522_ = lean_usize_of_nat(v___x_2513_);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2518_, v_todo_2428_, v_children_2512_, v___x_2521_, v___x_2522_, v_result_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v_children_2512_);
lean_dec(v_n_2518_);
return v___x_2523_;
}
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2513_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2518_, v_todo_2428_, v_children_2512_, v___x_2524_, v___x_2525_, v_result_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v_children_2512_);
lean_dec(v_n_2518_);
return v___x_2526_;
}
}
}
else
{
lean_object* v___x_2527_; 
lean_dec_ref(v_children_2512_);
lean_dec_ref(v_todo_2428_);
lean_dec(v_skip_2427_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_result_2430_);
return v___x_2527_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2528_, lean_object* v_as_2529_, size_t v_i_2530_, size_t v_stop_2531_, lean_object* v_b_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
uint8_t v___x_2538_; 
v___x_2538_ = lean_usize_dec_eq(v_i_2530_, v_stop_2531_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2539_ = lean_array_uget_borrowed(v_as_2529_, v_i_2530_);
v_fst_2540_ = lean_ctor_get(v___x_2539_, 0);
v_snd_2541_ = lean_ctor_get(v___x_2539_, 1);
v___x_2542_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2540_);
lean_inc(v_snd_2541_);
lean_inc_ref(v_todo_2528_);
v___x_2543_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2542_, v_todo_2528_, v_snd_2541_, v_b_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; size_t v___x_2545_; size_t v___x_2546_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = ((size_t)1ULL);
v___x_2546_ = lean_usize_add(v_i_2530_, v___x_2545_);
v_i_2530_ = v___x_2546_;
v_b_2532_ = v_a_2544_;
goto _start;
}
else
{
lean_dec_ref(v_todo_2528_);
return v___x_2543_;
}
}
else
{
lean_object* v___x_2548_; 
lean_dec_ref(v_todo_2528_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_b_2532_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2549_, lean_object* v_as_2550_, lean_object* v_i_2551_, lean_object* v_stop_2552_, lean_object* v_b_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
size_t v_i_boxed_2559_; size_t v_stop_boxed_2560_; lean_object* v_res_2561_; 
v_i_boxed_2559_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_stop_boxed_2560_ = lean_unbox_usize(v_stop_2552_);
lean_dec(v_stop_2552_);
v_res_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2549_, v_as_2550_, v_i_boxed_2559_, v_stop_boxed_2560_, v_b_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v_as_2550_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2562_, lean_object* v_todo_2563_, lean_object* v_as_2564_, lean_object* v_i_2565_, lean_object* v_stop_2566_, lean_object* v_b_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
size_t v_i_boxed_2573_; size_t v_stop_boxed_2574_; lean_object* v_res_2575_; 
v_i_boxed_2573_ = lean_unbox_usize(v_i_2565_);
lean_dec(v_i_2565_);
v_stop_boxed_2574_ = lean_unbox_usize(v_stop_2566_);
lean_dec(v_stop_2566_);
v_res_2575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2562_, v_todo_2563_, v_as_2564_, v_i_boxed_2573_, v_stop_boxed_2574_, v_b_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_as_2564_);
lean_dec(v_n_2562_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2576_, lean_object* v_todo_2577_, lean_object* v_c_2578_, lean_object* v_result_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2576_, v_todo_2577_, v_c_2578_, v_result_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2586_, lean_object* v_skip_2587_, lean_object* v_todo_2588_, lean_object* v_c_2589_, lean_object* v_result_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2587_, v_todo_2588_, v_c_2589_, v_result_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2597_, lean_object* v_skip_2598_, lean_object* v_todo_2599_, lean_object* v_c_2600_, lean_object* v_result_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2597_, v_skip_2598_, v_todo_2599_, v_c_2600_, v_result_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2608_, lean_object* v_todo_2609_, lean_object* v_as_2610_, size_t v_i_2611_, size_t v_stop_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2609_, v_as_2610_, v_i_2611_, v_stop_2612_, v_b_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2620_, lean_object* v_todo_2621_, lean_object* v_as_2622_, lean_object* v_i_2623_, lean_object* v_stop_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
size_t v_i_boxed_2631_; size_t v_stop_boxed_2632_; lean_object* v_res_2633_; 
v_i_boxed_2631_ = lean_unbox_usize(v_i_2623_);
lean_dec(v_i_2623_);
v_stop_boxed_2632_ = lean_unbox_usize(v_stop_2624_);
lean_dec(v_stop_2624_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2620_, v_todo_2621_, v_as_2622_, v_i_boxed_2631_, v_stop_boxed_2632_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_as_2622_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2634_, lean_object* v_n_2635_, lean_object* v_todo_2636_, lean_object* v_as_2637_, size_t v_i_2638_, size_t v_stop_2639_, lean_object* v_b_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2635_, v_todo_2636_, v_as_2637_, v_i_2638_, v_stop_2639_, v_b_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_n_2648_, lean_object* v_todo_2649_, lean_object* v_as_2650_, lean_object* v_i_2651_, lean_object* v_stop_2652_, lean_object* v_b_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
size_t v_i_boxed_2659_; size_t v_stop_boxed_2660_; lean_object* v_res_2661_; 
v_i_boxed_2659_ = lean_unbox_usize(v_i_2651_);
lean_dec(v_i_2651_);
v_stop_boxed_2660_ = lean_unbox_usize(v_stop_2652_);
lean_dec(v_stop_2652_);
v_res_2661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2647_, v_n_2648_, v_todo_2649_, v_as_2650_, v_i_boxed_2659_, v_stop_boxed_2660_, v_b_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v_as_2650_);
lean_dec(v_n_2648_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2662_, lean_object* v_k_2663_, lean_object* v_c_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2663_);
v___x_2671_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2672_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2670_, v___x_2671_, v_c_2664_, v_result_2662_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2673_, lean_object* v_k_2674_, lean_object* v_c_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2673_, v_k_2674_, v_c_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v_k_2674_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2682_, lean_object* v_keys_2683_, lean_object* v_vals_2684_, lean_object* v_i_2685_, lean_object* v_acc_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = lean_array_get_size(v_keys_2683_);
v___x_2693_ = lean_nat_dec_lt(v_i_2685_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
lean_dec(v_i_2685_);
lean_dec_ref(v_f_2682_);
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_acc_2686_);
return v___x_2694_;
}
else
{
lean_object* v_k_2695_; lean_object* v_v_2696_; lean_object* v___x_2697_; 
v_k_2695_ = lean_array_fget_borrowed(v_keys_2683_, v_i_2685_);
v_v_2696_ = lean_array_fget_borrowed(v_vals_2684_, v_i_2685_);
lean_inc_ref(v_f_2682_);
lean_inc(v___y_2690_);
lean_inc_ref(v___y_2689_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v_v_2696_);
lean_inc(v_k_2695_);
v___x_2697_ = lean_apply_8(v_f_2682_, v_acc_2686_, v_k_2695_, v_v_2696_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, lean_box(0));
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = lean_unsigned_to_nat(1u);
v___x_2700_ = lean_nat_add(v_i_2685_, v___x_2699_);
lean_dec(v_i_2685_);
v_i_2685_ = v___x_2700_;
v_acc_2686_ = v_a_2698_;
goto _start;
}
else
{
lean_dec(v_i_2685_);
lean_dec_ref(v_f_2682_);
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2702_, lean_object* v_keys_2703_, lean_object* v_vals_2704_, lean_object* v_i_2705_, lean_object* v_acc_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2702_, v_keys_2703_, v_vals_2704_, v_i_2705_, v_acc_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec_ref(v_vals_2704_);
lean_dec_ref(v_keys_2703_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
if (lean_obj_tag(v_x_2714_) == 0)
{
lean_object* v_es_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2741_; 
v_es_2721_ = lean_ctor_get(v_x_2714_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_x_2714_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2723_ = v_x_2714_;
v_isShared_2724_ = v_isSharedCheck_2741_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_es_2721_);
lean_dec(v_x_2714_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2741_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = lean_array_get_size(v_es_2721_);
v___x_2727_ = lean_nat_dec_lt(v___x_2725_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2729_; 
lean_dec_ref(v_es_2721_);
lean_dec_ref(v_f_2713_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v_x_2715_);
v___x_2729_ = v___x_2723_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_x_2715_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
else
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_nat_dec_le(v___x_2726_, v___x_2726_);
if (v___x_2731_ == 0)
{
if (v___x_2727_ == 0)
{
lean_object* v___x_2733_; 
lean_dec_ref(v_es_2721_);
lean_dec_ref(v_f_2713_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v_x_2715_);
v___x_2733_ = v___x_2723_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_x_2715_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
else
{
size_t v___x_2735_; size_t v___x_2736_; lean_object* v___x_2737_; 
lean_del_object(v___x_2723_);
v___x_2735_ = ((size_t)0ULL);
v___x_2736_ = lean_usize_of_nat(v___x_2726_);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2713_, v_es_2721_, v___x_2735_, v___x_2736_, v_x_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec_ref(v_es_2721_);
return v___x_2737_;
}
}
else
{
size_t v___x_2738_; size_t v___x_2739_; lean_object* v___x_2740_; 
lean_del_object(v___x_2723_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = lean_usize_of_nat(v___x_2726_);
v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2713_, v_es_2721_, v___x_2738_, v___x_2739_, v_x_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec_ref(v_es_2721_);
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_ks_2742_; lean_object* v_vs_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_ks_2742_ = lean_ctor_get(v_x_2714_, 0);
lean_inc_ref(v_ks_2742_);
v_vs_2743_ = lean_ctor_get(v_x_2714_, 1);
lean_inc_ref(v_vs_2743_);
lean_dec_ref(v_x_2714_);
v___x_2744_ = lean_unsigned_to_nat(0u);
v___x_2745_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2713_, v_ks_2742_, v_vs_2743_, v___x_2744_, v_x_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec_ref(v_vs_2743_);
lean_dec_ref(v_ks_2742_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2746_, lean_object* v_as_2747_, size_t v_i_2748_, size_t v_stop_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_a_2757_; lean_object* v___y_2762_; uint8_t v___x_2764_; 
v___x_2764_ = lean_usize_dec_eq(v_i_2748_, v_stop_2749_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_array_uget_borrowed(v_as_2747_, v_i_2748_);
switch(lean_obj_tag(v___x_2765_))
{
case 0:
{
lean_object* v_key_2766_; lean_object* v_val_2767_; lean_object* v___x_2768_; 
v_key_2766_ = lean_ctor_get(v___x_2765_, 0);
v_val_2767_ = lean_ctor_get(v___x_2765_, 1);
lean_inc_ref(v_f_2746_);
lean_inc(v___y_2754_);
lean_inc_ref(v___y_2753_);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v_val_2767_);
lean_inc(v_key_2766_);
v___x_2768_ = lean_apply_8(v_f_2746_, v_b_2750_, v_key_2766_, v_val_2767_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, lean_box(0));
v___y_2762_ = v___x_2768_;
goto v___jp_2761_;
}
case 1:
{
lean_object* v_node_2769_; lean_object* v___x_2770_; 
v_node_2769_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_node_2769_);
lean_inc_ref(v_f_2746_);
v___x_2770_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2746_, v_node_2769_, v_b_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
v___y_2762_ = v___x_2770_;
goto v___jp_2761_;
}
default: 
{
v_a_2757_ = v_b_2750_;
goto v___jp_2756_;
}
}
}
else
{
lean_object* v___x_2771_; 
lean_dec_ref(v_f_2746_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_b_2750_);
return v___x_2771_;
}
v___jp_2756_:
{
size_t v___x_2758_; size_t v___x_2759_; 
v___x_2758_ = ((size_t)1ULL);
v___x_2759_ = lean_usize_add(v_i_2748_, v___x_2758_);
v_i_2748_ = v___x_2759_;
v_b_2750_ = v_a_2757_;
goto _start;
}
v___jp_2761_:
{
if (lean_obj_tag(v___y_2762_) == 0)
{
lean_object* v_a_2763_; 
v_a_2763_ = lean_ctor_get(v___y_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___y_2762_);
v_a_2757_ = v_a_2763_;
goto v___jp_2756_;
}
else
{
lean_dec_ref(v_f_2746_);
return v___y_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2772_, lean_object* v_as_2773_, lean_object* v_i_2774_, lean_object* v_stop_2775_, lean_object* v_b_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
size_t v_i_boxed_2782_; size_t v_stop_boxed_2783_; lean_object* v_res_2784_; 
v_i_boxed_2782_ = lean_unbox_usize(v_i_2774_);
lean_dec(v_i_2774_);
v_stop_boxed_2783_ = lean_unbox_usize(v_stop_2775_);
lean_dec(v_stop_2775_);
v_res_2784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2772_, v_as_2773_, v_i_boxed_2782_, v_stop_boxed_2783_, v_b_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec_ref(v_as_2773_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2785_, v_x_2786_, v_x_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2795_, lean_object* v_e_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v___x_2802_; uint8_t v_foApprox_2803_; uint8_t v_ctxApprox_2804_; uint8_t v_quasiPatternApprox_2805_; uint8_t v_constApprox_2806_; uint8_t v_isDefEqStuckEx_2807_; uint8_t v_unificationHints_2808_; uint8_t v_proofIrrelevance_2809_; uint8_t v_assignSyntheticOpaque_2810_; uint8_t v_offsetCnstrs_2811_; uint8_t v_etaStruct_2812_; uint8_t v_univApprox_2813_; uint8_t v_iota_2814_; uint8_t v_beta_2815_; uint8_t v_proj_2816_; uint8_t v_zeta_2817_; uint8_t v_zetaDelta_2818_; uint8_t v_zetaUnused_2819_; uint8_t v_zetaHave_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2875_; 
v___x_2802_ = l_Lean_Meta_Context_config(v_a_2797_);
v_foApprox_2803_ = lean_ctor_get_uint8(v___x_2802_, 0);
v_ctxApprox_2804_ = lean_ctor_get_uint8(v___x_2802_, 1);
v_quasiPatternApprox_2805_ = lean_ctor_get_uint8(v___x_2802_, 2);
v_constApprox_2806_ = lean_ctor_get_uint8(v___x_2802_, 3);
v_isDefEqStuckEx_2807_ = lean_ctor_get_uint8(v___x_2802_, 4);
v_unificationHints_2808_ = lean_ctor_get_uint8(v___x_2802_, 5);
v_proofIrrelevance_2809_ = lean_ctor_get_uint8(v___x_2802_, 6);
v_assignSyntheticOpaque_2810_ = lean_ctor_get_uint8(v___x_2802_, 7);
v_offsetCnstrs_2811_ = lean_ctor_get_uint8(v___x_2802_, 8);
v_etaStruct_2812_ = lean_ctor_get_uint8(v___x_2802_, 10);
v_univApprox_2813_ = lean_ctor_get_uint8(v___x_2802_, 11);
v_iota_2814_ = lean_ctor_get_uint8(v___x_2802_, 12);
v_beta_2815_ = lean_ctor_get_uint8(v___x_2802_, 13);
v_proj_2816_ = lean_ctor_get_uint8(v___x_2802_, 14);
v_zeta_2817_ = lean_ctor_get_uint8(v___x_2802_, 15);
v_zetaDelta_2818_ = lean_ctor_get_uint8(v___x_2802_, 16);
v_zetaUnused_2819_ = lean_ctor_get_uint8(v___x_2802_, 17);
v_zetaHave_2820_ = lean_ctor_get_uint8(v___x_2802_, 18);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2822_ = v___x_2802_;
v_isShared_2823_ = v_isSharedCheck_2875_;
goto v_resetjp_2821_;
}
else
{
lean_dec(v___x_2802_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2875_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
uint8_t v_trackZetaDelta_2824_; lean_object* v_zetaDeltaSet_2825_; lean_object* v_lctx_2826_; lean_object* v_localInstances_2827_; lean_object* v_defEqCtx_x3f_2828_; lean_object* v_synthPendingDepth_2829_; lean_object* v_canUnfold_x3f_2830_; uint8_t v_univApprox_2831_; uint8_t v_inTypeClassResolution_2832_; uint8_t v_cacheInferType_2833_; uint8_t v___x_2834_; lean_object* v_config_2836_; 
v_trackZetaDelta_2824_ = lean_ctor_get_uint8(v_a_2797_, sizeof(void*)*7);
v_zetaDeltaSet_2825_ = lean_ctor_get(v_a_2797_, 1);
v_lctx_2826_ = lean_ctor_get(v_a_2797_, 2);
v_localInstances_2827_ = lean_ctor_get(v_a_2797_, 3);
v_defEqCtx_x3f_2828_ = lean_ctor_get(v_a_2797_, 4);
v_synthPendingDepth_2829_ = lean_ctor_get(v_a_2797_, 5);
v_canUnfold_x3f_2830_ = lean_ctor_get(v_a_2797_, 6);
v_univApprox_2831_ = lean_ctor_get_uint8(v_a_2797_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2832_ = lean_ctor_get_uint8(v_a_2797_, sizeof(void*)*7 + 2);
v_cacheInferType_2833_ = lean_ctor_get_uint8(v_a_2797_, sizeof(void*)*7 + 3);
v___x_2834_ = 2;
if (v_isShared_2823_ == 0)
{
v_config_2836_ = v___x_2822_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 0, v_foApprox_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 1, v_ctxApprox_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 2, v_quasiPatternApprox_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 3, v_constApprox_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 4, v_isDefEqStuckEx_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 5, v_unificationHints_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 6, v_proofIrrelevance_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 7, v_assignSyntheticOpaque_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 8, v_offsetCnstrs_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 10, v_etaStruct_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 11, v_univApprox_2813_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 12, v_iota_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 13, v_beta_2815_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 14, v_proj_2816_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 15, v_zeta_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 16, v_zetaDelta_2818_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 17, v_zetaUnused_2819_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, 18, v_zetaHave_2820_);
v_config_2836_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
uint64_t v___x_2837_; uint64_t v___x_2838_; uint64_t v___x_2839_; uint8_t v___x_2840_; uint64_t v___x_2841_; uint64_t v___x_2842_; uint64_t v_key_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; 
lean_ctor_set_uint8(v_config_2836_, 9, v___x_2834_);
v___x_2837_ = l_Lean_Meta_Context_configKey(v_a_2797_);
v___x_2838_ = 2ULL;
v___x_2839_ = lean_uint64_shift_right(v___x_2837_, v___x_2838_);
v___x_2840_ = 1;
v___x_2841_ = lean_uint64_shift_left(v___x_2839_, v___x_2838_);
v___x_2842_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2843_ = lean_uint64_lor(v___x_2841_, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2844_, 0, v_config_2836_);
lean_ctor_set_uint64(v___x_2844_, sizeof(void*)*1, v_key_2843_);
lean_inc(v_canUnfold_x3f_2830_);
lean_inc(v_synthPendingDepth_2829_);
lean_inc(v_defEqCtx_x3f_2828_);
lean_inc_ref(v_localInstances_2827_);
lean_inc_ref(v_lctx_2826_);
lean_inc(v_zetaDeltaSet_2825_);
v___x_2845_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v_zetaDeltaSet_2825_);
lean_ctor_set(v___x_2845_, 2, v_lctx_2826_);
lean_ctor_set(v___x_2845_, 3, v_localInstances_2827_);
lean_ctor_set(v___x_2845_, 4, v_defEqCtx_x3f_2828_);
lean_ctor_set(v___x_2845_, 5, v_synthPendingDepth_2829_);
lean_ctor_set(v___x_2845_, 6, v_canUnfold_x3f_2830_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7, v_trackZetaDelta_2824_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7 + 1, v_univApprox_2831_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2832_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7 + 3, v_cacheInferType_2833_);
v___x_2846_ = 0;
v___x_2847_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2796_, v___x_2846_, v___x_2840_, v___x_2845_, v_a_2798_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2865_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2865_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2865_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_fst_2852_; 
v_fst_2852_ = lean_ctor_get(v_a_2848_, 0);
lean_inc(v_fst_2852_);
if (lean_obj_tag(v_fst_2852_) == 0)
{
lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_del_object(v___x_2850_);
lean_dec(v_a_2848_);
v___f_2853_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2854_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_2855_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2853_, v_d_2795_, v___x_2854_, v___x_2845_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec_ref(v___x_2845_);
return v___x_2855_;
}
else
{
lean_object* v_snd_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_snd_2856_ = lean_ctor_get(v_a_2848_, 1);
lean_inc(v_snd_2856_);
lean_dec(v_a_2848_);
lean_inc_ref(v_d_2795_);
v___x_2857_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2795_);
v___x_2858_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2795_, v_fst_2852_);
lean_dec(v_fst_2852_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v___x_2860_; 
lean_dec(v_snd_2856_);
lean_dec_ref(v___x_2845_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2857_);
v___x_2860_ = v___x_2850_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2857_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
else
{
lean_object* v_val_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_del_object(v___x_2850_);
v_val_2862_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_val_2862_);
lean_dec_ref(v___x_2858_);
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2863_, v_snd_2856_, v_val_2862_, v___x_2857_, v___x_2845_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec_ref(v___x_2845_);
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v___x_2845_);
lean_dec_ref(v_d_2795_);
v_a_2866_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2847_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2847_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_2876_, lean_object* v_e_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2876_, v_e_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_2884_, lean_object* v_d_2885_, lean_object* v_e_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2885_, v_e_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_2893_, lean_object* v_d_2894_, lean_object* v_e_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_2893_, v_d_2894_, v_e_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_2902_, lean_object* v_f_2903_, lean_object* v_init_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2903_, v_map_2902_, v_init_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_2911_, lean_object* v_f_2912_, lean_object* v_init_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_2911_, v_f_2912_, v_init_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_2920_, lean_object* v_00_u03b2_2921_, lean_object* v_map_2922_, lean_object* v_f_2923_, lean_object* v_init_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2923_, v_map_2922_, v_init_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_map_2933_, lean_object* v_f_2934_, lean_object* v_init_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_2931_, v_00_u03b2_2932_, v_map_2933_, v_f_2934_, v_init_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_2942_, lean_object* v_00_u03b1_2943_, lean_object* v_00_u03b2_2944_, lean_object* v_f_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2945_, v_x_2946_, v_x_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2954_, lean_object* v_00_u03b1_2955_, lean_object* v_00_u03b2_2956_, lean_object* v_f_2957_, lean_object* v_x_2958_, lean_object* v_x_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_2954_, v_00_u03b1_2955_, v_00_u03b2_2956_, v_f_2957_, v_x_2958_, v_x_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2966_, lean_object* v_00_u03b2_2967_, lean_object* v_00_u03c3_2968_, lean_object* v_f_2969_, lean_object* v_as_2970_, size_t v_i_2971_, size_t v_stop_2972_, lean_object* v_b_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2969_, v_as_2970_, v_i_2971_, v_stop_2972_, v_b_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2980_, lean_object* v_00_u03b2_2981_, lean_object* v_00_u03c3_2982_, lean_object* v_f_2983_, lean_object* v_as_2984_, lean_object* v_i_2985_, lean_object* v_stop_2986_, lean_object* v_b_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
size_t v_i_boxed_2993_; size_t v_stop_boxed_2994_; lean_object* v_res_2995_; 
v_i_boxed_2993_ = lean_unbox_usize(v_i_2985_);
lean_dec(v_i_2985_);
v_stop_boxed_2994_ = lean_unbox_usize(v_stop_2986_);
lean_dec(v_stop_2986_);
v_res_2995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_2980_, v_00_u03b2_2981_, v_00_u03c3_2982_, v_f_2983_, v_as_2984_, v_i_boxed_2993_, v_stop_boxed_2994_, v_b_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_as_2984_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_2996_, lean_object* v_00_u03b1_2997_, lean_object* v_00_u03b2_2998_, lean_object* v_f_2999_, lean_object* v_keys_3000_, lean_object* v_vals_3001_, lean_object* v_heq_3002_, lean_object* v_i_3003_, lean_object* v_acc_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2999_, v_keys_3000_, v_vals_3001_, v_i_3003_, v_acc_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_3011_, lean_object* v_00_u03b1_3012_, lean_object* v_00_u03b2_3013_, lean_object* v_f_3014_, lean_object* v_keys_3015_, lean_object* v_vals_3016_, lean_object* v_heq_3017_, lean_object* v_i_3018_, lean_object* v_acc_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_3011_, v_00_u03b1_3012_, v_00_u03b2_3013_, v_f_3014_, v_keys_3015_, v_vals_3016_, v_heq_3017_, v_i_3018_, v_acc_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec_ref(v_vals_3016_);
lean_dec_ref(v_keys_3015_);
return v_res_3025_;
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
