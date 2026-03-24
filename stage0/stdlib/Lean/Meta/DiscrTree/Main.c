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
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
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
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
lean_inc(v_a_67_);
lean_inc_ref(v_a_66_);
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
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
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
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
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
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
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
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
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
lean_dec_ref(v_e_368_);
lean_dec(v_fName_367_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce(lean_object* v_e_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
lean_inc(v_a_379_);
lean_inc_ref(v_a_378_);
lean_inc(v_a_377_);
lean_inc_ref(v_a_376_);
v___x_381_ = l_Lean_Meta_whnfCore(v_e_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; uint8_t v___x_383_; lean_object* v___x_384_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref(v___x_381_);
v___x_383_ = 0;
lean_inc(v_a_379_);
lean_inc_ref(v_a_378_);
lean_inc(v_a_377_);
lean_inc_ref(v_a_376_);
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
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
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
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
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
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_reduce___boxed(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_DiscrTree_reduce(v_e_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
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
lean_inc(v_a_427_);
lean_inc_ref(v_a_426_);
lean_inc(v_a_425_);
lean_inc_ref(v_a_424_);
v___x_429_ = l_Lean_Meta_whnfCore(v_e_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; uint8_t v___x_431_; lean_object* v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v___x_429_);
v___x_431_ = 0;
lean_inc(v_a_427_);
lean_inc_ref(v_a_426_);
lean_inc(v_a_425_);
lean_inc_ref(v_a_424_);
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
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
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
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
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
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
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
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(lean_object* v_e_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_469_; 
lean_inc(v_a_467_);
lean_inc_ref(v_a_466_);
lean_inc(v_a_465_);
lean_inc_ref(v_a_464_);
v___x_469_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
v___x_471_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
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
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(lean_object* v_e_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(v_e_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
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
lean_inc(v_a_515_);
lean_inc_ref(v_a_514_);
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_inc(v_a_515_);
lean_inc_ref(v_a_514_);
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_inc(v___y_543_);
lean_inc_ref(v___y_542_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
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
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
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
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
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
lean_inc(v_a_684_);
lean_inc_ref(v_a_683_);
lean_inc(v_a_682_);
lean_inc_ref(v_a_681_);
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
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
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
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
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
lean_object* v___x_731_; uint8_t v_foApprox_732_; uint8_t v_ctxApprox_733_; uint8_t v_quasiPatternApprox_734_; uint8_t v_constApprox_735_; uint8_t v_isDefEqStuckEx_736_; uint8_t v_unificationHints_737_; uint8_t v_proofIrrelevance_738_; uint8_t v_assignSyntheticOpaque_739_; uint8_t v_offsetCnstrs_740_; uint8_t v_etaStruct_741_; uint8_t v_univApprox_742_; uint8_t v_iota_743_; uint8_t v_beta_744_; uint8_t v_proj_745_; uint8_t v_zeta_746_; uint8_t v_zetaDelta_747_; uint8_t v_zetaUnused_748_; uint8_t v_zetaHave_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_793_; 
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
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_793_ == 0)
{
v___x_751_ = v___x_731_;
v_isShared_752_ = v_isSharedCheck_793_;
goto v_resetjp_750_;
}
else
{
lean_dec(v___x_731_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_793_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
uint8_t v_trackZetaDelta_753_; lean_object* v_zetaDeltaSet_754_; lean_object* v_lctx_755_; lean_object* v_localInstances_756_; lean_object* v_defEqCtx_x3f_757_; lean_object* v_synthPendingDepth_758_; lean_object* v_canUnfold_x3f_759_; uint8_t v_univApprox_760_; uint8_t v_inTypeClassResolution_761_; uint8_t v_cacheInferType_762_; uint8_t v___x_763_; lean_object* v_config_765_; 
v_trackZetaDelta_753_ = lean_ctor_get_uint8(v_a_726_, sizeof(void*)*7);
v_zetaDeltaSet_754_ = lean_ctor_get(v_a_726_, 1);
lean_inc(v_zetaDeltaSet_754_);
v_lctx_755_ = lean_ctor_get(v_a_726_, 2);
lean_inc_ref(v_lctx_755_);
v_localInstances_756_ = lean_ctor_get(v_a_726_, 3);
lean_inc_ref(v_localInstances_756_);
v_defEqCtx_x3f_757_ = lean_ctor_get(v_a_726_, 4);
lean_inc(v_defEqCtx_x3f_757_);
v_synthPendingDepth_758_ = lean_ctor_get(v_a_726_, 5);
lean_inc(v_synthPendingDepth_758_);
v_canUnfold_x3f_759_ = lean_ctor_get(v_a_726_, 6);
lean_inc(v_canUnfold_x3f_759_);
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
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 0, v_foApprox_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 1, v_ctxApprox_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 2, v_quasiPatternApprox_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 3, v_constApprox_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 4, v_isDefEqStuckEx_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 5, v_unificationHints_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 6, v_proofIrrelevance_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 7, v_assignSyntheticOpaque_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 8, v_offsetCnstrs_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 10, v_etaStruct_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 11, v_univApprox_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 12, v_iota_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 13, v_beta_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 14, v_proj_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 15, v_zeta_746_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 16, v_zetaDelta_747_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 17, v_zetaUnused_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, 18, v_zetaHave_749_);
v_config_765_ = v_reuseFailAlloc_792_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
uint64_t v___x_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_784_; 
lean_ctor_set_uint8(v_config_765_, 9, v___x_763_);
v___x_766_ = l_Lean_Meta_Context_configKey(v_a_726_);
v_isSharedCheck_784_ = !lean_is_exclusive(v_a_726_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; 
v_unused_785_ = lean_ctor_get(v_a_726_, 6);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_a_726_, 5);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_a_726_, 4);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_a_726_, 3);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_a_726_, 2);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_a_726_, 1);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_a_726_, 0);
lean_dec(v_unused_791_);
v___x_768_ = v_a_726_;
v_isShared_769_ = v_isSharedCheck_784_;
goto v_resetjp_767_;
}
else
{
lean_dec(v_a_726_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_784_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint64_t v___x_770_; uint64_t v___x_771_; lean_object* v___x_772_; lean_object* v_todo_773_; uint8_t v___x_774_; lean_object* v___x_775_; uint64_t v___x_776_; uint64_t v___x_777_; uint64_t v_key_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_770_ = 2ULL;
v___x_771_ = lean_uint64_shift_right(v___x_766_, v___x_770_);
v___x_772_ = lean_unsigned_to_nat(8u);
v_todo_773_ = lean_mk_empty_array_with_capacity(v___x_772_);
v___x_774_ = 1;
lean_inc_ref(v_todo_773_);
v___x_775_ = lean_array_push(v_todo_773_, v_e_724_);
v___x_776_ = lean_uint64_shift_left(v___x_771_, v___x_770_);
v___x_777_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_778_ = lean_uint64_lor(v___x_776_, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_779_, 0, v_config_765_);
lean_ctor_set_uint64(v___x_779_, sizeof(void*)*1, v_key_778_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_779_);
v___x_781_ = v___x_768_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_zetaDeltaSet_754_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_lctx_755_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_localInstances_756_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_defEqCtx_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v_synthPendingDepth_758_);
lean_ctor_set(v_reuseFailAlloc_783_, 6, v_canUnfold_x3f_759_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*7, v_trackZetaDelta_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*7 + 1, v_univApprox_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*7 + 2, v_inTypeClassResolution_761_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*7 + 3, v_cacheInferType_762_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_DiscrTree_mkPathAux(v___x_774_, v___x_775_, v_todo_773_, v_noIndexAtArgs_725_, v___x_781_, v_a_727_, v_a_728_, v_a_729_);
return v___x_782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mkPath___boxed(lean_object* v_e_794_, lean_object* v_noIndexAtArgs_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_801_; lean_object* v_res_802_; 
v_noIndexAtArgs_boxed_801_ = lean_unbox(v_noIndexAtArgs_795_);
v_res_802_ = l_Lean_Meta_DiscrTree_mkPath(v_e_794_, v_noIndexAtArgs_boxed_801_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg(lean_object* v_inst_803_, lean_object* v_d_804_, lean_object* v_e_805_, lean_object* v_v_806_, uint8_t v_noIndexAtArgs_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_DiscrTree_mkPath(v_e_805_, v_noIndexAtArgs_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_822_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_803_, v_d_804_, v_a_814_, v_v_806_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_v_806_);
lean_dec_ref(v_d_804_);
lean_dec_ref(v_inst_803_);
v_a_823_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_813_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___redArg___boxed(lean_object* v_inst_831_, lean_object* v_d_832_, lean_object* v_e_833_, lean_object* v_v_834_, lean_object* v_noIndexAtArgs_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_841_; lean_object* v_res_842_; 
v_noIndexAtArgs_boxed_841_ = lean_unbox(v_noIndexAtArgs_835_);
v_res_842_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_831_, v_d_832_, v_e_833_, v_v_834_, v_noIndexAtArgs_boxed_841_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert(lean_object* v_00_u03b1_843_, lean_object* v_inst_844_, lean_object* v_d_845_, lean_object* v_e_846_, lean_object* v_v_847_, uint8_t v_noIndexAtArgs_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_DiscrTree_insert___redArg(v_inst_844_, v_d_845_, v_e_846_, v_v_847_, v_noIndexAtArgs_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insert___boxed(lean_object* v_00_u03b1_855_, lean_object* v_inst_856_, lean_object* v_d_857_, lean_object* v_e_858_, lean_object* v_v_859_, lean_object* v_noIndexAtArgs_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_866_; lean_object* v_res_867_; 
v_noIndexAtArgs_boxed_866_ = lean_unbox(v_noIndexAtArgs_860_);
v_res_867_ = l_Lean_Meta_DiscrTree_insert(v_00_u03b1_855_, v_inst_856_, v_d_857_, v_e_858_, v_v_859_, v_noIndexAtArgs_boxed_866_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
return v_res_867_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_883_ = lean_array_get_size(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_890_ = lean_array_get_size(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(lean_object* v_inst_891_, lean_object* v_d_892_, lean_object* v_e_893_, lean_object* v_v_894_, uint8_t v_noIndexAtArgs_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Meta_DiscrTree_mkPath(v_e_893_, v_noIndexAtArgs_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_926_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_926_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_926_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_926_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_919_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6));
v___x_920_ = lean_array_get_size(v_a_902_);
v___x_921_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7);
v___x_922_ = lean_nat_dec_eq(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
goto v___jp_911_;
}
else
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_924_ = l_Array_isEqvAux___redArg(v_a_902_, v___x_919_, v___x_923_, v___x_920_);
if (v___x_924_ == 0)
{
goto v___jp_911_;
}
else
{
lean_object* v___x_925_; 
lean_del_object(v___x_904_);
lean_dec(v_a_902_);
lean_dec(v_v_894_);
lean_dec_ref(v_inst_891_);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v_d_892_);
return v___x_925_;
}
}
v___jp_906_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_891_, v_d_892_, v_a_902_, v_v_894_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
v___jp_911_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_912_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3));
v___x_913_ = lean_array_get_size(v_a_902_);
v___x_914_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4, &l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once, _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4);
v___x_915_ = lean_nat_dec_eq(v___x_913_, v___x_914_);
if (v___x_915_ == 0)
{
goto v___jp_906_;
}
else
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5));
v___x_917_ = l_Array_isEqvAux___redArg(v_a_902_, v___x_912_, v___x_916_, v___x_913_);
if (v___x_917_ == 0)
{
goto v___jp_906_;
}
else
{
lean_object* v___x_918_; 
lean_del_object(v___x_904_);
lean_dec(v_a_902_);
lean_dec(v_v_894_);
lean_dec_ref(v_inst_891_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v_d_892_);
return v___x_918_;
}
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_v_894_);
lean_dec_ref(v_d_892_);
lean_dec_ref(v_inst_891_);
v_a_927_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_901_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_901_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(lean_object* v_inst_935_, lean_object* v_d_936_, lean_object* v_e_937_, lean_object* v_v_938_, lean_object* v_noIndexAtArgs_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_945_; lean_object* v_res_946_; 
v_noIndexAtArgs_boxed_945_ = lean_unbox(v_noIndexAtArgs_939_);
v_res_946_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_935_, v_d_936_, v_e_937_, v_v_938_, v_noIndexAtArgs_boxed_945_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific(lean_object* v_00_u03b1_947_, lean_object* v_inst_948_, lean_object* v_d_949_, lean_object* v_e_950_, lean_object* v_v_951_, uint8_t v_noIndexAtArgs_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(v_inst_948_, v_d_949_, v_e_950_, v_v_951_, v_noIndexAtArgs_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(lean_object* v_00_u03b1_959_, lean_object* v_inst_960_, lean_object* v_d_961_, lean_object* v_e_962_, lean_object* v_v_963_, lean_object* v_noIndexAtArgs_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
uint8_t v_noIndexAtArgs_boxed_970_; lean_object* v_res_971_; 
v_noIndexAtArgs_boxed_970_ = lean_unbox(v_noIndexAtArgs_964_);
v_res_971_ = l_Lean_Meta_DiscrTree_insertIfSpecific(v_00_u03b1_959_, v_inst_960_, v_d_961_, v_e_962_, v_v_963_, v_noIndexAtArgs_boxed_970_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(lean_object* v_declName_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v_env_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_975_ = lean_st_ref_get(v___y_973_);
v_env_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_ref(v_env_976_);
lean_dec(v___x_975_);
v___x_977_ = l_Lean_isRecCore(v_env_976_, v_declName_972_);
v___x_978_ = lean_box(v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_980_, v___y_981_);
lean_dec(v___y_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(lean_object* v_declName_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_984_, v___y_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(lean_object* v_declName_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(lean_object* v_a_998_, lean_object* v_b_999_){
_start:
{
lean_object* v_array_1001_; lean_object* v_start_1002_; lean_object* v_stop_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1020_; 
v_array_1001_ = lean_ctor_get(v_a_998_, 0);
v_start_1002_ = lean_ctor_get(v_a_998_, 1);
v_stop_1003_ = lean_ctor_get(v_a_998_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_a_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1005_ = v_a_998_;
v_isShared_1006_ = v_isSharedCheck_1020_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_stop_1003_);
lean_inc(v_start_1002_);
lean_inc(v_array_1001_);
lean_dec(v_a_998_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1020_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint8_t v___x_1007_; 
v___x_1007_ = lean_nat_dec_lt(v_start_1002_, v_stop_1003_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_del_object(v___x_1005_);
lean_dec(v_stop_1003_);
lean_dec(v_start_1002_);
lean_dec_ref(v_array_1001_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_b_999_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_unsigned_to_nat(1u);
v___x_1011_ = lean_nat_add(v_start_1002_, v___x_1010_);
lean_inc_ref(v_array_1001_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v___x_1011_);
v___x_1013_ = v___x_1005_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_array_1001_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_stop_1003_);
v___x_1013_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_array_fget(v_array_1001_, v_start_1002_);
lean_dec(v_start_1002_);
lean_dec_ref(v_array_1001_);
v___x_1015_ = l_Lean_Expr_hasExprMVar(v___x_1014_);
lean_dec(v___x_1014_);
if (v___x_1015_ == 0)
{
v_a_998_ = v___x_1013_;
v_b_999_ = v___x_1009_;
goto _start;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_dec_ref(v___x_1017_);
v_a_998_ = v___x_1013_;
v_b_999_ = v___x_1009_;
goto _start;
}
else
{
lean_dec_ref(v___x_1013_);
return v___x_1017_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1021_, v_b_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v_env_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1028_ = lean_st_ref_get(v___y_1026_);
v_env_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_env_1029_);
lean_dec(v___x_1028_);
v___x_1030_ = lean_get_reducibility_status(v_env_1029_, v_declName_1025_);
v___x_1031_ = lean_box(v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1033_, v___y_1034_);
lean_dec(v___y_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(lean_object* v_declName_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1059_; 
v___x_1043_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1037_, v___y_1041_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1059_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1059_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_unbox(v_a_1044_);
lean_dec(v_a_1044_);
if (v___x_1048_ == 0)
{
uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = 1;
v___x_1050_ = lean_box(v___x_1049_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1050_);
v___x_1052_ = v___x_1046_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
else
{
uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = 0;
v___x_1055_ = lean_box(v___x_1054_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1055_);
v___x_1057_ = v___x_1046_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(lean_object* v_e_1077_, uint8_t v_isMatch_1078_, uint8_t v_root_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1085_; 
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
v___x_1085_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1077_, v_root_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1266_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1266_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1266_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___y_1091_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; 
if (v_root_1079_ == 0)
{
lean_object* v___x_1254_; 
lean_inc(v_a_1086_);
v___x_1254_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_1086_);
if (lean_obj_tag(v___x_1254_) == 1)
{
lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1265_; 
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
v_val_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 2);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_val_1255_);
v___x_1260_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
}
else
{
lean_dec(v___x_1254_);
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
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref(v_a_1106_);
lean_dec_ref(v___x_1105_);
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
lean_object* v_declName_1111_; lean_object* v___x_1112_; 
v_declName_1111_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_declName_1111_);
lean_dec_ref(v___x_1105_);
v___x_1112_ = l_Lean_Meta_getConfig___redArg(v___y_1101_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; uint8_t v_isDefEqStuckEx_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref(v___x_1112_);
v_isDefEqStuckEx_1114_ = lean_ctor_get_uint8(v_a_1113_, 4);
lean_dec(v_a_1113_);
if (v_isDefEqStuckEx_1114_ == 0)
{
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_Expr_hasExprMVar(v_a_1086_);
if (v___x_1115_ == 0)
{
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1116_; 
lean_inc(v_declName_1111_);
v___x_1116_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_1111_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; uint8_t v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = lean_unbox(v_a_1117_);
lean_dec(v_a_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v_env_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_st_ref_get(v___y_1104_);
v_env_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc_ref(v_env_1120_);
lean_dec(v___x_1119_);
v___x_1121_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1120_, v_a_1086_);
if (lean_obj_tag(v___x_1121_) == 1)
{
lean_object* v_val_1122_; lean_object* v_numDiscrs_1123_; lean_object* v_nargs_1124_; lean_object* v_dummy_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v___y_1104_);
v_val_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1122_);
lean_dec_ref(v___x_1121_);
v_numDiscrs_1123_ = lean_ctor_get(v_val_1122_, 1);
lean_inc(v_numDiscrs_1123_);
v_nargs_1124_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
v_dummy_1125_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
lean_inc(v_nargs_1124_);
v___x_1126_ = lean_mk_array(v_nargs_1124_, v_dummy_1125_);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_sub(v_nargs_1124_, v___x_1127_);
lean_dec(v_nargs_1124_);
lean_inc(v_a_1086_);
v___x_1129_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1086_, v___x_1126_, v___x_1128_);
v___x_1130_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1122_);
lean_dec(v_val_1122_);
v___x_1131_ = lean_nat_add(v___x_1130_, v_numDiscrs_1123_);
lean_dec(v_numDiscrs_1123_);
v___x_1132_ = l_Array_toSubarray___redArg(v___x_1129_, v___x_1130_, v___x_1131_);
v___x_1133_ = lean_box(0);
v___x_1134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_1132_, v___x_1133_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_dec_ref(v___x_1134_);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_declName_1111_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v___x_1143_; lean_object* v_a_1144_; uint8_t v___x_1145_; 
lean_dec(v___x_1121_);
lean_inc(v_declName_1111_);
v___x_1143_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_1111_, v___y_1104_);
lean_dec(v___y_1104_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v___x_1143_);
v___x_1145_ = lean_unbox(v_a_1144_);
lean_dec(v_a_1144_);
if (v___x_1145_ == 0)
{
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_dec_ref(v___x_1146_);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_declName_1111_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
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
else
{
lean_object* v___x_1155_; 
lean_dec(v___y_1104_);
v___x_1155_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_dec_ref(v___x_1155_);
v___y_1091_ = v_declName_1111_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_declName_1111_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_declName_1111_);
lean_dec(v___y_1104_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1164_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1116_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1116_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_declName_1111_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_a_1172_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1112_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1112_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
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
case 1:
{
lean_object* v_fvarId_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_del_object(v___x_1088_);
v_fvarId_1180_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_fvarId_1180_);
lean_dec_ref(v___x_1105_);
v___x_1181_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
lean_inc(v___x_1181_);
v___x_1182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1182_, 0, v_fvarId_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_mk_empty_array_with_capacity(v___x_1181_);
lean_dec(v___x_1181_);
v___x_1184_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1086_, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1182_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
case 2:
{
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
if (v_isMatch_1078_ == 0)
{
lean_object* v_mvarId_1187_; lean_object* v___x_1188_; 
v_mvarId_1187_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_mvarId_1187_);
lean_dec_ref(v___x_1105_);
v___x_1188_ = l_Lean_Meta_getConfig___redArg(v___y_1101_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1221_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1221_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1221_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v_isDefEqStuckEx_1193_; 
v_isDefEqStuckEx_1193_ = lean_ctor_get_uint8(v_a_1189_, 4);
lean_dec(v_a_1189_);
if (v_isDefEqStuckEx_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_del_object(v___x_1191_);
v___x_1194_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1187_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1208_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_unbox(v_a_1195_);
lean_dec(v_a_1195_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1204_);
v___x_1206_ = v___x_1197_;
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
v_a_1209_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1194_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1194_);
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
lean_object* v___x_1217_; lean_object* v___x_1219_; 
lean_dec(v_mvarId_1187_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2));
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1217_);
v___x_1219_ = v___x_1191_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_mvarId_1187_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
v_a_1222_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1188_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1188_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref(v___x_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
case 11:
{
lean_object* v_typeName_1232_; lean_object* v_idx_1233_; lean_object* v_struct_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_del_object(v___x_1088_);
v_typeName_1232_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_typeName_1232_);
v_idx_1233_ = lean_ctor_get(v___x_1105_, 1);
lean_inc(v_idx_1233_);
v_struct_1234_ = lean_ctor_get(v___x_1105_, 2);
lean_inc_ref(v_struct_1234_);
lean_dec_ref(v___x_1105_);
v___x_1235_ = l_Lean_Expr_getAppNumArgs(v_a_1086_);
lean_inc(v___x_1235_);
v___x_1236_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1236_, 0, v_typeName_1232_);
lean_ctor_set(v___x_1236_, 1, v_idx_1233_);
lean_ctor_set(v___x_1236_, 2, v___x_1235_);
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_mk_empty_array_with_capacity(v___x_1237_);
v___x_1239_ = lean_array_push(v___x_1238_, v_struct_1234_);
v___x_1240_ = lean_mk_empty_array_with_capacity(v___x_1235_);
lean_dec(v___x_1235_);
v___x_1241_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1086_, v___x_1240_);
v___x_1242_ = l_Array_append___redArg(v___x_1239_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1236_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
case 7:
{
lean_object* v_binderType_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v_binderType_1245_ = lean_ctor_get(v___x_1105_, 1);
lean_inc_ref(v_binderType_1245_);
lean_dec_ref(v___x_1105_);
v___x_1246_ = lean_box(5);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_mk_empty_array_with_capacity(v___x_1247_);
v___x_1249_ = lean_array_push(v___x_1248_, v_binderType_1245_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1246_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
default: 
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v___x_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_del_object(v___x_1088_);
lean_dec(v_a_1086_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3));
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
v_a_1267_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1085_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1085_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(lean_object* v_e_1275_, lean_object* v_isMatch_1276_, lean_object* v_root_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
uint8_t v_isMatch_boxed_1283_; uint8_t v_root_boxed_1284_; lean_object* v_res_1285_; 
v_isMatch_boxed_1283_ = lean_unbox(v_isMatch_1276_);
v_root_boxed_1284_ = lean_unbox(v_root_1277_);
v_res_1285_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1275_, v_isMatch_boxed_1283_, v_root_boxed_1284_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_1286_, v___y_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(lean_object* v_inst_1300_, lean_object* v_R_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_, lean_object* v_c_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_1302_, v_b_1303_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(lean_object* v_inst_1311_, lean_object* v_R_1312_, lean_object* v_a_1313_, lean_object* v_b_1314_, lean_object* v_c_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_1311_, v_R_1312_, v_a_1313_, v_b_1314_, v_c_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(lean_object* v_e_1322_, uint8_t v_root_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
uint8_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = 1;
v___x_1330_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1322_, v___x_1329_, v_root_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(lean_object* v_e_1331_, lean_object* v_root_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
uint8_t v_root_boxed_1338_; lean_object* v_res_1339_; 
v_root_boxed_1338_ = lean_unbox(v_root_1332_);
v_res_1339_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(v_e_1331_, v_root_boxed_1338_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(lean_object* v_e_1340_, uint8_t v_root_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
uint8_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = 0;
v___x_1348_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1340_, v___x_1347_, v_root_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(lean_object* v_e_1349_, lean_object* v_root_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
uint8_t v_root_boxed_1356_; lean_object* v_res_1357_; 
v_root_boxed_1356_ = lean_unbox(v_root_1350_);
v_res_1357_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(v_e_1349_, v_root_boxed_1356_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1358_, lean_object* v_vals_1359_, lean_object* v_i_1360_, lean_object* v_k_1361_){
_start:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_array_get_size(v_keys_1358_);
v___x_1363_ = lean_nat_dec_lt(v_i_1360_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_dec(v_i_1360_);
v___x_1364_ = lean_box(0);
return v___x_1364_;
}
else
{
lean_object* v_k_x27_1365_; uint8_t v___x_1366_; 
v_k_x27_1365_ = lean_array_fget_borrowed(v_keys_1358_, v_i_1360_);
v___x_1366_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_1361_, v_k_x27_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v_i_1360_, v___x_1367_);
lean_dec(v_i_1360_);
v_i_1360_ = v___x_1368_;
goto _start;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_array_fget_borrowed(v_vals_1359_, v_i_1360_);
lean_dec(v_i_1360_);
lean_inc(v___x_1370_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_i_1374_, lean_object* v_k_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1372_, v_vals_1373_, v_i_1374_, v_k_1375_);
lean_dec(v_k_1375_);
lean_dec_ref(v_vals_1373_);
lean_dec_ref(v_keys_1372_);
return v_res_1376_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; 
v___x_1377_ = ((size_t)5ULL);
v___x_1378_ = ((size_t)1ULL);
v___x_1379_ = lean_usize_shift_left(v___x_1378_, v___x_1377_);
return v___x_1379_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0);
v___x_1382_ = lean_usize_sub(v___x_1381_, v___x_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(lean_object* v_x_1383_, size_t v_x_1384_, lean_object* v_x_1385_){
_start:
{
if (lean_obj_tag(v_x_1383_) == 0)
{
lean_object* v_es_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1407_; 
v_es_1386_ = lean_ctor_get(v_x_1383_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_x_1383_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1388_ = v_x_1383_;
v_isShared_1389_ = v_isSharedCheck_1407_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_es_1386_);
lean_dec(v_x_1383_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1407_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; lean_object* v_j_1394_; lean_object* v___x_1395_; 
v___x_1390_ = lean_box(2);
v___x_1391_ = ((size_t)5ULL);
v___x_1392_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1);
v___x_1393_ = lean_usize_land(v_x_1384_, v___x_1392_);
v_j_1394_ = lean_usize_to_nat(v___x_1393_);
v___x_1395_ = lean_array_get(v___x_1390_, v_es_1386_, v_j_1394_);
lean_dec(v_j_1394_);
lean_dec_ref(v_es_1386_);
switch(lean_obj_tag(v___x_1395_))
{
case 0:
{
lean_object* v_key_1396_; lean_object* v_val_1397_; uint8_t v___x_1398_; 
v_key_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_key_1396_);
v_val_1397_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_val_1397_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1385_, v_key_1396_);
lean_dec(v_key_1396_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; 
lean_dec(v_val_1397_);
lean_del_object(v___x_1388_);
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
else
{
lean_object* v___x_1401_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set_tag(v___x_1388_, 1);
lean_ctor_set(v___x_1388_, 0, v_val_1397_);
v___x_1401_ = v___x_1388_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_val_1397_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
case 1:
{
lean_object* v_node_1403_; size_t v___x_1404_; 
lean_del_object(v___x_1388_);
v_node_1403_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_node_1403_);
lean_dec_ref(v___x_1395_);
v___x_1404_ = lean_usize_shift_right(v_x_1384_, v___x_1391_);
v_x_1383_ = v_node_1403_;
v_x_1384_ = v___x_1404_;
goto _start;
}
default: 
{
lean_object* v___x_1406_; 
lean_del_object(v___x_1388_);
v___x_1406_ = lean_box(0);
return v___x_1406_;
}
}
}
}
else
{
lean_object* v_ks_1408_; lean_object* v_vs_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_ks_1408_ = lean_ctor_get(v_x_1383_, 0);
lean_inc_ref(v_ks_1408_);
v_vs_1409_ = lean_ctor_get(v_x_1383_, 1);
lean_inc_ref(v_vs_1409_);
lean_dec_ref(v_x_1383_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_1408_, v_vs_1409_, v___x_1410_, v_x_1385_);
lean_dec_ref(v_vs_1409_);
lean_dec_ref(v_ks_1408_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(lean_object* v_x_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
size_t v_x_181__boxed_1415_; lean_object* v_res_1416_; 
v_x_181__boxed_1415_ = lean_unbox_usize(v_x_1413_);
lean_dec(v_x_1413_);
v_res_1416_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1412_, v_x_181__boxed_1415_, v_x_1414_);
lean_dec(v_x_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
uint64_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_1418_);
v___x_1420_ = lean_uint64_to_usize(v___x_1419_);
v___x_1421_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1417_, v___x_1420_, v_x_1418_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1422_, v_x_1423_);
lean_dec(v_x_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(lean_object* v_d_1425_){
_start:
{
lean_object* v___x_1426_; lean_object* v_result_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = lean_unsigned_to_nat(8u);
v_result_1427_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1425_, v___x_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
return v_result_1427_;
}
else
{
lean_object* v_val_1430_; lean_object* v_vs_1431_; lean_object* v___x_1432_; 
v_val_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_val_1430_);
lean_dec_ref(v___x_1429_);
v_vs_1431_ = lean_ctor_get(v_val_1430_, 0);
lean_inc_ref(v_vs_1431_);
lean_dec(v_val_1430_);
v___x_1432_ = l_Array_append___redArg(v_result_1427_, v_vs_1431_);
lean_dec_ref(v_vs_1431_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(lean_object* v_00_u03b1_1433_, lean_object* v_d_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object* v_00_u03b2_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(lean_object* v_00_u03b2_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_1440_, v_x_1441_, v_x_1442_);
lean_dec(v_x_1442_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(lean_object* v_00_u03b2_1444_, lean_object* v_x_1445_, size_t v_x_1446_, lean_object* v_x_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_1445_, v_x_1446_, v_x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
size_t v_x_281__boxed_1453_; lean_object* v_res_1454_; 
v_x_281__boxed_1453_ = lean_unbox_usize(v_x_1451_);
lean_dec(v_x_1451_);
v_res_1454_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_1449_, v_x_1450_, v_x_281__boxed_1453_, v_x_1452_);
lean_dec(v_x_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1455_, lean_object* v_keys_1456_, lean_object* v_vals_1457_, lean_object* v_heq_1458_, lean_object* v_i_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_1456_, v_vals_1457_, v_i_1459_, v_k_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_keys_1463_, lean_object* v_vals_1464_, lean_object* v_heq_1465_, lean_object* v_i_1466_, lean_object* v_k_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_1462_, v_keys_1463_, v_vals_1464_, v_heq_1465_, v_i_1466_, v_k_1467_);
lean_dec(v_k_1467_);
lean_dec_ref(v_vals_1464_);
lean_dec_ref(v_keys_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(lean_object* v_a_1469_, lean_object* v_b_1470_){
_start:
{
lean_object* v_fst_1471_; lean_object* v_fst_1472_; uint8_t v___x_1473_; 
v_fst_1471_ = lean_ctor_get(v_a_1469_, 0);
v_fst_1472_ = lean_ctor_get(v_b_1470_, 0);
v___x_1473_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_1471_, v_fst_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(lean_object* v_a_1474_, lean_object* v_b_1475_){
_start:
{
uint8_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1474_, v_b_1475_);
lean_dec_ref(v_b_1475_);
lean_dec_ref(v_a_1474_);
v_r_1477_ = lean_box(v_res_1476_);
return v_r_1477_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(lean_object* v_cs_1484_, lean_object* v_k_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_array_get_size(v_cs_1484_);
v___x_1488_ = lean_nat_dec_lt(v___x_1486_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; 
lean_dec(v_k_1485_);
v___x_1489_ = lean_box(0);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_sub(v___x_1487_, v___x_1490_);
v___x_1492_ = lean_nat_dec_le(v___x_1486_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec(v___x_1491_);
lean_dec(v_k_1485_);
v___x_1493_ = lean_box(0);
return v___x_1493_;
}
else
{
lean_object* v___f_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___f_1494_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1495_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_k_1485_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1498_ = l_Array_binSearchAux___redArg(v___f_1494_, v___x_1497_, v_cs_1484_, v___x_1496_, v___x_1486_, v___x_1491_);
return v___x_1498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(lean_object* v_cs_1499_, lean_object* v_k_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(v_cs_1499_, v_k_1500_);
lean_dec_ref(v_cs_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(lean_object* v_00_u03b1_1502_, lean_object* v_cs_1503_, lean_object* v_k_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = lean_array_get_size(v_cs_1503_);
v___x_1507_ = lean_nat_dec_lt(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_dec(v_k_1504_);
v___x_1508_ = lean_box(0);
return v___x_1508_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_sub(v___x_1506_, v___x_1509_);
v___x_1511_ = lean_nat_dec_le(v___x_1505_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_dec(v___x_1510_);
lean_dec(v_k_1504_);
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
else
{
lean_object* v___f_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___f_1513_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0));
v___x_1514_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_k_1504_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3));
v___x_1517_ = l_Array_binSearchAux___redArg(v___f_1513_, v___x_1516_, v_cs_1503_, v___x_1515_, v___x_1505_, v___x_1510_);
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_cs_1519_, lean_object* v_k_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(v_00_u03b1_1518_, v_cs_1519_, v_k_1520_);
lean_dec_ref(v_cs_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(lean_object* v_as_1522_, lean_object* v_k_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_m_1528_; lean_object* v_a_1529_; uint8_t v___x_1530_; 
v___x_1526_ = lean_nat_add(v_x_1524_, v_x_1525_);
v___x_1527_ = lean_unsigned_to_nat(1u);
v_m_1528_ = lean_nat_shiftr(v___x_1526_, v___x_1527_);
lean_dec(v___x_1526_);
v_a_1529_ = lean_array_fget_borrowed(v_as_1522_, v_m_1528_);
v___x_1530_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_1529_, v_k_1523_);
if (v___x_1530_ == 0)
{
uint8_t v___x_1531_; 
lean_dec(v_x_1525_);
v___x_1531_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_1523_, v_a_1529_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec(v_m_1528_);
lean_dec(v_x_1524_);
lean_inc(v_a_1529_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_a_1529_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_nat_dec_eq(v_m_1528_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = lean_nat_sub(v_m_1528_, v___x_1527_);
lean_dec(v_m_1528_);
v___x_1536_ = lean_nat_dec_lt(v___x_1535_, v_x_1524_);
if (v___x_1536_ == 0)
{
v_x_1525_ = v___x_1535_;
goto _start;
}
else
{
lean_object* v___x_1538_; 
lean_dec(v___x_1535_);
lean_dec(v_x_1524_);
v___x_1538_ = lean_box(0);
return v___x_1538_;
}
}
else
{
lean_object* v___x_1539_; 
lean_dec(v_m_1528_);
lean_dec(v_x_1524_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
}
}
else
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
lean_dec(v_x_1524_);
v___x_1540_ = lean_nat_add(v_m_1528_, v___x_1527_);
lean_dec(v_m_1528_);
v___x_1541_ = lean_nat_dec_le(v___x_1540_, v_x_1525_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
lean_dec(v___x_1540_);
lean_dec(v_x_1525_);
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
else
{
v_x_1524_ = v___x_1540_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_1544_, lean_object* v_k_1545_, lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1544_, v_k_1545_, v_x_1546_, v_x_1547_);
lean_dec_ref(v_k_1545_);
lean_dec_ref(v_as_1544_);
return v_res_1548_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0(void){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return v___x_1549_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___x_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(lean_object* v_todo_1553_, lean_object* v_c_1554_, lean_object* v_result_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_vs_1561_; lean_object* v_children_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_vs_1561_ = lean_ctor_get(v_c_1554_, 0);
lean_inc_ref(v_vs_1561_);
v_children_1562_ = lean_ctor_get(v_c_1554_, 1);
lean_inc_ref(v_children_1562_);
lean_dec_ref(v_c_1554_);
v___x_1563_ = lean_array_get_size(v_todo_1553_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_nat_dec_eq(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
lean_dec_ref(v_vs_1561_);
v___x_1566_ = lean_array_get_size(v_children_1562_);
v___x_1567_ = lean_nat_dec_eq(v___x_1566_, v___x_1564_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_e_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1568_ = l_Lean_instInhabitedExpr;
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_nat_sub(v___x_1563_, v___x_1569_);
v_e_1571_ = lean_array_get_borrowed(v___x_1568_, v_todo_1553_, v___x_1570_);
lean_dec(v___x_1570_);
v___x_1572_ = 1;
lean_inc(v_a_1559_);
lean_inc_ref(v_a_1558_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
lean_inc(v_e_1571_);
v___x_1573_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1571_, v___x_1572_, v___x_1567_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1611_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1611_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1611_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_fst_1578_; lean_object* v_snd_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_first_1582_; lean_object* v_fst_1583_; lean_object* v_snd_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1610_; 
v_fst_1578_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_fst_1578_);
v_snd_1579_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_snd_1579_);
lean_dec(v_a_1574_);
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v_first_1582_ = lean_array_get(v___x_1581_, v_children_1562_, v___x_1564_);
v_fst_1583_ = lean_ctor_get(v_first_1582_, 0);
v_snd_1584_ = lean_ctor_get(v_first_1582_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_first_1582_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1586_ = v_first_1582_;
v_isShared_1587_ = v_isSharedCheck_1610_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_snd_1584_);
lean_inc(v_fst_1583_);
lean_dec(v_first_1582_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1610_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_todo_1588_; lean_object* v___y_1590_; lean_object* v_a_1591_; uint8_t v___x_1604_; 
v_todo_1588_ = lean_array_pop(v_todo_1553_);
v___x_1604_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_1583_, v___x_1580_);
lean_dec(v_fst_1583_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1606_; 
lean_dec(v_snd_1584_);
lean_inc_ref(v_result_1555_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_result_1555_);
v___x_1606_ = v___x_1576_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_result_1555_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v___y_1590_ = v___x_1606_;
v_a_1591_ = v_result_1555_;
goto v___jp_1589_;
}
}
else
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1576_);
lean_inc(v_a_1559_);
lean_inc_ref(v_a_1558_);
lean_inc(v_a_1557_);
lean_inc_ref(v_a_1556_);
lean_inc_ref(v_todo_1588_);
v___x_1608_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1588_, v_snd_1584_, v_result_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
v___y_1590_ = v___x_1608_;
v_a_1591_ = v_a_1609_;
goto v___jp_1589_;
}
else
{
lean_dec_ref(v_todo_1588_);
lean_del_object(v___x_1586_);
lean_dec(v_snd_1579_);
lean_dec(v_fst_1578_);
lean_dec_ref(v_children_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v___x_1608_;
}
}
v___jp_1589_:
{
if (lean_obj_tag(v_fst_1578_) == 0)
{
lean_dec_ref(v_a_1591_);
lean_dec_ref(v_todo_1588_);
lean_del_object(v___x_1586_);
lean_dec(v_snd_1579_);
lean_dec_ref(v_children_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v___y_1590_;
}
else
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_nat_dec_lt(v___x_1564_, v___x_1566_);
if (v___x_1592_ == 0)
{
lean_dec_ref(v_a_1591_);
lean_dec_ref(v_todo_1588_);
lean_del_object(v___x_1586_);
lean_dec(v_snd_1579_);
lean_dec(v_fst_1578_);
lean_dec_ref(v_children_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v___y_1590_;
}
else
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = lean_nat_sub(v___x_1566_, v___x_1569_);
v___x_1594_ = lean_nat_dec_le(v___x_1564_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_dec(v___x_1593_);
lean_dec_ref(v_a_1591_);
lean_dec_ref(v_todo_1588_);
lean_del_object(v___x_1586_);
lean_dec(v_snd_1579_);
lean_dec(v_fst_1578_);
lean_dec_ref(v_children_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v___y_1590_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v___x_1595_);
lean_ctor_set(v___x_1586_, 0, v_fst_1578_);
v___x_1597_ = v___x_1586_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_fst_1578_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_1562_, v___x_1597_, v___x_1564_, v___x_1593_);
lean_dec_ref(v___x_1597_);
lean_dec_ref(v_children_1562_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_dec_ref(v_a_1591_);
lean_dec_ref(v_todo_1588_);
lean_dec(v_snd_1579_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v___y_1590_;
}
else
{
lean_object* v_val_1599_; lean_object* v_snd_1600_; lean_object* v___x_1601_; 
lean_dec_ref(v___y_1590_);
v_val_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_val_1599_);
lean_dec_ref(v___x_1598_);
v_snd_1600_ = lean_ctor_get(v_val_1599_, 1);
lean_inc(v_snd_1600_);
lean_dec(v_val_1599_);
v___x_1601_ = l_Array_append___redArg(v_todo_1588_, v_snd_1579_);
lean_dec(v_snd_1579_);
v_todo_1553_ = v___x_1601_;
v_c_1554_ = v_snd_1600_;
v_result_1555_ = v_a_1591_;
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
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_children_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec_ref(v_result_1555_);
lean_dec_ref(v_todo_1553_);
v_a_1612_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1573_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1573_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v___x_1620_; 
lean_dec_ref(v_children_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec_ref(v_todo_1553_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_result_1555_);
return v___x_1620_;
}
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_children_1562_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec_ref(v_todo_1553_);
v___x_1621_ = l_Array_append___redArg(v_result_1555_, v_vs_1561_);
lean_dec_ref(v_vs_1561_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(lean_object* v_todo_1623_, lean_object* v_c_1624_, lean_object* v_result_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1623_, v_c_1624_, v_result_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(lean_object* v_00_u03b1_1632_, lean_object* v_todo_1633_, lean_object* v_c_1634_, lean_object* v_result_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_1633_, v_c_1634_, v_result_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_1642_, lean_object* v_todo_1643_, lean_object* v_c_1644_, lean_object* v_result_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(v_00_u03b1_1642_, v_todo_1643_, v_c_1644_, v_result_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(lean_object* v_00_u03b1_1652_, lean_object* v_as_1653_, lean_object* v_k_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_1653_, v_k_1654_, v_x_1655_, v_x_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_1659_, lean_object* v_as_1660_, lean_object* v_k_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_1659_, v_as_1660_, v_k_1661_, v_x_1662_, v_x_1663_, v_x_1664_);
lean_dec_ref(v_k_1661_);
lean_dec_ref(v_as_1660_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(lean_object* v_d_1666_, lean_object* v_k_1667_, lean_object* v_args_1668_, lean_object* v_result_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1666_, v_k_1667_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; 
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec_ref(v_args_1668_);
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_result_1669_);
return v___x_1676_;
}
else
{
lean_object* v_val_1677_; lean_object* v___x_1678_; 
v_val_1677_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1677_);
lean_dec_ref(v___x_1675_);
v___x_1678_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_args_1668_, v_val_1677_, v_result_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(lean_object* v_d_1679_, lean_object* v_k_1680_, lean_object* v_args_1681_, lean_object* v_result_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1679_, v_k_1680_, v_args_1681_, v_result_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_k_1680_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(lean_object* v_00_u03b1_1689_, lean_object* v_d_1690_, lean_object* v_k_1691_, lean_object* v_args_1692_, lean_object* v_result_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1690_, v_k_1691_, v_args_1692_, v_result_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_d_1701_, lean_object* v_k_1702_, lean_object* v_args_1703_, lean_object* v_result_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(v_00_u03b1_1700_, v_d_1701_, v_k_1702_, v_args_1703_, v_result_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_k_1702_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(lean_object* v_d_1711_, lean_object* v_e_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1718_; uint8_t v_foApprox_1719_; uint8_t v_ctxApprox_1720_; uint8_t v_quasiPatternApprox_1721_; uint8_t v_constApprox_1722_; uint8_t v_isDefEqStuckEx_1723_; uint8_t v_unificationHints_1724_; uint8_t v_proofIrrelevance_1725_; uint8_t v_assignSyntheticOpaque_1726_; uint8_t v_offsetCnstrs_1727_; uint8_t v_etaStruct_1728_; uint8_t v_univApprox_1729_; uint8_t v_iota_1730_; uint8_t v_beta_1731_; uint8_t v_proj_1732_; uint8_t v_zeta_1733_; uint8_t v_zetaDelta_1734_; uint8_t v_zetaUnused_1735_; uint8_t v_zetaHave_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1823_; 
v___x_1718_ = l_Lean_Meta_Context_config(v_a_1713_);
v_foApprox_1719_ = lean_ctor_get_uint8(v___x_1718_, 0);
v_ctxApprox_1720_ = lean_ctor_get_uint8(v___x_1718_, 1);
v_quasiPatternApprox_1721_ = lean_ctor_get_uint8(v___x_1718_, 2);
v_constApprox_1722_ = lean_ctor_get_uint8(v___x_1718_, 3);
v_isDefEqStuckEx_1723_ = lean_ctor_get_uint8(v___x_1718_, 4);
v_unificationHints_1724_ = lean_ctor_get_uint8(v___x_1718_, 5);
v_proofIrrelevance_1725_ = lean_ctor_get_uint8(v___x_1718_, 6);
v_assignSyntheticOpaque_1726_ = lean_ctor_get_uint8(v___x_1718_, 7);
v_offsetCnstrs_1727_ = lean_ctor_get_uint8(v___x_1718_, 8);
v_etaStruct_1728_ = lean_ctor_get_uint8(v___x_1718_, 10);
v_univApprox_1729_ = lean_ctor_get_uint8(v___x_1718_, 11);
v_iota_1730_ = lean_ctor_get_uint8(v___x_1718_, 12);
v_beta_1731_ = lean_ctor_get_uint8(v___x_1718_, 13);
v_proj_1732_ = lean_ctor_get_uint8(v___x_1718_, 14);
v_zeta_1733_ = lean_ctor_get_uint8(v___x_1718_, 15);
v_zetaDelta_1734_ = lean_ctor_get_uint8(v___x_1718_, 16);
v_zetaUnused_1735_ = lean_ctor_get_uint8(v___x_1718_, 17);
v_zetaHave_1736_ = lean_ctor_get_uint8(v___x_1718_, 18);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1738_ = v___x_1718_;
v_isShared_1739_ = v_isSharedCheck_1823_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v___x_1718_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1823_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
uint8_t v_trackZetaDelta_1740_; lean_object* v_zetaDeltaSet_1741_; lean_object* v_lctx_1742_; lean_object* v_localInstances_1743_; lean_object* v_defEqCtx_x3f_1744_; lean_object* v_synthPendingDepth_1745_; lean_object* v_canUnfold_x3f_1746_; uint8_t v_univApprox_1747_; uint8_t v_inTypeClassResolution_1748_; uint8_t v_cacheInferType_1749_; uint8_t v___x_1750_; lean_object* v_config_1752_; 
v_trackZetaDelta_1740_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*7);
v_zetaDeltaSet_1741_ = lean_ctor_get(v_a_1713_, 1);
lean_inc(v_zetaDeltaSet_1741_);
v_lctx_1742_ = lean_ctor_get(v_a_1713_, 2);
lean_inc_ref(v_lctx_1742_);
v_localInstances_1743_ = lean_ctor_get(v_a_1713_, 3);
lean_inc_ref(v_localInstances_1743_);
v_defEqCtx_x3f_1744_ = lean_ctor_get(v_a_1713_, 4);
lean_inc(v_defEqCtx_x3f_1744_);
v_synthPendingDepth_1745_ = lean_ctor_get(v_a_1713_, 5);
lean_inc(v_synthPendingDepth_1745_);
v_canUnfold_x3f_1746_ = lean_ctor_get(v_a_1713_, 6);
lean_inc(v_canUnfold_x3f_1746_);
v_univApprox_1747_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1748_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*7 + 2);
v_cacheInferType_1749_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*7 + 3);
v___x_1750_ = 2;
if (v_isShared_1739_ == 0)
{
v_config_1752_ = v___x_1738_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 0, v_foApprox_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 1, v_ctxApprox_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 2, v_quasiPatternApprox_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 3, v_constApprox_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 4, v_isDefEqStuckEx_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 5, v_unificationHints_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 6, v_proofIrrelevance_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 7, v_assignSyntheticOpaque_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 8, v_offsetCnstrs_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 10, v_etaStruct_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 11, v_univApprox_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 12, v_iota_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 13, v_beta_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 14, v_proj_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 15, v_zeta_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 16, v_zetaDelta_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 17, v_zetaUnused_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, 18, v_zetaHave_1736_);
v_config_1752_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
uint64_t v___x_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1814_; 
lean_ctor_set_uint8(v_config_1752_, 9, v___x_1750_);
v___x_1753_ = l_Lean_Meta_Context_configKey(v_a_1713_);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_a_1713_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; lean_object* v_unused_1816_; lean_object* v_unused_1817_; lean_object* v_unused_1818_; lean_object* v_unused_1819_; lean_object* v_unused_1820_; lean_object* v_unused_1821_; 
v_unused_1815_ = lean_ctor_get(v_a_1713_, 6);
lean_dec(v_unused_1815_);
v_unused_1816_ = lean_ctor_get(v_a_1713_, 5);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v_a_1713_, 4);
lean_dec(v_unused_1817_);
v_unused_1818_ = lean_ctor_get(v_a_1713_, 3);
lean_dec(v_unused_1818_);
v_unused_1819_ = lean_ctor_get(v_a_1713_, 2);
lean_dec(v_unused_1819_);
v_unused_1820_ = lean_ctor_get(v_a_1713_, 1);
lean_dec(v_unused_1820_);
v_unused_1821_ = lean_ctor_get(v_a_1713_, 0);
lean_dec(v_unused_1821_);
v___x_1755_ = v_a_1713_;
v_isShared_1756_ = v_isSharedCheck_1814_;
goto v_resetjp_1754_;
}
else
{
lean_dec(v_a_1713_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1814_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
uint64_t v___x_1757_; uint64_t v___x_1758_; uint8_t v___x_1759_; uint64_t v___x_1760_; uint64_t v___x_1761_; uint64_t v_key_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1757_ = 2ULL;
v___x_1758_ = lean_uint64_shift_right(v___x_1753_, v___x_1757_);
v___x_1759_ = 1;
v___x_1760_ = lean_uint64_shift_left(v___x_1758_, v___x_1757_);
v___x_1761_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_1762_ = lean_uint64_lor(v___x_1760_, v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1763_, 0, v_config_1752_);
lean_ctor_set_uint64(v___x_1763_, sizeof(void*)*1, v_key_1762_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1763_);
v___x_1765_ = v___x_1755_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_zetaDeltaSet_1741_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_lctx_1742_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_localInstances_1743_);
lean_ctor_set(v_reuseFailAlloc_1813_, 4, v_defEqCtx_x3f_1744_);
lean_ctor_set(v_reuseFailAlloc_1813_, 5, v_synthPendingDepth_1745_);
lean_ctor_set(v_reuseFailAlloc_1813_, 6, v_canUnfold_x3f_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*7, v_trackZetaDelta_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*7 + 1, v_univApprox_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*7 + 3, v_cacheInferType_1749_);
v___x_1765_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; 
lean_inc(v_a_1716_);
lean_inc_ref(v_a_1715_);
lean_inc(v_a_1714_);
lean_inc_ref(v___x_1765_);
v___x_1766_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_1712_, v___x_1759_, v___x_1759_, v___x_1765_, v_a_1714_, v_a_1715_, v_a_1716_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1804_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1804_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1804_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_fst_1771_; lean_object* v_snd_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1803_; 
v_fst_1771_ = lean_ctor_get(v_a_1767_, 0);
v_snd_1772_ = lean_ctor_get(v_a_1767_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1774_ = v_a_1767_;
v_isShared_1775_ = v_isSharedCheck_1803_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_snd_1772_);
lean_inc(v_fst_1771_);
lean_dec(v_a_1767_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1803_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_result_1776_; 
lean_inc_ref(v_d_1711_);
v_result_1776_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_1711_);
if (lean_obj_tag(v_fst_1771_) == 0)
{
lean_object* v___x_1778_; 
lean_dec(v_snd_1772_);
lean_dec_ref(v___x_1765_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_d_1711_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_result_1776_);
v___x_1778_ = v___x_1774_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_fst_1771_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_result_1776_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1778_);
v___x_1780_ = v___x_1769_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
else
{
lean_object* v___x_1783_; 
lean_del_object(v___x_1769_);
v___x_1783_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_1711_, v_fst_1771_, v_snd_1772_, v_result_1776_, v___x_1765_, v_a_1714_, v_a_1715_, v_a_1716_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1794_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1794_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_a_1784_);
v___x_1789_ = v___x_1774_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_fst_1771_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1789_);
v___x_1791_ = v___x_1786_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_del_object(v___x_1774_);
lean_dec(v_fst_1771_);
v_a_1795_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1783_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1783_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec_ref(v___x_1765_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_d_1711_);
v_a_1805_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1766_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1766_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(lean_object* v_d_1824_, lean_object* v_e_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1824_, v_e_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(lean_object* v_00_u03b1_1832_, lean_object* v_d_1833_, lean_object* v_e_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1833_, v_e_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_d_1842_, lean_object* v_e_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(v_00_u03b1_1841_, v_d_1842_, v_e_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object* v_d_1850_, lean_object* v_e_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_1850_, v_e_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1866_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_snd_1862_; lean_object* v___x_1864_; 
v_snd_1862_ = lean_ctor_get(v_a_1858_, 1);
lean_inc(v_snd_1862_);
lean_dec(v_a_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v_snd_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_snd_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1857_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1857_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(lean_object* v_d_1875_, lean_object* v_e_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1875_, v_e_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch(lean_object* v_00_u03b1_1883_, lean_object* v_d_1884_, lean_object* v_e_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_d_1884_, v_e_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatch___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_d_1893_, lean_object* v_e_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Meta_DiscrTree_getMatch(v_00_u03b1_1892_, v_d_1893_, v_e_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_1901_, lean_object* v_k_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_k_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; 
switch(lean_obj_tag(v_k_1902_))
{
case 4:
{
lean_object* v_a_1930_; lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1942_; 
v_a_1930_ = lean_ctor_get(v_k_1902_, 0);
v_a_1931_ = lean_ctor_get(v_k_1902_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_k_1902_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1933_ = v_k_1902_;
v_isShared_1934_ = v_isSharedCheck_1942_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_inc(v_a_1930_);
lean_dec(v_k_1902_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1942_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_zero_1935_; uint8_t v_isZero_1936_; 
v_zero_1935_ = lean_unsigned_to_nat(0u);
v_isZero_1936_ = lean_nat_dec_eq(v_a_1931_, v_zero_1935_);
if (v_isZero_1936_ == 0)
{
lean_object* v_one_1937_; lean_object* v_n_1938_; lean_object* v___x_1940_; 
v_one_1937_ = lean_unsigned_to_nat(1u);
v_n_1938_ = lean_nat_sub(v_a_1931_, v_one_1937_);
lean_dec(v_a_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v_n_1938_);
v___x_1940_ = v___x_1933_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1930_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_n_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
v_k_1913_ = v___x_1940_;
v___y_1914_ = v_a_1903_;
v___y_1915_ = v_a_1904_;
v___y_1916_ = v_a_1905_;
v___y_1917_ = v_a_1906_;
goto v___jp_1912_;
}
}
else
{
lean_del_object(v___x_1933_);
lean_dec(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_d_1901_);
goto v___jp_1908_;
}
}
}
case 3:
{
lean_object* v_a_1943_; lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1955_; 
v_a_1943_ = lean_ctor_get(v_k_1902_, 0);
v_a_1944_ = lean_ctor_get(v_k_1902_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_k_1902_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1946_ = v_k_1902_;
v_isShared_1947_ = v_isSharedCheck_1955_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_inc(v_a_1943_);
lean_dec(v_k_1902_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1955_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v_zero_1948_; uint8_t v_isZero_1949_; 
v_zero_1948_ = lean_unsigned_to_nat(0u);
v_isZero_1949_ = lean_nat_dec_eq(v_a_1944_, v_zero_1948_);
if (v_isZero_1949_ == 0)
{
lean_object* v_one_1950_; lean_object* v_n_1951_; lean_object* v___x_1953_; 
v_one_1950_ = lean_unsigned_to_nat(1u);
v_n_1951_ = lean_nat_sub(v_a_1944_, v_one_1950_);
lean_dec(v_a_1944_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 1, v_n_1951_);
v___x_1953_ = v___x_1946_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1943_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_n_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
v_k_1913_ = v___x_1953_;
v___y_1914_ = v_a_1903_;
v___y_1915_ = v_a_1904_;
v___y_1916_ = v_a_1905_;
v___y_1917_ = v_a_1906_;
goto v___jp_1912_;
}
}
else
{
lean_del_object(v___x_1946_);
lean_dec(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_d_1901_);
goto v___jp_1908_;
}
}
}
case 6:
{
lean_object* v_a_1956_; lean_object* v_a_1957_; lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1969_; 
v_a_1956_ = lean_ctor_get(v_k_1902_, 0);
v_a_1957_ = lean_ctor_get(v_k_1902_, 1);
v_a_1958_ = lean_ctor_get(v_k_1902_, 2);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_k_1902_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1960_ = v_k_1902_;
v_isShared_1961_ = v_isSharedCheck_1969_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_inc(v_a_1957_);
lean_inc(v_a_1956_);
lean_dec(v_k_1902_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1969_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_zero_1962_; uint8_t v_isZero_1963_; 
v_zero_1962_ = lean_unsigned_to_nat(0u);
v_isZero_1963_ = lean_nat_dec_eq(v_a_1958_, v_zero_1962_);
if (v_isZero_1963_ == 0)
{
lean_object* v_one_1964_; lean_object* v_n_1965_; lean_object* v___x_1967_; 
v_one_1964_ = lean_unsigned_to_nat(1u);
v_n_1965_ = lean_nat_sub(v_a_1958_, v_one_1964_);
lean_dec(v_a_1958_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 2, v_n_1965_);
v___x_1967_ = v___x_1960_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1956_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1957_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_n_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
v_k_1913_ = v___x_1967_;
v___y_1914_ = v_a_1903_;
v___y_1915_ = v_a_1904_;
v___y_1916_ = v_a_1905_;
v___y_1917_ = v_a_1906_;
goto v___jp_1912_;
}
}
else
{
lean_del_object(v___x_1960_);
lean_dec(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_d_1901_);
goto v___jp_1908_;
}
}
}
default: 
{
lean_dec(v_k_1902_);
lean_dec_ref(v_d_1901_);
goto v___jp_1908_;
}
}
v___jp_1908_:
{
uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = 0;
v___x_1910_ = lean_box(v___x_1909_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
v___jp_1912_:
{
lean_object* v___x_1918_; 
lean_inc_ref(v_d_1901_);
v___x_1918_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_1901_, v_k_1913_);
if (lean_obj_tag(v___x_1918_) == 0)
{
v_k_1902_ = v_k_1913_;
v_a_1903_ = v___y_1914_;
v_a_1904_ = v___y_1915_;
v_a_1905_ = v___y_1916_;
v_a_1906_ = v___y_1917_;
goto _start;
}
else
{
lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_k_1913_);
lean_dec_ref(v_d_1901_);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1918_, 0);
lean_dec(v_unused_1929_);
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
else
{
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = 1;
v___x_1924_ = lean_box(v___x_1923_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1924_);
v___x_1926_ = v___x_1921_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_1970_, lean_object* v_k_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1970_, v_k_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_1978_, lean_object* v_d_1979_, lean_object* v_k_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_1979_, v_k_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_1987_, lean_object* v_d_1988_, lean_object* v_k_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_1987_, v_d_1988_, v_k_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_1996_, size_t v_sz_1997_, size_t v_i_1998_, lean_object* v_bs_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_usize_dec_lt(v_i_1998_, v_sz_1997_);
if (v___x_2000_ == 0)
{
lean_dec(v_numExtra_1996_);
return v_bs_1999_;
}
else
{
lean_object* v_v_2001_; lean_object* v___x_2002_; lean_object* v_bs_x27_2003_; lean_object* v___x_2004_; size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v_v_2001_ = lean_array_uget(v_bs_1999_, v_i_1998_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v_bs_x27_2003_ = lean_array_uset(v_bs_1999_, v_i_1998_, v___x_2002_);
lean_inc(v_numExtra_1996_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v_v_2001_);
lean_ctor_set(v___x_2004_, 1, v_numExtra_1996_);
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_add(v_i_1998_, v___x_2005_);
v___x_2007_ = lean_array_uset(v_bs_x27_2003_, v_i_1998_, v___x_2004_);
v_i_1998_ = v___x_2006_;
v_bs_1999_ = v___x_2007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_2009_, lean_object* v_sz_2010_, lean_object* v_i_2011_, lean_object* v_bs_2012_){
_start:
{
size_t v_sz_boxed_2013_; size_t v_i_boxed_2014_; lean_object* v_res_2015_; 
v_sz_boxed_2013_ = lean_unbox_usize(v_sz_2010_);
lean_dec(v_sz_2010_);
v_i_boxed_2014_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2009_, v_sz_boxed_2013_, v_i_boxed_2014_, v_bs_2012_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(lean_object* v_d_2016_, lean_object* v_e_2017_, lean_object* v_numExtra_2018_, lean_object* v_result_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v___x_2025_; 
lean_inc(v_a_2023_);
lean_inc_ref(v_a_2022_);
lean_inc(v_a_2021_);
lean_inc_ref(v_a_2020_);
lean_inc_ref(v_e_2017_);
lean_inc_ref(v_d_2016_);
v___x_2025_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2016_, v_e_2017_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2043_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2043_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2043_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_snd_2030_; size_t v_sz_2031_; size_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_snd_2030_ = lean_ctor_get(v_a_2026_, 1);
lean_inc(v_snd_2030_);
lean_dec(v_a_2026_);
v_sz_2031_ = lean_array_size(v_snd_2030_);
v___x_2032_ = ((size_t)0ULL);
lean_inc(v_numExtra_2018_);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2018_, v_sz_2031_, v___x_2032_, v_snd_2030_);
v___x_2034_ = l_Array_append___redArg(v_result_2019_, v___x_2033_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_Expr_isApp(v_e_2017_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2037_; 
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_numExtra_2018_);
lean_dec_ref(v_e_2017_);
lean_dec_ref(v_d_2016_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2034_);
v___x_2037_ = v___x_2028_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2034_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_del_object(v___x_2028_);
v___x_2039_ = l_Lean_Expr_appFn_x21(v_e_2017_);
lean_dec_ref(v_e_2017_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_numExtra_2018_, v___x_2040_);
lean_dec(v_numExtra_2018_);
v_e_2017_ = v___x_2039_;
v_numExtra_2018_ = v___x_2041_;
v_result_2019_ = v___x_2034_;
goto _start;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec_ref(v_result_2019_);
lean_dec(v_numExtra_2018_);
lean_dec_ref(v_e_2017_);
lean_dec_ref(v_d_2016_);
v_a_2044_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2025_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2025_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_2052_, lean_object* v_e_2053_, lean_object* v_numExtra_2054_, lean_object* v_result_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2052_, v_e_2053_, v_numExtra_2054_, v_result_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(lean_object* v_00_u03b1_2062_, lean_object* v_d_2063_, lean_object* v_e_2064_, lean_object* v_numExtra_2065_, lean_object* v_result_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2063_, v_e_2064_, v_numExtra_2065_, v_result_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_2073_, lean_object* v_d_2074_, lean_object* v_e_2075_, lean_object* v_numExtra_2076_, lean_object* v_result_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(v_00_u03b1_2073_, v_d_2074_, v_e_2075_, v_numExtra_2076_, v_result_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_2084_, lean_object* v_numExtra_2085_, size_t v_sz_2086_, size_t v_i_2087_, lean_object* v_bs_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_2085_, v_sz_2086_, v_i_2087_, v_bs_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_numExtra_2091_, lean_object* v_sz_2092_, lean_object* v_i_2093_, lean_object* v_bs_2094_){
_start:
{
size_t v_sz_boxed_2095_; size_t v_i_boxed_2096_; lean_object* v_res_2097_; 
v_sz_boxed_2095_ = lean_unbox_usize(v_sz_2092_);
lean_dec(v_sz_2092_);
v_i_boxed_2096_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_2090_, v_numExtra_2091_, v_sz_boxed_2095_, v_i_boxed_2096_, v_bs_2094_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(size_t v_sz_2098_, size_t v_i_2099_, lean_object* v_bs_2100_){
_start:
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_usize_dec_lt(v_i_2099_, v_sz_2098_);
if (v___x_2101_ == 0)
{
return v_bs_2100_;
}
else
{
lean_object* v_v_2102_; lean_object* v___x_2103_; lean_object* v_bs_x27_2104_; lean_object* v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; lean_object* v___x_2108_; 
v_v_2102_ = lean_array_uget(v_bs_2100_, v_i_2099_);
v___x_2103_ = lean_unsigned_to_nat(0u);
v_bs_x27_2104_ = lean_array_uset(v_bs_2100_, v_i_2099_, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_v_2102_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_i_2099_, v___x_2106_);
v___x_2108_ = lean_array_uset(v_bs_x27_2104_, v_i_2099_, v___x_2105_);
v_i_2099_ = v___x_2107_;
v_bs_2100_ = v___x_2108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_2110_, lean_object* v_i_2111_, lean_object* v_bs_2112_){
_start:
{
size_t v_sz_boxed_2113_; size_t v_i_boxed_2114_; lean_object* v_res_2115_; 
v_sz_boxed_2113_ = lean_unbox_usize(v_sz_2110_);
lean_dec(v_sz_2110_);
v_i_boxed_2114_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_res_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_2113_, v_i_boxed_2114_, v_bs_2112_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object* v_d_2116_, lean_object* v_e_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; 
lean_inc(v_a_2121_);
lean_inc_ref(v_a_2120_);
lean_inc(v_a_2119_);
lean_inc_ref(v_a_2118_);
lean_inc_ref(v_e_2117_);
lean_inc_ref(v_d_2116_);
v___x_2123_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_2116_, v_e_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2158_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2158_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2158_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_fst_2128_; lean_object* v_snd_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v_fst_2128_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_fst_2128_);
v_snd_2129_ = lean_ctor_get(v_a_2124_, 1);
lean_inc(v_snd_2129_);
lean_dec(v_a_2124_);
v_sz_2130_ = lean_array_size(v_snd_2129_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2130_, v___x_2131_, v_snd_2129_);
v___x_2133_ = l_Lean_Expr_isApp(v_e_2117_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2135_; 
lean_dec(v_fst_2128_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_e_2117_);
lean_dec_ref(v_d_2116_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2132_);
v___x_2135_ = v___x_2126_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2132_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
else
{
lean_object* v___x_2137_; 
lean_del_object(v___x_2126_);
lean_inc_ref(v_d_2116_);
v___x_2137_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_2116_, v_fst_2128_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2149_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2149_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2149_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_unbox(v_a_2138_);
lean_dec(v_a_2138_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2144_; 
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_e_2117_);
lean_dec_ref(v_d_2116_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2132_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2132_);
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
lean_del_object(v___x_2140_);
v___x_2146_ = l_Lean_Expr_appFn_x21(v_e_2117_);
lean_dec_ref(v_e_2117_);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_2116_, v___x_2146_, v___x_2147_, v___x_2132_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2148_;
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v___x_2132_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_e_2117_);
lean_dec_ref(v_d_2116_);
v_a_2150_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2137_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2137_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_e_2117_);
lean_dec_ref(v_d_2116_);
v_a_2159_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2123_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2123_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(lean_object* v_d_2167_, lean_object* v_e_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2167_, v_e_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object* v_00_u03b1_2175_, lean_object* v_d_2176_, lean_object* v_e_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_d_2176_, v_e_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(lean_object* v_00_u03b1_2184_, lean_object* v_d_2185_, lean_object* v_e_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(v_00_u03b1_2184_, v_d_2185_, v_e_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_2193_, size_t v_sz_2194_, size_t v_i_2195_, lean_object* v_bs_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_2194_, v_i_2195_, v_bs_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_2198_, lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_bs_2201_){
_start:
{
size_t v_sz_boxed_2202_; size_t v_i_boxed_2203_; lean_object* v_res_2204_; 
v_sz_boxed_2202_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2203_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_2198_, v_sz_boxed_2202_, v_i_boxed_2203_, v_bs_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor(lean_object* v_e_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
uint8_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = 1;
v___x_2212_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2205_, v___x_2211_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2237_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2237_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2237_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___y_2219_; lean_object* v___x_2224_; 
v___x_2217_ = l_Lean_Expr_getAppNumArgs(v_a_2213_);
v___x_2224_ = l_Lean_Expr_getAppFn(v_a_2213_);
lean_dec(v_a_2213_);
switch(lean_obj_tag(v___x_2224_))
{
case 9:
{
lean_object* v_a_2225_; lean_object* v___x_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc_ref(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_a_2225_);
v___y_2219_ = v___x_2226_;
goto v___jp_2218_;
}
case 1:
{
lean_object* v_fvarId_2227_; lean_object* v___x_2228_; 
v_fvarId_2227_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_fvarId_2227_);
lean_dec_ref(v___x_2224_);
lean_inc(v___x_2217_);
v___x_2228_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_fvarId_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2217_);
v___y_2219_ = v___x_2228_;
goto v___jp_2218_;
}
case 2:
{
lean_object* v___x_2229_; 
lean_dec_ref(v___x_2224_);
v___x_2229_ = lean_box(1);
v___y_2219_ = v___x_2229_;
goto v___jp_2218_;
}
case 11:
{
lean_object* v_typeName_2230_; lean_object* v_idx_2231_; lean_object* v___x_2232_; 
v_typeName_2230_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_typeName_2230_);
v_idx_2231_ = lean_ctor_get(v___x_2224_, 1);
lean_inc(v_idx_2231_);
lean_dec_ref(v___x_2224_);
lean_inc(v___x_2217_);
v___x_2232_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2232_, 0, v_typeName_2230_);
lean_ctor_set(v___x_2232_, 1, v_idx_2231_);
lean_ctor_set(v___x_2232_, 2, v___x_2217_);
v___y_2219_ = v___x_2232_;
goto v___jp_2218_;
}
case 7:
{
lean_object* v___x_2233_; 
lean_dec_ref(v___x_2224_);
v___x_2233_ = lean_box(5);
v___y_2219_ = v___x_2233_;
goto v___jp_2218_;
}
case 4:
{
lean_object* v_declName_2234_; lean_object* v___x_2235_; 
v_declName_2234_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_declName_2234_);
lean_dec_ref(v___x_2224_);
lean_inc(v___x_2217_);
v___x_2235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_declName_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2217_);
v___y_2219_ = v___x_2235_;
goto v___jp_2218_;
}
default: 
{
lean_object* v___x_2236_; 
lean_dec_ref(v___x_2224_);
v___x_2236_ = lean_box(1);
v___y_2219_ = v___x_2236_;
goto v___jp_2218_;
}
}
v___jp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___y_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_2217_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2220_);
v___x_2222_ = v___x_2215_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
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
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_a_2238_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2212_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2212_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(lean_object* v_e_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(lean_object* v_as_2253_, size_t v_sz_2254_, size_t v_i_2255_, lean_object* v_b_2256_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_usize_dec_lt(v_i_2255_, v_sz_2254_);
if (v___x_2257_ == 0)
{
return v_b_2256_;
}
else
{
lean_object* v_a_2258_; lean_object* v_snd_2259_; lean_object* v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; 
v_a_2258_ = lean_array_uget_borrowed(v_as_2253_, v_i_2255_);
v_snd_2259_ = lean_ctor_get(v_a_2258_, 1);
v___x_2260_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_2259_, v_b_2256_);
v___x_2261_ = ((size_t)1ULL);
v___x_2262_ = lean_usize_add(v_i_2255_, v___x_2261_);
v_i_2255_ = v___x_2262_;
v_b_2256_ = v___x_2260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(lean_object* v_trie_2264_, lean_object* v_result_2265_){
_start:
{
lean_object* v_vs_2266_; lean_object* v_children_2267_; lean_object* v_result_2268_; size_t v_sz_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v_vs_2266_ = lean_ctor_get(v_trie_2264_, 0);
v_children_2267_ = lean_ctor_get(v_trie_2264_, 1);
v_result_2268_ = l_Array_append___redArg(v_result_2265_, v_vs_2266_);
v_sz_2269_ = lean_array_size(v_children_2267_);
v___x_2270_ = ((size_t)0ULL);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_2267_, v_sz_2269_, v___x_2270_, v_result_2268_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(lean_object* v_trie_2272_, lean_object* v_result_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2272_, v_result_2273_);
lean_dec_ref(v_trie_2272_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(lean_object* v_as_2275_, lean_object* v_sz_2276_, lean_object* v_i_2277_, lean_object* v_b_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2276_);
lean_dec(v_sz_2276_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2275_, v_sz_boxed_2279_, v_i_boxed_2280_, v_b_2278_);
lean_dec_ref(v_as_2275_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(lean_object* v_00_u03b1_2282_, lean_object* v_trie_2283_, lean_object* v_result_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_trie_2283_, v_result_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_trie_2287_, lean_object* v_result_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(v_00_u03b1_2286_, v_trie_2287_, v_result_2288_);
lean_dec_ref(v_trie_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(lean_object* v_00_u03b1_2290_, lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_b_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_2291_, v_sz_2292_, v_i_2293_, v_b_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_as_2297_, lean_object* v_sz_2298_, lean_object* v_i_2299_, lean_object* v_b_2300_){
_start:
{
size_t v_sz_boxed_2301_; size_t v_i_boxed_2302_; lean_object* v_res_2303_; 
v_sz_boxed_2301_ = lean_unbox_usize(v_sz_2298_);
lean_dec(v_sz_2298_);
v_i_boxed_2302_ = lean_unbox_usize(v_i_2299_);
lean_dec(v_i_2299_);
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_2296_, v_as_2297_, v_sz_boxed_2301_, v_i_boxed_2302_, v_b_2300_);
lean_dec_ref(v_as_2297_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(lean_object* v_d_2304_, lean_object* v_k_2305_, lean_object* v_result_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2304_, v_k_2305_);
if (lean_obj_tag(v___x_2307_) == 0)
{
return v_result_2306_;
}
else
{
lean_object* v_val_2308_; lean_object* v___x_2309_; 
v_val_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_val_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_2308_, v_result_2306_);
lean_dec(v_val_2308_);
return v___x_2309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(lean_object* v_d_2310_, lean_object* v_k_2311_, lean_object* v_result_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2310_, v_k_2311_, v_result_2312_);
lean_dec(v_k_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(lean_object* v_00_u03b1_2314_, lean_object* v_d_2315_, lean_object* v_k_2316_, lean_object* v_result_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2315_, v_k_2316_, v_result_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(lean_object* v_00_u03b1_2319_, lean_object* v_d_2320_, lean_object* v_k_2321_, lean_object* v_result_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(v_00_u03b1_2319_, v_d_2320_, v_k_2321_, v_result_2322_);
lean_dec(v_k_2321_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object* v_d_2324_, lean_object* v_e_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___x_2331_; uint8_t v_foApprox_2332_; uint8_t v_ctxApprox_2333_; uint8_t v_quasiPatternApprox_2334_; uint8_t v_constApprox_2335_; uint8_t v_isDefEqStuckEx_2336_; uint8_t v_unificationHints_2337_; uint8_t v_proofIrrelevance_2338_; uint8_t v_assignSyntheticOpaque_2339_; uint8_t v_offsetCnstrs_2340_; uint8_t v_etaStruct_2341_; uint8_t v_univApprox_2342_; uint8_t v_iota_2343_; uint8_t v_beta_2344_; uint8_t v_proj_2345_; uint8_t v_zeta_2346_; uint8_t v_zetaDelta_2347_; uint8_t v_zetaUnused_2348_; uint8_t v_zetaHave_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2416_; 
v___x_2331_ = l_Lean_Meta_Context_config(v_a_2326_);
v_foApprox_2332_ = lean_ctor_get_uint8(v___x_2331_, 0);
v_ctxApprox_2333_ = lean_ctor_get_uint8(v___x_2331_, 1);
v_quasiPatternApprox_2334_ = lean_ctor_get_uint8(v___x_2331_, 2);
v_constApprox_2335_ = lean_ctor_get_uint8(v___x_2331_, 3);
v_isDefEqStuckEx_2336_ = lean_ctor_get_uint8(v___x_2331_, 4);
v_unificationHints_2337_ = lean_ctor_get_uint8(v___x_2331_, 5);
v_proofIrrelevance_2338_ = lean_ctor_get_uint8(v___x_2331_, 6);
v_assignSyntheticOpaque_2339_ = lean_ctor_get_uint8(v___x_2331_, 7);
v_offsetCnstrs_2340_ = lean_ctor_get_uint8(v___x_2331_, 8);
v_etaStruct_2341_ = lean_ctor_get_uint8(v___x_2331_, 10);
v_univApprox_2342_ = lean_ctor_get_uint8(v___x_2331_, 11);
v_iota_2343_ = lean_ctor_get_uint8(v___x_2331_, 12);
v_beta_2344_ = lean_ctor_get_uint8(v___x_2331_, 13);
v_proj_2345_ = lean_ctor_get_uint8(v___x_2331_, 14);
v_zeta_2346_ = lean_ctor_get_uint8(v___x_2331_, 15);
v_zetaDelta_2347_ = lean_ctor_get_uint8(v___x_2331_, 16);
v_zetaUnused_2348_ = lean_ctor_get_uint8(v___x_2331_, 17);
v_zetaHave_2349_ = lean_ctor_get_uint8(v___x_2331_, 18);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2351_ = v___x_2331_;
v_isShared_2352_ = v_isSharedCheck_2416_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v___x_2331_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2416_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
uint8_t v_trackZetaDelta_2353_; lean_object* v_zetaDeltaSet_2354_; lean_object* v_lctx_2355_; lean_object* v_localInstances_2356_; lean_object* v_defEqCtx_x3f_2357_; lean_object* v_synthPendingDepth_2358_; lean_object* v_canUnfold_x3f_2359_; uint8_t v_univApprox_2360_; uint8_t v_inTypeClassResolution_2361_; uint8_t v_cacheInferType_2362_; uint8_t v___x_2363_; lean_object* v_config_2365_; 
v_trackZetaDelta_2353_ = lean_ctor_get_uint8(v_a_2326_, sizeof(void*)*7);
v_zetaDeltaSet_2354_ = lean_ctor_get(v_a_2326_, 1);
lean_inc(v_zetaDeltaSet_2354_);
v_lctx_2355_ = lean_ctor_get(v_a_2326_, 2);
lean_inc_ref(v_lctx_2355_);
v_localInstances_2356_ = lean_ctor_get(v_a_2326_, 3);
lean_inc_ref(v_localInstances_2356_);
v_defEqCtx_x3f_2357_ = lean_ctor_get(v_a_2326_, 4);
lean_inc(v_defEqCtx_x3f_2357_);
v_synthPendingDepth_2358_ = lean_ctor_get(v_a_2326_, 5);
lean_inc(v_synthPendingDepth_2358_);
v_canUnfold_x3f_2359_ = lean_ctor_get(v_a_2326_, 6);
lean_inc(v_canUnfold_x3f_2359_);
v_univApprox_2360_ = lean_ctor_get_uint8(v_a_2326_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2361_ = lean_ctor_get_uint8(v_a_2326_, sizeof(void*)*7 + 2);
v_cacheInferType_2362_ = lean_ctor_get_uint8(v_a_2326_, sizeof(void*)*7 + 3);
v___x_2363_ = 2;
if (v_isShared_2352_ == 0)
{
v_config_2365_ = v___x_2351_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 0, v_foApprox_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 1, v_ctxApprox_2333_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 2, v_quasiPatternApprox_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 3, v_constApprox_2335_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 4, v_isDefEqStuckEx_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 5, v_unificationHints_2337_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 6, v_proofIrrelevance_2338_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 7, v_assignSyntheticOpaque_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 8, v_offsetCnstrs_2340_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 10, v_etaStruct_2341_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 11, v_univApprox_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 12, v_iota_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 13, v_beta_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 14, v_proj_2345_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 15, v_zeta_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 16, v_zetaDelta_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 17, v_zetaUnused_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 18, v_zetaHave_2349_);
v_config_2365_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
uint64_t v___x_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2407_; 
lean_ctor_set_uint8(v_config_2365_, 9, v___x_2363_);
v___x_2366_ = l_Lean_Meta_Context_configKey(v_a_2326_);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_a_2326_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; lean_object* v_unused_2409_; lean_object* v_unused_2410_; lean_object* v_unused_2411_; lean_object* v_unused_2412_; lean_object* v_unused_2413_; lean_object* v_unused_2414_; 
v_unused_2408_ = lean_ctor_get(v_a_2326_, 6);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_a_2326_, 5);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v_a_2326_, 4);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_a_2326_, 3);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_a_2326_, 2);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_a_2326_, 1);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_a_2326_, 0);
lean_dec(v_unused_2414_);
v___x_2368_ = v_a_2326_;
v_isShared_2369_ = v_isSharedCheck_2407_;
goto v_resetjp_2367_;
}
else
{
lean_dec(v_a_2326_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2407_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
uint64_t v___x_2370_; uint64_t v___x_2371_; uint64_t v___x_2372_; uint64_t v___x_2373_; uint64_t v_key_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2370_ = 2ULL;
v___x_2371_ = lean_uint64_shift_right(v___x_2366_, v___x_2370_);
v___x_2372_ = lean_uint64_shift_left(v___x_2371_, v___x_2370_);
v___x_2373_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2374_ = lean_uint64_lor(v___x_2372_, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2375_, 0, v_config_2365_);
lean_ctor_set_uint64(v___x_2375_, sizeof(void*)*1, v_key_2374_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2375_);
v___x_2377_ = v___x_2368_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_zetaDeltaSet_2354_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v_lctx_2355_);
lean_ctor_set(v_reuseFailAlloc_2406_, 3, v_localInstances_2356_);
lean_ctor_set(v_reuseFailAlloc_2406_, 4, v_defEqCtx_x3f_2357_);
lean_ctor_set(v_reuseFailAlloc_2406_, 5, v_synthPendingDepth_2358_);
lean_ctor_set(v_reuseFailAlloc_2406_, 6, v_canUnfold_x3f_2359_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*7, v_trackZetaDelta_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*7 + 1, v_univApprox_2360_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*7 + 3, v_cacheInferType_2362_);
v___x_2377_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(v_e_2325_, v___x_2377_, v_a_2327_, v_a_2328_, v_a_2329_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2397_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2397_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2397_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v_fst_2383_; lean_object* v_snd_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2396_; 
v_fst_2383_ = lean_ctor_get(v_a_2379_, 0);
v_snd_2384_ = lean_ctor_get(v_a_2379_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_a_2379_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2386_ = v_a_2379_;
v_isShared_2387_ = v_isSharedCheck_2396_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_snd_2384_);
lean_inc(v_fst_2383_);
lean_dec(v_a_2379_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2396_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v_result_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
lean_inc_ref(v_d_2324_);
v_result_2388_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2324_);
v___x_2389_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_2324_, v_fst_2383_, v_result_2388_);
lean_dec(v_fst_2383_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2389_);
v___x_2391_ = v___x_2386_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_snd_2384_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2393_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2391_);
v___x_2393_ = v___x_2381_;
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
lean_dec_ref(v_d_2324_);
v_a_2398_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2378_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2378_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(lean_object* v_d_2417_, lean_object* v_e_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2417_, v_e_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal(lean_object* v_00_u03b1_2425_, lean_object* v_d_2426_, lean_object* v_e_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(v_d_2426_, v_e_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_d_2435_, lean_object* v_e_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Meta_DiscrTree_getMatchLiberal(v_00_u03b1_2434_, v_d_2435_, v_e_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(lean_object* v_n_2443_, lean_object* v_todo_2444_, lean_object* v_as_2445_, size_t v_i_2446_, size_t v_stop_2447_, lean_object* v_b_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_usize_dec_eq(v_i_2446_, v_stop_2447_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2455_ = lean_array_uget_borrowed(v_as_2445_, v_i_2446_);
v_fst_2456_ = lean_ctor_get(v___x_2455_, 0);
v_snd_2457_ = lean_ctor_get(v___x_2455_, 1);
v___x_2458_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2456_);
v___x_2459_ = lean_nat_add(v_n_2443_, v___x_2458_);
lean_dec(v___x_2458_);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v_snd_2457_);
lean_inc_ref(v_todo_2444_);
v___x_2460_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2459_, v_todo_2444_, v_snd_2457_, v_b_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; size_t v___x_2462_; size_t v___x_2463_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref(v___x_2460_);
v___x_2462_ = ((size_t)1ULL);
v___x_2463_ = lean_usize_add(v_i_2446_, v___x_2462_);
v_i_2446_ = v___x_2463_;
v_b_2448_ = v_a_2461_;
goto _start;
}
else
{
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v_todo_2444_);
return v___x_2460_;
}
}
else
{
lean_object* v___x_2465_; 
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v_todo_2444_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_b_2448_);
return v___x_2465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(lean_object* v_skip_2466_, lean_object* v_todo_2467_, lean_object* v_c_2468_, lean_object* v_result_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_zero_2475_; uint8_t v_isZero_2476_; 
v_zero_2475_ = lean_unsigned_to_nat(0u);
v_isZero_2476_ = lean_nat_dec_eq(v_skip_2466_, v_zero_2475_);
if (v_isZero_2476_ == 1)
{
lean_object* v_vs_2477_; lean_object* v_children_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
lean_dec(v_skip_2466_);
v_vs_2477_ = lean_ctor_get(v_c_2468_, 0);
lean_inc_ref(v_vs_2477_);
v_children_2478_ = lean_ctor_get(v_c_2468_, 1);
lean_inc_ref(v_children_2478_);
lean_dec_ref(v_c_2468_);
v___x_2479_ = lean_array_get_size(v_todo_2467_);
v___x_2480_ = lean_nat_dec_eq(v___x_2479_, v_zero_2475_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
lean_dec_ref(v_vs_2477_);
v___x_2481_ = lean_array_get_size(v_children_2478_);
v___x_2482_ = lean_nat_dec_eq(v___x_2481_, v_zero_2475_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v_e_2486_; lean_object* v___x_2487_; 
v___x_2483_ = l_Lean_instInhabitedExpr;
v___x_2484_ = lean_unsigned_to_nat(1u);
v___x_2485_ = lean_nat_sub(v___x_2479_, v___x_2484_);
v_e_2486_ = lean_array_get_borrowed(v___x_2483_, v_todo_2467_, v___x_2485_);
lean_dec(v___x_2485_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
lean_inc(v_e_2486_);
v___x_2487_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2486_, v___x_2482_, v___x_2482_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2539_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2539_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2539_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2538_; 
v_fst_2492_ = lean_ctor_get(v_a_2488_, 0);
v_snd_2493_ = lean_ctor_get(v_a_2488_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_a_2488_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2495_ = v_a_2488_;
v_isShared_2496_ = v_isSharedCheck_2538_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_snd_2493_);
lean_inc(v_fst_2492_);
lean_dec(v_a_2488_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2538_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_todo_2497_; lean_object* v___y_2499_; lean_object* v_a_2500_; 
v_todo_2497_ = lean_array_pop(v_todo_2467_);
if (lean_obj_tag(v_fst_2492_) == 0)
{
uint8_t v___x_2513_; 
lean_del_object(v___x_2495_);
lean_dec(v_snd_2493_);
v___x_2513_ = lean_nat_dec_lt(v_zero_2475_, v___x_2481_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2515_; 
lean_dec_ref(v_todo_2497_);
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v_result_2469_);
v___x_2515_ = v___x_2490_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_result_2469_);
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
v___x_2517_ = lean_nat_dec_le(v___x_2481_, v___x_2481_);
if (v___x_2517_ == 0)
{
if (v___x_2513_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v_todo_2497_);
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v_result_2469_);
v___x_2519_ = v___x_2490_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_result_2469_);
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
lean_del_object(v___x_2490_);
v___x_2521_ = ((size_t)0ULL);
v___x_2522_ = lean_usize_of_nat(v___x_2481_);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2497_, v_children_2478_, v___x_2521_, v___x_2522_, v_result_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec_ref(v_children_2478_);
return v___x_2523_;
}
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
lean_del_object(v___x_2490_);
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2481_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2497_, v_children_2478_, v___x_2524_, v___x_2525_, v_result_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec_ref(v_children_2478_);
return v___x_2526_;
}
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_fst_2530_; lean_object* v_snd_2531_; uint8_t v___x_2532_; 
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
v___x_2529_ = lean_array_get_borrowed(v___x_2528_, v_children_2478_, v_zero_2475_);
v_fst_2530_ = lean_ctor_get(v___x_2529_, 0);
v_snd_2531_ = lean_ctor_get(v___x_2529_, 1);
v___x_2532_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_2530_, v___x_2527_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2534_; 
lean_inc_ref(v_result_2469_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v_result_2469_);
v___x_2534_ = v___x_2490_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_result_2469_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
v___y_2499_ = v___x_2534_;
v_a_2500_ = v_result_2469_;
goto v___jp_2498_;
}
}
else
{
lean_object* v___x_2536_; 
lean_del_object(v___x_2490_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v_a_2471_);
lean_inc_ref(v_a_2470_);
lean_inc(v_snd_2531_);
lean_inc_ref(v_todo_2497_);
v___x_2536_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_2475_, v_todo_2497_, v_snd_2531_, v_result_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
v___y_2499_ = v___x_2536_;
v_a_2500_ = v_a_2537_;
goto v___jp_2498_;
}
else
{
lean_dec_ref(v_todo_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_snd_2493_);
lean_dec(v_fst_2492_);
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
return v___x_2536_;
}
}
}
v___jp_2498_:
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_nat_dec_lt(v_zero_2475_, v___x_2481_);
if (v___x_2501_ == 0)
{
lean_dec_ref(v_a_2500_);
lean_dec_ref(v_todo_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_snd_2493_);
lean_dec(v_fst_2492_);
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
return v___y_2499_;
}
else
{
lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2502_ = lean_nat_sub(v___x_2481_, v___x_2484_);
v___x_2503_ = lean_nat_dec_le(v_zero_2475_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec(v___x_2502_);
lean_dec_ref(v_a_2500_);
lean_dec_ref(v_todo_2497_);
lean_del_object(v___x_2495_);
lean_dec(v_snd_2493_);
lean_dec(v_fst_2492_);
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
return v___y_2499_;
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2, &l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_once, _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v___x_2504_);
v___x_2506_ = v___x_2495_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_fst_2492_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_2478_, v___x_2506_, v_zero_2475_, v___x_2502_);
lean_dec_ref(v___x_2506_);
lean_dec_ref(v_children_2478_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_dec_ref(v_a_2500_);
lean_dec_ref(v_todo_2497_);
lean_dec(v_snd_2493_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
return v___y_2499_;
}
else
{
lean_object* v_val_2508_; lean_object* v_snd_2509_; lean_object* v___x_2510_; 
lean_dec_ref(v___y_2499_);
v_val_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_val_2508_);
lean_dec_ref(v___x_2507_);
v_snd_2509_ = lean_ctor_get(v_val_2508_, 1);
lean_inc(v_snd_2509_);
lean_dec(v_val_2508_);
v___x_2510_ = l_Array_append___redArg(v_todo_2497_, v_snd_2493_);
lean_dec(v_snd_2493_);
v_skip_2466_ = v_zero_2475_;
v_todo_2467_ = v___x_2510_;
v_c_2468_ = v_snd_2509_;
v_result_2469_ = v_a_2500_;
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
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_result_2469_);
lean_dec_ref(v_todo_2467_);
v_a_2540_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2487_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2487_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_object* v___x_2548_; 
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_todo_2467_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v_result_2469_);
return v___x_2548_;
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec_ref(v_children_2478_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_todo_2467_);
v___x_2549_ = l_Array_append___redArg(v_result_2469_, v_vs_2477_);
lean_dec_ref(v_vs_2477_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
else
{
lean_object* v_children_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_children_2551_ = lean_ctor_get(v_c_2468_, 1);
lean_inc_ref(v_children_2551_);
lean_dec_ref(v_c_2468_);
v___x_2552_ = lean_array_get_size(v_children_2551_);
v___x_2553_ = lean_nat_dec_eq(v___x_2552_, v_zero_2475_);
if (v___x_2553_ == 0)
{
uint8_t v___x_2554_; 
v___x_2554_ = lean_nat_dec_lt(v_zero_2475_, v___x_2552_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
lean_dec_ref(v_children_2551_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_todo_2467_);
lean_dec(v_skip_2466_);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_result_2469_);
return v___x_2555_;
}
else
{
lean_object* v_one_2556_; lean_object* v_n_2557_; uint8_t v___x_2558_; 
v_one_2556_ = lean_unsigned_to_nat(1u);
v_n_2557_ = lean_nat_sub(v_skip_2466_, v_one_2556_);
lean_dec(v_skip_2466_);
v___x_2558_ = lean_nat_dec_le(v___x_2552_, v___x_2552_);
if (v___x_2558_ == 0)
{
if (v___x_2554_ == 0)
{
lean_object* v___x_2559_; 
lean_dec(v_n_2557_);
lean_dec_ref(v_children_2551_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_todo_2467_);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_result_2469_);
return v___x_2559_;
}
else
{
size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = lean_usize_of_nat(v___x_2552_);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2557_, v_todo_2467_, v_children_2551_, v___x_2560_, v___x_2561_, v_result_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec_ref(v_children_2551_);
lean_dec(v_n_2557_);
return v___x_2562_;
}
}
else
{
size_t v___x_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((size_t)0ULL);
v___x_2564_ = lean_usize_of_nat(v___x_2552_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2557_, v_todo_2467_, v_children_2551_, v___x_2563_, v___x_2564_, v_result_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec_ref(v_children_2551_);
lean_dec(v_n_2557_);
return v___x_2565_;
}
}
}
else
{
lean_object* v___x_2566_; 
lean_dec_ref(v_children_2551_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec_ref(v_todo_2467_);
lean_dec(v_skip_2466_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_result_2469_);
return v___x_2566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(lean_object* v_todo_2567_, lean_object* v_as_2568_, size_t v_i_2569_, size_t v_stop_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
uint8_t v___x_2577_; 
v___x_2577_ = lean_usize_dec_eq(v_i_2569_, v_stop_2570_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v_fst_2579_; lean_object* v_snd_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2578_ = lean_array_uget_borrowed(v_as_2568_, v_i_2569_);
v_fst_2579_ = lean_ctor_get(v___x_2578_, 0);
v_snd_2580_ = lean_ctor_get(v___x_2578_, 1);
v___x_2581_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_2579_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
lean_inc(v___y_2573_);
lean_inc_ref(v___y_2572_);
lean_inc(v_snd_2580_);
lean_inc_ref(v_todo_2567_);
v___x_2582_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2581_, v_todo_2567_, v_snd_2580_, v_b_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; size_t v___x_2584_; size_t v___x_2585_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = ((size_t)1ULL);
v___x_2585_ = lean_usize_add(v_i_2569_, v___x_2584_);
v_i_2569_ = v___x_2585_;
v_b_2571_ = v_a_2583_;
goto _start;
}
else
{
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v_todo_2567_);
return v___x_2582_;
}
}
else
{
lean_object* v___x_2587_; 
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v_todo_2567_);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_b_2571_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(lean_object* v_todo_2588_, lean_object* v_as_2589_, lean_object* v_i_2590_, lean_object* v_stop_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
size_t v_i_boxed_2598_; size_t v_stop_boxed_2599_; lean_object* v_res_2600_; 
v_i_boxed_2598_ = lean_unbox_usize(v_i_2590_);
lean_dec(v_i_2590_);
v_stop_boxed_2599_ = lean_unbox_usize(v_stop_2591_);
lean_dec(v_stop_2591_);
v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2588_, v_as_2589_, v_i_boxed_2598_, v_stop_boxed_2599_, v_b_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec_ref(v_as_2589_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(lean_object* v_n_2601_, lean_object* v_todo_2602_, lean_object* v_as_2603_, lean_object* v_i_2604_, lean_object* v_stop_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
size_t v_i_boxed_2612_; size_t v_stop_boxed_2613_; lean_object* v_res_2614_; 
v_i_boxed_2612_ = lean_unbox_usize(v_i_2604_);
lean_dec(v_i_2604_);
v_stop_boxed_2613_ = lean_unbox_usize(v_stop_2605_);
lean_dec(v_stop_2605_);
v_res_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2601_, v_todo_2602_, v_as_2603_, v_i_boxed_2612_, v_stop_boxed_2613_, v_b_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec_ref(v_as_2603_);
lean_dec(v_n_2601_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(lean_object* v_skip_2615_, lean_object* v_todo_2616_, lean_object* v_c_2617_, lean_object* v_result_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2615_, v_todo_2616_, v_c_2617_, v_result_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(lean_object* v_00_u03b1_2625_, lean_object* v_skip_2626_, lean_object* v_todo_2627_, lean_object* v_c_2628_, lean_object* v_result_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_skip_2626_, v_todo_2627_, v_c_2628_, v_result_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_skip_2637_, lean_object* v_todo_2638_, lean_object* v_c_2639_, lean_object* v_result_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(v_00_u03b1_2636_, v_skip_2637_, v_todo_2638_, v_c_2639_, v_result_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(lean_object* v_00_u03b1_2647_, lean_object* v_todo_2648_, lean_object* v_as_2649_, size_t v_i_2650_, size_t v_stop_2651_, lean_object* v_b_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_2648_, v_as_2649_, v_i_2650_, v_stop_2651_, v_b_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(lean_object* v_00_u03b1_2659_, lean_object* v_todo_2660_, lean_object* v_as_2661_, lean_object* v_i_2662_, lean_object* v_stop_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
size_t v_i_boxed_2670_; size_t v_stop_boxed_2671_; lean_object* v_res_2672_; 
v_i_boxed_2670_ = lean_unbox_usize(v_i_2662_);
lean_dec(v_i_2662_);
v_stop_boxed_2671_ = lean_unbox_usize(v_stop_2663_);
lean_dec(v_stop_2663_);
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_2659_, v_todo_2660_, v_as_2661_, v_i_boxed_2670_, v_stop_boxed_2671_, v_b_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec_ref(v_as_2661_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(lean_object* v_00_u03b1_2673_, lean_object* v_n_2674_, lean_object* v_todo_2675_, lean_object* v_as_2676_, size_t v_i_2677_, size_t v_stop_2678_, lean_object* v_b_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_2674_, v_todo_2675_, v_as_2676_, v_i_2677_, v_stop_2678_, v_b_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(lean_object* v_00_u03b1_2686_, lean_object* v_n_2687_, lean_object* v_todo_2688_, lean_object* v_as_2689_, lean_object* v_i_2690_, lean_object* v_stop_2691_, lean_object* v_b_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
size_t v_i_boxed_2698_; size_t v_stop_boxed_2699_; lean_object* v_res_2700_; 
v_i_boxed_2698_ = lean_unbox_usize(v_i_2690_);
lean_dec(v_i_2690_);
v_stop_boxed_2699_ = lean_unbox_usize(v_stop_2691_);
lean_dec(v_stop_2691_);
v_res_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_2686_, v_n_2687_, v_todo_2688_, v_as_2689_, v_i_boxed_2698_, v_stop_boxed_2699_, v_b_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec_ref(v_as_2689_);
lean_dec(v_n_2687_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(lean_object* v_result_2701_, lean_object* v_k_2702_, lean_object* v_c_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_2702_);
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0));
v___x_2711_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2709_, v___x_2710_, v_c_2703_, v_result_2701_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(lean_object* v_result_2712_, lean_object* v_k_2713_, lean_object* v_c_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(v_result_2712_, v_k_2713_, v_c_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v_k_2713_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(lean_object* v_f_2721_, lean_object* v_keys_2722_, lean_object* v_vals_2723_, lean_object* v_i_2724_, lean_object* v_acc_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_array_get_size(v_keys_2722_);
v___x_2732_ = lean_nat_dec_lt(v_i_2724_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_i_2724_);
lean_dec_ref(v_f_2721_);
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_acc_2725_);
return v___x_2733_;
}
else
{
lean_object* v_k_2734_; lean_object* v_v_2735_; lean_object* v___x_2736_; 
v_k_2734_ = lean_array_fget_borrowed(v_keys_2722_, v_i_2724_);
v_v_2735_ = lean_array_fget_borrowed(v_vals_2723_, v_i_2724_);
lean_inc_ref(v_f_2721_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v_v_2735_);
lean_inc(v_k_2734_);
v___x_2736_ = lean_apply_8(v_f_2721_, v_acc_2725_, v_k_2734_, v_v_2735_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, lean_box(0));
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref(v___x_2736_);
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = lean_nat_add(v_i_2724_, v___x_2738_);
lean_dec(v_i_2724_);
v_i_2724_ = v___x_2739_;
v_acc_2725_ = v_a_2737_;
goto _start;
}
else
{
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_i_2724_);
lean_dec_ref(v_f_2721_);
return v___x_2736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_2741_, lean_object* v_keys_2742_, lean_object* v_vals_2743_, lean_object* v_i_2744_, lean_object* v_acc_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2741_, v_keys_2742_, v_vals_2743_, v_i_2744_, v_acc_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec_ref(v_vals_2743_);
lean_dec_ref(v_keys_2742_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(lean_object* v_f_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
if (lean_obj_tag(v_x_2753_) == 0)
{
lean_object* v_es_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2780_; 
v_es_2760_ = lean_ctor_get(v_x_2753_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_x_2753_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2762_ = v_x_2753_;
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_es_2760_);
lean_dec(v_x_2753_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = lean_array_get_size(v_es_2760_);
v___x_2766_ = lean_nat_dec_lt(v___x_2764_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2768_; 
lean_dec_ref(v_es_2760_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v_f_2752_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_x_2754_);
v___x_2768_ = v___x_2762_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_x_2754_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
uint8_t v___x_2770_; 
v___x_2770_ = lean_nat_dec_le(v___x_2765_, v___x_2765_);
if (v___x_2770_ == 0)
{
if (v___x_2766_ == 0)
{
lean_object* v___x_2772_; 
lean_dec_ref(v_es_2760_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v_f_2752_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_x_2754_);
v___x_2772_ = v___x_2762_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_x_2754_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
else
{
size_t v___x_2774_; size_t v___x_2775_; lean_object* v___x_2776_; 
lean_del_object(v___x_2762_);
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = lean_usize_of_nat(v___x_2765_);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2752_, v_es_2760_, v___x_2774_, v___x_2775_, v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
lean_dec_ref(v_es_2760_);
return v___x_2776_;
}
}
else
{
size_t v___x_2777_; size_t v___x_2778_; lean_object* v___x_2779_; 
lean_del_object(v___x_2762_);
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = lean_usize_of_nat(v___x_2765_);
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2752_, v_es_2760_, v___x_2777_, v___x_2778_, v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
lean_dec_ref(v_es_2760_);
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_ks_2781_; lean_object* v_vs_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v_ks_2781_ = lean_ctor_get(v_x_2753_, 0);
lean_inc_ref(v_ks_2781_);
v_vs_2782_ = lean_ctor_get(v_x_2753_, 1);
lean_inc_ref(v_vs_2782_);
lean_dec_ref(v_x_2753_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_2752_, v_ks_2781_, v_vs_2782_, v___x_2783_, v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
lean_dec_ref(v_vs_2782_);
lean_dec_ref(v_ks_2781_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2785_, lean_object* v_as_2786_, size_t v_i_2787_, size_t v_stop_2788_, lean_object* v_b_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_a_2796_; lean_object* v___y_2801_; uint8_t v___x_2803_; 
v___x_2803_ = lean_usize_dec_eq(v_i_2787_, v_stop_2788_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_array_uget_borrowed(v_as_2786_, v_i_2787_);
switch(lean_obj_tag(v___x_2804_))
{
case 0:
{
lean_object* v_key_2805_; lean_object* v_val_2806_; lean_object* v___x_2807_; 
v_key_2805_ = lean_ctor_get(v___x_2804_, 0);
v_val_2806_ = lean_ctor_get(v___x_2804_, 1);
lean_inc_ref(v_f_2785_);
lean_inc(v___y_2793_);
lean_inc_ref(v___y_2792_);
lean_inc(v___y_2791_);
lean_inc_ref(v___y_2790_);
lean_inc(v_val_2806_);
lean_inc(v_key_2805_);
v___x_2807_ = lean_apply_8(v_f_2785_, v_b_2789_, v_key_2805_, v_val_2806_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, lean_box(0));
v___y_2801_ = v___x_2807_;
goto v___jp_2800_;
}
case 1:
{
lean_object* v_node_2808_; lean_object* v___x_2809_; 
v_node_2808_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v___y_2793_);
lean_inc_ref(v___y_2792_);
lean_inc(v___y_2791_);
lean_inc_ref(v___y_2790_);
lean_inc(v_node_2808_);
lean_inc_ref(v_f_2785_);
v___x_2809_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2785_, v_node_2808_, v_b_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
v___y_2801_ = v___x_2809_;
goto v___jp_2800_;
}
default: 
{
v_a_2796_ = v_b_2789_;
goto v___jp_2795_;
}
}
}
else
{
lean_object* v___x_2810_; 
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v_f_2785_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_b_2789_);
return v___x_2810_;
}
v___jp_2795_:
{
size_t v___x_2797_; size_t v___x_2798_; 
v___x_2797_ = ((size_t)1ULL);
v___x_2798_ = lean_usize_add(v_i_2787_, v___x_2797_);
v_i_2787_ = v___x_2798_;
v_b_2789_ = v_a_2796_;
goto _start;
}
v___jp_2800_:
{
if (lean_obj_tag(v___y_2801_) == 0)
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___y_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref(v___y_2801_);
v_a_2796_ = v_a_2802_;
goto v___jp_2795_;
}
else
{
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v_f_2785_);
return v___y_2801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2811_, lean_object* v_as_2812_, lean_object* v_i_2813_, lean_object* v_stop_2814_, lean_object* v_b_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
size_t v_i_boxed_2821_; size_t v_stop_boxed_2822_; lean_object* v_res_2823_; 
v_i_boxed_2821_ = lean_unbox_usize(v_i_2813_);
lean_dec(v_i_2813_);
v_stop_boxed_2822_ = lean_unbox_usize(v_stop_2814_);
lean_dec(v_stop_2814_);
v_res_2823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_2811_, v_as_2812_, v_i_boxed_2821_, v_stop_boxed_2822_, v_b_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref(v_as_2812_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(lean_object* v_f_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2824_, v_x_2825_, v_x_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg(lean_object* v_d_2834_, lean_object* v_e_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___x_2841_; uint8_t v_foApprox_2842_; uint8_t v_ctxApprox_2843_; uint8_t v_quasiPatternApprox_2844_; uint8_t v_constApprox_2845_; uint8_t v_isDefEqStuckEx_2846_; uint8_t v_unificationHints_2847_; uint8_t v_proofIrrelevance_2848_; uint8_t v_assignSyntheticOpaque_2849_; uint8_t v_offsetCnstrs_2850_; uint8_t v_etaStruct_2851_; uint8_t v_univApprox_2852_; uint8_t v_iota_2853_; uint8_t v_beta_2854_; uint8_t v_proj_2855_; uint8_t v_zeta_2856_; uint8_t v_zetaDelta_2857_; uint8_t v_zetaUnused_2858_; uint8_t v_zetaHave_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2927_; 
v___x_2841_ = l_Lean_Meta_Context_config(v_a_2836_);
v_foApprox_2842_ = lean_ctor_get_uint8(v___x_2841_, 0);
v_ctxApprox_2843_ = lean_ctor_get_uint8(v___x_2841_, 1);
v_quasiPatternApprox_2844_ = lean_ctor_get_uint8(v___x_2841_, 2);
v_constApprox_2845_ = lean_ctor_get_uint8(v___x_2841_, 3);
v_isDefEqStuckEx_2846_ = lean_ctor_get_uint8(v___x_2841_, 4);
v_unificationHints_2847_ = lean_ctor_get_uint8(v___x_2841_, 5);
v_proofIrrelevance_2848_ = lean_ctor_get_uint8(v___x_2841_, 6);
v_assignSyntheticOpaque_2849_ = lean_ctor_get_uint8(v___x_2841_, 7);
v_offsetCnstrs_2850_ = lean_ctor_get_uint8(v___x_2841_, 8);
v_etaStruct_2851_ = lean_ctor_get_uint8(v___x_2841_, 10);
v_univApprox_2852_ = lean_ctor_get_uint8(v___x_2841_, 11);
v_iota_2853_ = lean_ctor_get_uint8(v___x_2841_, 12);
v_beta_2854_ = lean_ctor_get_uint8(v___x_2841_, 13);
v_proj_2855_ = lean_ctor_get_uint8(v___x_2841_, 14);
v_zeta_2856_ = lean_ctor_get_uint8(v___x_2841_, 15);
v_zetaDelta_2857_ = lean_ctor_get_uint8(v___x_2841_, 16);
v_zetaUnused_2858_ = lean_ctor_get_uint8(v___x_2841_, 17);
v_zetaHave_2859_ = lean_ctor_get_uint8(v___x_2841_, 18);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2861_ = v___x_2841_;
v_isShared_2862_ = v_isSharedCheck_2927_;
goto v_resetjp_2860_;
}
else
{
lean_dec(v___x_2841_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2927_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
uint8_t v_trackZetaDelta_2863_; lean_object* v_zetaDeltaSet_2864_; lean_object* v_lctx_2865_; lean_object* v_localInstances_2866_; lean_object* v_defEqCtx_x3f_2867_; lean_object* v_synthPendingDepth_2868_; lean_object* v_canUnfold_x3f_2869_; uint8_t v_univApprox_2870_; uint8_t v_inTypeClassResolution_2871_; uint8_t v_cacheInferType_2872_; uint8_t v___x_2873_; lean_object* v_config_2875_; 
v_trackZetaDelta_2863_ = lean_ctor_get_uint8(v_a_2836_, sizeof(void*)*7);
v_zetaDeltaSet_2864_ = lean_ctor_get(v_a_2836_, 1);
lean_inc(v_zetaDeltaSet_2864_);
v_lctx_2865_ = lean_ctor_get(v_a_2836_, 2);
lean_inc_ref(v_lctx_2865_);
v_localInstances_2866_ = lean_ctor_get(v_a_2836_, 3);
lean_inc_ref(v_localInstances_2866_);
v_defEqCtx_x3f_2867_ = lean_ctor_get(v_a_2836_, 4);
lean_inc(v_defEqCtx_x3f_2867_);
v_synthPendingDepth_2868_ = lean_ctor_get(v_a_2836_, 5);
lean_inc(v_synthPendingDepth_2868_);
v_canUnfold_x3f_2869_ = lean_ctor_get(v_a_2836_, 6);
lean_inc(v_canUnfold_x3f_2869_);
v_univApprox_2870_ = lean_ctor_get_uint8(v_a_2836_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2871_ = lean_ctor_get_uint8(v_a_2836_, sizeof(void*)*7 + 2);
v_cacheInferType_2872_ = lean_ctor_get_uint8(v_a_2836_, sizeof(void*)*7 + 3);
v___x_2873_ = 2;
if (v_isShared_2862_ == 0)
{
v_config_2875_ = v___x_2861_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 0, v_foApprox_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 1, v_ctxApprox_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 2, v_quasiPatternApprox_2844_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 3, v_constApprox_2845_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 4, v_isDefEqStuckEx_2846_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 5, v_unificationHints_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 6, v_proofIrrelevance_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 7, v_assignSyntheticOpaque_2849_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 8, v_offsetCnstrs_2850_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 10, v_etaStruct_2851_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 11, v_univApprox_2852_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 12, v_iota_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 13, v_beta_2854_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 14, v_proj_2855_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 15, v_zeta_2856_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 16, v_zetaDelta_2857_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 17, v_zetaUnused_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2926_, 18, v_zetaHave_2859_);
v_config_2875_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
uint64_t v___x_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2918_; 
lean_ctor_set_uint8(v_config_2875_, 9, v___x_2873_);
v___x_2876_ = l_Lean_Meta_Context_configKey(v_a_2836_);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_a_2836_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; lean_object* v_unused_2924_; lean_object* v_unused_2925_; 
v_unused_2919_ = lean_ctor_get(v_a_2836_, 6);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_a_2836_, 5);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_a_2836_, 4);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_a_2836_, 3);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_a_2836_, 2);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_a_2836_, 1);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_a_2836_, 0);
lean_dec(v_unused_2925_);
v___x_2878_ = v_a_2836_;
v_isShared_2879_ = v_isSharedCheck_2918_;
goto v_resetjp_2877_;
}
else
{
lean_dec(v_a_2836_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2918_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint64_t v___x_2880_; uint64_t v___x_2881_; uint8_t v___x_2882_; uint64_t v___x_2883_; uint64_t v___x_2884_; uint64_t v_key_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2880_ = 2ULL;
v___x_2881_ = lean_uint64_shift_right(v___x_2876_, v___x_2880_);
v___x_2882_ = 1;
v___x_2883_ = lean_uint64_shift_left(v___x_2881_, v___x_2880_);
v___x_2884_ = lean_uint64_once(&l_Lean_Meta_DiscrTree_mkPath___closed__0, &l_Lean_Meta_DiscrTree_mkPath___closed__0_once, _init_l_Lean_Meta_DiscrTree_mkPath___closed__0);
v_key_2885_ = lean_uint64_lor(v___x_2883_, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2886_, 0, v_config_2875_);
lean_ctor_set_uint64(v___x_2886_, sizeof(void*)*1, v_key_2885_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2886_);
v___x_2888_ = v___x_2878_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_zetaDeltaSet_2864_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_lctx_2865_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v_localInstances_2866_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v_defEqCtx_x3f_2867_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v_synthPendingDepth_2868_);
lean_ctor_set(v_reuseFailAlloc_2917_, 6, v_canUnfold_x3f_2869_);
lean_ctor_set_uint8(v_reuseFailAlloc_2917_, sizeof(void*)*7, v_trackZetaDelta_2863_);
lean_ctor_set_uint8(v_reuseFailAlloc_2917_, sizeof(void*)*7 + 1, v_univApprox_2870_);
lean_ctor_set_uint8(v_reuseFailAlloc_2917_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2871_);
lean_ctor_set_uint8(v_reuseFailAlloc_2917_, sizeof(void*)*7 + 3, v_cacheInferType_2872_);
v___x_2888_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
uint8_t v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = 0;
lean_inc(v_a_2839_);
lean_inc_ref(v_a_2838_);
lean_inc(v_a_2837_);
lean_inc_ref(v___x_2888_);
v___x_2890_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_2835_, v___x_2889_, v___x_2882_, v___x_2888_, v_a_2837_, v_a_2838_, v_a_2839_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2908_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2908_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2908_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_fst_2895_; 
v_fst_2895_ = lean_ctor_get(v_a_2891_, 0);
lean_inc(v_fst_2895_);
if (lean_obj_tag(v_fst_2895_) == 0)
{
lean_object* v___f_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_del_object(v___x_2893_);
lean_dec(v_a_2891_);
v___f_2896_ = ((lean_object*)(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0));
v___x_2897_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1));
v___x_2898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_2896_, v_d_2834_, v___x_2897_, v___x_2888_, v_a_2837_, v_a_2838_, v_a_2839_);
return v___x_2898_;
}
else
{
lean_object* v_snd_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_snd_2899_ = lean_ctor_get(v_a_2891_, 1);
lean_inc(v_snd_2899_);
lean_dec(v_a_2891_);
lean_inc_ref(v_d_2834_);
v___x_2900_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_2834_);
v___x_2901_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_2834_, v_fst_2895_);
lean_dec(v_fst_2895_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v___x_2903_; 
lean_dec(v_snd_2899_);
lean_dec_ref(v___x_2888_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2900_);
v___x_2903_ = v___x_2893_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2900_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
else
{
lean_object* v_val_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_del_object(v___x_2893_);
v_val_2905_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_val_2905_);
lean_dec_ref(v___x_2901_);
v___x_2906_ = lean_unsigned_to_nat(0u);
v___x_2907_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_2906_, v_snd_2899_, v_val_2905_, v___x_2900_, v___x_2888_, v_a_2837_, v_a_2838_, v_a_2839_);
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v___x_2888_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_d_2834_);
v_a_2909_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2890_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2890_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(lean_object* v_d_2928_, lean_object* v_e_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2928_, v_e_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify(lean_object* v_00_u03b1_2936_, lean_object* v_d_2937_, lean_object* v_e_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Meta_DiscrTree_getUnify___redArg(v_d_2937_, v_e_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_getUnify___boxed(lean_object* v_00_u03b1_2945_, lean_object* v_d_2946_, lean_object* v_e_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_Meta_DiscrTree_getUnify(v_00_u03b1_2945_, v_d_2946_, v_e_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(lean_object* v_map_2954_, lean_object* v_f_2955_, lean_object* v_init_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2955_, v_map_2954_, v_init_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(lean_object* v_map_2963_, lean_object* v_f_2964_, lean_object* v_init_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(v_map_2963_, v_f_2964_, v_init_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(lean_object* v_00_u03c3_2972_, lean_object* v_00_u03b2_2973_, lean_object* v_map_2974_, lean_object* v_f_2975_, lean_object* v_init_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2975_, v_map_2974_, v_init_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(lean_object* v_00_u03c3_2983_, lean_object* v_00_u03b2_2984_, lean_object* v_map_2985_, lean_object* v_f_2986_, lean_object* v_init_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(v_00_u03c3_2983_, v_00_u03b2_2984_, v_map_2985_, v_f_2986_, v_init_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(lean_object* v_00_u03c3_2994_, lean_object* v_00_u03b1_2995_, lean_object* v_00_u03b2_2996_, lean_object* v_f_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_2997_, v_x_2998_, v_x_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3006_, lean_object* v_00_u03b1_3007_, lean_object* v_00_u03b2_3008_, lean_object* v_f_3009_, lean_object* v_x_3010_, lean_object* v_x_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_3006_, v_00_u03b1_3007_, v_00_u03b2_3008_, v_f_3009_, v_x_3010_, v_x_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3018_, lean_object* v_00_u03b2_3019_, lean_object* v_00_u03c3_3020_, lean_object* v_f_3021_, lean_object* v_as_3022_, size_t v_i_3023_, size_t v_stop_3024_, lean_object* v_b_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_3021_, v_as_3022_, v_i_3023_, v_stop_3024_, v_b_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3032_, lean_object* v_00_u03b2_3033_, lean_object* v_00_u03c3_3034_, lean_object* v_f_3035_, lean_object* v_as_3036_, lean_object* v_i_3037_, lean_object* v_stop_3038_, lean_object* v_b_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
size_t v_i_boxed_3045_; size_t v_stop_boxed_3046_; lean_object* v_res_3047_; 
v_i_boxed_3045_ = lean_unbox_usize(v_i_3037_);
lean_dec(v_i_3037_);
v_stop_boxed_3046_ = lean_unbox_usize(v_stop_3038_);
lean_dec(v_stop_3038_);
v_res_3047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_3032_, v_00_u03b2_3033_, v_00_u03c3_3034_, v_f_3035_, v_as_3036_, v_i_boxed_3045_, v_stop_boxed_3046_, v_b_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec_ref(v_as_3036_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_3048_, lean_object* v_00_u03b1_3049_, lean_object* v_00_u03b2_3050_, lean_object* v_f_3051_, lean_object* v_keys_3052_, lean_object* v_vals_3053_, lean_object* v_heq_3054_, lean_object* v_i_3055_, lean_object* v_acc_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_3051_, v_keys_3052_, v_vals_3053_, v_i_3055_, v_acc_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_3063_, lean_object* v_00_u03b1_3064_, lean_object* v_00_u03b2_3065_, lean_object* v_f_3066_, lean_object* v_keys_3067_, lean_object* v_vals_3068_, lean_object* v_heq_3069_, lean_object* v_i_3070_, lean_object* v_acc_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_3063_, v_00_u03b1_3064_, v_00_u03b2_3065_, v_f_3066_, v_keys_3067_, v_vals_3068_, v_heq_3069_, v_i_3070_, v_acc_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec_ref(v_vals_3068_);
lean_dec_ref(v_keys_3067_);
return v_res_3077_;
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
