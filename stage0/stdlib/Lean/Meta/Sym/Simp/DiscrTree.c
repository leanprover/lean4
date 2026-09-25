// Lean compiler output
// Module: Lean.Meta.Sym.Simp.DiscrTree
// Imports: public import Lean.Meta.Sym.Pattern public import Lean.Meta.DiscrTree.Util import Lean.Meta.Sym.Offset import Lean.Meta.Sym.Eta import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_getMatch___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_getMatch___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getMatch___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(lean_object* v_infos_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_array_get_size(v_infos_1_);
v___x_4_ = lean_nat_dec_lt(v_i_2_, v___x_3_);
if (v___x_4_ == 0)
{
return v___x_4_;
}
else
{
lean_object* v_info_5_; uint8_t v_isInstance_6_; 
v_info_5_ = lean_array_fget_borrowed(v_infos_1_, v_i_2_);
v_isInstance_6_ = lean_ctor_get_uint8(v_info_5_, 1);
if (v_isInstance_6_ == 0)
{
uint8_t v_isProof_7_; 
v_isProof_7_ = lean_ctor_get_uint8(v_info_5_, 0);
return v_isProof_7_;
}
else
{
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg___boxed(lean_object* v_infos_8_, lean_object* v_i_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(v_infos_8_, v_i_9_);
lean_dec(v_i_9_);
lean_dec_ref(v_infos_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(lean_object* v_e_12_, lean_object* v_todo_13_){
_start:
{
if (lean_obj_tag(v_e_12_) == 5)
{
lean_object* v_fn_14_; lean_object* v_arg_15_; lean_object* v___x_16_; 
v_fn_14_ = lean_ctor_get(v_e_12_, 0);
lean_inc_ref(v_fn_14_);
v_arg_15_ = lean_ctor_get(v_e_12_, 1);
lean_inc_ref(v_arg_15_);
lean_dec_ref_known(v_e_12_, 2);
v___x_16_ = lean_array_push(v_todo_13_, v_arg_15_);
v_e_12_ = v_fn_14_;
v_todo_13_ = v___x_16_;
goto _start;
}
else
{
lean_dec_ref(v_e_12_);
return v_todo_13_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v_dummyBVar_19_; 
v___x_18_ = lean_unsigned_to_nat(1000000u);
v_dummyBVar_19_ = l_Lean_Expr_bvar___override(v___x_18_);
return v_dummyBVar_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(lean_object* v_infos_20_, lean_object* v_i_21_, lean_object* v_e_22_, lean_object* v_todo_23_){
_start:
{
if (lean_obj_tag(v_e_22_) == 5)
{
lean_object* v_fn_24_; lean_object* v_arg_25_; uint8_t v___x_26_; 
v_fn_24_ = lean_ctor_get(v_e_22_, 0);
lean_inc_ref(v_fn_24_);
v_arg_25_ = lean_ctor_get(v_e_22_, 1);
lean_inc_ref(v_arg_25_);
lean_dec_ref_known(v_e_22_, 2);
v___x_26_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(v_infos_20_, v_i_21_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_sub(v_i_21_, v___x_27_);
lean_dec(v_i_21_);
v___x_29_ = lean_array_push(v_todo_23_, v_arg_25_);
v_i_21_ = v___x_28_;
v_e_22_ = v_fn_24_;
v_todo_23_ = v___x_29_;
goto _start;
}
else
{
lean_object* v_dummyBVar_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec_ref(v_arg_25_);
v_dummyBVar_31_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0, &l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_sub(v_i_21_, v___x_32_);
lean_dec(v_i_21_);
v___x_34_ = lean_array_push(v_todo_23_, v_dummyBVar_31_);
v_i_21_ = v___x_33_;
v_e_22_ = v_fn_24_;
v_todo_23_ = v___x_34_;
goto _start;
}
}
else
{
lean_dec_ref(v_e_22_);
lean_dec(v_i_21_);
return v_todo_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___boxed(lean_object* v_infos_36_, lean_object* v_i_37_, lean_object* v_e_38_, lean_object* v_todo_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(v_infos_36_, v_i_37_, v_e_38_, v_todo_39_);
lean_dec_ref(v_infos_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(lean_object* v_a_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
else
{
lean_object* v_key_44_; lean_object* v_value_45_; lean_object* v_tail_46_; uint8_t v___x_47_; 
v_key_44_ = lean_ctor_get(v_x_42_, 0);
v_value_45_ = lean_ctor_get(v_x_42_, 1);
v_tail_46_ = lean_ctor_get(v_x_42_, 2);
v___x_47_ = lean_name_eq(v_key_44_, v_a_41_);
if (v___x_47_ == 0)
{
v_x_42_ = v_tail_46_;
goto _start;
}
else
{
lean_object* v___x_49_; 
lean_inc(v_value_45_);
v___x_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_49_, 0, v_value_45_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg___boxed(lean_object* v_a_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_50_, v_x_51_);
lean_dec(v_x_51_);
lean_dec(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(uint8_t v_root_53_, lean_object* v_fnInfos_54_, lean_object* v_todo_55_, lean_object* v_e_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_56_);
if (v___x_57_ == 0)
{
lean_object* v_fn_58_; 
v_fn_58_ = l_Lean_Expr_getAppFn(v_e_56_);
switch(lean_obj_tag(v_fn_58_))
{
case 9:
{
lean_object* v_a_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec_ref(v_e_56_);
v_a_59_ = lean_ctor_get(v_fn_58_, 0);
lean_inc_ref(v_a_59_);
lean_dec_ref_known(v_fn_58_, 1);
v___x_60_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_60_, 0, v_a_59_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v_todo_55_);
return v___x_61_;
}
case 0:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec_ref_known(v_fn_58_, 1);
lean_dec_ref(v_e_56_);
v___x_62_ = lean_box(0);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v_todo_55_);
return v___x_63_;
}
case 7:
{
lean_object* v_binderType_64_; lean_object* v_body_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec_ref(v_e_56_);
v_binderType_64_ = lean_ctor_get(v_fn_58_, 1);
lean_inc_ref(v_binderType_64_);
v_body_65_ = lean_ctor_get(v_fn_58_, 2);
lean_inc_ref(v_body_65_);
lean_dec_ref_known(v_fn_58_, 3);
v___x_66_ = lean_box(5);
v___x_67_ = lean_array_push(v_todo_55_, v_body_65_);
v___x_68_ = lean_array_push(v___x_67_, v_binderType_64_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_66_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
return v___x_69_;
}
case 4:
{
lean_object* v_declName_70_; lean_object* v___y_72_; lean_object* v___y_73_; uint8_t v___y_77_; 
v_declName_70_ = lean_ctor_get(v_fn_58_, 0);
lean_inc(v_declName_70_);
lean_dec_ref_known(v_fn_58_, 2);
if (v_root_53_ == 0)
{
goto v___jp_87_;
}
else
{
if (v___x_57_ == 0)
{
v___y_77_ = v___x_57_;
goto v___jp_76_;
}
else
{
goto v___jp_87_;
}
}
v___jp_71_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v_declName_70_);
lean_ctor_set(v___x_74_, 1, v___y_72_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___y_73_);
return v___x_75_;
}
v___jp_76_:
{
if (v___y_77_ == 0)
{
lean_object* v_numArgs_78_; lean_object* v___x_79_; 
v_numArgs_78_ = l_Lean_Expr_getAppNumArgs(v_e_56_);
v___x_79_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_declName_70_, v_fnInfos_54_);
if (lean_obj_tag(v___x_79_) == 1)
{
lean_object* v_val_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_val_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v___x_79_, 1);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_sub(v_numArgs_78_, v___x_81_);
v___x_83_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(v_val_80_, v___x_82_, v_e_56_, v_todo_55_);
lean_dec(v_val_80_);
v___y_72_ = v_numArgs_78_;
v___y_73_ = v___x_83_;
goto v___jp_71_;
}
else
{
lean_object* v___x_84_; 
lean_dec(v___x_79_);
v___x_84_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_56_, v_todo_55_);
v___y_72_ = v_numArgs_78_;
v___y_73_ = v___x_84_;
goto v___jp_71_;
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_declName_70_);
lean_dec_ref(v_e_56_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_todo_55_);
return v___x_86_;
}
}
v___jp_87_:
{
uint8_t v___x_88_; 
lean_inc_ref(v_e_56_);
v___x_88_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_70_, v_e_56_);
v___y_77_ = v___x_88_;
goto v___jp_76_;
}
}
case 1:
{
lean_object* v_fvarId_89_; lean_object* v_numArgs_90_; lean_object* v_todo_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_fvarId_89_ = lean_ctor_get(v_fn_58_, 0);
lean_inc(v_fvarId_89_);
lean_dec_ref_known(v_fn_58_, 1);
v_numArgs_90_ = l_Lean_Expr_getAppNumArgs(v_e_56_);
v_todo_91_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_56_, v_todo_55_);
v___x_92_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_92_, 0, v_fvarId_89_);
lean_ctor_set(v___x_92_, 1, v_numArgs_90_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v_todo_91_);
return v___x_93_;
}
default: 
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec_ref(v_fn_58_);
lean_dec_ref(v_e_56_);
v___x_94_ = lean_box(1);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_todo_55_);
return v___x_95_;
}
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec_ref(v_e_56_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_todo_55_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs___boxed(lean_object* v_root_98_, lean_object* v_fnInfos_99_, lean_object* v_todo_100_, lean_object* v_e_101_){
_start:
{
uint8_t v_root_boxed_102_; lean_object* v_res_103_; 
v_root_boxed_102_ = lean_unbox(v_root_98_);
v_res_103_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_boxed_102_, v_fnInfos_99_, v_todo_100_, v_e_101_);
lean_dec(v_fnInfos_99_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(lean_object* v_00_u03b2_104_, lean_object* v_a_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___boxed(lean_object* v_00_u03b2_108_, lean_object* v_a_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(v_00_u03b2_108_, v_a_109_, v_x_110_);
lean_dec(v_x_110_);
lean_dec(v_a_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(uint8_t v_root_112_, lean_object* v_fnInfos_113_, lean_object* v_todo_114_, lean_object* v_keys_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_array_get_size(v_todo_114_);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_dec_eq(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_e_122_; lean_object* v_todo_123_; lean_object* v___x_124_; lean_object* v_fst_125_; lean_object* v_snd_126_; lean_object* v___x_127_; 
v___x_119_ = l_Lean_instInhabitedExpr;
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_sub(v___x_116_, v___x_120_);
v_e_122_ = lean_array_get(v___x_119_, v_todo_114_, v___x_121_);
lean_dec(v___x_121_);
v_todo_123_ = lean_array_pop(v_todo_114_);
v___x_124_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_112_, v_fnInfos_113_, v_todo_123_, v_e_122_);
v_fst_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_fst_125_);
v_snd_126_ = lean_ctor_get(v___x_124_, 1);
lean_inc(v_snd_126_);
lean_dec_ref(v___x_124_);
v___x_127_ = lean_array_push(v_keys_115_, v_fst_125_);
v_root_112_ = v___x_118_;
v_todo_114_ = v_snd_126_;
v_keys_115_ = v___x_127_;
goto _start;
}
else
{
lean_dec_ref(v_todo_114_);
return v_keys_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux___boxed(lean_object* v_root_129_, lean_object* v_fnInfos_130_, lean_object* v_todo_131_, lean_object* v_keys_132_){
_start:
{
uint8_t v_root_boxed_133_; lean_object* v_res_134_; 
v_root_boxed_133_ = lean_unbox(v_root_129_);
v_res_134_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v_root_boxed_133_, v_fnInfos_130_, v_todo_131_, v_keys_132_);
lean_dec(v_fnInfos_130_);
return v_res_134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(8u);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object* v_p_136_){
_start:
{
lean_object* v_pattern_137_; lean_object* v_fnInfos_138_; lean_object* v___x_139_; lean_object* v_todo_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_pattern_137_ = lean_ctor_get(v_p_136_, 3);
lean_inc_ref(v_pattern_137_);
v_fnInfos_138_ = lean_ctor_get(v_p_136_, 4);
lean_inc(v_fnInfos_138_);
lean_dec_ref(v_p_136_);
v___x_139_ = lean_unsigned_to_nat(8u);
v_todo_140_ = lean_mk_empty_array_with_capacity(v___x_139_);
v___x_141_ = 1;
lean_inc_ref(v_todo_140_);
v___x_142_ = lean_array_push(v_todo_140_, v_pattern_137_);
v___x_143_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v___x_141_, v_fnInfos_138_, v___x_142_, v_todo_140_);
lean_dec(v_fnInfos_138_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___redArg(lean_object* v_inst_144_, lean_object* v_d_145_, lean_object* v_p_146_, lean_object* v_v_147_){
_start:
{
lean_object* v_keys_148_; lean_object* v___x_149_; 
v_keys_148_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_146_);
v___x_149_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_144_, v_d_145_, v_keys_148_, v_v_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern(lean_object* v_00_u03b1_150_, lean_object* v_inst_151_, lean_object* v_d_152_, lean_object* v_p_153_, lean_object* v_v_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Sym_insertPattern___redArg(v_inst_151_, v_d_152_, v_p_153_, v_v_154_);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(lean_object* v_a_156_, lean_object* v_b_157_){
_start:
{
lean_object* v_fst_158_; lean_object* v_fst_159_; uint8_t v___x_160_; 
v_fst_158_ = lean_ctor_get(v_a_156_, 0);
v_fst_159_ = lean_ctor_get(v_b_157_, 0);
v___x_160_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_158_, v_fst_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed(lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_161_, v_b_162_);
lean_dec_ref(v_b_162_);
lean_dec_ref(v_a_161_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(lean_object* v_cs_171_, lean_object* v_k_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_array_get_size(v_cs_171_);
v___x_175_ = lean_nat_dec_lt(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v_k_172_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_sub(v___x_174_, v___x_177_);
v___x_179_ = lean_nat_dec_le(v___x_173_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec(v___x_178_);
lean_dec(v_k_172_);
v___x_180_ = lean_box(0);
return v___x_180_;
}
else
{
lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___f_181_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_k_172_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_185_ = l_Array_binSearchAux___redArg(v___f_181_, v___x_184_, v_cs_171_, v___x_183_, v___x_173_, v___x_178_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___boxed(lean_object* v_cs_186_, lean_object* v_k_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(v_cs_186_, v_k_187_);
lean_dec_ref(v_cs_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(lean_object* v_00_u03b1_189_, lean_object* v_cs_190_, lean_object* v_k_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_array_get_size(v_cs_190_);
v___x_194_ = lean_nat_dec_lt(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec(v_k_191_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_sub(v___x_193_, v___x_196_);
v___x_198_ = lean_nat_dec_le(v___x_192_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec(v___x_197_);
lean_dec(v_k_191_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___f_200_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_k_191_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_204_ = l_Array_binSearchAux___redArg(v___f_200_, v___x_203_, v_cs_190_, v___x_202_, v___x_192_, v___x_197_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___boxed(lean_object* v_00_u03b1_205_, lean_object* v_cs_206_, lean_object* v_k_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(v_00_u03b1_205_, v_cs_206_, v_k_207_);
lean_dec_ref(v_cs_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(lean_object* v_e_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Expr_getAppFn_x27(v_e_209_);
switch(lean_obj_tag(v___x_210_))
{
case 9:
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_212_, 0, v_a_211_);
return v___x_212_;
}
case 4:
{
lean_object* v_declName_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_declName_213_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_declName_213_);
lean_dec_ref_known(v___x_210_, 2);
v___x_214_ = l_Lean_Expr_getAppNumArgs_x27(v_e_209_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v_declName_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
return v___x_215_;
}
case 1:
{
lean_object* v_fvarId_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_fvarId_216_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_fvarId_216_);
lean_dec_ref_known(v___x_210_, 1);
v___x_217_ = l_Lean_Expr_getAppNumArgs_x27(v_e_209_);
v___x_218_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_218_, 0, v_fvarId_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
return v___x_218_;
}
case 7:
{
lean_object* v___x_219_; 
lean_dec_ref_known(v___x_210_, 3);
v___x_219_ = lean_box(5);
return v___x_219_;
}
default: 
{
lean_object* v___x_220_; 
lean_dec_ref(v___x_210_);
v___x_220_ = lean_box(1);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(lean_object* v_e_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_221_);
lean_dec_ref(v_e_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(lean_object* v_mctx_223_, lean_object* v_e_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_Lean_Expr_hasExprMVar(v_e_224_);
if (v___x_225_ == 0)
{
return v_e_224_;
}
else
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Expr_getAppFn(v_e_224_);
if (lean_obj_tag(v___x_226_) == 2)
{
lean_object* v_mvarId_227_; lean_object* v___x_228_; 
v_mvarId_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_mvarId_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_223_, v_mvarId_227_);
lean_dec(v_mvarId_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
return v_e_224_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; 
v_val_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = l_Lean_Expr_getAppNumArgs(v_e_224_);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
lean_dec(v___x_230_);
v___x_232_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_224_, v___x_231_);
v___x_233_ = 0;
v___x_234_ = l_Lean_Expr_betaRev(v_val_229_, v___x_232_, v___x_233_, v___x_233_);
lean_dec_ref(v___x_232_);
v_e_224_ = v___x_234_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_226_);
return v_e_224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars___boxed(lean_object* v_mctx_236_, lean_object* v_e_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_236_, v_e_237_);
lean_dec_ref(v_mctx_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object* v_todo_239_, lean_object* v_e_240_){
_start:
{
switch(lean_obj_tag(v_e_240_))
{
case 5:
{
lean_object* v_fn_241_; lean_object* v_arg_242_; lean_object* v___x_243_; 
v_fn_241_ = lean_ctor_get(v_e_240_, 0);
lean_inc_ref(v_fn_241_);
v_arg_242_ = lean_ctor_get(v_e_240_, 1);
lean_inc_ref(v_arg_242_);
lean_dec_ref_known(v_e_240_, 2);
v___x_243_ = lean_array_push(v_todo_239_, v_arg_242_);
v_todo_239_ = v___x_243_;
v_e_240_ = v_fn_241_;
goto _start;
}
case 7:
{
lean_object* v_binderType_245_; lean_object* v_body_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_binderType_245_ = lean_ctor_get(v_e_240_, 1);
lean_inc_ref(v_binderType_245_);
v_body_246_ = lean_ctor_get(v_e_240_, 2);
lean_inc_ref(v_body_246_);
lean_dec_ref_known(v_e_240_, 3);
v___x_247_ = lean_array_push(v_todo_239_, v_body_246_);
v___x_248_ = lean_array_push(v___x_247_, v_binderType_245_);
return v___x_248_;
}
case 10:
{
lean_object* v_expr_249_; 
v_expr_249_ = lean_ctor_get(v_e_240_, 1);
lean_inc_ref(v_expr_249_);
lean_dec_ref_known(v_e_240_, 2);
v_e_240_ = v_expr_249_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_240_);
return v_todo_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_as_251_, lean_object* v_k_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_m_257_; lean_object* v_a_258_; uint8_t v___x_259_; 
v___x_255_ = lean_nat_add(v_x_253_, v_x_254_);
v___x_256_ = lean_unsigned_to_nat(1u);
v_m_257_ = lean_nat_shiftr(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
v_a_258_ = lean_array_fget_borrowed(v_as_251_, v_m_257_);
v___x_259_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_258_, v_k_252_);
if (v___x_259_ == 0)
{
uint8_t v___x_260_; 
lean_dec(v_x_254_);
v___x_260_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_252_, v_a_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v_m_257_);
lean_dec(v_x_253_);
lean_inc(v_a_258_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_a_258_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; uint8_t v___y_266_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v_m_257_, v___x_262_);
v___x_264_ = lean_nat_sub(v_m_257_, v___x_256_);
lean_dec(v_m_257_);
if (v___x_263_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_lt(v___x_264_, v_x_253_);
v___y_266_ = v___x_269_;
goto v___jp_265_;
}
else
{
v___y_266_ = v___x_263_;
goto v___jp_265_;
}
v___jp_265_:
{
if (v___y_266_ == 0)
{
v_x_254_ = v___x_264_;
goto _start;
}
else
{
lean_object* v___x_268_; 
lean_dec(v___x_264_);
lean_dec(v_x_253_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
}
}
else
{
lean_object* v___x_270_; uint8_t v___x_271_; 
lean_dec(v_x_253_);
v___x_270_ = lean_nat_add(v_m_257_, v___x_256_);
lean_dec(v_m_257_);
v___x_271_ = lean_nat_dec_le(v___x_270_, v_x_254_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
lean_dec(v___x_270_);
lean_dec(v_x_254_);
v___x_272_ = lean_box(0);
return v___x_272_;
}
else
{
v_x_253_ = v___x_270_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_274_, lean_object* v_k_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_274_, v_k_275_, v_x_276_, v_x_277_);
lean_dec_ref(v_k_275_);
lean_dec_ref(v_as_274_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_mctx_279_, lean_object* v_todo_280_, lean_object* v_c_281_, lean_object* v_result_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_c_281_) == 0)
{
lean_object* v_key_284_; lean_object* v_child_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_key_284_ = lean_ctor_get(v_c_281_, 0);
lean_inc(v_key_284_);
v_child_285_ = lean_ctor_get(v_c_281_, 1);
lean_inc_ref(v_child_285_);
lean_dec_ref_known(v_c_281_, 2);
v___x_286_ = lean_array_get_size(v_todo_280_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_todo_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_sub(v___x_286_, v___x_289_);
v___x_291_ = lean_array_get(v___x_283_, v_todo_280_, v___x_290_);
lean_dec(v___x_290_);
v_todo_292_ = lean_array_pop(v_todo_280_);
v___x_293_ = lean_box(0);
v___x_294_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_284_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v_e_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_295_ = l_Lean_Meta_Sym_etaReduce(v___x_291_);
lean_dec(v___x_291_);
v_e_296_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_279_, v___x_295_);
v___x_297_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_296_);
v___x_298_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_284_, v___x_297_);
lean_dec(v___x_297_);
lean_dec(v_key_284_);
if (v___x_298_ == 0)
{
lean_dec_ref(v_e_296_);
lean_dec_ref(v_todo_292_);
lean_dec_ref(v_child_285_);
return v_result_282_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_292_, v_e_296_);
v_todo_280_ = v___x_299_;
v_c_281_ = v_child_285_;
goto _start;
}
}
else
{
lean_dec(v___x_291_);
lean_dec(v_key_284_);
v_todo_280_ = v_todo_292_;
v_c_281_ = v_child_285_;
goto _start;
}
}
else
{
lean_dec_ref(v_child_285_);
lean_dec(v_key_284_);
lean_dec_ref(v_todo_280_);
return v_result_282_;
}
}
else
{
lean_object* v_vs_302_; lean_object* v_children_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_vs_302_ = lean_ctor_get(v_c_281_, 0);
lean_inc_ref(v_vs_302_);
v_children_303_ = lean_ctor_get(v_c_281_, 1);
lean_inc_ref(v_children_303_);
lean_dec_ref_known(v_c_281_, 2);
v___x_304_ = lean_array_get_size(v_todo_280_);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_nat_dec_eq(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v_csize_307_; uint8_t v___x_308_; 
lean_dec_ref(v_vs_302_);
v_csize_307_ = lean_array_get_size(v_children_303_);
v___x_308_ = lean_nat_dec_eq(v_csize_307_, v___x_305_);
if (v___x_308_ == 0)
{
lean_object* v_first_309_; lean_object* v_fst_310_; lean_object* v_snd_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_339_; 
v_first_309_ = lean_array_fget(v_children_303_, v___x_305_);
v_fst_310_ = lean_ctor_get(v_first_309_, 0);
v_snd_311_ = lean_ctor_get(v_first_309_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_first_309_);
if (v_isSharedCheck_339_ == 0)
{
v___x_313_ = v_first_309_;
v_isShared_314_ = v_isSharedCheck_339_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snd_311_);
lean_inc(v_fst_310_);
lean_dec(v_first_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_339_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_e_319_; lean_object* v_todo_320_; lean_object* v___y_322_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_sub(v___x_304_, v___x_315_);
v___x_317_ = lean_array_get_borrowed(v___x_283_, v_todo_280_, v___x_316_);
lean_dec(v___x_316_);
v___x_318_ = l_Lean_Meta_Sym_etaReduce(v___x_317_);
v_e_319_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_279_, v___x_318_);
v_todo_320_ = lean_array_pop(v_todo_280_);
v___x_336_ = lean_box(0);
v___x_337_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_310_, v___x_336_);
lean_dec(v_fst_310_);
if (v___x_337_ == 0)
{
lean_dec(v_snd_311_);
v___y_322_ = v_result_282_;
goto v___jp_321_;
}
else
{
lean_object* v___x_338_; 
lean_inc_ref(v_todo_320_);
v___x_338_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_279_, v_todo_320_, v_snd_311_, v_result_282_);
v___y_322_ = v___x_338_;
goto v___jp_321_;
}
v___jp_321_:
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_lt(v___x_305_, v_csize_307_);
if (v___x_323_ == 0)
{
lean_dec_ref(v_todo_320_);
lean_dec_ref(v_e_319_);
lean_del_object(v___x_313_);
lean_dec_ref(v_children_303_);
return v___y_322_;
}
else
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_nat_sub(v_csize_307_, v___x_315_);
v___x_325_ = lean_nat_dec_le(v___x_305_, v___x_324_);
if (v___x_325_ == 0)
{
lean_dec(v___x_324_);
lean_dec_ref(v_todo_320_);
lean_dec_ref(v_e_319_);
lean_del_object(v___x_313_);
lean_dec_ref(v_children_303_);
return v___y_322_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_319_);
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_327_);
lean_ctor_set(v___x_313_, 0, v___x_326_);
v___x_329_ = v___x_313_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_335_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; 
v___x_330_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_303_, v___x_329_, v___x_305_, v___x_324_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v_children_303_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_dec_ref(v_todo_320_);
lean_dec_ref(v_e_319_);
return v___y_322_;
}
else
{
lean_object* v_val_331_; lean_object* v_snd_332_; lean_object* v___x_333_; 
v_val_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_331_);
lean_dec_ref_known(v___x_330_, 1);
v_snd_332_ = lean_ctor_get(v_val_331_, 1);
lean_inc(v_snd_332_);
lean_dec(v_val_331_);
v___x_333_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_320_, v_e_319_);
v_todo_280_ = v___x_333_;
v_c_281_ = v_snd_332_;
v_result_282_ = v___y_322_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_children_303_);
lean_dec_ref(v_todo_280_);
return v_result_282_;
}
}
else
{
lean_object* v___x_340_; 
lean_dec_ref(v_children_303_);
lean_dec_ref(v_todo_280_);
v___x_340_ = l_Array_append___redArg(v_result_282_, v_vs_302_);
lean_dec_ref(v_vs_302_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_341_, lean_object* v_todo_342_, lean_object* v_c_343_, lean_object* v_result_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_341_, v_todo_342_, v_c_343_, v_result_344_);
lean_dec_ref(v_mctx_341_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_346_, lean_object* v_mctx_347_, lean_object* v_todo_348_, lean_object* v_c_349_, lean_object* v_result_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_347_, v_todo_348_, v_c_349_, v_result_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_352_, lean_object* v_mctx_353_, lean_object* v_todo_354_, lean_object* v_c_355_, lean_object* v_result_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_352_, v_mctx_353_, v_todo_354_, v_c_355_, v_result_356_);
lean_dec_ref(v_mctx_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_358_, lean_object* v_as_359_, lean_object* v_k_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_359_, v_k_360_, v_x_361_, v_x_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_365_, lean_object* v_as_366_, lean_object* v_k_367_, lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_365_, v_as_366_, v_k_367_, v_x_368_, v_x_369_, v_x_370_);
lean_dec_ref(v_k_367_);
lean_dec_ref(v_as_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_372_, lean_object* v_vals_373_, lean_object* v_i_374_, lean_object* v_k_375_){
_start:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = lean_array_get_size(v_keys_372_);
v___x_377_ = lean_nat_dec_lt(v_i_374_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_i_374_);
v___x_378_ = lean_box(0);
return v___x_378_;
}
else
{
lean_object* v_k_x27_379_; uint8_t v___x_380_; 
v_k_x27_379_ = lean_array_fget_borrowed(v_keys_372_, v_i_374_);
v___x_380_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_375_, v_k_x27_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_add(v_i_374_, v___x_381_);
lean_dec(v_i_374_);
v_i_374_ = v___x_382_;
goto _start;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_array_fget_borrowed(v_vals_373_, v_i_374_);
lean_dec(v_i_374_);
lean_inc(v___x_384_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_386_, lean_object* v_vals_387_, lean_object* v_i_388_, lean_object* v_k_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_386_, v_vals_387_, v_i_388_, v_k_389_);
lean_dec(v_k_389_);
lean_dec_ref(v_vals_387_);
lean_dec_ref(v_keys_386_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_391_, size_t v_x_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_object* v_es_394_; lean_object* v___x_395_; size_t v___x_396_; size_t v___x_397_; lean_object* v_j_398_; lean_object* v___x_399_; 
v_es_394_ = lean_ctor_get(v_x_391_, 0);
v___x_395_ = lean_box(2);
v___x_396_ = ((size_t)31ULL);
v___x_397_ = lean_usize_land(v_x_392_, v___x_396_);
v_j_398_ = lean_usize_to_nat(v___x_397_);
v___x_399_ = lean_array_get_borrowed(v___x_395_, v_es_394_, v_j_398_);
lean_dec(v_j_398_);
switch(lean_obj_tag(v___x_399_))
{
case 0:
{
lean_object* v_key_400_; lean_object* v_val_401_; uint8_t v___x_402_; 
v_key_400_ = lean_ctor_get(v___x_399_, 0);
v_val_401_ = lean_ctor_get(v___x_399_, 1);
v___x_402_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_393_, v_key_400_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_box(0);
return v___x_403_;
}
else
{
lean_object* v___x_404_; 
lean_inc(v_val_401_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v_val_401_);
return v___x_404_;
}
}
case 1:
{
lean_object* v_node_405_; size_t v___x_406_; size_t v___x_407_; 
v_node_405_ = lean_ctor_get(v___x_399_, 0);
v___x_406_ = ((size_t)5ULL);
v___x_407_ = lean_usize_shift_right(v_x_392_, v___x_406_);
v_x_391_ = v_node_405_;
v_x_392_ = v___x_407_;
goto _start;
}
default: 
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
return v___x_409_;
}
}
}
else
{
lean_object* v_ks_410_; lean_object* v_vs_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_ks_410_ = lean_ctor_get(v_x_391_, 0);
v_vs_411_ = lean_ctor_get(v_x_391_, 1);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_410_, v_vs_411_, v___x_412_, v_x_393_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
size_t v_x_203__boxed_417_; lean_object* v_res_418_; 
v_x_203__boxed_417_ = lean_unbox_usize(v_x_415_);
lean_dec(v_x_415_);
v_res_418_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_414_, v_x_203__boxed_417_, v_x_416_);
lean_dec(v_x_416_);
lean_dec_ref(v_x_414_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint64_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_420_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
v___x_423_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_419_, v___x_422_, v_x_420_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_424_, v_x_425_);
lean_dec(v_x_425_);
lean_dec_ref(v_x_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_429_, lean_object* v_d_430_, lean_object* v_e_431_){
_start:
{
lean_object* v___y_433_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_box(0);
v___x_443_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_430_, v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(8u);
v___x_445_ = lean_mk_empty_array_with_capacity(v___x_444_);
v___y_433_ = v___x_445_;
goto v___jp_432_;
}
else
{
lean_object* v_val_446_; 
v_val_446_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_443_, 1);
if (lean_obj_tag(v_val_446_) == 0)
{
lean_object* v___x_447_; 
lean_dec_ref_known(v_val_446_, 2);
v___x_447_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1));
v___y_433_ = v___x_447_;
goto v___jp_432_;
}
else
{
lean_object* v_vs_448_; 
v_vs_448_ = lean_ctor_get(v_val_446_, 0);
lean_inc_ref(v_vs_448_);
lean_dec_ref_known(v_val_446_, 2);
v___y_433_ = v_vs_448_;
goto v___jp_432_;
}
}
v___jp_432_:
{
lean_object* v___x_434_; lean_object* v_e_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = l_Lean_Meta_Sym_etaReduce(v_e_431_);
v_e_435_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_429_, v___x_434_);
v___x_436_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_435_);
v___x_437_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_430_, v___x_436_);
lean_dec(v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_dec_ref(v_e_435_);
return v___y_433_;
}
else
{
lean_object* v_val_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_440_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_439_, v_e_435_);
v___x_441_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_429_, v___x_440_, v_val_438_, v___y_433_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_449_, lean_object* v_d_450_, lean_object* v_e_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_449_, v_d_450_, v_e_451_);
lean_dec_ref(v_e_451_);
lean_dec_ref(v_d_450_);
lean_dec_ref(v_mctx_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_453_, lean_object* v_mctx_454_, lean_object* v_d_455_, lean_object* v_e_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_454_, v_d_455_, v_e_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_458_, lean_object* v_mctx_459_, lean_object* v_d_460_, lean_object* v_e_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_458_, v_mctx_459_, v_d_460_, v_e_461_);
lean_dec_ref(v_e_461_);
lean_dec_ref(v_d_460_);
lean_dec_ref(v_mctx_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_467_, v_x_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec_ref(v_x_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, size_t v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_472_, v_x_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
size_t v_x_315__boxed_480_; lean_object* v_res_481_; 
v_x_315__boxed_480_ = lean_unbox_usize(v_x_478_);
lean_dec(v_x_478_);
v_res_481_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_476_, v_x_477_, v_x_315__boxed_480_, v_x_479_);
lean_dec(v_x_479_);
lean_dec_ref(v_x_477_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_heq_485_, lean_object* v_i_486_, lean_object* v_k_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_483_, v_vals_484_, v_i_486_, v_k_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_489_, lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_heq_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_489_, v_keys_490_, v_vals_491_, v_heq_492_, v_i_493_, v_k_494_);
lean_dec(v_k_494_);
lean_dec_ref(v_vals_491_);
lean_dec_ref(v_keys_490_);
return v_res_495_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_496_, lean_object* v_k_497_){
_start:
{
lean_object* v_k_499_; 
switch(lean_obj_tag(v_k_497_))
{
case 4:
{
lean_object* v_a_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_516_; 
v_a_503_ = lean_ctor_get(v_k_497_, 0);
v_a_504_ = lean_ctor_get(v_k_497_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_k_497_);
if (v_isSharedCheck_516_ == 0)
{
v___x_506_ = v_k_497_;
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_inc(v_a_503_);
lean_dec(v_k_497_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v_zero_508_; uint8_t v_isZero_509_; 
v_zero_508_ = lean_unsigned_to_nat(0u);
v_isZero_509_ = lean_nat_dec_eq(v_a_504_, v_zero_508_);
if (v_isZero_509_ == 0)
{
lean_object* v_one_510_; lean_object* v_n_511_; lean_object* v___x_513_; 
v_one_510_ = lean_unsigned_to_nat(1u);
v_n_511_ = lean_nat_sub(v_a_504_, v_one_510_);
lean_dec(v_a_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_n_511_);
v___x_513_ = v___x_506_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_n_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v_k_499_ = v___x_513_;
goto v___jp_498_;
}
}
else
{
uint8_t v___x_515_; 
lean_del_object(v___x_506_);
lean_dec(v_a_504_);
lean_dec(v_a_503_);
v___x_515_ = 0;
return v___x_515_;
}
}
}
case 3:
{
lean_object* v_a_517_; lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_530_; 
v_a_517_ = lean_ctor_get(v_k_497_, 0);
v_a_518_ = lean_ctor_get(v_k_497_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_k_497_);
if (v_isSharedCheck_530_ == 0)
{
v___x_520_ = v_k_497_;
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_inc(v_a_517_);
lean_dec(v_k_497_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_zero_522_; uint8_t v_isZero_523_; 
v_zero_522_ = lean_unsigned_to_nat(0u);
v_isZero_523_ = lean_nat_dec_eq(v_a_518_, v_zero_522_);
if (v_isZero_523_ == 0)
{
lean_object* v_one_524_; lean_object* v_n_525_; lean_object* v___x_527_; 
v_one_524_ = lean_unsigned_to_nat(1u);
v_n_525_ = lean_nat_sub(v_a_518_, v_one_524_);
lean_dec(v_a_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v_n_525_);
v___x_527_ = v___x_520_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_517_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_n_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v_k_499_ = v___x_527_;
goto v___jp_498_;
}
}
else
{
uint8_t v___x_529_; 
lean_del_object(v___x_520_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
v___x_529_ = 0;
return v___x_529_;
}
}
}
default: 
{
uint8_t v___x_531_; 
lean_dec(v_k_497_);
v___x_531_ = 0;
return v___x_531_;
}
}
v___jp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_496_, v_k_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
v_k_497_ = v_k_499_;
goto _start;
}
else
{
uint8_t v___x_502_; 
lean_dec_ref_known(v___x_500_, 1);
lean_dec(v_k_499_);
v___x_502_ = 1;
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_532_, lean_object* v_k_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_532_, v_k_533_);
lean_dec_ref(v_d_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_536_, lean_object* v_d_537_, lean_object* v_k_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_537_, v_k_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_540_, lean_object* v_d_541_, lean_object* v_k_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_540_, v_d_541_, v_k_542_);
lean_dec_ref(v_d_541_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_545_, size_t v_sz_546_, size_t v_i_547_, lean_object* v_bs_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_lt(v_i_547_, v_sz_546_);
if (v___x_549_ == 0)
{
lean_dec(v_numExtra_545_);
return v_bs_548_;
}
else
{
lean_object* v_v_550_; lean_object* v___x_551_; lean_object* v_bs_x27_552_; lean_object* v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; 
v_v_550_ = lean_array_uget(v_bs_548_, v_i_547_);
v___x_551_ = lean_unsigned_to_nat(0u);
v_bs_x27_552_ = lean_array_uset(v_bs_548_, v_i_547_, v___x_551_);
lean_inc(v_numExtra_545_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_v_550_);
lean_ctor_set(v___x_553_, 1, v_numExtra_545_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_547_, v___x_554_);
v___x_556_ = lean_array_uset(v_bs_x27_552_, v_i_547_, v___x_553_);
v_i_547_ = v___x_555_;
v_bs_548_ = v___x_556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_558_, lean_object* v_sz_559_, lean_object* v_i_560_, lean_object* v_bs_561_){
_start:
{
size_t v_sz_boxed_562_; size_t v_i_boxed_563_; lean_object* v_res_564_; 
v_sz_boxed_562_ = lean_unbox_usize(v_sz_559_);
lean_dec(v_sz_559_);
v_i_boxed_563_ = lean_unbox_usize(v_i_560_);
lean_dec(v_i_560_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_558_, v_sz_boxed_562_, v_i_boxed_563_, v_bs_561_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_565_, lean_object* v_d_566_, lean_object* v_e_567_, lean_object* v_numExtra_568_, lean_object* v_result_569_){
_start:
{
lean_object* v___x_570_; size_t v_sz_571_; size_t v___x_572_; lean_object* v___x_573_; lean_object* v_result_574_; lean_object* v_e_575_; uint8_t v___x_576_; 
v___x_570_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_565_, v_d_566_, v_e_567_);
v_sz_571_ = lean_array_size(v___x_570_);
v___x_572_ = ((size_t)0ULL);
lean_inc(v_numExtra_568_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_568_, v_sz_571_, v___x_572_, v___x_570_);
v_result_574_ = l_Array_append___redArg(v_result_569_, v___x_573_);
lean_dec_ref(v___x_573_);
v_e_575_ = l_Lean_Expr_consumeMData(v_e_567_);
lean_dec_ref(v_e_567_);
v___x_576_ = l_Lean_Expr_isApp(v_e_575_);
if (v___x_576_ == 0)
{
lean_dec_ref(v_e_575_);
lean_dec(v_numExtra_568_);
return v_result_574_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = l_Lean_Expr_appFn_x21(v_e_575_);
lean_dec_ref(v_e_575_);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_numExtra_568_, v___x_578_);
lean_dec(v_numExtra_568_);
v_e_567_ = v___x_577_;
v_numExtra_568_ = v___x_579_;
v_result_569_ = v_result_574_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_581_, lean_object* v_d_582_, lean_object* v_e_583_, lean_object* v_numExtra_584_, lean_object* v_result_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_581_, v_d_582_, v_e_583_, v_numExtra_584_, v_result_585_);
lean_dec_ref(v_d_582_);
lean_dec_ref(v_mctx_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_587_, lean_object* v_mctx_588_, lean_object* v_d_589_, lean_object* v_e_590_, lean_object* v_numExtra_591_, lean_object* v_result_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_588_, v_d_589_, v_e_590_, v_numExtra_591_, v_result_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_594_, lean_object* v_mctx_595_, lean_object* v_d_596_, lean_object* v_e_597_, lean_object* v_numExtra_598_, lean_object* v_result_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_594_, v_mctx_595_, v_d_596_, v_e_597_, v_numExtra_598_, v_result_599_);
lean_dec_ref(v_d_596_);
lean_dec_ref(v_mctx_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_601_, lean_object* v_numExtra_602_, size_t v_sz_603_, size_t v_i_604_, lean_object* v_bs_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_602_, v_sz_603_, v_i_604_, v_bs_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_607_, lean_object* v_numExtra_608_, lean_object* v_sz_609_, lean_object* v_i_610_, lean_object* v_bs_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_609_);
lean_dec(v_sz_609_);
v_i_boxed_613_ = lean_unbox_usize(v_i_610_);
lean_dec(v_i_610_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_607_, v_numExtra_608_, v_sz_boxed_612_, v_i_boxed_613_, v_bs_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_615_, size_t v_i_616_, lean_object* v_bs_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_lt(v_i_616_, v_sz_615_);
if (v___x_618_ == 0)
{
return v_bs_617_;
}
else
{
lean_object* v_v_619_; lean_object* v___x_620_; lean_object* v_bs_x27_621_; lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v_v_619_ = lean_array_uget(v_bs_617_, v_i_616_);
v___x_620_ = lean_unsigned_to_nat(0u);
v_bs_x27_621_ = lean_array_uset(v_bs_617_, v_i_616_, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_v_619_);
lean_ctor_set(v___x_622_, 1, v___x_620_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_616_, v___x_623_);
v___x_625_ = lean_array_uset(v_bs_x27_621_, v_i_616_, v___x_622_);
v_i_616_ = v___x_624_;
v_bs_617_ = v___x_625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_627_, lean_object* v_i_628_, lean_object* v_bs_629_){
_start:
{
size_t v_sz_boxed_630_; size_t v_i_boxed_631_; lean_object* v_res_632_; 
v_sz_boxed_630_ = lean_unbox_usize(v_sz_627_);
lean_dec(v_sz_627_);
v_i_boxed_631_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_630_, v_i_boxed_631_, v_bs_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_633_, lean_object* v_d_634_, lean_object* v_e_635_){
_start:
{
lean_object* v___x_636_; lean_object* v_e_637_; lean_object* v_e_638_; lean_object* v_result_639_; size_t v_sz_640_; size_t v___x_641_; lean_object* v_result_642_; uint8_t v___x_643_; 
v___x_636_ = l_Lean_Meta_Sym_etaReduce(v_e_635_);
v_e_637_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_633_, v___x_636_);
v_e_638_ = l_Lean_Expr_consumeMData(v_e_637_);
lean_dec_ref(v_e_637_);
v_result_639_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_633_, v_d_634_, v_e_638_);
v_sz_640_ = lean_array_size(v_result_639_);
v___x_641_ = ((size_t)0ULL);
v_result_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_640_, v___x_641_, v_result_639_);
v___x_643_ = l_Lean_Expr_isApp(v_e_638_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_e_638_);
return v_result_642_;
}
else
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_638_);
v___x_645_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_634_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec_ref(v_e_638_);
return v_result_642_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = l_Lean_Expr_appFn_x21(v_e_638_);
lean_dec_ref(v_e_638_);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_633_, v_d_634_, v___x_646_, v___x_647_, v_result_642_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_649_, lean_object* v_d_650_, lean_object* v_e_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_649_, v_d_650_, v_e_651_);
lean_dec_ref(v_e_651_);
lean_dec_ref(v_d_650_);
lean_dec_ref(v_mctx_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_653_, lean_object* v_mctx_654_, lean_object* v_d_655_, lean_object* v_e_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_654_, v_d_655_, v_e_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_658_, lean_object* v_mctx_659_, lean_object* v_d_660_, lean_object* v_e_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_658_, v_mctx_659_, v_d_660_, v_e_661_);
lean_dec_ref(v_e_661_);
lean_dec_ref(v_d_660_);
lean_dec_ref(v_mctx_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_663_, size_t v_sz_664_, size_t v_i_665_, lean_object* v_bs_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_664_, v_i_665_, v_bs_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_668_, lean_object* v_sz_669_, lean_object* v_i_670_, lean_object* v_bs_671_){
_start:
{
size_t v_sz_boxed_672_; size_t v_i_boxed_673_; lean_object* v_res_674_; 
v_sz_boxed_672_ = lean_unbox_usize(v_sz_669_);
lean_dec(v_sz_669_);
v_i_boxed_673_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_668_, v_sz_boxed_672_, v_i_boxed_673_, v_bs_671_);
return v_res_674_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Offset(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Eta(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity = _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Offset(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Eta(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
}
#ifdef __cplusplus
}
#endif
