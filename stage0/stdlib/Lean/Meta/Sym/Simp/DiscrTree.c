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
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs_x27(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isQuasiOffset(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_60_; 
v___x_60_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_56_);
if (v___x_60_ == 0)
{
lean_object* v_fn_61_; 
v_fn_61_ = l_Lean_Expr_getAppFn(v_e_56_);
switch(lean_obj_tag(v_fn_61_))
{
case 9:
{
lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec_ref(v_e_56_);
v_a_62_ = lean_ctor_get(v_fn_61_, 0);
lean_inc_ref(v_a_62_);
lean_dec_ref_known(v_fn_61_, 1);
v___x_63_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_63_, 0, v_a_62_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v_todo_55_);
return v___x_64_;
}
case 0:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec_ref_known(v_fn_61_, 1);
lean_dec_ref(v_e_56_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_todo_55_);
return v___x_66_;
}
case 7:
{
lean_object* v_binderType_67_; lean_object* v_body_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec_ref(v_e_56_);
v_binderType_67_ = lean_ctor_get(v_fn_61_, 1);
lean_inc_ref(v_binderType_67_);
v_body_68_ = lean_ctor_get(v_fn_61_, 2);
lean_inc_ref(v_body_68_);
lean_dec_ref_known(v_fn_61_, 3);
v___x_69_ = lean_box(5);
v___x_70_ = lean_array_push(v_todo_55_, v_body_68_);
v___x_71_ = lean_array_push(v___x_70_, v_binderType_67_);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
return v___x_72_;
}
case 4:
{
lean_object* v_declName_73_; lean_object* v___y_75_; lean_object* v___y_76_; 
v_declName_73_ = lean_ctor_get(v_fn_61_, 0);
lean_inc(v_declName_73_);
lean_dec_ref_known(v_fn_61_, 2);
if (v_root_53_ == 0)
{
uint8_t v___x_87_; 
v___x_87_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_73_, v_e_56_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
v___x_88_ = l_Lean_Meta_Sym_isQuasiOffset(v_e_56_);
if (v___x_88_ == 0)
{
goto v___jp_79_;
}
else
{
lean_dec(v_declName_73_);
lean_dec_ref(v_e_56_);
goto v___jp_57_;
}
}
else
{
lean_dec(v_declName_73_);
lean_dec_ref(v_e_56_);
goto v___jp_57_;
}
}
else
{
goto v___jp_79_;
}
v___jp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_77_, 0, v_declName_73_);
lean_ctor_set(v___x_77_, 1, v___y_75_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___y_76_);
return v___x_78_;
}
v___jp_79_:
{
lean_object* v_numArgs_80_; lean_object* v___x_81_; 
v_numArgs_80_ = l_Lean_Expr_getAppNumArgs(v_e_56_);
v___x_81_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_declName_73_, v_fnInfos_54_);
if (lean_obj_tag(v___x_81_) == 1)
{
lean_object* v_val_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_val_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v___x_81_, 1);
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_sub(v_numArgs_80_, v___x_83_);
v___x_85_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(v_val_82_, v___x_84_, v_e_56_, v_todo_55_);
lean_dec(v_val_82_);
v___y_75_ = v_numArgs_80_;
v___y_76_ = v___x_85_;
goto v___jp_74_;
}
else
{
lean_object* v___x_86_; 
lean_dec(v___x_81_);
v___x_86_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_56_, v_todo_55_);
v___y_75_ = v_numArgs_80_;
v___y_76_ = v___x_86_;
goto v___jp_74_;
}
}
}
case 1:
{
lean_object* v_fvarId_89_; lean_object* v_numArgs_90_; lean_object* v_todo_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_fvarId_89_ = lean_ctor_get(v_fn_61_, 0);
lean_inc(v_fvarId_89_);
lean_dec_ref_known(v_fn_61_, 1);
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
lean_dec_ref(v_fn_61_);
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
v___jp_57_:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_box(0);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v_todo_55_);
return v___x_59_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(lean_object* v_e_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Expr_getAppFn_x27(v_e_156_);
switch(lean_obj_tag(v___x_157_))
{
case 9:
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_159_, 0, v_a_158_);
return v___x_159_;
}
case 4:
{
lean_object* v_declName_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_declName_160_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_declName_160_);
lean_dec_ref_known(v___x_157_, 2);
v___x_161_ = l_Lean_Expr_getAppNumArgs_x27(v_e_156_);
v___x_162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_162_, 0, v_declName_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
return v___x_162_;
}
case 1:
{
lean_object* v_fvarId_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_fvarId_163_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_fvarId_163_);
lean_dec_ref_known(v___x_157_, 1);
v___x_164_ = l_Lean_Expr_getAppNumArgs_x27(v_e_156_);
v___x_165_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_165_, 0, v_fvarId_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
return v___x_165_;
}
case 7:
{
lean_object* v___x_166_; 
lean_dec_ref_known(v___x_157_, 3);
v___x_166_ = lean_box(5);
return v___x_166_;
}
default: 
{
lean_object* v___x_167_; 
lean_dec_ref(v___x_157_);
v___x_167_ = lean_box(1);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(lean_object* v_e_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_168_);
lean_dec_ref(v_e_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(lean_object* v_mctx_170_, lean_object* v_e_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = l_Lean_Expr_hasExprMVar(v_e_171_);
if (v___x_172_ == 0)
{
return v_e_171_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Expr_getAppFn(v_e_171_);
if (lean_obj_tag(v___x_173_) == 2)
{
lean_object* v_mvarId_174_; lean_object* v___x_175_; 
v_mvarId_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_mvarId_174_);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_170_, v_mvarId_174_);
lean_dec(v_mvarId_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
return v_e_171_;
}
else
{
lean_object* v_val_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; 
v_val_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = l_Lean_Expr_getAppNumArgs(v_e_171_);
v___x_178_ = lean_mk_empty_array_with_capacity(v___x_177_);
lean_dec(v___x_177_);
v___x_179_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_171_, v___x_178_);
v___x_180_ = 0;
v___x_181_ = l_Lean_Expr_betaRev(v_val_176_, v___x_179_, v___x_180_, v___x_180_);
lean_dec_ref(v___x_179_);
v_e_171_ = v___x_181_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_173_);
return v_e_171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars___boxed(lean_object* v_mctx_183_, lean_object* v_e_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_183_, v_e_184_);
lean_dec_ref(v_mctx_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object* v_todo_186_, lean_object* v_e_187_){
_start:
{
switch(lean_obj_tag(v_e_187_))
{
case 5:
{
lean_object* v_fn_188_; lean_object* v_arg_189_; lean_object* v___x_190_; 
v_fn_188_ = lean_ctor_get(v_e_187_, 0);
lean_inc_ref(v_fn_188_);
v_arg_189_ = lean_ctor_get(v_e_187_, 1);
lean_inc_ref(v_arg_189_);
lean_dec_ref_known(v_e_187_, 2);
v___x_190_ = lean_array_push(v_todo_186_, v_arg_189_);
v_todo_186_ = v___x_190_;
v_e_187_ = v_fn_188_;
goto _start;
}
case 7:
{
lean_object* v_binderType_192_; lean_object* v_body_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_binderType_192_ = lean_ctor_get(v_e_187_, 1);
lean_inc_ref(v_binderType_192_);
v_body_193_ = lean_ctor_get(v_e_187_, 2);
lean_inc_ref(v_body_193_);
lean_dec_ref_known(v_e_187_, 3);
v___x_194_ = lean_array_push(v_todo_186_, v_body_193_);
v___x_195_ = lean_array_push(v___x_194_, v_binderType_192_);
return v___x_195_;
}
case 10:
{
lean_object* v_expr_196_; 
v_expr_196_ = lean_ctor_get(v_e_187_, 1);
lean_inc_ref(v_expr_196_);
lean_dec_ref_known(v_e_187_, 2);
v_e_187_ = v_expr_196_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_187_);
return v_todo_186_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__1(lean_object* v_mctx_198_, lean_object* v_todo_199_, lean_object* v_ks_200_, lean_object* v_i_201_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_array_get_size(v_ks_200_);
v___x_203_ = lean_nat_dec_lt(v_i_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
lean_dec(v_i_201_);
v___x_204_ = lean_array_get_size(v_todo_199_);
lean_dec_ref(v_todo_199_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_207_ = lean_array_get_size(v_todo_199_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_e_213_; lean_object* v_todo_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_210_ = l_Lean_instInhabitedExpr;
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_sub(v___x_207_, v___x_211_);
v_e_213_ = lean_array_get(v___x_210_, v_todo_199_, v___x_212_);
lean_dec(v___x_212_);
v_todo_214_ = lean_array_pop(v_todo_199_);
v___x_215_ = lean_array_fget_borrowed(v_ks_200_, v_i_201_);
v___x_216_ = lean_box(0);
v___x_217_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v_e_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_218_ = l_Lean_Meta_Sym_etaReduce(v_e_213_);
lean_dec(v_e_213_);
v_e_219_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_198_, v___x_218_);
v___x_220_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_219_);
v___x_221_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_215_, v___x_220_);
lean_dec(v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_e_219_);
lean_dec_ref(v_todo_214_);
lean_dec(v_i_201_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_214_, v_e_219_);
v___x_223_ = lean_nat_add(v_i_201_, v___x_211_);
lean_dec(v_i_201_);
v_todo_199_ = v___x_222_;
v_i_201_ = v___x_223_;
goto _start;
}
}
else
{
lean_object* v___x_225_; 
lean_dec(v_e_213_);
v___x_225_ = lean_nat_add(v_i_201_, v___x_211_);
lean_dec(v_i_201_);
v_todo_199_ = v_todo_214_;
v_i_201_ = v___x_225_;
goto _start;
}
}
else
{
uint8_t v___x_227_; 
lean_dec(v_i_201_);
lean_dec_ref(v_todo_199_);
v___x_227_ = 0;
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__1___boxed(lean_object* v_mctx_228_, lean_object* v_todo_229_, lean_object* v_ks_230_, lean_object* v_i_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__1(v_mctx_228_, v_todo_229_, v_ks_230_, v_i_231_);
lean_dec_ref(v_ks_230_);
lean_dec_ref(v_mctx_228_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___lam__0(lean_object* v_a_234_, lean_object* v_b_235_){
_start:
{
lean_object* v_fst_236_; lean_object* v_fst_237_; uint8_t v___x_238_; 
v_fst_236_ = lean_ctor_get(v_a_234_, 0);
v_fst_237_ = lean_ctor_get(v_b_235_, 0);
v___x_238_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_236_, v_fst_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___lam__0(v_a_239_, v_b_240_);
lean_dec_ref(v_b_240_);
lean_dec_ref(v_a_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg(lean_object* v_as_243_, lean_object* v_k_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_m_249_; lean_object* v_a_250_; uint8_t v___x_251_; 
v___x_247_ = lean_nat_add(v_x_245_, v_x_246_);
v___x_248_ = lean_unsigned_to_nat(1u);
v_m_249_ = lean_nat_shiftr(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v_a_250_ = lean_array_fget_borrowed(v_as_243_, v_m_249_);
v___x_251_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___lam__0(v_a_250_, v_k_244_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
lean_dec(v_x_246_);
v___x_252_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___lam__0(v_k_244_, v_a_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_m_249_);
lean_dec(v_x_245_);
lean_inc(v_a_250_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_a_250_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_nat_dec_eq(v_m_249_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_nat_sub(v_m_249_, v___x_248_);
lean_dec(v_m_249_);
v___x_257_ = lean_nat_dec_lt(v___x_256_, v_x_245_);
if (v___x_257_ == 0)
{
v_x_246_ = v___x_256_;
goto _start;
}
else
{
lean_object* v___x_259_; 
lean_dec(v___x_256_);
lean_dec(v_x_245_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
else
{
lean_object* v___x_260_; 
lean_dec(v_m_249_);
lean_dec(v_x_245_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
}
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
lean_dec(v_x_245_);
v___x_261_ = lean_nat_add(v_m_249_, v___x_248_);
lean_dec(v_m_249_);
v___x_262_ = lean_nat_dec_le(v___x_261_, v_x_246_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec(v___x_261_);
lean_dec(v_x_246_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
else
{
v_x_245_ = v___x_261_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg___boxed(lean_object* v_as_265_, lean_object* v_k_266_, lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg(v_as_265_, v_k_266_, v_x_267_, v_x_268_);
lean_dec_ref(v_k_266_);
lean_dec_ref(v_as_265_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_mctx_274_, lean_object* v_todo_275_, lean_object* v_c_276_, lean_object* v_result_277_){
_start:
{
lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v_val_282_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v_val_291_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v_result_318_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v_val_328_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v_val_335_; 
if (lean_obj_tag(v_c_276_) == 3)
{
lean_object* v_keys_349_; lean_object* v_i_350_; lean_object* v_v_351_; uint8_t v___x_352_; 
v_keys_349_ = lean_ctor_get(v_c_276_, 0);
lean_inc_ref(v_keys_349_);
v_i_350_ = lean_ctor_get(v_c_276_, 1);
lean_inc(v_i_350_);
v_v_351_ = lean_ctor_get(v_c_276_, 2);
lean_inc(v_v_351_);
lean_dec_ref_known(v_c_276_, 3);
v___x_352_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__1(v_mctx_274_, v_todo_275_, v_keys_349_, v_i_350_);
lean_dec_ref(v_keys_349_);
if (v___x_352_ == 0)
{
lean_dec(v_v_351_);
return v_result_277_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_array_push(v_result_277_, v_v_351_);
return v___x_353_;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_val_357_; uint8_t v___x_362_; 
v___x_354_ = lean_array_get_size(v_todo_275_);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v___x_354_, v___x_355_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v_val_375_; 
v___x_363_ = l_Lean_instInhabitedExpr;
switch(lean_obj_tag(v_c_276_))
{
case 2:
{
lean_object* v___x_379_; 
lean_inc_ref(v_c_276_);
v___x_379_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_375_ = v___x_379_;
goto v___jp_374_;
}
case 3:
{
lean_object* v___x_380_; 
lean_inc_ref(v_c_276_);
v___x_380_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_375_ = v___x_380_;
goto v___jp_374_;
}
default: 
{
lean_inc_ref(v_c_276_);
v_val_375_ = v_c_276_;
goto v___jp_374_;
}
}
v___jp_364_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_e_367_; lean_object* v_todo_368_; lean_object* v___x_369_; lean_object* v_e_370_; lean_object* v___x_371_; 
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_sub(v___x_354_, v___x_365_);
v_e_367_ = lean_array_get(v___x_363_, v_todo_275_, v___x_366_);
lean_dec(v___x_366_);
v_todo_368_ = lean_array_pop(v_todo_275_);
v___x_369_ = l_Lean_Meta_Sym_etaReduce(v_e_367_);
lean_dec(v_e_367_);
v_e_370_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_274_, v___x_369_);
v___x_371_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_370_);
switch(lean_obj_tag(v_c_276_))
{
case 2:
{
lean_object* v___x_372_; 
lean_inc_ref(v_c_276_);
v___x_372_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_331_ = v_e_370_;
v___y_332_ = v___x_365_;
v___y_333_ = v___x_371_;
v___y_334_ = v_todo_368_;
v_val_335_ = v___x_372_;
goto v___jp_330_;
}
case 3:
{
lean_object* v___x_373_; 
lean_inc_ref(v_c_276_);
v___x_373_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_331_ = v_e_370_;
v___y_332_ = v___x_365_;
v___y_333_ = v___x_371_;
v___y_334_ = v_todo_368_;
v_val_335_ = v___x_373_;
goto v___jp_330_;
}
default: 
{
lean_inc_ref(v_c_276_);
v___y_331_ = v_e_370_;
v___y_332_ = v___x_365_;
v___y_333_ = v___x_371_;
v___y_334_ = v_todo_368_;
v_val_335_ = v_c_276_;
goto v___jp_330_;
}
}
}
v___jp_374_:
{
if (lean_obj_tag(v_val_375_) == 0)
{
lean_dec_ref_known(v_val_375_, 2);
goto v___jp_364_;
}
else
{
lean_object* v_children_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_children_376_ = lean_ctor_get(v_val_375_, 1);
lean_inc_ref(v_children_376_);
lean_dec_ref_known(v_val_375_, 2);
v___x_377_ = lean_array_get_size(v_children_376_);
lean_dec_ref(v_children_376_);
v___x_378_ = lean_nat_dec_eq(v___x_377_, v___x_355_);
if (v___x_378_ == 0)
{
goto v___jp_364_;
}
else
{
lean_dec_ref(v_c_276_);
lean_dec_ref(v_todo_275_);
return v_result_277_;
}
}
}
}
else
{
lean_dec_ref(v_todo_275_);
switch(lean_obj_tag(v_c_276_))
{
case 2:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_357_ = v___x_381_;
goto v___jp_356_;
}
case 3:
{
lean_object* v___x_382_; 
v___x_382_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_357_ = v___x_382_;
goto v___jp_356_;
}
default: 
{
v_val_357_ = v_c_276_;
goto v___jp_356_;
}
}
}
v___jp_356_:
{
if (lean_obj_tag(v_val_357_) == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec_ref_known(v_val_357_, 2);
v___x_358_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__0));
v___x_359_ = l_Array_append___redArg(v_result_277_, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v_vs_360_; lean_object* v___x_361_; 
v_vs_360_ = lean_ctor_get(v_val_357_, 0);
lean_inc_ref(v_vs_360_);
lean_dec_ref_known(v_val_357_, 2);
v___x_361_ = l_Array_append___redArg(v_result_277_, v_vs_360_);
lean_dec_ref(v_vs_360_);
return v___x_361_;
}
}
}
v___jp_278_:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___y_281_, v___y_279_);
v_todo_275_ = v___x_283_;
v_c_276_ = v_val_282_;
v_result_277_ = v___y_280_;
goto _start;
}
v___jp_285_:
{
if (lean_obj_tag(v_val_291_) == 0)
{
lean_object* v_key_292_; lean_object* v_child_293_; uint8_t v___x_294_; 
v_key_292_ = lean_ctor_get(v_val_291_, 0);
lean_inc(v_key_292_);
v_child_293_ = lean_ctor_get(v_val_291_, 1);
lean_inc_ref(v_child_293_);
lean_dec_ref_known(v_val_291_, 2);
v___x_294_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_292_, v___y_288_);
lean_dec(v___y_288_);
lean_dec(v_key_292_);
if (v___x_294_ == 0)
{
lean_dec_ref(v_child_293_);
lean_dec_ref(v___y_290_);
lean_dec_ref(v___y_286_);
return v___y_289_;
}
else
{
v___y_279_ = v___y_286_;
v___y_280_ = v___y_289_;
v___y_281_ = v___y_290_;
v_val_282_ = v_child_293_;
goto v___jp_278_;
}
}
else
{
lean_object* v_children_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_311_; 
v_children_295_ = lean_ctor_get(v_val_291_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_val_291_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v_val_291_, 0);
lean_dec(v_unused_312_);
v___x_297_ = v_val_291_;
v_isShared_298_ = v_isSharedCheck_311_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_children_295_);
lean_dec(v_val_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_311_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_array_get_size(v_children_295_);
v___x_301_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_del_object(v___x_297_);
lean_dec_ref(v_children_295_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_286_);
return v___y_289_;
}
else
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_nat_sub(v___x_300_, v___y_287_);
v___x_303_ = lean_nat_dec_le(v___x_299_, v___x_302_);
if (v___x_303_ == 0)
{
lean_dec(v___x_302_);
lean_del_object(v___x_297_);
lean_dec_ref(v_children_295_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_286_);
return v___y_289_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__1));
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 0);
lean_ctor_set(v___x_297_, 1, v___x_304_);
lean_ctor_set(v___x_297_, 0, v___y_288_);
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___y_288_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg(v_children_295_, v___x_306_, v___x_299_, v___x_302_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_children_295_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_dec_ref(v___y_290_);
lean_dec_ref(v___y_286_);
return v___y_289_;
}
else
{
lean_object* v_val_308_; lean_object* v_snd_309_; 
v_val_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_307_, 1);
v_snd_309_ = lean_ctor_get(v_val_308_, 1);
lean_inc(v_snd_309_);
lean_dec(v_val_308_);
v___y_279_ = v___y_286_;
v___y_280_ = v___y_289_;
v___y_281_ = v___y_290_;
v_val_282_ = v_snd_309_;
goto v___jp_278_;
}
}
}
}
}
}
}
v___jp_313_:
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_box(0);
v___x_320_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___y_316_, v___x_319_);
if (v___x_320_ == 0)
{
switch(lean_obj_tag(v_c_276_))
{
case 2:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_316_;
v___y_289_ = v_result_318_;
v___y_290_ = v___y_317_;
v_val_291_ = v___x_321_;
goto v___jp_285_;
}
case 3:
{
lean_object* v___x_322_; 
v___x_322_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_316_;
v___y_289_ = v_result_318_;
v___y_290_ = v___y_317_;
v_val_291_ = v___x_322_;
goto v___jp_285_;
}
default: 
{
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_316_;
v___y_289_ = v_result_318_;
v___y_290_ = v___y_317_;
v_val_291_ = v_c_276_;
goto v___jp_285_;
}
}
}
else
{
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_314_);
lean_dec_ref(v_c_276_);
return v_result_318_;
}
}
v___jp_323_:
{
lean_object* v___x_329_; 
lean_inc_ref(v___y_327_);
v___x_329_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_mctx_274_, v___y_327_, v_val_328_, v_result_277_);
v___y_314_ = v___y_324_;
v___y_315_ = v___y_325_;
v___y_316_ = v___y_326_;
v___y_317_ = v___y_327_;
v_result_318_ = v___x_329_;
goto v___jp_313_;
}
v___jp_330_:
{
if (lean_obj_tag(v_val_335_) == 0)
{
lean_object* v_key_336_; lean_object* v_child_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_key_336_ = lean_ctor_get(v_val_335_, 0);
lean_inc(v_key_336_);
v_child_337_ = lean_ctor_get(v_val_335_, 1);
lean_inc_ref(v_child_337_);
lean_dec_ref_known(v_val_335_, 2);
v___x_338_ = lean_box(0);
v___x_339_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_336_, v___x_338_);
lean_dec(v_key_336_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_child_337_);
v___y_314_ = v___y_331_;
v___y_315_ = v___y_332_;
v___y_316_ = v___y_333_;
v___y_317_ = v___y_334_;
v_result_318_ = v_result_277_;
goto v___jp_313_;
}
else
{
v___y_324_ = v___y_331_;
v___y_325_ = v___y_332_;
v___y_326_ = v___y_333_;
v___y_327_ = v___y_334_;
v_val_328_ = v_child_337_;
goto v___jp_323_;
}
}
else
{
lean_object* v_children_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_children_340_ = lean_ctor_get(v_val_335_, 1);
lean_inc_ref(v_children_340_);
lean_dec_ref_known(v_val_335_, 2);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_array_get_size(v_children_340_);
v___x_343_ = lean_nat_dec_lt(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v_children_340_);
v___y_314_ = v___y_331_;
v___y_315_ = v___y_332_;
v___y_316_ = v___y_333_;
v___y_317_ = v___y_334_;
v_result_318_ = v_result_277_;
goto v___jp_313_;
}
else
{
lean_object* v___x_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_344_ = lean_array_fget(v_children_340_, v___x_341_);
lean_dec_ref(v_children_340_);
v_fst_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_fst_345_);
v_snd_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc(v_snd_346_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v___x_348_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_345_, v___x_347_);
lean_dec(v_fst_345_);
if (v___x_348_ == 0)
{
lean_dec(v_snd_346_);
v___y_314_ = v___y_331_;
v___y_315_ = v___y_332_;
v___y_316_ = v___y_333_;
v___y_317_ = v___y_334_;
v_result_318_ = v_result_277_;
goto v___jp_313_;
}
else
{
v___y_324_ = v___y_331_;
v___y_325_ = v___y_332_;
v___y_326_ = v___y_333_;
v___y_327_ = v___y_334_;
v_val_328_ = v_snd_346_;
goto v___jp_323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_mctx_383_, lean_object* v_todo_384_, lean_object* v_c_385_, lean_object* v_result_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_mctx_383_, v_todo_384_, v_c_385_, v_result_386_);
lean_dec_ref(v_mctx_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_mctx_388_, lean_object* v_todo_389_, lean_object* v_c_390_, lean_object* v_result_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_mctx_388_, v_todo_389_, v_c_390_, v_result_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_393_, lean_object* v_todo_394_, lean_object* v_c_395_, lean_object* v_result_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_393_, v_todo_394_, v_c_395_, v_result_396_);
lean_dec_ref(v_mctx_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_398_, lean_object* v_mctx_399_, lean_object* v_todo_400_, lean_object* v_c_401_, lean_object* v_result_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_mctx_399_, v_todo_400_, v_c_401_, v_result_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_404_, lean_object* v_mctx_405_, lean_object* v_todo_406_, lean_object* v_c_407_, lean_object* v_result_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_404_, v_mctx_405_, v_todo_406_, v_c_407_, v_result_408_);
lean_dec_ref(v_mctx_405_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_mctx_410_, lean_object* v_00_u03b1_411_, lean_object* v_todo_412_, lean_object* v_c_413_, lean_object* v_result_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_mctx_410_, v_todo_412_, v_c_413_, v_result_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_mctx_416_, lean_object* v_00_u03b1_417_, lean_object* v_todo_418_, lean_object* v_c_419_, lean_object* v_result_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_mctx_416_, v_00_u03b1_417_, v_todo_418_, v_c_419_, v_result_420_);
lean_dec_ref(v_mctx_416_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0(lean_object* v_00_u03b1_422_, lean_object* v_as_423_, lean_object* v_k_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___redArg(v_as_423_, v_k_424_, v_x_425_, v_x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_429_, lean_object* v_as_430_, lean_object* v_k_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Array_binSearchAux___at___00Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0_spec__0(v_00_u03b1_429_, v_as_430_, v_k_431_, v_x_432_, v_x_433_, v_x_434_);
lean_dec_ref(v_k_431_);
lean_dec_ref(v_as_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_436_, lean_object* v_vals_437_, lean_object* v_i_438_, lean_object* v_k_439_){
_start:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_array_get_size(v_keys_436_);
v___x_441_ = lean_nat_dec_lt(v_i_438_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_dec(v_i_438_);
v___x_442_ = lean_box(0);
return v___x_442_;
}
else
{
lean_object* v_k_x27_443_; uint8_t v___x_444_; 
v_k_x27_443_ = lean_array_fget_borrowed(v_keys_436_, v_i_438_);
v___x_444_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_439_, v_k_x27_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_i_438_, v___x_445_);
lean_dec(v_i_438_);
v_i_438_ = v___x_446_;
goto _start;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_array_fget_borrowed(v_vals_437_, v_i_438_);
lean_dec(v_i_438_);
lean_inc(v___x_448_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_450_, lean_object* v_vals_451_, lean_object* v_i_452_, lean_object* v_k_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_450_, v_vals_451_, v_i_452_, v_k_453_);
lean_dec(v_k_453_);
lean_dec_ref(v_vals_451_);
lean_dec_ref(v_keys_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_455_, size_t v_x_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v_es_458_; lean_object* v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v_j_462_; lean_object* v___x_463_; 
v_es_458_ = lean_ctor_get(v_x_455_, 0);
v___x_459_ = lean_box(2);
v___x_460_ = ((size_t)31ULL);
v___x_461_ = lean_usize_land(v_x_456_, v___x_460_);
v_j_462_ = lean_usize_to_nat(v___x_461_);
v___x_463_ = lean_array_get_borrowed(v___x_459_, v_es_458_, v_j_462_);
lean_dec(v_j_462_);
switch(lean_obj_tag(v___x_463_))
{
case 0:
{
lean_object* v_key_464_; lean_object* v_val_465_; uint8_t v___x_466_; 
v_key_464_ = lean_ctor_get(v___x_463_, 0);
v_val_465_ = lean_ctor_get(v___x_463_, 1);
v___x_466_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_457_, v_key_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_box(0);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
lean_inc(v_val_465_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_val_465_);
return v___x_468_;
}
}
case 1:
{
lean_object* v_node_469_; size_t v___x_470_; size_t v___x_471_; 
v_node_469_ = lean_ctor_get(v___x_463_, 0);
v___x_470_ = ((size_t)5ULL);
v___x_471_ = lean_usize_shift_right(v_x_456_, v___x_470_);
v_x_455_ = v_node_469_;
v_x_456_ = v___x_471_;
goto _start;
}
default: 
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
return v___x_473_;
}
}
}
else
{
lean_object* v_ks_474_; lean_object* v_vs_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_ks_474_ = lean_ctor_get(v_x_455_, 0);
v_vs_475_ = lean_ctor_get(v_x_455_, 1);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_474_, v_vs_475_, v___x_476_, v_x_457_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
size_t v_x_229__boxed_481_; lean_object* v_res_482_; 
v_x_229__boxed_481_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_res_482_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_478_, v_x_229__boxed_481_, v_x_480_);
lean_dec(v_x_480_);
lean_dec_ref(v_x_478_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
uint64_t v___x_485_; size_t v___x_486_; lean_object* v___x_487_; 
v___x_485_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_484_);
v___x_486_ = lean_uint64_to_usize(v___x_485_);
v___x_487_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_483_, v___x_486_, v_x_484_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_488_, v_x_489_);
lean_dec(v_x_489_);
lean_dec_ref(v_x_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_493_, lean_object* v_d_494_, lean_object* v_e_495_){
_start:
{
lean_object* v___y_497_; lean_object* v_val_507_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_box(0);
v___x_511_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_494_, v___x_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(8u);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_512_);
v___y_497_ = v___x_513_;
goto v___jp_496_;
}
else
{
lean_object* v_val_514_; 
v_val_514_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v___x_511_, 1);
switch(lean_obj_tag(v_val_514_))
{
case 2:
{
lean_object* v___x_515_; 
v___x_515_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_val_514_);
v_val_507_ = v___x_515_;
goto v___jp_506_;
}
case 3:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_val_514_);
v_val_507_ = v___x_516_;
goto v___jp_506_;
}
default: 
{
v_val_507_ = v_val_514_;
goto v___jp_506_;
}
}
}
v___jp_496_:
{
lean_object* v___x_498_; lean_object* v_e_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = l_Lean_Meta_Sym_etaReduce(v_e_495_);
v_e_499_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_493_, v___x_498_);
v___x_500_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_499_);
v___x_501_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_494_, v___x_500_);
lean_dec(v___x_500_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_dec_ref(v_e_499_);
return v___y_497_;
}
else
{
lean_object* v_val_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_val_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_val_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_504_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_503_, v_e_499_);
v___x_505_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_mctx_493_, v___x_504_, v_val_502_, v___y_497_);
return v___x_505_;
}
}
v___jp_506_:
{
if (lean_obj_tag(v_val_507_) == 0)
{
lean_object* v___x_508_; 
lean_dec_ref_known(v_val_507_, 2);
v___x_508_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___closed__0));
v___y_497_ = v___x_508_;
goto v___jp_496_;
}
else
{
lean_object* v_vs_509_; 
v_vs_509_ = lean_ctor_get(v_val_507_, 0);
lean_inc_ref(v_vs_509_);
lean_dec_ref_known(v_val_507_, 2);
v___y_497_ = v_vs_509_;
goto v___jp_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_517_, lean_object* v_d_518_, lean_object* v_e_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_517_, v_d_518_, v_e_519_);
lean_dec_ref(v_e_519_);
lean_dec_ref(v_d_518_);
lean_dec_ref(v_mctx_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_521_, lean_object* v_mctx_522_, lean_object* v_d_523_, lean_object* v_e_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_522_, v_d_523_, v_e_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_526_, lean_object* v_mctx_527_, lean_object* v_d_528_, lean_object* v_e_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_526_, v_mctx_527_, v_d_528_, v_e_529_);
lean_dec_ref(v_e_529_);
lean_dec_ref(v_d_528_);
lean_dec_ref(v_mctx_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_532_, v_x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_535_, v_x_536_, v_x_537_);
lean_dec(v_x_537_);
lean_dec_ref(v_x_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_539_, lean_object* v_x_540_, size_t v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_540_, v_x_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
size_t v_x_353__boxed_548_; lean_object* v_res_549_; 
v_x_353__boxed_548_ = lean_unbox_usize(v_x_546_);
lean_dec(v_x_546_);
v_res_549_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_544_, v_x_545_, v_x_353__boxed_548_, v_x_547_);
lean_dec(v_x_547_);
lean_dec_ref(v_x_545_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_550_, lean_object* v_keys_551_, lean_object* v_vals_552_, lean_object* v_heq_553_, lean_object* v_i_554_, lean_object* v_k_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_551_, v_vals_552_, v_i_554_, v_k_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_557_, lean_object* v_keys_558_, lean_object* v_vals_559_, lean_object* v_heq_560_, lean_object* v_i_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_557_, v_keys_558_, v_vals_559_, v_heq_560_, v_i_561_, v_k_562_);
lean_dec(v_k_562_);
lean_dec_ref(v_vals_559_);
lean_dec_ref(v_keys_558_);
return v_res_563_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_564_, lean_object* v_k_565_){
_start:
{
lean_object* v_k_567_; 
switch(lean_obj_tag(v_k_565_))
{
case 4:
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_584_; 
v_a_571_ = lean_ctor_get(v_k_565_, 0);
v_a_572_ = lean_ctor_get(v_k_565_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_k_565_);
if (v_isSharedCheck_584_ == 0)
{
v___x_574_ = v_k_565_;
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_inc(v_a_571_);
lean_dec(v_k_565_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_zero_576_; uint8_t v_isZero_577_; 
v_zero_576_ = lean_unsigned_to_nat(0u);
v_isZero_577_ = lean_nat_dec_eq(v_a_572_, v_zero_576_);
if (v_isZero_577_ == 0)
{
lean_object* v_one_578_; lean_object* v_n_579_; lean_object* v___x_581_; 
v_one_578_ = lean_unsigned_to_nat(1u);
v_n_579_ = lean_nat_sub(v_a_572_, v_one_578_);
lean_dec(v_a_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v_n_579_);
v___x_581_ = v___x_574_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_571_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_n_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
v_k_567_ = v___x_581_;
goto v___jp_566_;
}
}
else
{
uint8_t v___x_583_; 
lean_del_object(v___x_574_);
lean_dec(v_a_572_);
lean_dec(v_a_571_);
v___x_583_ = 0;
return v___x_583_;
}
}
}
case 3:
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_598_; 
v_a_585_ = lean_ctor_get(v_k_565_, 0);
v_a_586_ = lean_ctor_get(v_k_565_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_k_565_);
if (v_isSharedCheck_598_ == 0)
{
v___x_588_ = v_k_565_;
v_isShared_589_ = v_isSharedCheck_598_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_inc(v_a_585_);
lean_dec(v_k_565_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_598_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_zero_590_; uint8_t v_isZero_591_; 
v_zero_590_ = lean_unsigned_to_nat(0u);
v_isZero_591_ = lean_nat_dec_eq(v_a_586_, v_zero_590_);
if (v_isZero_591_ == 0)
{
lean_object* v_one_592_; lean_object* v_n_593_; lean_object* v___x_595_; 
v_one_592_ = lean_unsigned_to_nat(1u);
v_n_593_ = lean_nat_sub(v_a_586_, v_one_592_);
lean_dec(v_a_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_n_593_);
v___x_595_ = v___x_588_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_585_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_n_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v_k_567_ = v___x_595_;
goto v___jp_566_;
}
}
else
{
uint8_t v___x_597_; 
lean_del_object(v___x_588_);
lean_dec(v_a_586_);
lean_dec(v_a_585_);
v___x_597_ = 0;
return v___x_597_;
}
}
}
default: 
{
uint8_t v___x_599_; 
lean_dec(v_k_565_);
v___x_599_ = 0;
return v___x_599_;
}
}
v___jp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_564_, v_k_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
v_k_565_ = v_k_567_;
goto _start;
}
else
{
uint8_t v___x_570_; 
lean_dec_ref_known(v___x_568_, 1);
lean_dec(v_k_567_);
v___x_570_ = 1;
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_600_, lean_object* v_k_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_600_, v_k_601_);
lean_dec_ref(v_d_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_604_, lean_object* v_d_605_, lean_object* v_k_606_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_605_, v_k_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_608_, lean_object* v_d_609_, lean_object* v_k_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_608_, v_d_609_, v_k_610_);
lean_dec_ref(v_d_609_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_613_, size_t v_sz_614_, size_t v_i_615_, lean_object* v_bs_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_617_ == 0)
{
lean_dec(v_numExtra_613_);
return v_bs_616_;
}
else
{
lean_object* v_v_618_; lean_object* v___x_619_; lean_object* v_bs_x27_620_; lean_object* v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v_v_618_ = lean_array_uget(v_bs_616_, v_i_615_);
v___x_619_ = lean_unsigned_to_nat(0u);
v_bs_x27_620_ = lean_array_uset(v_bs_616_, v_i_615_, v___x_619_);
lean_inc(v_numExtra_613_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_v_618_);
lean_ctor_set(v___x_621_, 1, v_numExtra_613_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_615_, v___x_622_);
v___x_624_ = lean_array_uset(v_bs_x27_620_, v_i_615_, v___x_621_);
v_i_615_ = v___x_623_;
v_bs_616_ = v___x_624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_626_, lean_object* v_sz_627_, lean_object* v_i_628_, lean_object* v_bs_629_){
_start:
{
size_t v_sz_boxed_630_; size_t v_i_boxed_631_; lean_object* v_res_632_; 
v_sz_boxed_630_ = lean_unbox_usize(v_sz_627_);
lean_dec(v_sz_627_);
v_i_boxed_631_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_626_, v_sz_boxed_630_, v_i_boxed_631_, v_bs_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_633_, lean_object* v_d_634_, lean_object* v_e_635_, lean_object* v_numExtra_636_, lean_object* v_result_637_){
_start:
{
lean_object* v___x_638_; size_t v_sz_639_; size_t v___x_640_; lean_object* v___x_641_; lean_object* v_result_642_; lean_object* v_e_643_; uint8_t v___x_644_; 
v___x_638_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_633_, v_d_634_, v_e_635_);
v_sz_639_ = lean_array_size(v___x_638_);
v___x_640_ = ((size_t)0ULL);
lean_inc(v_numExtra_636_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_636_, v_sz_639_, v___x_640_, v___x_638_);
v_result_642_ = l_Array_append___redArg(v_result_637_, v___x_641_);
lean_dec_ref(v___x_641_);
v_e_643_ = l_Lean_Expr_consumeMData(v_e_635_);
lean_dec_ref(v_e_635_);
v___x_644_ = l_Lean_Expr_isApp(v_e_643_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_e_643_);
lean_dec(v_numExtra_636_);
return v_result_642_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_Expr_appFn_x21(v_e_643_);
lean_dec_ref(v_e_643_);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_numExtra_636_, v___x_646_);
lean_dec(v_numExtra_636_);
v_e_635_ = v___x_645_;
v_numExtra_636_ = v___x_647_;
v_result_637_ = v_result_642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_649_, lean_object* v_d_650_, lean_object* v_e_651_, lean_object* v_numExtra_652_, lean_object* v_result_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_649_, v_d_650_, v_e_651_, v_numExtra_652_, v_result_653_);
lean_dec_ref(v_d_650_);
lean_dec_ref(v_mctx_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_655_, lean_object* v_mctx_656_, lean_object* v_d_657_, lean_object* v_e_658_, lean_object* v_numExtra_659_, lean_object* v_result_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_656_, v_d_657_, v_e_658_, v_numExtra_659_, v_result_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_662_, lean_object* v_mctx_663_, lean_object* v_d_664_, lean_object* v_e_665_, lean_object* v_numExtra_666_, lean_object* v_result_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_662_, v_mctx_663_, v_d_664_, v_e_665_, v_numExtra_666_, v_result_667_);
lean_dec_ref(v_d_664_);
lean_dec_ref(v_mctx_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_669_, lean_object* v_numExtra_670_, size_t v_sz_671_, size_t v_i_672_, lean_object* v_bs_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_670_, v_sz_671_, v_i_672_, v_bs_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_675_, lean_object* v_numExtra_676_, lean_object* v_sz_677_, lean_object* v_i_678_, lean_object* v_bs_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_677_);
lean_dec(v_sz_677_);
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_675_, v_numExtra_676_, v_sz_boxed_680_, v_i_boxed_681_, v_bs_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_683_, size_t v_i_684_, lean_object* v_bs_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_lt(v_i_684_, v_sz_683_);
if (v___x_686_ == 0)
{
return v_bs_685_;
}
else
{
lean_object* v_v_687_; lean_object* v___x_688_; lean_object* v_bs_x27_689_; lean_object* v___x_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v_v_687_ = lean_array_uget(v_bs_685_, v_i_684_);
v___x_688_ = lean_unsigned_to_nat(0u);
v_bs_x27_689_ = lean_array_uset(v_bs_685_, v_i_684_, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_v_687_);
lean_ctor_set(v___x_690_, 1, v___x_688_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_684_, v___x_691_);
v___x_693_ = lean_array_uset(v_bs_x27_689_, v_i_684_, v___x_690_);
v_i_684_ = v___x_692_;
v_bs_685_ = v___x_693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_695_, lean_object* v_i_696_, lean_object* v_bs_697_){
_start:
{
size_t v_sz_boxed_698_; size_t v_i_boxed_699_; lean_object* v_res_700_; 
v_sz_boxed_698_ = lean_unbox_usize(v_sz_695_);
lean_dec(v_sz_695_);
v_i_boxed_699_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_698_, v_i_boxed_699_, v_bs_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_701_, lean_object* v_d_702_, lean_object* v_e_703_){
_start:
{
lean_object* v___x_704_; lean_object* v_e_705_; lean_object* v_e_706_; lean_object* v_result_707_; size_t v_sz_708_; size_t v___x_709_; lean_object* v_result_710_; uint8_t v___x_711_; 
v___x_704_ = l_Lean_Meta_Sym_etaReduce(v_e_703_);
v_e_705_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_701_, v___x_704_);
v_e_706_ = l_Lean_Expr_consumeMData(v_e_705_);
lean_dec_ref(v_e_705_);
v_result_707_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_701_, v_d_702_, v_e_706_);
v_sz_708_ = lean_array_size(v_result_707_);
v___x_709_ = ((size_t)0ULL);
v_result_710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_708_, v___x_709_, v_result_707_);
v___x_711_ = l_Lean_Expr_isApp(v_e_706_);
if (v___x_711_ == 0)
{
lean_dec_ref(v_e_706_);
return v_result_710_;
}
else
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_706_);
v___x_713_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_702_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec_ref(v_e_706_);
return v_result_710_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = l_Lean_Expr_appFn_x21(v_e_706_);
lean_dec_ref(v_e_706_);
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_701_, v_d_702_, v___x_714_, v___x_715_, v_result_710_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_717_, lean_object* v_d_718_, lean_object* v_e_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_717_, v_d_718_, v_e_719_);
lean_dec_ref(v_e_719_);
lean_dec_ref(v_d_718_);
lean_dec_ref(v_mctx_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_721_, lean_object* v_mctx_722_, lean_object* v_d_723_, lean_object* v_e_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_722_, v_d_723_, v_e_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_726_, lean_object* v_mctx_727_, lean_object* v_d_728_, lean_object* v_e_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_726_, v_mctx_727_, v_d_728_, v_e_729_);
lean_dec_ref(v_e_729_);
lean_dec_ref(v_d_728_);
lean_dec_ref(v_mctx_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_731_, size_t v_sz_732_, size_t v_i_733_, lean_object* v_bs_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_732_, v_i_733_, v_bs_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_736_, lean_object* v_sz_737_, lean_object* v_i_738_, lean_object* v_bs_739_){
_start:
{
size_t v_sz_boxed_740_; size_t v_i_boxed_741_; lean_object* v_res_742_; 
v_sz_boxed_740_ = lean_unbox_usize(v_sz_737_);
lean_dec(v_sz_737_);
v_i_boxed_741_ = lean_unbox_usize(v_i_738_);
lean_dec(v_i_738_);
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_736_, v_sz_boxed_740_, v_i_boxed_741_, v_bs_739_);
return v_res_742_;
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
