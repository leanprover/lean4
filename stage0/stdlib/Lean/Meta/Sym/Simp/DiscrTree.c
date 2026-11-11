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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__0_value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__1_value;
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___lam__0(lean_object* v_a_198_, lean_object* v_b_199_){
_start:
{
lean_object* v_fst_200_; lean_object* v_fst_201_; uint8_t v___x_202_; 
v_fst_200_ = lean_ctor_get(v_a_198_, 0);
v_fst_201_ = lean_ctor_get(v_b_199_, 0);
v___x_202_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_200_, v_fst_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___lam__0___boxed(lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___lam__0(v_a_203_, v_b_204_);
lean_dec_ref(v_b_204_);
lean_dec_ref(v_a_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_as_207_, lean_object* v_k_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_m_213_; lean_object* v_a_214_; uint8_t v___x_215_; 
v___x_211_ = lean_nat_add(v_x_209_, v_x_210_);
v___x_212_ = lean_unsigned_to_nat(1u);
v_m_213_ = lean_nat_shiftr(v___x_211_, v___x_212_);
lean_dec(v___x_211_);
v_a_214_ = lean_array_fget_borrowed(v_as_207_, v_m_213_);
v___x_215_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___lam__0(v_a_214_, v_k_208_);
if (v___x_215_ == 0)
{
uint8_t v___x_216_; 
lean_dec(v_x_210_);
v___x_216_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___lam__0(v_k_208_, v_a_214_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec(v_m_213_);
lean_dec(v_x_209_);
lean_inc(v_a_214_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_a_214_);
return v___x_217_;
}
else
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_dec_eq(v_m_213_, v___x_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_nat_sub(v_m_213_, v___x_212_);
lean_dec(v_m_213_);
v___x_221_ = lean_nat_dec_lt(v___x_220_, v_x_209_);
if (v___x_221_ == 0)
{
v_x_210_ = v___x_220_;
goto _start;
}
else
{
lean_object* v___x_223_; 
lean_dec(v___x_220_);
lean_dec(v_x_209_);
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v_m_213_);
lean_dec(v_x_209_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
}
else
{
lean_object* v___x_225_; uint8_t v___x_226_; 
lean_dec(v_x_209_);
v___x_225_ = lean_nat_add(v_m_213_, v___x_212_);
lean_dec(v_m_213_);
v___x_226_ = lean_nat_dec_le(v___x_225_, v_x_210_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec(v___x_225_);
lean_dec(v_x_210_);
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
v_x_209_ = v___x_225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_229_, lean_object* v_k_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_229_, v_k_230_, v_x_231_, v_x_232_);
lean_dec_ref(v_k_230_);
lean_dec_ref(v_as_229_);
return v_res_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__1(lean_object* v_mctx_234_, lean_object* v_todo_235_, lean_object* v_ks_236_, lean_object* v_i_237_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_array_get_size(v_ks_236_);
v___x_239_ = lean_nat_dec_lt(v_i_237_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
lean_dec(v_i_237_);
v___x_240_ = lean_array_get_size(v_todo_235_);
lean_dec_ref(v_todo_235_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_nat_dec_eq(v___x_240_, v___x_241_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_array_get_size(v_todo_235_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v_e_249_; lean_object* v_todo_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_246_ = l_Lean_instInhabitedExpr;
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_sub(v___x_243_, v___x_247_);
v_e_249_ = lean_array_get(v___x_246_, v_todo_235_, v___x_248_);
lean_dec(v___x_248_);
v_todo_250_ = lean_array_pop(v_todo_235_);
v___x_251_ = lean_array_fget_borrowed(v_ks_236_, v_i_237_);
v___x_252_ = lean_box(0);
v___x_253_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v_e_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = l_Lean_Meta_Sym_etaReduce(v_e_249_);
lean_dec(v_e_249_);
v_e_255_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_234_, v___x_254_);
v___x_256_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_255_);
v___x_257_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_251_, v___x_256_);
lean_dec(v___x_256_);
if (v___x_257_ == 0)
{
lean_dec_ref(v_e_255_);
lean_dec_ref(v_todo_250_);
lean_dec(v_i_237_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_250_, v_e_255_);
v___x_259_ = lean_nat_add(v_i_237_, v___x_247_);
lean_dec(v_i_237_);
v_todo_235_ = v___x_258_;
v_i_237_ = v___x_259_;
goto _start;
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v_e_249_);
v___x_261_ = lean_nat_add(v_i_237_, v___x_247_);
lean_dec(v_i_237_);
v_todo_235_ = v_todo_250_;
v_i_237_ = v___x_261_;
goto _start;
}
}
else
{
uint8_t v___x_263_; 
lean_dec(v_i_237_);
lean_dec_ref(v_todo_235_);
v___x_263_ = 0;
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__1___boxed(lean_object* v_mctx_264_, lean_object* v_todo_265_, lean_object* v_ks_266_, lean_object* v_i_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__1(v_mctx_264_, v_todo_265_, v_ks_266_, v_i_267_);
lean_dec_ref(v_ks_266_);
lean_dec_ref(v_mctx_264_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_mctx_274_, lean_object* v_todo_275_, lean_object* v_c_276_, lean_object* v_result_277_){
_start:
{
lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v_val_282_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v_val_291_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v_val_325_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v_val_331_; lean_object* v_val_346_; 
if (lean_obj_tag(v_c_276_) == 3)
{
lean_object* v_keys_351_; lean_object* v_i_352_; lean_object* v_v_353_; uint8_t v___x_354_; 
v_keys_351_ = lean_ctor_get(v_c_276_, 0);
lean_inc_ref(v_keys_351_);
v_i_352_ = lean_ctor_get(v_c_276_, 1);
lean_inc(v_i_352_);
v_v_353_ = lean_ctor_get(v_c_276_, 2);
lean_inc(v_v_353_);
lean_dec_ref_known(v_c_276_, 3);
v___x_354_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__1(v_mctx_274_, v_todo_275_, v_keys_351_, v_i_352_);
lean_dec_ref(v_keys_351_);
if (v___x_354_ == 0)
{
lean_dec(v_v_353_);
return v_result_277_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_array_push(v_result_277_, v_v_353_);
return v___x_355_;
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_array_get_size(v_todo_275_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_nat_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v_val_370_; 
v___x_359_ = l_Lean_instInhabitedExpr;
switch(lean_obj_tag(v_c_276_))
{
case 2:
{
lean_object* v___x_374_; 
lean_inc_ref(v_c_276_);
v___x_374_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_370_ = v___x_374_;
goto v___jp_369_;
}
case 3:
{
lean_object* v___x_375_; 
lean_inc_ref(v_c_276_);
v___x_375_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_370_ = v___x_375_;
goto v___jp_369_;
}
default: 
{
lean_inc_ref(v_c_276_);
v_val_370_ = v_c_276_;
goto v___jp_369_;
}
}
v___jp_360_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_e_365_; lean_object* v_todo_366_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_sub(v___x_356_, v___x_361_);
v___x_363_ = lean_array_get_borrowed(v___x_359_, v_todo_275_, v___x_362_);
lean_dec(v___x_362_);
v___x_364_ = l_Lean_Meta_Sym_etaReduce(v___x_363_);
v_e_365_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_274_, v___x_364_);
v_todo_366_ = lean_array_pop(v_todo_275_);
switch(lean_obj_tag(v_c_276_))
{
case 2:
{
lean_object* v___x_367_; 
lean_inc_ref(v_c_276_);
v___x_367_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_328_ = v_e_365_;
v___y_329_ = v___x_361_;
v___y_330_ = v_todo_366_;
v_val_331_ = v___x_367_;
goto v___jp_327_;
}
case 3:
{
lean_object* v___x_368_; 
lean_inc_ref(v_c_276_);
v___x_368_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_328_ = v_e_365_;
v___y_329_ = v___x_361_;
v___y_330_ = v_todo_366_;
v_val_331_ = v___x_368_;
goto v___jp_327_;
}
default: 
{
lean_inc_ref(v_c_276_);
v___y_328_ = v_e_365_;
v___y_329_ = v___x_361_;
v___y_330_ = v_todo_366_;
v_val_331_ = v_c_276_;
goto v___jp_327_;
}
}
}
v___jp_369_:
{
if (lean_obj_tag(v_val_370_) == 0)
{
lean_dec_ref_known(v_val_370_, 2);
goto v___jp_360_;
}
else
{
lean_object* v_children_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_children_371_ = lean_ctor_get(v_val_370_, 1);
lean_inc_ref(v_children_371_);
lean_dec_ref_known(v_val_370_, 2);
v___x_372_ = lean_array_get_size(v_children_371_);
lean_dec_ref(v_children_371_);
v___x_373_ = lean_nat_dec_eq(v___x_372_, v___x_357_);
if (v___x_373_ == 0)
{
goto v___jp_360_;
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
lean_object* v___x_376_; 
v___x_376_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_346_ = v___x_376_;
goto v___jp_345_;
}
case 3:
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v_val_346_ = v___x_377_;
goto v___jp_345_;
}
default: 
{
v_val_346_ = v_c_276_;
goto v___jp_345_;
}
}
}
}
v___jp_278_:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___y_280_, v___y_279_);
v_todo_275_ = v___x_283_;
v_c_276_ = v_val_282_;
v_result_277_ = v___y_281_;
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
v___x_294_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_292_, v___y_290_);
lean_dec(v___y_290_);
lean_dec(v_key_292_);
if (v___x_294_ == 0)
{
lean_dec_ref(v_child_293_);
lean_dec_ref(v___y_288_);
lean_dec_ref(v___y_286_);
return v___y_289_;
}
else
{
v___y_279_ = v___y_286_;
v___y_280_ = v___y_288_;
v___y_281_ = v___y_289_;
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
lean_dec(v___y_290_);
lean_dec_ref(v___y_288_);
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
lean_dec(v___y_290_);
lean_dec_ref(v___y_288_);
lean_dec_ref(v___y_286_);
return v___y_289_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__1));
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 0);
lean_ctor_set(v___x_297_, 1, v___x_304_);
lean_ctor_set(v___x_297_, 0, v___y_290_);
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___y_290_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_295_, v___x_306_, v___x_299_, v___x_302_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_children_295_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_dec_ref(v___y_288_);
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
v___y_280_ = v___y_288_;
v___y_281_ = v___y_289_;
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
lean_object* v___x_318_; 
v___x_318_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v___y_314_);
switch(lean_obj_tag(v_c_276_))
{
case 2:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_316_;
v___y_289_ = v___y_317_;
v___y_290_ = v___x_318_;
v_val_291_ = v___x_319_;
goto v___jp_285_;
}
case 3:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_276_);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_316_;
v___y_289_ = v___y_317_;
v___y_290_ = v___x_318_;
v_val_291_ = v___x_320_;
goto v___jp_285_;
}
default: 
{
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_316_;
v___y_289_ = v___y_317_;
v___y_290_ = v___x_318_;
v_val_291_ = v_c_276_;
goto v___jp_285_;
}
}
}
v___jp_321_:
{
lean_object* v___x_326_; 
lean_inc_ref(v___y_324_);
v___x_326_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_274_, v___y_324_, v_val_325_, v_result_277_);
v___y_314_ = v___y_322_;
v___y_315_ = v___y_323_;
v___y_316_ = v___y_324_;
v___y_317_ = v___x_326_;
goto v___jp_313_;
}
v___jp_327_:
{
if (lean_obj_tag(v_val_331_) == 0)
{
lean_object* v_key_332_; lean_object* v_child_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_key_332_ = lean_ctor_get(v_val_331_, 0);
lean_inc(v_key_332_);
v_child_333_ = lean_ctor_get(v_val_331_, 1);
lean_inc_ref(v_child_333_);
lean_dec_ref_known(v_val_331_, 2);
v___x_334_ = lean_box(0);
v___x_335_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_332_, v___x_334_);
lean_dec(v_key_332_);
if (v___x_335_ == 0)
{
lean_dec_ref(v_child_333_);
v___y_314_ = v___y_328_;
v___y_315_ = v___y_329_;
v___y_316_ = v___y_330_;
v___y_317_ = v_result_277_;
goto v___jp_313_;
}
else
{
v___y_322_ = v___y_328_;
v___y_323_ = v___y_329_;
v___y_324_ = v___y_330_;
v_val_325_ = v_child_333_;
goto v___jp_321_;
}
}
else
{
lean_object* v_children_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_children_336_ = lean_ctor_get(v_val_331_, 1);
lean_inc_ref(v_children_336_);
lean_dec_ref_known(v_val_331_, 2);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_array_get_size(v_children_336_);
v___x_339_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_children_336_);
v___y_314_ = v___y_328_;
v___y_315_ = v___y_329_;
v___y_316_ = v___y_330_;
v___y_317_ = v_result_277_;
goto v___jp_313_;
}
else
{
lean_object* v___x_340_; lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_340_ = lean_array_fget(v_children_336_, v___x_337_);
lean_dec_ref(v_children_336_);
v_fst_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_fst_341_);
v_snd_342_ = lean_ctor_get(v___x_340_, 1);
lean_inc(v_snd_342_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v___x_344_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_341_, v___x_343_);
lean_dec(v_fst_341_);
if (v___x_344_ == 0)
{
lean_dec(v_snd_342_);
v___y_314_ = v___y_328_;
v___y_315_ = v___y_329_;
v___y_316_ = v___y_330_;
v___y_317_ = v_result_277_;
goto v___jp_313_;
}
else
{
v___y_322_ = v___y_328_;
v___y_323_ = v___y_329_;
v___y_324_ = v___y_330_;
v_val_325_ = v_snd_342_;
goto v___jp_321_;
}
}
}
}
v___jp_345_:
{
if (lean_obj_tag(v_val_346_) == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec_ref_known(v_val_346_, 2);
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__0));
v___x_348_ = l_Array_append___redArg(v_result_277_, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v_vs_349_; lean_object* v___x_350_; 
v_vs_349_ = lean_ctor_get(v_val_346_, 0);
lean_inc_ref(v_vs_349_);
lean_dec_ref_known(v_val_346_, 2);
v___x_350_ = l_Array_append___redArg(v_result_277_, v_vs_349_);
lean_dec_ref(v_vs_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_378_, lean_object* v_todo_379_, lean_object* v_c_380_, lean_object* v_result_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_378_, v_todo_379_, v_c_380_, v_result_381_);
lean_dec_ref(v_mctx_378_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_383_, lean_object* v_mctx_384_, lean_object* v_todo_385_, lean_object* v_c_386_, lean_object* v_result_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_384_, v_todo_385_, v_c_386_, v_result_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_389_, lean_object* v_mctx_390_, lean_object* v_todo_391_, lean_object* v_c_392_, lean_object* v_result_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_389_, v_mctx_390_, v_todo_391_, v_c_392_, v_result_393_);
lean_dec_ref(v_mctx_390_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_395_, lean_object* v_as_396_, lean_object* v_k_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_396_, v_k_397_, v_x_398_, v_x_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_402_, lean_object* v_as_403_, lean_object* v_k_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_402_, v_as_403_, v_k_404_, v_x_405_, v_x_406_, v_x_407_);
lean_dec_ref(v_k_404_);
lean_dec_ref(v_as_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_409_, lean_object* v_vals_410_, lean_object* v_i_411_, lean_object* v_k_412_){
_start:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_array_get_size(v_keys_409_);
v___x_414_ = lean_nat_dec_lt(v_i_411_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v_i_411_);
v___x_415_ = lean_box(0);
return v___x_415_;
}
else
{
lean_object* v_k_x27_416_; uint8_t v___x_417_; 
v_k_x27_416_ = lean_array_fget_borrowed(v_keys_409_, v_i_411_);
v___x_417_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_412_, v_k_x27_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_i_411_, v___x_418_);
lean_dec(v_i_411_);
v_i_411_ = v___x_419_;
goto _start;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_array_fget_borrowed(v_vals_410_, v_i_411_);
lean_dec(v_i_411_);
lean_inc(v___x_421_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_423_, lean_object* v_vals_424_, lean_object* v_i_425_, lean_object* v_k_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_423_, v_vals_424_, v_i_425_, v_k_426_);
lean_dec(v_k_426_);
lean_dec_ref(v_vals_424_);
lean_dec_ref(v_keys_423_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_428_, size_t v_x_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_object* v_es_431_; lean_object* v___x_432_; size_t v___x_433_; size_t v___x_434_; lean_object* v_j_435_; lean_object* v___x_436_; 
v_es_431_ = lean_ctor_get(v_x_428_, 0);
v___x_432_ = lean_box(2);
v___x_433_ = ((size_t)31ULL);
v___x_434_ = lean_usize_land(v_x_429_, v___x_433_);
v_j_435_ = lean_usize_to_nat(v___x_434_);
v___x_436_ = lean_array_get_borrowed(v___x_432_, v_es_431_, v_j_435_);
lean_dec(v_j_435_);
switch(lean_obj_tag(v___x_436_))
{
case 0:
{
lean_object* v_key_437_; lean_object* v_val_438_; uint8_t v___x_439_; 
v_key_437_ = lean_ctor_get(v___x_436_, 0);
v_val_438_ = lean_ctor_get(v___x_436_, 1);
v___x_439_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_430_, v_key_437_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_box(0);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
lean_inc(v_val_438_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_val_438_);
return v___x_441_;
}
}
case 1:
{
lean_object* v_node_442_; size_t v___x_443_; size_t v___x_444_; 
v_node_442_ = lean_ctor_get(v___x_436_, 0);
v___x_443_ = ((size_t)5ULL);
v___x_444_ = lean_usize_shift_right(v_x_429_, v___x_443_);
v_x_428_ = v_node_442_;
v_x_429_ = v___x_444_;
goto _start;
}
default: 
{
lean_object* v___x_446_; 
v___x_446_ = lean_box(0);
return v___x_446_;
}
}
}
else
{
lean_object* v_ks_447_; lean_object* v_vs_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_ks_447_ = lean_ctor_get(v_x_428_, 0);
v_vs_448_ = lean_ctor_get(v_x_428_, 1);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_447_, v_vs_448_, v___x_449_, v_x_430_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
size_t v_x_228__boxed_454_; lean_object* v_res_455_; 
v_x_228__boxed_454_ = lean_unbox_usize(v_x_452_);
lean_dec(v_x_452_);
v_res_455_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_451_, v_x_228__boxed_454_, v_x_453_);
lean_dec(v_x_453_);
lean_dec_ref(v_x_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
uint64_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_457_);
v___x_459_ = lean_uint64_to_usize(v___x_458_);
v___x_460_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_456_, v___x_459_, v_x_457_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_461_, v_x_462_);
lean_dec(v_x_462_);
lean_dec_ref(v_x_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_466_, lean_object* v_d_467_, lean_object* v_e_468_){
_start:
{
lean_object* v___y_470_; lean_object* v_val_480_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(0);
v___x_484_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_467_, v___x_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(8u);
v___x_486_ = lean_mk_empty_array_with_capacity(v___x_485_);
v___y_470_ = v___x_486_;
goto v___jp_469_;
}
else
{
lean_object* v_val_487_; 
v_val_487_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v___x_484_, 1);
switch(lean_obj_tag(v_val_487_))
{
case 2:
{
lean_object* v___x_488_; 
v___x_488_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_val_487_);
v_val_480_ = v___x_488_;
goto v___jp_479_;
}
case 3:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_val_487_);
v_val_480_ = v___x_489_;
goto v___jp_479_;
}
default: 
{
v_val_480_ = v_val_487_;
goto v___jp_479_;
}
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v_e_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = l_Lean_Meta_Sym_etaReduce(v_e_468_);
v_e_472_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_466_, v___x_471_);
v___x_473_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_472_);
v___x_474_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_467_, v___x_473_);
lean_dec(v___x_473_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_dec_ref(v_e_472_);
return v___y_470_;
}
else
{
lean_object* v_val_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_477_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_476_, v_e_472_);
v___x_478_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_466_, v___x_477_, v_val_475_, v___y_470_);
return v___x_478_;
}
}
v___jp_479_:
{
if (lean_obj_tag(v_val_480_) == 0)
{
lean_object* v___x_481_; 
lean_dec_ref_known(v_val_480_, 2);
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___closed__0));
v___y_470_ = v___x_481_;
goto v___jp_469_;
}
else
{
lean_object* v_vs_482_; 
v_vs_482_ = lean_ctor_get(v_val_480_, 0);
lean_inc_ref(v_vs_482_);
lean_dec_ref_known(v_val_480_, 2);
v___y_470_ = v_vs_482_;
goto v___jp_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_490_, lean_object* v_d_491_, lean_object* v_e_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_490_, v_d_491_, v_e_492_);
lean_dec_ref(v_e_492_);
lean_dec_ref(v_d_491_);
lean_dec_ref(v_mctx_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_494_, lean_object* v_mctx_495_, lean_object* v_d_496_, lean_object* v_e_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_495_, v_d_496_, v_e_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_499_, lean_object* v_mctx_500_, lean_object* v_d_501_, lean_object* v_e_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_499_, v_mctx_500_, v_d_501_, v_e_502_);
lean_dec_ref(v_e_502_);
lean_dec_ref(v_d_501_);
lean_dec_ref(v_mctx_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_504_, lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_505_, v_x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_508_, v_x_509_, v_x_510_);
lean_dec(v_x_510_);
lean_dec_ref(v_x_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, size_t v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_513_, v_x_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
size_t v_x_352__boxed_521_; lean_object* v_res_522_; 
v_x_352__boxed_521_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_res_522_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_517_, v_x_518_, v_x_352__boxed_521_, v_x_520_);
lean_dec(v_x_520_);
lean_dec_ref(v_x_518_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_523_, lean_object* v_keys_524_, lean_object* v_vals_525_, lean_object* v_heq_526_, lean_object* v_i_527_, lean_object* v_k_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_524_, v_vals_525_, v_i_527_, v_k_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_530_, lean_object* v_keys_531_, lean_object* v_vals_532_, lean_object* v_heq_533_, lean_object* v_i_534_, lean_object* v_k_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_530_, v_keys_531_, v_vals_532_, v_heq_533_, v_i_534_, v_k_535_);
lean_dec(v_k_535_);
lean_dec_ref(v_vals_532_);
lean_dec_ref(v_keys_531_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_537_, lean_object* v_k_538_){
_start:
{
lean_object* v_k_540_; 
switch(lean_obj_tag(v_k_538_))
{
case 4:
{
lean_object* v_a_544_; lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_557_; 
v_a_544_ = lean_ctor_get(v_k_538_, 0);
v_a_545_ = lean_ctor_get(v_k_538_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_k_538_);
if (v_isSharedCheck_557_ == 0)
{
v___x_547_ = v_k_538_;
v_isShared_548_ = v_isSharedCheck_557_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_inc(v_a_544_);
lean_dec(v_k_538_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_557_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_zero_549_; uint8_t v_isZero_550_; 
v_zero_549_ = lean_unsigned_to_nat(0u);
v_isZero_550_ = lean_nat_dec_eq(v_a_545_, v_zero_549_);
if (v_isZero_550_ == 0)
{
lean_object* v_one_551_; lean_object* v_n_552_; lean_object* v___x_554_; 
v_one_551_ = lean_unsigned_to_nat(1u);
v_n_552_ = lean_nat_sub(v_a_545_, v_one_551_);
lean_dec(v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 1, v_n_552_);
v___x_554_ = v___x_547_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_544_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_n_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v_k_540_ = v___x_554_;
goto v___jp_539_;
}
}
else
{
uint8_t v___x_556_; 
lean_del_object(v___x_547_);
lean_dec(v_a_545_);
lean_dec(v_a_544_);
v___x_556_ = 0;
return v___x_556_;
}
}
}
case 3:
{
lean_object* v_a_558_; lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_571_; 
v_a_558_ = lean_ctor_get(v_k_538_, 0);
v_a_559_ = lean_ctor_get(v_k_538_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_k_538_);
if (v_isSharedCheck_571_ == 0)
{
v___x_561_ = v_k_538_;
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_inc(v_a_558_);
lean_dec(v_k_538_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_zero_563_; uint8_t v_isZero_564_; 
v_zero_563_ = lean_unsigned_to_nat(0u);
v_isZero_564_ = lean_nat_dec_eq(v_a_559_, v_zero_563_);
if (v_isZero_564_ == 0)
{
lean_object* v_one_565_; lean_object* v_n_566_; lean_object* v___x_568_; 
v_one_565_ = lean_unsigned_to_nat(1u);
v_n_566_ = lean_nat_sub(v_a_559_, v_one_565_);
lean_dec(v_a_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_n_566_);
v___x_568_ = v___x_561_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_558_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_n_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v_k_540_ = v___x_568_;
goto v___jp_539_;
}
}
else
{
uint8_t v___x_570_; 
lean_del_object(v___x_561_);
lean_dec(v_a_559_);
lean_dec(v_a_558_);
v___x_570_ = 0;
return v___x_570_;
}
}
}
default: 
{
uint8_t v___x_572_; 
lean_dec(v_k_538_);
v___x_572_ = 0;
return v___x_572_;
}
}
v___jp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_537_, v_k_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
v_k_538_ = v_k_540_;
goto _start;
}
else
{
uint8_t v___x_543_; 
lean_dec_ref_known(v___x_541_, 1);
lean_dec(v_k_540_);
v___x_543_ = 1;
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_573_, lean_object* v_k_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_573_, v_k_574_);
lean_dec_ref(v_d_573_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_577_, lean_object* v_d_578_, lean_object* v_k_579_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_578_, v_k_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_581_, lean_object* v_d_582_, lean_object* v_k_583_){
_start:
{
uint8_t v_res_584_; lean_object* v_r_585_; 
v_res_584_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_581_, v_d_582_, v_k_583_);
lean_dec_ref(v_d_582_);
v_r_585_ = lean_box(v_res_584_);
return v_r_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_586_, size_t v_sz_587_, size_t v_i_588_, lean_object* v_bs_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = lean_usize_dec_lt(v_i_588_, v_sz_587_);
if (v___x_590_ == 0)
{
lean_dec(v_numExtra_586_);
return v_bs_589_;
}
else
{
lean_object* v_v_591_; lean_object* v___x_592_; lean_object* v_bs_x27_593_; lean_object* v___x_594_; size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v_v_591_ = lean_array_uget(v_bs_589_, v_i_588_);
v___x_592_ = lean_unsigned_to_nat(0u);
v_bs_x27_593_ = lean_array_uset(v_bs_589_, v_i_588_, v___x_592_);
lean_inc(v_numExtra_586_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_v_591_);
lean_ctor_set(v___x_594_, 1, v_numExtra_586_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_588_, v___x_595_);
v___x_597_ = lean_array_uset(v_bs_x27_593_, v_i_588_, v___x_594_);
v_i_588_ = v___x_596_;
v_bs_589_ = v___x_597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_599_, lean_object* v_sz_600_, lean_object* v_i_601_, lean_object* v_bs_602_){
_start:
{
size_t v_sz_boxed_603_; size_t v_i_boxed_604_; lean_object* v_res_605_; 
v_sz_boxed_603_ = lean_unbox_usize(v_sz_600_);
lean_dec(v_sz_600_);
v_i_boxed_604_ = lean_unbox_usize(v_i_601_);
lean_dec(v_i_601_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_599_, v_sz_boxed_603_, v_i_boxed_604_, v_bs_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_606_, lean_object* v_d_607_, lean_object* v_e_608_, lean_object* v_numExtra_609_, lean_object* v_result_610_){
_start:
{
lean_object* v___x_611_; size_t v_sz_612_; size_t v___x_613_; lean_object* v___x_614_; lean_object* v_result_615_; lean_object* v_e_616_; uint8_t v___x_617_; 
v___x_611_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_606_, v_d_607_, v_e_608_);
v_sz_612_ = lean_array_size(v___x_611_);
v___x_613_ = ((size_t)0ULL);
lean_inc(v_numExtra_609_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_609_, v_sz_612_, v___x_613_, v___x_611_);
v_result_615_ = l_Array_append___redArg(v_result_610_, v___x_614_);
lean_dec_ref(v___x_614_);
v_e_616_ = l_Lean_Expr_consumeMData(v_e_608_);
lean_dec_ref(v_e_608_);
v___x_617_ = l_Lean_Expr_isApp(v_e_616_);
if (v___x_617_ == 0)
{
lean_dec_ref(v_e_616_);
lean_dec(v_numExtra_609_);
return v_result_615_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_Expr_appFn_x21(v_e_616_);
lean_dec_ref(v_e_616_);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_add(v_numExtra_609_, v___x_619_);
lean_dec(v_numExtra_609_);
v_e_608_ = v___x_618_;
v_numExtra_609_ = v___x_620_;
v_result_610_ = v_result_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_622_, lean_object* v_d_623_, lean_object* v_e_624_, lean_object* v_numExtra_625_, lean_object* v_result_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_622_, v_d_623_, v_e_624_, v_numExtra_625_, v_result_626_);
lean_dec_ref(v_d_623_);
lean_dec_ref(v_mctx_622_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_628_, lean_object* v_mctx_629_, lean_object* v_d_630_, lean_object* v_e_631_, lean_object* v_numExtra_632_, lean_object* v_result_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_629_, v_d_630_, v_e_631_, v_numExtra_632_, v_result_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_635_, lean_object* v_mctx_636_, lean_object* v_d_637_, lean_object* v_e_638_, lean_object* v_numExtra_639_, lean_object* v_result_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_635_, v_mctx_636_, v_d_637_, v_e_638_, v_numExtra_639_, v_result_640_);
lean_dec_ref(v_d_637_);
lean_dec_ref(v_mctx_636_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_642_, lean_object* v_numExtra_643_, size_t v_sz_644_, size_t v_i_645_, lean_object* v_bs_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_643_, v_sz_644_, v_i_645_, v_bs_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_648_, lean_object* v_numExtra_649_, lean_object* v_sz_650_, lean_object* v_i_651_, lean_object* v_bs_652_){
_start:
{
size_t v_sz_boxed_653_; size_t v_i_boxed_654_; lean_object* v_res_655_; 
v_sz_boxed_653_ = lean_unbox_usize(v_sz_650_);
lean_dec(v_sz_650_);
v_i_boxed_654_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_648_, v_numExtra_649_, v_sz_boxed_653_, v_i_boxed_654_, v_bs_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_656_, size_t v_i_657_, lean_object* v_bs_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_lt(v_i_657_, v_sz_656_);
if (v___x_659_ == 0)
{
return v_bs_658_;
}
else
{
lean_object* v_v_660_; lean_object* v___x_661_; lean_object* v_bs_x27_662_; lean_object* v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
v_v_660_ = lean_array_uget(v_bs_658_, v_i_657_);
v___x_661_ = lean_unsigned_to_nat(0u);
v_bs_x27_662_ = lean_array_uset(v_bs_658_, v_i_657_, v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_v_660_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_add(v_i_657_, v___x_664_);
v___x_666_ = lean_array_uset(v_bs_x27_662_, v_i_657_, v___x_663_);
v_i_657_ = v___x_665_;
v_bs_658_ = v___x_666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_668_, lean_object* v_i_669_, lean_object* v_bs_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v_i_boxed_672_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_671_, v_i_boxed_672_, v_bs_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_674_, lean_object* v_d_675_, lean_object* v_e_676_){
_start:
{
lean_object* v___x_677_; lean_object* v_e_678_; lean_object* v_e_679_; lean_object* v_result_680_; size_t v_sz_681_; size_t v___x_682_; lean_object* v_result_683_; uint8_t v___x_684_; 
v___x_677_ = l_Lean_Meta_Sym_etaReduce(v_e_676_);
v_e_678_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_674_, v___x_677_);
v_e_679_ = l_Lean_Expr_consumeMData(v_e_678_);
lean_dec_ref(v_e_678_);
v_result_680_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_674_, v_d_675_, v_e_679_);
v_sz_681_ = lean_array_size(v_result_680_);
v___x_682_ = ((size_t)0ULL);
v_result_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_681_, v___x_682_, v_result_680_);
v___x_684_ = l_Lean_Expr_isApp(v_e_679_);
if (v___x_684_ == 0)
{
lean_dec_ref(v_e_679_);
return v_result_683_;
}
else
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_679_);
v___x_686_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_675_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec_ref(v_e_679_);
return v_result_683_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = l_Lean_Expr_appFn_x21(v_e_679_);
lean_dec_ref(v_e_679_);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_674_, v_d_675_, v___x_687_, v___x_688_, v_result_683_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_690_, lean_object* v_d_691_, lean_object* v_e_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_690_, v_d_691_, v_e_692_);
lean_dec_ref(v_e_692_);
lean_dec_ref(v_d_691_);
lean_dec_ref(v_mctx_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_694_, lean_object* v_mctx_695_, lean_object* v_d_696_, lean_object* v_e_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_695_, v_d_696_, v_e_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_699_, lean_object* v_mctx_700_, lean_object* v_d_701_, lean_object* v_e_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_699_, v_mctx_700_, v_d_701_, v_e_702_);
lean_dec_ref(v_e_702_);
lean_dec_ref(v_d_701_);
lean_dec_ref(v_mctx_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_704_, size_t v_sz_705_, size_t v_i_706_, lean_object* v_bs_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_705_, v_i_706_, v_bs_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_709_, lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_bs_712_){
_start:
{
size_t v_sz_boxed_713_; size_t v_i_boxed_714_; lean_object* v_res_715_; 
v_sz_boxed_713_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_709_, v_sz_boxed_713_, v_i_boxed_714_, v_bs_712_);
return v_res_715_;
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
