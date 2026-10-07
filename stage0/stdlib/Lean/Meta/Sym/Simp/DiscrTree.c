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
lean_object* v_declName_73_; lean_object* v___y_75_; lean_object* v___y_76_; uint8_t v___y_80_; 
v_declName_73_ = lean_ctor_get(v_fn_61_, 0);
lean_inc(v_declName_73_);
lean_dec_ref_known(v_fn_61_, 2);
if (v_root_53_ == 0)
{
goto v___jp_88_;
}
else
{
if (v___x_60_ == 0)
{
v___y_80_ = v___x_60_;
goto v___jp_79_;
}
else
{
goto v___jp_88_;
}
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
if (v___y_80_ == 0)
{
lean_object* v_numArgs_81_; lean_object* v___x_82_; 
v_numArgs_81_ = l_Lean_Expr_getAppNumArgs(v_e_56_);
v___x_82_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_declName_73_, v_fnInfos_54_);
if (lean_obj_tag(v___x_82_) == 1)
{
lean_object* v_val_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_val_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v___x_82_, 1);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_sub(v_numArgs_81_, v___x_84_);
v___x_86_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(v_val_83_, v___x_85_, v_e_56_, v_todo_55_);
lean_dec(v_val_83_);
v___y_75_ = v_numArgs_81_;
v___y_76_ = v___x_86_;
goto v___jp_74_;
}
else
{
lean_object* v___x_87_; 
lean_dec(v___x_82_);
v___x_87_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_56_, v_todo_55_);
v___y_75_ = v_numArgs_81_;
v___y_76_ = v___x_87_;
goto v___jp_74_;
}
}
else
{
lean_dec(v_declName_73_);
lean_dec_ref(v_e_56_);
goto v___jp_57_;
}
}
v___jp_88_:
{
uint8_t v___x_89_; 
lean_inc_ref(v_e_56_);
v___x_89_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_73_, v_e_56_);
if (v___x_89_ == 0)
{
uint8_t v___x_90_; 
lean_inc_ref(v_e_56_);
v___x_90_ = l_Lean_Meta_Sym_isQuasiOffset(v_e_56_);
v___y_80_ = v___x_90_;
goto v___jp_79_;
}
else
{
lean_dec(v_declName_73_);
lean_dec_ref(v_e_56_);
goto v___jp_57_;
}
}
}
case 1:
{
lean_object* v_fvarId_91_; lean_object* v_numArgs_92_; lean_object* v_todo_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_fvarId_91_ = lean_ctor_get(v_fn_61_, 0);
lean_inc(v_fvarId_91_);
lean_dec_ref_known(v_fn_61_, 1);
v_numArgs_92_ = l_Lean_Expr_getAppNumArgs(v_e_56_);
v_todo_93_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_56_, v_todo_55_);
v___x_94_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_94_, 0, v_fvarId_91_);
lean_ctor_set(v___x_94_, 1, v_numArgs_92_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_todo_93_);
return v___x_95_;
}
default: 
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec_ref(v_fn_61_);
lean_dec_ref(v_e_56_);
v___x_96_ = lean_box(1);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_todo_55_);
return v___x_97_;
}
}
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec_ref(v_e_56_);
v___x_98_ = lean_box(0);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_todo_55_);
return v___x_99_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs___boxed(lean_object* v_root_100_, lean_object* v_fnInfos_101_, lean_object* v_todo_102_, lean_object* v_e_103_){
_start:
{
uint8_t v_root_boxed_104_; lean_object* v_res_105_; 
v_root_boxed_104_ = lean_unbox(v_root_100_);
v_res_105_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_boxed_104_, v_fnInfos_101_, v_todo_102_, v_e_103_);
lean_dec(v_fnInfos_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(lean_object* v_00_u03b2_106_, lean_object* v_a_107_, lean_object* v_x_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_107_, v_x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___boxed(lean_object* v_00_u03b2_110_, lean_object* v_a_111_, lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(v_00_u03b2_110_, v_a_111_, v_x_112_);
lean_dec(v_x_112_);
lean_dec(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(uint8_t v_root_114_, lean_object* v_fnInfos_115_, lean_object* v_todo_116_, lean_object* v_keys_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = lean_array_get_size(v_todo_116_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_dec_eq(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_e_124_; lean_object* v_todo_125_; lean_object* v___x_126_; lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___x_129_; 
v___x_121_ = l_Lean_instInhabitedExpr;
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_sub(v___x_118_, v___x_122_);
v_e_124_ = lean_array_get(v___x_121_, v_todo_116_, v___x_123_);
lean_dec(v___x_123_);
v_todo_125_ = lean_array_pop(v_todo_116_);
v___x_126_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_114_, v_fnInfos_115_, v_todo_125_, v_e_124_);
v_fst_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_fst_127_);
v_snd_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_snd_128_);
lean_dec_ref(v___x_126_);
v___x_129_ = lean_array_push(v_keys_117_, v_fst_127_);
v_root_114_ = v___x_120_;
v_todo_116_ = v_snd_128_;
v_keys_117_ = v___x_129_;
goto _start;
}
else
{
lean_dec_ref(v_todo_116_);
return v_keys_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux___boxed(lean_object* v_root_131_, lean_object* v_fnInfos_132_, lean_object* v_todo_133_, lean_object* v_keys_134_){
_start:
{
uint8_t v_root_boxed_135_; lean_object* v_res_136_; 
v_root_boxed_135_ = lean_unbox(v_root_131_);
v_res_136_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v_root_boxed_135_, v_fnInfos_132_, v_todo_133_, v_keys_134_);
lean_dec(v_fnInfos_132_);
return v_res_136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(8u);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object* v_p_138_){
_start:
{
lean_object* v_pattern_139_; lean_object* v_fnInfos_140_; lean_object* v___x_141_; lean_object* v_todo_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_pattern_139_ = lean_ctor_get(v_p_138_, 3);
lean_inc_ref(v_pattern_139_);
v_fnInfos_140_ = lean_ctor_get(v_p_138_, 4);
lean_inc(v_fnInfos_140_);
lean_dec_ref(v_p_138_);
v___x_141_ = lean_unsigned_to_nat(8u);
v_todo_142_ = lean_mk_empty_array_with_capacity(v___x_141_);
v___x_143_ = 1;
lean_inc_ref(v_todo_142_);
v___x_144_ = lean_array_push(v_todo_142_, v_pattern_139_);
v___x_145_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v___x_143_, v_fnInfos_140_, v___x_144_, v_todo_142_);
lean_dec(v_fnInfos_140_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___redArg(lean_object* v_inst_146_, lean_object* v_d_147_, lean_object* v_p_148_, lean_object* v_v_149_){
_start:
{
lean_object* v_keys_150_; lean_object* v___x_151_; 
v_keys_150_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_148_);
v___x_151_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_146_, v_d_147_, v_keys_150_, v_v_149_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern(lean_object* v_00_u03b1_152_, lean_object* v_inst_153_, lean_object* v_d_154_, lean_object* v_p_155_, lean_object* v_v_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_Sym_insertPattern___redArg(v_inst_153_, v_d_154_, v_p_155_, v_v_156_);
return v___x_157_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(lean_object* v_a_158_, lean_object* v_b_159_){
_start:
{
lean_object* v_fst_160_; lean_object* v_fst_161_; uint8_t v___x_162_; 
v_fst_160_ = lean_ctor_get(v_a_158_, 0);
v_fst_161_ = lean_ctor_get(v_b_159_, 0);
v___x_162_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_160_, v_fst_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed(lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_163_, v_b_164_);
lean_dec_ref(v_b_164_);
lean_dec_ref(v_a_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(lean_object* v_cs_173_, lean_object* v_k_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_array_get_size(v_cs_173_);
v___x_177_ = lean_nat_dec_lt(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec(v_k_174_);
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_sub(v___x_176_, v___x_179_);
v___x_181_ = lean_nat_dec_le(v___x_175_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v___x_180_);
lean_dec(v_k_174_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___f_183_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_184_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_k_174_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_187_ = l_Array_binSearchAux___redArg(v___f_183_, v___x_186_, v_cs_173_, v___x_185_, v___x_175_, v___x_180_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___boxed(lean_object* v_cs_188_, lean_object* v_k_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(v_cs_188_, v_k_189_);
lean_dec_ref(v_cs_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(lean_object* v_00_u03b1_191_, lean_object* v_cs_192_, lean_object* v_k_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_array_get_size(v_cs_192_);
v___x_196_ = lean_nat_dec_lt(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_dec(v_k_193_);
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_sub(v___x_195_, v___x_198_);
v___x_200_ = lean_nat_dec_le(v___x_194_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec(v___x_199_);
lean_dec(v_k_193_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___f_202_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_k_193_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_206_ = l_Array_binSearchAux___redArg(v___f_202_, v___x_205_, v_cs_192_, v___x_204_, v___x_194_, v___x_199_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___boxed(lean_object* v_00_u03b1_207_, lean_object* v_cs_208_, lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(v_00_u03b1_207_, v_cs_208_, v_k_209_);
lean_dec_ref(v_cs_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(lean_object* v_e_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Expr_getAppFn_x27(v_e_211_);
switch(lean_obj_tag(v___x_212_))
{
case 9:
{
lean_object* v_a_213_; lean_object* v___x_214_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc_ref(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_214_, 0, v_a_213_);
return v___x_214_;
}
case 4:
{
lean_object* v_declName_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_declName_215_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_declName_215_);
lean_dec_ref_known(v___x_212_, 2);
v___x_216_ = l_Lean_Expr_getAppNumArgs_x27(v_e_211_);
v___x_217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_217_, 0, v_declName_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
case 1:
{
lean_object* v_fvarId_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_fvarId_218_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_fvarId_218_);
lean_dec_ref_known(v___x_212_, 1);
v___x_219_ = l_Lean_Expr_getAppNumArgs_x27(v_e_211_);
v___x_220_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_220_, 0, v_fvarId_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
case 7:
{
lean_object* v___x_221_; 
lean_dec_ref_known(v___x_212_, 3);
v___x_221_ = lean_box(5);
return v___x_221_;
}
default: 
{
lean_object* v___x_222_; 
lean_dec_ref(v___x_212_);
v___x_222_ = lean_box(1);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(lean_object* v_e_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_223_);
lean_dec_ref(v_e_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(lean_object* v_mctx_225_, lean_object* v_e_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = l_Lean_Expr_hasExprMVar(v_e_226_);
if (v___x_227_ == 0)
{
return v_e_226_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Expr_getAppFn(v_e_226_);
if (lean_obj_tag(v___x_228_) == 2)
{
lean_object* v_mvarId_229_; lean_object* v___x_230_; 
v_mvarId_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_mvarId_229_);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_225_, v_mvarId_229_);
lean_dec(v_mvarId_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
return v_e_226_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; 
v_val_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = l_Lean_Expr_getAppNumArgs(v_e_226_);
v___x_233_ = lean_mk_empty_array_with_capacity(v___x_232_);
lean_dec(v___x_232_);
v___x_234_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_226_, v___x_233_);
v___x_235_ = 0;
v___x_236_ = l_Lean_Expr_betaRev(v_val_231_, v___x_234_, v___x_235_, v___x_235_);
lean_dec_ref(v___x_234_);
v_e_226_ = v___x_236_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_228_);
return v_e_226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars___boxed(lean_object* v_mctx_238_, lean_object* v_e_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_238_, v_e_239_);
lean_dec_ref(v_mctx_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object* v_todo_241_, lean_object* v_e_242_){
_start:
{
switch(lean_obj_tag(v_e_242_))
{
case 5:
{
lean_object* v_fn_243_; lean_object* v_arg_244_; lean_object* v___x_245_; 
v_fn_243_ = lean_ctor_get(v_e_242_, 0);
lean_inc_ref(v_fn_243_);
v_arg_244_ = lean_ctor_get(v_e_242_, 1);
lean_inc_ref(v_arg_244_);
lean_dec_ref_known(v_e_242_, 2);
v___x_245_ = lean_array_push(v_todo_241_, v_arg_244_);
v_todo_241_ = v___x_245_;
v_e_242_ = v_fn_243_;
goto _start;
}
case 7:
{
lean_object* v_binderType_247_; lean_object* v_body_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_binderType_247_ = lean_ctor_get(v_e_242_, 1);
lean_inc_ref(v_binderType_247_);
v_body_248_ = lean_ctor_get(v_e_242_, 2);
lean_inc_ref(v_body_248_);
lean_dec_ref_known(v_e_242_, 3);
v___x_249_ = lean_array_push(v_todo_241_, v_body_248_);
v___x_250_ = lean_array_push(v___x_249_, v_binderType_247_);
return v___x_250_;
}
case 10:
{
lean_object* v_expr_251_; 
v_expr_251_ = lean_ctor_get(v_e_242_, 1);
lean_inc_ref(v_expr_251_);
lean_dec_ref_known(v_e_242_, 2);
v_e_242_ = v_expr_251_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_242_);
return v_todo_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_as_253_, lean_object* v_k_254_, lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_m_259_; lean_object* v_a_260_; uint8_t v___x_261_; 
v___x_257_ = lean_nat_add(v_x_255_, v_x_256_);
v___x_258_ = lean_unsigned_to_nat(1u);
v_m_259_ = lean_nat_shiftr(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
v_a_260_ = lean_array_fget_borrowed(v_as_253_, v_m_259_);
v___x_261_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_260_, v_k_254_);
if (v___x_261_ == 0)
{
uint8_t v___x_262_; 
lean_dec(v_x_256_);
v___x_262_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_254_, v_a_260_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec(v_m_259_);
lean_dec(v_x_255_);
lean_inc(v_a_260_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_a_260_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_nat_dec_eq(v_m_259_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_nat_sub(v_m_259_, v___x_258_);
lean_dec(v_m_259_);
v___x_267_ = lean_nat_dec_lt(v___x_266_, v_x_255_);
if (v___x_267_ == 0)
{
v_x_256_ = v___x_266_;
goto _start;
}
else
{
lean_object* v___x_269_; 
lean_dec(v___x_266_);
lean_dec(v_x_255_);
v___x_269_ = lean_box(0);
return v___x_269_;
}
}
else
{
lean_object* v___x_270_; 
lean_dec(v_m_259_);
lean_dec(v_x_255_);
v___x_270_ = lean_box(0);
return v___x_270_;
}
}
}
else
{
lean_object* v___x_271_; uint8_t v___x_272_; 
lean_dec(v_x_255_);
v___x_271_ = lean_nat_add(v_m_259_, v___x_258_);
lean_dec(v_m_259_);
v___x_272_ = lean_nat_dec_le(v___x_271_, v_x_256_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec(v___x_271_);
lean_dec(v_x_256_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
v_x_255_ = v___x_271_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_275_, lean_object* v_k_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_275_, v_k_276_, v_x_277_, v_x_278_);
lean_dec_ref(v_k_276_);
lean_dec_ref(v_as_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_mctx_280_, lean_object* v_todo_281_, lean_object* v_c_282_, lean_object* v_result_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_c_282_) == 0)
{
lean_object* v_key_285_; lean_object* v_child_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_key_285_ = lean_ctor_get(v_c_282_, 0);
lean_inc(v_key_285_);
v_child_286_ = lean_ctor_get(v_c_282_, 1);
lean_inc_ref(v_child_286_);
lean_dec_ref_known(v_c_282_, 2);
v___x_287_ = lean_array_get_size(v_todo_281_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_nat_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_todo_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_sub(v___x_287_, v___x_290_);
v___x_292_ = lean_array_get(v___x_284_, v_todo_281_, v___x_291_);
lean_dec(v___x_291_);
v_todo_293_ = lean_array_pop(v_todo_281_);
v___x_294_ = lean_box(0);
v___x_295_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_285_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v_e_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_296_ = l_Lean_Meta_Sym_etaReduce(v___x_292_);
lean_dec(v___x_292_);
v_e_297_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_280_, v___x_296_);
v___x_298_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_297_);
v___x_299_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_285_, v___x_298_);
lean_dec(v___x_298_);
lean_dec(v_key_285_);
if (v___x_299_ == 0)
{
lean_dec_ref(v_e_297_);
lean_dec_ref(v_todo_293_);
lean_dec_ref(v_child_286_);
return v_result_283_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_293_, v_e_297_);
v_todo_281_ = v___x_300_;
v_c_282_ = v_child_286_;
goto _start;
}
}
else
{
lean_dec(v___x_292_);
lean_dec(v_key_285_);
v_todo_281_ = v_todo_293_;
v_c_282_ = v_child_286_;
goto _start;
}
}
else
{
lean_dec_ref(v_child_286_);
lean_dec(v_key_285_);
lean_dec_ref(v_todo_281_);
return v_result_283_;
}
}
else
{
lean_object* v_vs_303_; lean_object* v_children_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_vs_303_ = lean_ctor_get(v_c_282_, 0);
lean_inc_ref(v_vs_303_);
v_children_304_ = lean_ctor_get(v_c_282_, 1);
lean_inc_ref(v_children_304_);
lean_dec_ref_known(v_c_282_, 2);
v___x_305_ = lean_array_get_size(v_todo_281_);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v_csize_308_; uint8_t v___x_309_; 
lean_dec_ref(v_vs_303_);
v_csize_308_ = lean_array_get_size(v_children_304_);
v___x_309_ = lean_nat_dec_eq(v_csize_308_, v___x_306_);
if (v___x_309_ == 0)
{
lean_object* v_first_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_340_; 
v_first_310_ = lean_array_fget(v_children_304_, v___x_306_);
v_fst_311_ = lean_ctor_get(v_first_310_, 0);
v_snd_312_ = lean_ctor_get(v_first_310_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_first_310_);
if (v_isSharedCheck_340_ == 0)
{
v___x_314_ = v_first_310_;
v_isShared_315_ = v_isSharedCheck_340_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_snd_312_);
lean_inc(v_fst_311_);
lean_dec(v_first_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_340_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_e_320_; lean_object* v_todo_321_; lean_object* v___y_323_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_sub(v___x_305_, v___x_316_);
v___x_318_ = lean_array_get_borrowed(v___x_284_, v_todo_281_, v___x_317_);
lean_dec(v___x_317_);
v___x_319_ = l_Lean_Meta_Sym_etaReduce(v___x_318_);
v_e_320_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_280_, v___x_319_);
v_todo_321_ = lean_array_pop(v_todo_281_);
v___x_337_ = lean_box(0);
v___x_338_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_311_, v___x_337_);
lean_dec(v_fst_311_);
if (v___x_338_ == 0)
{
lean_dec(v_snd_312_);
v___y_323_ = v_result_283_;
goto v___jp_322_;
}
else
{
lean_object* v___x_339_; 
lean_inc_ref(v_todo_321_);
v___x_339_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_280_, v_todo_321_, v_snd_312_, v_result_283_);
v___y_323_ = v___x_339_;
goto v___jp_322_;
}
v___jp_322_:
{
uint8_t v___x_324_; 
v___x_324_ = lean_nat_dec_lt(v___x_306_, v_csize_308_);
if (v___x_324_ == 0)
{
lean_dec_ref(v_todo_321_);
lean_dec_ref(v_e_320_);
lean_del_object(v___x_314_);
lean_dec_ref(v_children_304_);
return v___y_323_;
}
else
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_nat_sub(v_csize_308_, v___x_316_);
v___x_326_ = lean_nat_dec_le(v___x_306_, v___x_325_);
if (v___x_326_ == 0)
{
lean_dec(v___x_325_);
lean_dec_ref(v_todo_321_);
lean_dec_ref(v_e_320_);
lean_del_object(v___x_314_);
lean_dec_ref(v_children_304_);
return v___y_323_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_320_);
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_328_);
lean_ctor_set(v___x_314_, 0, v___x_327_);
v___x_330_ = v___x_314_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_336_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; 
v___x_331_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_304_, v___x_330_, v___x_306_, v___x_325_);
lean_dec_ref(v___x_330_);
lean_dec_ref(v_children_304_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_dec_ref(v_todo_321_);
lean_dec_ref(v_e_320_);
return v___y_323_;
}
else
{
lean_object* v_val_332_; lean_object* v_snd_333_; lean_object* v___x_334_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_331_, 1);
v_snd_333_ = lean_ctor_get(v_val_332_, 1);
lean_inc(v_snd_333_);
lean_dec(v_val_332_);
v___x_334_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_321_, v_e_320_);
v_todo_281_ = v___x_334_;
v_c_282_ = v_snd_333_;
v_result_283_ = v___y_323_;
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
lean_dec_ref(v_children_304_);
lean_dec_ref(v_todo_281_);
return v_result_283_;
}
}
else
{
lean_object* v___x_341_; 
lean_dec_ref(v_children_304_);
lean_dec_ref(v_todo_281_);
v___x_341_ = l_Array_append___redArg(v_result_283_, v_vs_303_);
lean_dec_ref(v_vs_303_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_342_, lean_object* v_todo_343_, lean_object* v_c_344_, lean_object* v_result_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_342_, v_todo_343_, v_c_344_, v_result_345_);
lean_dec_ref(v_mctx_342_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_347_, lean_object* v_mctx_348_, lean_object* v_todo_349_, lean_object* v_c_350_, lean_object* v_result_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_348_, v_todo_349_, v_c_350_, v_result_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_353_, lean_object* v_mctx_354_, lean_object* v_todo_355_, lean_object* v_c_356_, lean_object* v_result_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_353_, v_mctx_354_, v_todo_355_, v_c_356_, v_result_357_);
lean_dec_ref(v_mctx_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_359_, lean_object* v_as_360_, lean_object* v_k_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_360_, v_k_361_, v_x_362_, v_x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_366_, lean_object* v_as_367_, lean_object* v_k_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_366_, v_as_367_, v_k_368_, v_x_369_, v_x_370_, v_x_371_);
lean_dec_ref(v_k_368_);
lean_dec_ref(v_as_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_i_375_, lean_object* v_k_376_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = lean_array_get_size(v_keys_373_);
v___x_378_ = lean_nat_dec_lt(v_i_375_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_i_375_);
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v_k_x27_380_; uint8_t v___x_381_; 
v_k_x27_380_ = lean_array_fget_borrowed(v_keys_373_, v_i_375_);
v___x_381_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_376_, v_k_x27_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_add(v_i_375_, v___x_382_);
lean_dec(v_i_375_);
v_i_375_ = v___x_383_;
goto _start;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_array_fget_borrowed(v_vals_374_, v_i_375_);
lean_dec(v_i_375_);
lean_inc(v___x_385_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_387_, lean_object* v_vals_388_, lean_object* v_i_389_, lean_object* v_k_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_387_, v_vals_388_, v_i_389_, v_k_390_);
lean_dec(v_k_390_);
lean_dec_ref(v_vals_388_);
lean_dec_ref(v_keys_387_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_392_, size_t v_x_393_, lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_object* v_es_395_; lean_object* v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v_j_399_; lean_object* v___x_400_; 
v_es_395_ = lean_ctor_get(v_x_392_, 0);
v___x_396_ = lean_box(2);
v___x_397_ = ((size_t)31ULL);
v___x_398_ = lean_usize_land(v_x_393_, v___x_397_);
v_j_399_ = lean_usize_to_nat(v___x_398_);
v___x_400_ = lean_array_get_borrowed(v___x_396_, v_es_395_, v_j_399_);
lean_dec(v_j_399_);
switch(lean_obj_tag(v___x_400_))
{
case 0:
{
lean_object* v_key_401_; lean_object* v_val_402_; uint8_t v___x_403_; 
v_key_401_ = lean_ctor_get(v___x_400_, 0);
v_val_402_ = lean_ctor_get(v___x_400_, 1);
v___x_403_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_394_, v_key_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_box(0);
return v___x_404_;
}
else
{
lean_object* v___x_405_; 
lean_inc(v_val_402_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v_val_402_);
return v___x_405_;
}
}
case 1:
{
lean_object* v_node_406_; size_t v___x_407_; size_t v___x_408_; 
v_node_406_ = lean_ctor_get(v___x_400_, 0);
v___x_407_ = ((size_t)5ULL);
v___x_408_ = lean_usize_shift_right(v_x_393_, v___x_407_);
v_x_392_ = v_node_406_;
v_x_393_ = v___x_408_;
goto _start;
}
default: 
{
lean_object* v___x_410_; 
v___x_410_ = lean_box(0);
return v___x_410_;
}
}
}
else
{
lean_object* v_ks_411_; lean_object* v_vs_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_ks_411_ = lean_ctor_get(v_x_392_, 0);
v_vs_412_ = lean_ctor_get(v_x_392_, 1);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_411_, v_vs_412_, v___x_413_, v_x_394_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
size_t v_x_203__boxed_418_; lean_object* v_res_419_; 
v_x_203__boxed_418_ = lean_unbox_usize(v_x_416_);
lean_dec(v_x_416_);
v_res_419_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_415_, v_x_203__boxed_418_, v_x_417_);
lean_dec(v_x_417_);
lean_dec_ref(v_x_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint64_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; 
v___x_422_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_421_);
v___x_423_ = lean_uint64_to_usize(v___x_422_);
v___x_424_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_420_, v___x_423_, v_x_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_425_, v_x_426_);
lean_dec(v_x_426_);
lean_dec_ref(v_x_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_430_, lean_object* v_d_431_, lean_object* v_e_432_){
_start:
{
lean_object* v___y_434_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_box(0);
v___x_444_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_431_, v___x_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(8u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___y_434_ = v___x_446_;
goto v___jp_433_;
}
else
{
lean_object* v_val_447_; 
v_val_447_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v___x_444_, 1);
if (lean_obj_tag(v_val_447_) == 0)
{
lean_object* v___x_448_; 
lean_dec_ref_known(v_val_447_, 2);
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1));
v___y_434_ = v___x_448_;
goto v___jp_433_;
}
else
{
lean_object* v_vs_449_; 
v_vs_449_ = lean_ctor_get(v_val_447_, 0);
lean_inc_ref(v_vs_449_);
lean_dec_ref_known(v_val_447_, 2);
v___y_434_ = v_vs_449_;
goto v___jp_433_;
}
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v_e_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_435_ = l_Lean_Meta_Sym_etaReduce(v_e_432_);
v_e_436_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_430_, v___x_435_);
v___x_437_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_436_);
v___x_438_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_431_, v___x_437_);
lean_dec(v___x_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_dec_ref(v_e_436_);
return v___y_434_;
}
else
{
lean_object* v_val_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_val_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_441_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_440_, v_e_436_);
v___x_442_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_430_, v___x_441_, v_val_439_, v___y_434_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_450_, lean_object* v_d_451_, lean_object* v_e_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_450_, v_d_451_, v_e_452_);
lean_dec_ref(v_e_452_);
lean_dec_ref(v_d_451_);
lean_dec_ref(v_mctx_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_454_, lean_object* v_mctx_455_, lean_object* v_d_456_, lean_object* v_e_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_455_, v_d_456_, v_e_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_459_, lean_object* v_mctx_460_, lean_object* v_d_461_, lean_object* v_e_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_459_, v_mctx_460_, v_d_461_, v_e_462_);
lean_dec_ref(v_e_462_);
lean_dec_ref(v_d_461_);
lean_dec_ref(v_mctx_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_468_, v_x_469_, v_x_470_);
lean_dec(v_x_470_);
lean_dec_ref(v_x_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, size_t v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_473_, v_x_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
size_t v_x_315__boxed_481_; lean_object* v_res_482_; 
v_x_315__boxed_481_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_res_482_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_477_, v_x_478_, v_x_315__boxed_481_, v_x_480_);
lean_dec(v_x_480_);
lean_dec_ref(v_x_478_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_heq_486_, lean_object* v_i_487_, lean_object* v_k_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_484_, v_vals_485_, v_i_487_, v_k_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_490_, lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_heq_493_, lean_object* v_i_494_, lean_object* v_k_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_490_, v_keys_491_, v_vals_492_, v_heq_493_, v_i_494_, v_k_495_);
lean_dec(v_k_495_);
lean_dec_ref(v_vals_492_);
lean_dec_ref(v_keys_491_);
return v_res_496_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_497_, lean_object* v_k_498_){
_start:
{
lean_object* v_k_500_; 
switch(lean_obj_tag(v_k_498_))
{
case 4:
{
lean_object* v_a_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_517_; 
v_a_504_ = lean_ctor_get(v_k_498_, 0);
v_a_505_ = lean_ctor_get(v_k_498_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_k_498_);
if (v_isSharedCheck_517_ == 0)
{
v___x_507_ = v_k_498_;
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_inc(v_a_504_);
lean_dec(v_k_498_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_zero_509_; uint8_t v_isZero_510_; 
v_zero_509_ = lean_unsigned_to_nat(0u);
v_isZero_510_ = lean_nat_dec_eq(v_a_505_, v_zero_509_);
if (v_isZero_510_ == 0)
{
lean_object* v_one_511_; lean_object* v_n_512_; lean_object* v___x_514_; 
v_one_511_ = lean_unsigned_to_nat(1u);
v_n_512_ = lean_nat_sub(v_a_505_, v_one_511_);
lean_dec(v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v_n_512_);
v___x_514_ = v___x_507_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_504_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_n_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
v_k_500_ = v___x_514_;
goto v___jp_499_;
}
}
else
{
uint8_t v___x_516_; 
lean_del_object(v___x_507_);
lean_dec(v_a_505_);
lean_dec(v_a_504_);
v___x_516_ = 0;
return v___x_516_;
}
}
}
case 3:
{
lean_object* v_a_518_; lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v_a_518_ = lean_ctor_get(v_k_498_, 0);
v_a_519_ = lean_ctor_get(v_k_498_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_k_498_);
if (v_isSharedCheck_531_ == 0)
{
v___x_521_ = v_k_498_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_inc(v_a_518_);
lean_dec(v_k_498_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_zero_523_; uint8_t v_isZero_524_; 
v_zero_523_ = lean_unsigned_to_nat(0u);
v_isZero_524_ = lean_nat_dec_eq(v_a_519_, v_zero_523_);
if (v_isZero_524_ == 0)
{
lean_object* v_one_525_; lean_object* v_n_526_; lean_object* v___x_528_; 
v_one_525_ = lean_unsigned_to_nat(1u);
v_n_526_ = lean_nat_sub(v_a_519_, v_one_525_);
lean_dec(v_a_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_n_526_);
v___x_528_ = v___x_521_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_518_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_n_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_k_500_ = v___x_528_;
goto v___jp_499_;
}
}
else
{
uint8_t v___x_530_; 
lean_del_object(v___x_521_);
lean_dec(v_a_519_);
lean_dec(v_a_518_);
v___x_530_ = 0;
return v___x_530_;
}
}
}
default: 
{
uint8_t v___x_532_; 
lean_dec(v_k_498_);
v___x_532_ = 0;
return v___x_532_;
}
}
v___jp_499_:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_497_, v_k_500_);
if (lean_obj_tag(v___x_501_) == 0)
{
v_k_498_ = v_k_500_;
goto _start;
}
else
{
uint8_t v___x_503_; 
lean_dec_ref_known(v___x_501_, 1);
lean_dec(v_k_500_);
v___x_503_ = 1;
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_533_, lean_object* v_k_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_533_, v_k_534_);
lean_dec_ref(v_d_533_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_537_, lean_object* v_d_538_, lean_object* v_k_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_538_, v_k_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_541_, lean_object* v_d_542_, lean_object* v_k_543_){
_start:
{
uint8_t v_res_544_; lean_object* v_r_545_; 
v_res_544_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_541_, v_d_542_, v_k_543_);
lean_dec_ref(v_d_542_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_546_, size_t v_sz_547_, size_t v_i_548_, lean_object* v_bs_549_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_548_, v_sz_547_);
if (v___x_550_ == 0)
{
lean_dec(v_numExtra_546_);
return v_bs_549_;
}
else
{
lean_object* v_v_551_; lean_object* v___x_552_; lean_object* v_bs_x27_553_; lean_object* v___x_554_; size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v_v_551_ = lean_array_uget(v_bs_549_, v_i_548_);
v___x_552_ = lean_unsigned_to_nat(0u);
v_bs_x27_553_ = lean_array_uset(v_bs_549_, v_i_548_, v___x_552_);
lean_inc(v_numExtra_546_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v_v_551_);
lean_ctor_set(v___x_554_, 1, v_numExtra_546_);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_548_, v___x_555_);
v___x_557_ = lean_array_uset(v_bs_x27_553_, v_i_548_, v___x_554_);
v_i_548_ = v___x_556_;
v_bs_549_ = v___x_557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_559_, lean_object* v_sz_560_, lean_object* v_i_561_, lean_object* v_bs_562_){
_start:
{
size_t v_sz_boxed_563_; size_t v_i_boxed_564_; lean_object* v_res_565_; 
v_sz_boxed_563_ = lean_unbox_usize(v_sz_560_);
lean_dec(v_sz_560_);
v_i_boxed_564_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_559_, v_sz_boxed_563_, v_i_boxed_564_, v_bs_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_566_, lean_object* v_d_567_, lean_object* v_e_568_, lean_object* v_numExtra_569_, lean_object* v_result_570_){
_start:
{
lean_object* v___x_571_; size_t v_sz_572_; size_t v___x_573_; lean_object* v___x_574_; lean_object* v_result_575_; lean_object* v_e_576_; uint8_t v___x_577_; 
v___x_571_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_566_, v_d_567_, v_e_568_);
v_sz_572_ = lean_array_size(v___x_571_);
v___x_573_ = ((size_t)0ULL);
lean_inc(v_numExtra_569_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_569_, v_sz_572_, v___x_573_, v___x_571_);
v_result_575_ = l_Array_append___redArg(v_result_570_, v___x_574_);
lean_dec_ref(v___x_574_);
v_e_576_ = l_Lean_Expr_consumeMData(v_e_568_);
lean_dec_ref(v_e_568_);
v___x_577_ = l_Lean_Expr_isApp(v_e_576_);
if (v___x_577_ == 0)
{
lean_dec_ref(v_e_576_);
lean_dec(v_numExtra_569_);
return v_result_575_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = l_Lean_Expr_appFn_x21(v_e_576_);
lean_dec_ref(v_e_576_);
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_numExtra_569_, v___x_579_);
lean_dec(v_numExtra_569_);
v_e_568_ = v___x_578_;
v_numExtra_569_ = v___x_580_;
v_result_570_ = v_result_575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_582_, lean_object* v_d_583_, lean_object* v_e_584_, lean_object* v_numExtra_585_, lean_object* v_result_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_582_, v_d_583_, v_e_584_, v_numExtra_585_, v_result_586_);
lean_dec_ref(v_d_583_);
lean_dec_ref(v_mctx_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_588_, lean_object* v_mctx_589_, lean_object* v_d_590_, lean_object* v_e_591_, lean_object* v_numExtra_592_, lean_object* v_result_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_589_, v_d_590_, v_e_591_, v_numExtra_592_, v_result_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_595_, lean_object* v_mctx_596_, lean_object* v_d_597_, lean_object* v_e_598_, lean_object* v_numExtra_599_, lean_object* v_result_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_595_, v_mctx_596_, v_d_597_, v_e_598_, v_numExtra_599_, v_result_600_);
lean_dec_ref(v_d_597_);
lean_dec_ref(v_mctx_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_602_, lean_object* v_numExtra_603_, size_t v_sz_604_, size_t v_i_605_, lean_object* v_bs_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_603_, v_sz_604_, v_i_605_, v_bs_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_608_, lean_object* v_numExtra_609_, lean_object* v_sz_610_, lean_object* v_i_611_, lean_object* v_bs_612_){
_start:
{
size_t v_sz_boxed_613_; size_t v_i_boxed_614_; lean_object* v_res_615_; 
v_sz_boxed_613_ = lean_unbox_usize(v_sz_610_);
lean_dec(v_sz_610_);
v_i_boxed_614_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_res_615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_608_, v_numExtra_609_, v_sz_boxed_613_, v_i_boxed_614_, v_bs_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_616_, size_t v_i_617_, lean_object* v_bs_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_lt(v_i_617_, v_sz_616_);
if (v___x_619_ == 0)
{
return v_bs_618_;
}
else
{
lean_object* v_v_620_; lean_object* v___x_621_; lean_object* v_bs_x27_622_; lean_object* v___x_623_; size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v_v_620_ = lean_array_uget(v_bs_618_, v_i_617_);
v___x_621_ = lean_unsigned_to_nat(0u);
v_bs_x27_622_ = lean_array_uset(v_bs_618_, v_i_617_, v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_v_620_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_i_617_, v___x_624_);
v___x_626_ = lean_array_uset(v_bs_x27_622_, v_i_617_, v___x_623_);
v_i_617_ = v___x_625_;
v_bs_618_ = v___x_626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_628_, lean_object* v_i_629_, lean_object* v_bs_630_){
_start:
{
size_t v_sz_boxed_631_; size_t v_i_boxed_632_; lean_object* v_res_633_; 
v_sz_boxed_631_ = lean_unbox_usize(v_sz_628_);
lean_dec(v_sz_628_);
v_i_boxed_632_ = lean_unbox_usize(v_i_629_);
lean_dec(v_i_629_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_631_, v_i_boxed_632_, v_bs_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_634_, lean_object* v_d_635_, lean_object* v_e_636_){
_start:
{
lean_object* v___x_637_; lean_object* v_e_638_; lean_object* v_e_639_; lean_object* v_result_640_; size_t v_sz_641_; size_t v___x_642_; lean_object* v_result_643_; uint8_t v___x_644_; 
v___x_637_ = l_Lean_Meta_Sym_etaReduce(v_e_636_);
v_e_638_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_634_, v___x_637_);
v_e_639_ = l_Lean_Expr_consumeMData(v_e_638_);
lean_dec_ref(v_e_638_);
v_result_640_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_634_, v_d_635_, v_e_639_);
v_sz_641_ = lean_array_size(v_result_640_);
v___x_642_ = ((size_t)0ULL);
v_result_643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_641_, v___x_642_, v_result_640_);
v___x_644_ = l_Lean_Expr_isApp(v_e_639_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_e_639_);
return v_result_643_;
}
else
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_639_);
v___x_646_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_635_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec_ref(v_e_639_);
return v_result_643_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = l_Lean_Expr_appFn_x21(v_e_639_);
lean_dec_ref(v_e_639_);
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_634_, v_d_635_, v___x_647_, v___x_648_, v_result_643_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_650_, lean_object* v_d_651_, lean_object* v_e_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_650_, v_d_651_, v_e_652_);
lean_dec_ref(v_e_652_);
lean_dec_ref(v_d_651_);
lean_dec_ref(v_mctx_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_654_, lean_object* v_mctx_655_, lean_object* v_d_656_, lean_object* v_e_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_655_, v_d_656_, v_e_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_659_, lean_object* v_mctx_660_, lean_object* v_d_661_, lean_object* v_e_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_659_, v_mctx_660_, v_d_661_, v_e_662_);
lean_dec_ref(v_e_662_);
lean_dec_ref(v_d_661_);
lean_dec_ref(v_mctx_660_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_664_, size_t v_sz_665_, size_t v_i_666_, lean_object* v_bs_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_665_, v_i_666_, v_bs_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_669_, lean_object* v_sz_670_, lean_object* v_i_671_, lean_object* v_bs_672_){
_start:
{
size_t v_sz_boxed_673_; size_t v_i_boxed_674_; lean_object* v_res_675_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_670_);
lean_dec(v_sz_670_);
v_i_boxed_674_ = lean_unbox_usize(v_i_671_);
lean_dec(v_i_671_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_669_, v_sz_boxed_673_, v_i_boxed_674_, v_bs_672_);
return v_res_675_;
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
