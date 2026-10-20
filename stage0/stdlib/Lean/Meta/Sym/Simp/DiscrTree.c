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
lean_object* v_declName_73_; lean_object* v___y_75_; lean_object* v___y_76_; 
v_declName_73_ = lean_ctor_get(v_fn_61_, 0);
lean_inc(v_declName_73_);
lean_dec_ref_known(v_fn_61_, 2);
if (v_root_53_ == 0)
{
uint8_t v___x_87_; 
lean_inc_ref(v_e_56_);
v___x_87_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_73_, v_e_56_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
lean_inc_ref(v_e_56_);
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
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v_m_257_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_nat_sub(v_m_257_, v___x_256_);
lean_dec(v_m_257_);
v___x_265_ = lean_nat_dec_lt(v___x_264_, v_x_253_);
if (v___x_265_ == 0)
{
v_x_254_ = v___x_264_;
goto _start;
}
else
{
lean_object* v___x_267_; 
lean_dec(v___x_264_);
lean_dec(v_x_253_);
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
else
{
lean_object* v___x_268_; 
lean_dec(v_m_257_);
lean_dec(v_x_253_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
}
else
{
lean_object* v___x_269_; uint8_t v___x_270_; 
lean_dec(v_x_253_);
v___x_269_ = lean_nat_add(v_m_257_, v___x_256_);
lean_dec(v_m_257_);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_x_254_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec(v___x_269_);
lean_dec(v_x_254_);
v___x_271_ = lean_box(0);
return v___x_271_;
}
else
{
v_x_253_ = v___x_269_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_273_, lean_object* v_k_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_273_, v_k_274_, v_x_275_, v_x_276_);
lean_dec_ref(v_k_274_);
lean_dec_ref(v_as_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_mctx_278_, lean_object* v_todo_279_, lean_object* v_c_280_, lean_object* v_result_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_c_280_) == 0)
{
lean_object* v_key_283_; lean_object* v_child_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_key_283_ = lean_ctor_get(v_c_280_, 0);
lean_inc(v_key_283_);
v_child_284_ = lean_ctor_get(v_c_280_, 1);
lean_inc_ref(v_child_284_);
lean_dec_ref_known(v_c_280_, 2);
v___x_285_ = lean_array_get_size(v_todo_279_);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_todo_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_sub(v___x_285_, v___x_288_);
v___x_290_ = lean_array_get(v___x_282_, v_todo_279_, v___x_289_);
lean_dec(v___x_289_);
v_todo_291_ = lean_array_pop(v_todo_279_);
v___x_292_ = lean_box(0);
v___x_293_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_283_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v_e_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_294_ = l_Lean_Meta_Sym_etaReduce(v___x_290_);
lean_dec(v___x_290_);
v_e_295_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_278_, v___x_294_);
v___x_296_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_295_);
v___x_297_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_283_, v___x_296_);
lean_dec(v___x_296_);
lean_dec(v_key_283_);
if (v___x_297_ == 0)
{
lean_dec_ref(v_e_295_);
lean_dec_ref(v_todo_291_);
lean_dec_ref(v_child_284_);
return v_result_281_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_291_, v_e_295_);
v_todo_279_ = v___x_298_;
v_c_280_ = v_child_284_;
goto _start;
}
}
else
{
lean_dec(v___x_290_);
lean_dec(v_key_283_);
v_todo_279_ = v_todo_291_;
v_c_280_ = v_child_284_;
goto _start;
}
}
else
{
lean_dec_ref(v_child_284_);
lean_dec(v_key_283_);
lean_dec_ref(v_todo_279_);
return v_result_281_;
}
}
else
{
lean_object* v_vs_301_; lean_object* v_children_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_vs_301_ = lean_ctor_get(v_c_280_, 0);
lean_inc_ref(v_vs_301_);
v_children_302_ = lean_ctor_get(v_c_280_, 1);
lean_inc_ref(v_children_302_);
lean_dec_ref_known(v_c_280_, 2);
v___x_303_ = lean_array_get_size(v_todo_279_);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_dec_eq(v___x_303_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v_csize_306_; uint8_t v___x_307_; 
lean_dec_ref(v_vs_301_);
v_csize_306_ = lean_array_get_size(v_children_302_);
v___x_307_ = lean_nat_dec_eq(v_csize_306_, v___x_304_);
if (v___x_307_ == 0)
{
lean_object* v_first_308_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_338_; 
v_first_308_ = lean_array_fget(v_children_302_, v___x_304_);
v_fst_309_ = lean_ctor_get(v_first_308_, 0);
v_snd_310_ = lean_ctor_get(v_first_308_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_first_308_);
if (v_isSharedCheck_338_ == 0)
{
v___x_312_ = v_first_308_;
v_isShared_313_ = v_isSharedCheck_338_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snd_310_);
lean_inc(v_fst_309_);
lean_dec(v_first_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_338_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_e_318_; lean_object* v_todo_319_; lean_object* v___y_321_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_sub(v___x_303_, v___x_314_);
v___x_316_ = lean_array_get_borrowed(v___x_282_, v_todo_279_, v___x_315_);
lean_dec(v___x_315_);
v___x_317_ = l_Lean_Meta_Sym_etaReduce(v___x_316_);
v_e_318_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_278_, v___x_317_);
v_todo_319_ = lean_array_pop(v_todo_279_);
v___x_335_ = lean_box(0);
v___x_336_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_309_, v___x_335_);
lean_dec(v_fst_309_);
if (v___x_336_ == 0)
{
lean_dec(v_snd_310_);
v___y_321_ = v_result_281_;
goto v___jp_320_;
}
else
{
lean_object* v___x_337_; 
lean_inc_ref(v_todo_319_);
v___x_337_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_278_, v_todo_319_, v_snd_310_, v_result_281_);
v___y_321_ = v___x_337_;
goto v___jp_320_;
}
v___jp_320_:
{
uint8_t v___x_322_; 
v___x_322_ = lean_nat_dec_lt(v___x_304_, v_csize_306_);
if (v___x_322_ == 0)
{
lean_dec_ref(v_todo_319_);
lean_dec_ref(v_e_318_);
lean_del_object(v___x_312_);
lean_dec_ref(v_children_302_);
return v___y_321_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_nat_sub(v_csize_306_, v___x_314_);
v___x_324_ = lean_nat_dec_le(v___x_304_, v___x_323_);
if (v___x_324_ == 0)
{
lean_dec(v___x_323_);
lean_dec_ref(v_todo_319_);
lean_dec_ref(v_e_318_);
lean_del_object(v___x_312_);
lean_dec_ref(v_children_302_);
return v___y_321_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_318_);
v___x_326_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_326_);
lean_ctor_set(v___x_312_, 0, v___x_325_);
v___x_328_ = v___x_312_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_334_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_302_, v___x_328_, v___x_304_, v___x_323_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v_children_302_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_dec_ref(v_todo_319_);
lean_dec_ref(v_e_318_);
return v___y_321_;
}
else
{
lean_object* v_val_330_; lean_object* v_snd_331_; lean_object* v___x_332_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref_known(v___x_329_, 1);
v_snd_331_ = lean_ctor_get(v_val_330_, 1);
lean_inc(v_snd_331_);
lean_dec(v_val_330_);
v___x_332_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_319_, v_e_318_);
v_todo_279_ = v___x_332_;
v_c_280_ = v_snd_331_;
v_result_281_ = v___y_321_;
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
lean_dec_ref(v_children_302_);
lean_dec_ref(v_todo_279_);
return v_result_281_;
}
}
else
{
lean_object* v___x_339_; 
lean_dec_ref(v_children_302_);
lean_dec_ref(v_todo_279_);
v___x_339_ = l_Array_append___redArg(v_result_281_, v_vs_301_);
lean_dec_ref(v_vs_301_);
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_340_, lean_object* v_todo_341_, lean_object* v_c_342_, lean_object* v_result_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_340_, v_todo_341_, v_c_342_, v_result_343_);
lean_dec_ref(v_mctx_340_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_345_, lean_object* v_mctx_346_, lean_object* v_todo_347_, lean_object* v_c_348_, lean_object* v_result_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_346_, v_todo_347_, v_c_348_, v_result_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_351_, lean_object* v_mctx_352_, lean_object* v_todo_353_, lean_object* v_c_354_, lean_object* v_result_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_351_, v_mctx_352_, v_todo_353_, v_c_354_, v_result_355_);
lean_dec_ref(v_mctx_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_357_, lean_object* v_as_358_, lean_object* v_k_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_358_, v_k_359_, v_x_360_, v_x_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_364_, lean_object* v_as_365_, lean_object* v_k_366_, lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_364_, v_as_365_, v_k_366_, v_x_367_, v_x_368_, v_x_369_);
lean_dec_ref(v_k_366_);
lean_dec_ref(v_as_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_371_, lean_object* v_vals_372_, lean_object* v_i_373_, lean_object* v_k_374_){
_start:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_array_get_size(v_keys_371_);
v___x_376_ = lean_nat_dec_lt(v_i_373_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_i_373_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v_k_x27_378_; uint8_t v___x_379_; 
v_k_x27_378_ = lean_array_fget_borrowed(v_keys_371_, v_i_373_);
v___x_379_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_374_, v_k_x27_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_add(v_i_373_, v___x_380_);
lean_dec(v_i_373_);
v_i_373_ = v___x_381_;
goto _start;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_array_fget_borrowed(v_vals_372_, v_i_373_);
lean_dec(v_i_373_);
lean_inc(v___x_383_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_i_387_, lean_object* v_k_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_385_, v_vals_386_, v_i_387_, v_k_388_);
lean_dec(v_k_388_);
lean_dec_ref(v_vals_386_);
lean_dec_ref(v_keys_385_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_390_, size_t v_x_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v_es_393_; lean_object* v___x_394_; size_t v___x_395_; size_t v___x_396_; lean_object* v_j_397_; lean_object* v___x_398_; 
v_es_393_ = lean_ctor_get(v_x_390_, 0);
v___x_394_ = lean_box(2);
v___x_395_ = ((size_t)31ULL);
v___x_396_ = lean_usize_land(v_x_391_, v___x_395_);
v_j_397_ = lean_usize_to_nat(v___x_396_);
v___x_398_ = lean_array_get_borrowed(v___x_394_, v_es_393_, v_j_397_);
lean_dec(v_j_397_);
switch(lean_obj_tag(v___x_398_))
{
case 0:
{
lean_object* v_key_399_; lean_object* v_val_400_; uint8_t v___x_401_; 
v_key_399_ = lean_ctor_get(v___x_398_, 0);
v_val_400_ = lean_ctor_get(v___x_398_, 1);
v___x_401_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_392_, v_key_399_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_box(0);
return v___x_402_;
}
else
{
lean_object* v___x_403_; 
lean_inc(v_val_400_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_val_400_);
return v___x_403_;
}
}
case 1:
{
lean_object* v_node_404_; size_t v___x_405_; size_t v___x_406_; 
v_node_404_ = lean_ctor_get(v___x_398_, 0);
v___x_405_ = ((size_t)5ULL);
v___x_406_ = lean_usize_shift_right(v_x_391_, v___x_405_);
v_x_390_ = v_node_404_;
v_x_391_ = v___x_406_;
goto _start;
}
default: 
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
}
else
{
lean_object* v_ks_409_; lean_object* v_vs_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_ks_409_ = lean_ctor_get(v_x_390_, 0);
v_vs_410_ = lean_ctor_get(v_x_390_, 1);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_409_, v_vs_410_, v___x_411_, v_x_392_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
size_t v_x_203__boxed_416_; lean_object* v_res_417_; 
v_x_203__boxed_416_ = lean_unbox_usize(v_x_414_);
lean_dec(v_x_414_);
v_res_417_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_413_, v_x_203__boxed_416_, v_x_415_);
lean_dec(v_x_415_);
lean_dec_ref(v_x_413_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
uint64_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; 
v___x_420_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_419_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_418_, v___x_421_, v_x_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_423_, v_x_424_);
lean_dec(v_x_424_);
lean_dec_ref(v_x_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_428_, lean_object* v_d_429_, lean_object* v_e_430_){
_start:
{
lean_object* v___y_432_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_429_, v___x_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(8u);
v___x_444_ = lean_mk_empty_array_with_capacity(v___x_443_);
v___y_432_ = v___x_444_;
goto v___jp_431_;
}
else
{
lean_object* v_val_445_; 
v_val_445_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v___x_442_, 1);
if (lean_obj_tag(v_val_445_) == 0)
{
lean_object* v___x_446_; 
lean_dec_ref_known(v_val_445_, 2);
v___x_446_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1));
v___y_432_ = v___x_446_;
goto v___jp_431_;
}
else
{
lean_object* v_vs_447_; 
v_vs_447_ = lean_ctor_get(v_val_445_, 0);
lean_inc_ref(v_vs_447_);
lean_dec_ref_known(v_val_445_, 2);
v___y_432_ = v_vs_447_;
goto v___jp_431_;
}
}
v___jp_431_:
{
lean_object* v___x_433_; lean_object* v_e_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = l_Lean_Meta_Sym_etaReduce(v_e_430_);
v_e_434_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_428_, v___x_433_);
v___x_435_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_434_);
v___x_436_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_429_, v___x_435_);
lean_dec(v___x_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_dec_ref(v_e_434_);
return v___y_432_;
}
else
{
lean_object* v_val_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_439_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_438_, v_e_434_);
v___x_440_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_428_, v___x_439_, v_val_437_, v___y_432_);
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_448_, lean_object* v_d_449_, lean_object* v_e_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_448_, v_d_449_, v_e_450_);
lean_dec_ref(v_e_450_);
lean_dec_ref(v_d_449_);
lean_dec_ref(v_mctx_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_452_, lean_object* v_mctx_453_, lean_object* v_d_454_, lean_object* v_e_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_453_, v_d_454_, v_e_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_457_, lean_object* v_mctx_458_, lean_object* v_d_459_, lean_object* v_e_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_457_, v_mctx_458_, v_d_459_, v_e_460_);
lean_dec_ref(v_e_460_);
lean_dec_ref(v_d_459_);
lean_dec_ref(v_mctx_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_466_, v_x_467_, v_x_468_);
lean_dec(v_x_468_);
lean_dec_ref(v_x_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, size_t v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_471_, v_x_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
size_t v_x_315__boxed_479_; lean_object* v_res_480_; 
v_x_315__boxed_479_ = lean_unbox_usize(v_x_477_);
lean_dec(v_x_477_);
v_res_480_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_475_, v_x_476_, v_x_315__boxed_479_, v_x_478_);
lean_dec(v_x_478_);
lean_dec_ref(v_x_476_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_481_, lean_object* v_keys_482_, lean_object* v_vals_483_, lean_object* v_heq_484_, lean_object* v_i_485_, lean_object* v_k_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_482_, v_vals_483_, v_i_485_, v_k_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_488_, lean_object* v_keys_489_, lean_object* v_vals_490_, lean_object* v_heq_491_, lean_object* v_i_492_, lean_object* v_k_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_488_, v_keys_489_, v_vals_490_, v_heq_491_, v_i_492_, v_k_493_);
lean_dec(v_k_493_);
lean_dec_ref(v_vals_490_);
lean_dec_ref(v_keys_489_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_495_, lean_object* v_k_496_){
_start:
{
lean_object* v_k_498_; 
switch(lean_obj_tag(v_k_496_))
{
case 4:
{
lean_object* v_a_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_515_; 
v_a_502_ = lean_ctor_get(v_k_496_, 0);
v_a_503_ = lean_ctor_get(v_k_496_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_k_496_);
if (v_isSharedCheck_515_ == 0)
{
v___x_505_ = v_k_496_;
v_isShared_506_ = v_isSharedCheck_515_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_inc(v_a_502_);
lean_dec(v_k_496_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_515_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_zero_507_; uint8_t v_isZero_508_; 
v_zero_507_ = lean_unsigned_to_nat(0u);
v_isZero_508_ = lean_nat_dec_eq(v_a_503_, v_zero_507_);
if (v_isZero_508_ == 0)
{
lean_object* v_one_509_; lean_object* v_n_510_; lean_object* v___x_512_; 
v_one_509_ = lean_unsigned_to_nat(1u);
v_n_510_ = lean_nat_sub(v_a_503_, v_one_509_);
lean_dec(v_a_503_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v_n_510_);
v___x_512_ = v___x_505_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_502_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_n_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
v_k_498_ = v___x_512_;
goto v___jp_497_;
}
}
else
{
uint8_t v___x_514_; 
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_a_502_);
v___x_514_ = 0;
return v___x_514_;
}
}
}
case 3:
{
lean_object* v_a_516_; lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_529_; 
v_a_516_ = lean_ctor_get(v_k_496_, 0);
v_a_517_ = lean_ctor_get(v_k_496_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_k_496_);
if (v_isSharedCheck_529_ == 0)
{
v___x_519_ = v_k_496_;
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_inc(v_a_516_);
lean_dec(v_k_496_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_zero_521_; uint8_t v_isZero_522_; 
v_zero_521_ = lean_unsigned_to_nat(0u);
v_isZero_522_ = lean_nat_dec_eq(v_a_517_, v_zero_521_);
if (v_isZero_522_ == 0)
{
lean_object* v_one_523_; lean_object* v_n_524_; lean_object* v___x_526_; 
v_one_523_ = lean_unsigned_to_nat(1u);
v_n_524_ = lean_nat_sub(v_a_517_, v_one_523_);
lean_dec(v_a_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_n_524_);
v___x_526_ = v___x_519_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_n_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v_k_498_ = v___x_526_;
goto v___jp_497_;
}
}
else
{
uint8_t v___x_528_; 
lean_del_object(v___x_519_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
v___x_528_ = 0;
return v___x_528_;
}
}
}
default: 
{
uint8_t v___x_530_; 
lean_dec(v_k_496_);
v___x_530_ = 0;
return v___x_530_;
}
}
v___jp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_495_, v_k_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
v_k_496_ = v_k_498_;
goto _start;
}
else
{
uint8_t v___x_501_; 
lean_dec_ref_known(v___x_499_, 1);
lean_dec(v_k_498_);
v___x_501_ = 1;
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_531_, lean_object* v_k_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_531_, v_k_532_);
lean_dec_ref(v_d_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_535_, lean_object* v_d_536_, lean_object* v_k_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_536_, v_k_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_539_, lean_object* v_d_540_, lean_object* v_k_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_539_, v_d_540_, v_k_541_);
lean_dec_ref(v_d_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_544_, size_t v_sz_545_, size_t v_i_546_, lean_object* v_bs_547_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = lean_usize_dec_lt(v_i_546_, v_sz_545_);
if (v___x_548_ == 0)
{
lean_dec(v_numExtra_544_);
return v_bs_547_;
}
else
{
lean_object* v_v_549_; lean_object* v___x_550_; lean_object* v_bs_x27_551_; lean_object* v___x_552_; size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
v_v_549_ = lean_array_uget(v_bs_547_, v_i_546_);
v___x_550_ = lean_unsigned_to_nat(0u);
v_bs_x27_551_ = lean_array_uset(v_bs_547_, v_i_546_, v___x_550_);
lean_inc(v_numExtra_544_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_v_549_);
lean_ctor_set(v___x_552_, 1, v_numExtra_544_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_546_, v___x_553_);
v___x_555_ = lean_array_uset(v_bs_x27_551_, v_i_546_, v___x_552_);
v_i_546_ = v___x_554_;
v_bs_547_ = v___x_555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_557_, lean_object* v_sz_558_, lean_object* v_i_559_, lean_object* v_bs_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_558_);
lean_dec(v_sz_558_);
v_i_boxed_562_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_557_, v_sz_boxed_561_, v_i_boxed_562_, v_bs_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_564_, lean_object* v_d_565_, lean_object* v_e_566_, lean_object* v_numExtra_567_, lean_object* v_result_568_){
_start:
{
lean_object* v___x_569_; size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; lean_object* v_result_573_; lean_object* v_e_574_; uint8_t v___x_575_; 
v___x_569_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_564_, v_d_565_, v_e_566_);
v_sz_570_ = lean_array_size(v___x_569_);
v___x_571_ = ((size_t)0ULL);
lean_inc(v_numExtra_567_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_567_, v_sz_570_, v___x_571_, v___x_569_);
v_result_573_ = l_Array_append___redArg(v_result_568_, v___x_572_);
lean_dec_ref(v___x_572_);
v_e_574_ = l_Lean_Expr_consumeMData(v_e_566_);
lean_dec_ref(v_e_566_);
v___x_575_ = l_Lean_Expr_isApp(v_e_574_);
if (v___x_575_ == 0)
{
lean_dec_ref(v_e_574_);
lean_dec(v_numExtra_567_);
return v_result_573_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = l_Lean_Expr_appFn_x21(v_e_574_);
lean_dec_ref(v_e_574_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_numExtra_567_, v___x_577_);
lean_dec(v_numExtra_567_);
v_e_566_ = v___x_576_;
v_numExtra_567_ = v___x_578_;
v_result_568_ = v_result_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_580_, lean_object* v_d_581_, lean_object* v_e_582_, lean_object* v_numExtra_583_, lean_object* v_result_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_580_, v_d_581_, v_e_582_, v_numExtra_583_, v_result_584_);
lean_dec_ref(v_d_581_);
lean_dec_ref(v_mctx_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_586_, lean_object* v_mctx_587_, lean_object* v_d_588_, lean_object* v_e_589_, lean_object* v_numExtra_590_, lean_object* v_result_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_587_, v_d_588_, v_e_589_, v_numExtra_590_, v_result_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_593_, lean_object* v_mctx_594_, lean_object* v_d_595_, lean_object* v_e_596_, lean_object* v_numExtra_597_, lean_object* v_result_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_593_, v_mctx_594_, v_d_595_, v_e_596_, v_numExtra_597_, v_result_598_);
lean_dec_ref(v_d_595_);
lean_dec_ref(v_mctx_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_600_, lean_object* v_numExtra_601_, size_t v_sz_602_, size_t v_i_603_, lean_object* v_bs_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_601_, v_sz_602_, v_i_603_, v_bs_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_606_, lean_object* v_numExtra_607_, lean_object* v_sz_608_, lean_object* v_i_609_, lean_object* v_bs_610_){
_start:
{
size_t v_sz_boxed_611_; size_t v_i_boxed_612_; lean_object* v_res_613_; 
v_sz_boxed_611_ = lean_unbox_usize(v_sz_608_);
lean_dec(v_sz_608_);
v_i_boxed_612_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_res_613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_606_, v_numExtra_607_, v_sz_boxed_611_, v_i_boxed_612_, v_bs_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_614_, size_t v_i_615_, lean_object* v_bs_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_617_ == 0)
{
return v_bs_616_;
}
else
{
lean_object* v_v_618_; lean_object* v___x_619_; lean_object* v_bs_x27_620_; lean_object* v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v_v_618_ = lean_array_uget(v_bs_616_, v_i_615_);
v___x_619_ = lean_unsigned_to_nat(0u);
v_bs_x27_620_ = lean_array_uset(v_bs_616_, v_i_615_, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_v_618_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_615_, v___x_622_);
v___x_624_ = lean_array_uset(v_bs_x27_620_, v_i_615_, v___x_621_);
v_i_615_ = v___x_623_;
v_bs_616_ = v___x_624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_626_, lean_object* v_i_627_, lean_object* v_bs_628_){
_start:
{
size_t v_sz_boxed_629_; size_t v_i_boxed_630_; lean_object* v_res_631_; 
v_sz_boxed_629_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_i_boxed_630_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_629_, v_i_boxed_630_, v_bs_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_632_, lean_object* v_d_633_, lean_object* v_e_634_){
_start:
{
lean_object* v___x_635_; lean_object* v_e_636_; lean_object* v_e_637_; lean_object* v_result_638_; size_t v_sz_639_; size_t v___x_640_; lean_object* v_result_641_; uint8_t v___x_642_; 
v___x_635_ = l_Lean_Meta_Sym_etaReduce(v_e_634_);
v_e_636_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_632_, v___x_635_);
v_e_637_ = l_Lean_Expr_consumeMData(v_e_636_);
lean_dec_ref(v_e_636_);
v_result_638_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_632_, v_d_633_, v_e_637_);
v_sz_639_ = lean_array_size(v_result_638_);
v___x_640_ = ((size_t)0ULL);
v_result_641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_639_, v___x_640_, v_result_638_);
v___x_642_ = l_Lean_Expr_isApp(v_e_637_);
if (v___x_642_ == 0)
{
lean_dec_ref(v_e_637_);
return v_result_641_;
}
else
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_637_);
v___x_644_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_633_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_e_637_);
return v_result_641_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_Expr_appFn_x21(v_e_637_);
lean_dec_ref(v_e_637_);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_632_, v_d_633_, v___x_645_, v___x_646_, v_result_641_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_648_, lean_object* v_d_649_, lean_object* v_e_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_648_, v_d_649_, v_e_650_);
lean_dec_ref(v_e_650_);
lean_dec_ref(v_d_649_);
lean_dec_ref(v_mctx_648_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_652_, lean_object* v_mctx_653_, lean_object* v_d_654_, lean_object* v_e_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_653_, v_d_654_, v_e_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_657_, lean_object* v_mctx_658_, lean_object* v_d_659_, lean_object* v_e_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_657_, v_mctx_658_, v_d_659_, v_e_660_);
lean_dec_ref(v_e_660_);
lean_dec_ref(v_d_659_);
lean_dec_ref(v_mctx_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_662_, size_t v_sz_663_, size_t v_i_664_, lean_object* v_bs_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_663_, v_i_664_, v_bs_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_667_, lean_object* v_sz_668_, lean_object* v_i_669_, lean_object* v_bs_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v_i_boxed_672_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_667_, v_sz_boxed_671_, v_i_boxed_672_, v_bs_670_);
return v_res_673_;
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
