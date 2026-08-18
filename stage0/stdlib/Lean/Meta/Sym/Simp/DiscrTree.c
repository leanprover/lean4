// Lean compiler output
// Module: Lean.Meta.Sym.Simp.DiscrTree
// Imports: public import Lean.Meta.Sym.Pattern public import Lean.Meta.DiscrTree.Basic import Lean.Meta.Sym.Offset import Lean.Meta.Sym.Eta import Init.Omega
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_pop(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value),((lean_object*)&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1_value)}};
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
return v_isInstance_6_;
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
lean_object* v_declName_70_; lean_object* v___y_72_; lean_object* v___y_73_; 
v_declName_70_ = lean_ctor_get(v_fn_58_, 0);
lean_inc(v_declName_70_);
lean_dec_ref_known(v_fn_58_, 2);
if (v_root_53_ == 0)
{
goto v___jp_84_;
}
else
{
if (v___x_57_ == 0)
{
goto v___jp_76_;
}
else
{
goto v___jp_84_;
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
lean_object* v_numArgs_77_; lean_object* v___x_78_; 
v_numArgs_77_ = l_Lean_Expr_getAppNumArgs(v_e_56_);
v___x_78_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_declName_70_, v_fnInfos_54_);
if (lean_obj_tag(v___x_78_) == 1)
{
lean_object* v_val_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_val_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_val_79_);
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_sub(v_numArgs_77_, v___x_80_);
v___x_82_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(v_val_79_, v___x_81_, v_e_56_, v_todo_55_);
lean_dec(v_val_79_);
v___y_72_ = v_numArgs_77_;
v___y_73_ = v___x_82_;
goto v___jp_71_;
}
else
{
lean_object* v___x_83_; 
lean_dec(v___x_78_);
v___x_83_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_56_, v_todo_55_);
v___y_72_ = v_numArgs_77_;
v___y_73_ = v___x_83_;
goto v___jp_71_;
}
}
v___jp_84_:
{
uint8_t v___x_85_; 
lean_inc_ref(v_e_56_);
v___x_85_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_70_, v_e_56_);
if (v___x_85_ == 0)
{
goto v___jp_76_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_declName_70_);
lean_dec_ref(v_e_56_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_todo_55_);
return v___x_87_;
}
}
}
case 1:
{
lean_object* v_fvarId_88_; lean_object* v_numArgs_89_; lean_object* v_todo_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_fvarId_88_ = lean_ctor_get(v_fn_58_, 0);
lean_inc(v_fvarId_88_);
lean_dec_ref_known(v_fn_58_, 1);
v_numArgs_89_ = l_Lean_Expr_getAppNumArgs(v_e_56_);
v_todo_90_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_56_, v_todo_55_);
v___x_91_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_91_, 0, v_fvarId_88_);
lean_ctor_set(v___x_91_, 1, v_numArgs_89_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v_todo_90_);
return v___x_92_;
}
default: 
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec_ref(v_fn_58_);
lean_dec_ref(v_e_56_);
v___x_93_ = lean_box(1);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v_todo_55_);
return v___x_94_;
}
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; 
lean_dec_ref(v_e_56_);
v___x_95_ = lean_box(0);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_todo_55_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs___boxed(lean_object* v_root_97_, lean_object* v_fnInfos_98_, lean_object* v_todo_99_, lean_object* v_e_100_){
_start:
{
uint8_t v_root_boxed_101_; lean_object* v_res_102_; 
v_root_boxed_101_ = lean_unbox(v_root_97_);
v_res_102_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_boxed_101_, v_fnInfos_98_, v_todo_99_, v_e_100_);
lean_dec(v_fnInfos_98_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(lean_object* v_00_u03b2_103_, lean_object* v_a_104_, lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_104_, v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___boxed(lean_object* v_00_u03b2_107_, lean_object* v_a_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(v_00_u03b2_107_, v_a_108_, v_x_109_);
lean_dec(v_x_109_);
lean_dec(v_a_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(uint8_t v_root_111_, lean_object* v_fnInfos_112_, lean_object* v_todo_113_, lean_object* v_keys_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_array_get_size(v_todo_113_);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_dec_eq(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_e_121_; lean_object* v_todo_122_; lean_object* v___x_123_; lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v___x_126_; 
v___x_118_ = l_Lean_instInhabitedExpr;
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_sub(v___x_115_, v___x_119_);
v_e_121_ = lean_array_get(v___x_118_, v_todo_113_, v___x_120_);
lean_dec(v___x_120_);
v_todo_122_ = lean_array_pop(v_todo_113_);
v___x_123_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_111_, v_fnInfos_112_, v_todo_122_, v_e_121_);
v_fst_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_fst_124_);
v_snd_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc(v_snd_125_);
lean_dec_ref(v___x_123_);
v___x_126_ = lean_array_push(v_keys_114_, v_fst_124_);
v_root_111_ = v___x_117_;
v_todo_113_ = v_snd_125_;
v_keys_114_ = v___x_126_;
goto _start;
}
else
{
lean_dec_ref(v_todo_113_);
return v_keys_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux___boxed(lean_object* v_root_128_, lean_object* v_fnInfos_129_, lean_object* v_todo_130_, lean_object* v_keys_131_){
_start:
{
uint8_t v_root_boxed_132_; lean_object* v_res_133_; 
v_root_boxed_132_ = lean_unbox(v_root_128_);
v_res_133_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v_root_boxed_132_, v_fnInfos_129_, v_todo_130_, v_keys_131_);
lean_dec(v_fnInfos_129_);
return v_res_133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(8u);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object* v_p_135_){
_start:
{
lean_object* v_pattern_136_; lean_object* v_fnInfos_137_; lean_object* v___x_138_; lean_object* v_todo_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_pattern_136_ = lean_ctor_get(v_p_135_, 3);
lean_inc_ref(v_pattern_136_);
v_fnInfos_137_ = lean_ctor_get(v_p_135_, 4);
lean_inc(v_fnInfos_137_);
lean_dec_ref(v_p_135_);
v___x_138_ = lean_unsigned_to_nat(8u);
v_todo_139_ = lean_mk_empty_array_with_capacity(v___x_138_);
v___x_140_ = 1;
lean_inc_ref(v_todo_139_);
v___x_141_ = lean_array_push(v_todo_139_, v_pattern_136_);
v___x_142_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v___x_140_, v_fnInfos_137_, v___x_141_, v_todo_139_);
lean_dec(v_fnInfos_137_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___redArg(lean_object* v_inst_143_, lean_object* v_d_144_, lean_object* v_p_145_, lean_object* v_v_146_){
_start:
{
lean_object* v_keys_147_; lean_object* v___x_148_; 
v_keys_147_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_145_);
v___x_148_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_143_, v_d_144_, v_keys_147_, v_v_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern(lean_object* v_00_u03b1_149_, lean_object* v_inst_150_, lean_object* v_d_151_, lean_object* v_p_152_, lean_object* v_v_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Sym_insertPattern___redArg(v_inst_150_, v_d_151_, v_p_152_, v_v_153_);
return v___x_154_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
lean_object* v_fst_157_; lean_object* v_fst_158_; uint8_t v___x_159_; 
v_fst_157_ = lean_ctor_get(v_a_155_, 0);
v_fst_158_ = lean_ctor_get(v_b_156_, 0);
v___x_159_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_157_, v_fst_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed(lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_160_, v_b_161_);
lean_dec_ref(v_b_161_);
lean_dec_ref(v_a_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(lean_object* v_cs_170_, lean_object* v_k_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_array_get_size(v_cs_170_);
v___x_174_ = lean_nat_dec_lt(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v_k_171_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_sub(v___x_173_, v___x_176_);
v___x_178_ = lean_nat_dec_le(v___x_172_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
lean_dec(v___x_177_);
lean_dec(v_k_171_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
else
{
lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___f_180_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_k_171_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_184_ = l_Array_binSearchAux___redArg(v___f_180_, v___x_183_, v_cs_170_, v___x_182_, v___x_172_, v___x_177_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___boxed(lean_object* v_cs_185_, lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(v_cs_185_, v_k_186_);
lean_dec_ref(v_cs_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(lean_object* v_00_u03b1_188_, lean_object* v_cs_189_, lean_object* v_k_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_array_get_size(v_cs_189_);
v___x_193_ = lean_nat_dec_lt(v___x_191_, v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_dec(v_k_190_);
v___x_194_ = lean_box(0);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_sub(v___x_192_, v___x_195_);
v___x_197_ = lean_nat_dec_le(v___x_191_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_dec(v___x_196_);
lean_dec(v_k_190_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___f_199_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v_k_190_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_203_ = l_Array_binSearchAux___redArg(v___f_199_, v___x_202_, v_cs_189_, v___x_201_, v___x_191_, v___x_196_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___boxed(lean_object* v_00_u03b1_204_, lean_object* v_cs_205_, lean_object* v_k_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(v_00_u03b1_204_, v_cs_205_, v_k_206_);
lean_dec_ref(v_cs_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(lean_object* v_e_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Expr_getAppFn_x27(v_e_208_);
switch(lean_obj_tag(v___x_209_))
{
case 9:
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_a_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_211_, 0, v_a_210_);
return v___x_211_;
}
case 4:
{
lean_object* v_declName_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_declName_212_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_declName_212_);
lean_dec_ref_known(v___x_209_, 2);
v___x_213_ = l_Lean_Expr_getAppNumArgs_x27(v_e_208_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v_declName_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
case 1:
{
lean_object* v_fvarId_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_fvarId_215_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_fvarId_215_);
lean_dec_ref_known(v___x_209_, 1);
v___x_216_ = l_Lean_Expr_getAppNumArgs_x27(v_e_208_);
v___x_217_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_217_, 0, v_fvarId_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
case 7:
{
lean_object* v___x_218_; 
lean_dec_ref_known(v___x_209_, 3);
v___x_218_ = lean_box(5);
return v___x_218_;
}
default: 
{
lean_object* v___x_219_; 
lean_dec_ref(v___x_209_);
v___x_219_ = lean_box(1);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(lean_object* v_e_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_220_);
lean_dec_ref(v_e_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(lean_object* v_mctx_222_, lean_object* v_e_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Lean_Expr_hasExprMVar(v_e_223_);
if (v___x_224_ == 0)
{
return v_e_223_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Expr_getAppFn(v_e_223_);
if (lean_obj_tag(v___x_225_) == 2)
{
lean_object* v_mvarId_226_; lean_object* v___x_227_; 
v_mvarId_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_mvarId_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_222_, v_mvarId_226_);
lean_dec(v_mvarId_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
return v_e_223_;
}
else
{
lean_object* v_val_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v_val_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = l_Lean_Expr_getAppNumArgs(v_e_223_);
v___x_230_ = lean_mk_empty_array_with_capacity(v___x_229_);
lean_dec(v___x_229_);
v___x_231_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_223_, v___x_230_);
v___x_232_ = 0;
v___x_233_ = l_Lean_Expr_betaRev(v_val_228_, v___x_231_, v___x_232_, v___x_232_);
lean_dec_ref(v___x_231_);
v_e_223_ = v___x_233_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_225_);
return v_e_223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars___boxed(lean_object* v_mctx_235_, lean_object* v_e_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_235_, v_e_236_);
lean_dec_ref(v_mctx_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object* v_todo_238_, lean_object* v_e_239_){
_start:
{
switch(lean_obj_tag(v_e_239_))
{
case 5:
{
lean_object* v_fn_240_; lean_object* v_arg_241_; lean_object* v___x_242_; 
v_fn_240_ = lean_ctor_get(v_e_239_, 0);
lean_inc_ref(v_fn_240_);
v_arg_241_ = lean_ctor_get(v_e_239_, 1);
lean_inc_ref(v_arg_241_);
lean_dec_ref_known(v_e_239_, 2);
v___x_242_ = lean_array_push(v_todo_238_, v_arg_241_);
v_todo_238_ = v___x_242_;
v_e_239_ = v_fn_240_;
goto _start;
}
case 7:
{
lean_object* v_binderType_244_; lean_object* v_body_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_binderType_244_ = lean_ctor_get(v_e_239_, 1);
lean_inc_ref(v_binderType_244_);
v_body_245_ = lean_ctor_get(v_e_239_, 2);
lean_inc_ref(v_body_245_);
lean_dec_ref_known(v_e_239_, 3);
v___x_246_ = lean_array_push(v_todo_238_, v_body_245_);
v___x_247_ = lean_array_push(v___x_246_, v_binderType_244_);
return v___x_247_;
}
case 10:
{
lean_object* v_expr_248_; 
v_expr_248_ = lean_ctor_get(v_e_239_, 1);
lean_inc_ref(v_expr_248_);
lean_dec_ref_known(v_e_239_, 2);
v_e_239_ = v_expr_248_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_239_);
return v_todo_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_as_250_, lean_object* v_k_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_m_256_; lean_object* v_a_257_; uint8_t v___x_258_; 
v___x_254_ = lean_nat_add(v_x_252_, v_x_253_);
v___x_255_ = lean_unsigned_to_nat(1u);
v_m_256_ = lean_nat_shiftr(v___x_254_, v___x_255_);
lean_dec(v___x_254_);
v_a_257_ = lean_array_fget_borrowed(v_as_250_, v_m_256_);
v___x_258_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_257_, v_k_251_);
if (v___x_258_ == 0)
{
uint8_t v___x_259_; 
lean_dec(v_x_253_);
v___x_259_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_251_, v_a_257_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_m_256_);
lean_dec(v_x_252_);
lean_inc(v_a_257_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_a_257_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_nat_dec_eq(v_m_256_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_nat_sub(v_m_256_, v___x_255_);
lean_dec(v_m_256_);
v___x_264_ = lean_nat_dec_lt(v___x_263_, v_x_252_);
if (v___x_264_ == 0)
{
v_x_253_ = v___x_263_;
goto _start;
}
else
{
lean_object* v___x_266_; 
lean_dec(v___x_263_);
lean_dec(v_x_252_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
else
{
lean_object* v___x_267_; 
lean_dec(v_m_256_);
lean_dec(v_x_252_);
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
lean_dec(v_x_252_);
v___x_268_ = lean_nat_add(v_m_256_, v___x_255_);
lean_dec(v_m_256_);
v___x_269_ = lean_nat_dec_le(v___x_268_, v_x_253_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec(v___x_268_);
lean_dec(v_x_253_);
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
v_x_252_ = v___x_268_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_272_, lean_object* v_k_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_272_, v_k_273_, v_x_274_, v_x_275_);
lean_dec_ref(v_k_273_);
lean_dec_ref(v_as_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_mctx_277_, lean_object* v_todo_278_, lean_object* v_c_279_, lean_object* v_result_280_){
_start:
{
lean_object* v_vs_281_; lean_object* v_children_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_330_; 
v_vs_281_ = lean_ctor_get(v_c_279_, 0);
v_children_282_ = lean_ctor_get(v_c_279_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_c_279_);
if (v_isSharedCheck_330_ == 0)
{
v___x_284_ = v_c_279_;
v_isShared_285_ = v_isSharedCheck_330_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_children_282_);
lean_inc(v_vs_281_);
lean_dec(v_c_279_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_330_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_array_get_size(v_todo_278_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v_csize_289_; uint8_t v___x_290_; 
lean_dec_ref(v_vs_281_);
v_csize_289_ = lean_array_get_size(v_children_282_);
v___x_290_ = lean_nat_dec_eq(v_csize_289_, v___x_287_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_e_296_; lean_object* v_todo_297_; lean_object* v___y_299_; lean_object* v_first_313_; uint8_t v___x_314_; 
v___x_291_ = l_Lean_instInhabitedExpr;
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_sub(v___x_286_, v___x_292_);
v___x_294_ = lean_array_get_borrowed(v___x_291_, v_todo_278_, v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = l_Lean_Meta_Sym_etaReduce(v___x_294_);
v_e_296_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_277_, v___x_295_);
v_todo_297_ = lean_array_pop(v_todo_278_);
v_first_313_ = lean_array_fget_borrowed(v_children_282_, v___x_287_);
v___x_314_ = lean_nat_dec_eq(v_csize_289_, v___x_292_);
if (v___x_314_ == 0)
{
lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_fst_315_ = lean_ctor_get(v_first_313_, 0);
v_snd_316_ = lean_ctor_get(v_first_313_, 1);
v___x_317_ = lean_box(0);
v___x_318_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_315_, v___x_317_);
if (v___x_318_ == 0)
{
v___y_299_ = v_result_280_;
goto v___jp_298_;
}
else
{
lean_object* v___x_319_; 
lean_inc(v_snd_316_);
lean_inc_ref(v_todo_297_);
v___x_319_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_277_, v_todo_297_, v_snd_316_, v_result_280_);
v___y_299_ = v___x_319_;
goto v___jp_298_;
}
}
else
{
lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
lean_inc(v_first_313_);
lean_del_object(v___x_284_);
lean_dec_ref(v_children_282_);
v_fst_320_ = lean_ctor_get(v_first_313_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_first_313_, 1);
lean_inc(v_snd_321_);
lean_dec(v_first_313_);
v___x_322_ = lean_box(0);
v___x_323_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_320_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_296_);
v___x_325_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_320_, v___x_324_);
lean_dec(v___x_324_);
lean_dec(v_fst_320_);
if (v___x_325_ == 0)
{
lean_dec(v_snd_321_);
lean_dec_ref(v_todo_297_);
lean_dec_ref(v_e_296_);
return v_result_280_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_297_, v_e_296_);
v_todo_278_ = v___x_326_;
v_c_279_ = v_snd_321_;
goto _start;
}
}
else
{
lean_dec(v_fst_320_);
lean_dec_ref(v_e_296_);
v_todo_278_ = v_todo_297_;
v_c_279_ = v_snd_321_;
goto _start;
}
}
v___jp_298_:
{
uint8_t v___x_300_; 
v___x_300_ = lean_nat_dec_lt(v___x_287_, v_csize_289_);
if (v___x_300_ == 0)
{
lean_dec_ref(v_todo_297_);
lean_dec_ref(v_e_296_);
lean_del_object(v___x_284_);
lean_dec_ref(v_children_282_);
return v___y_299_;
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_nat_sub(v_csize_289_, v___x_292_);
v___x_302_ = lean_nat_dec_le(v___x_287_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v___x_301_);
lean_dec_ref(v_todo_297_);
lean_dec_ref(v_e_296_);
lean_del_object(v___x_284_);
lean_dec_ref(v_children_282_);
return v___y_299_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_303_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_296_);
v___x_304_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_304_);
lean_ctor_set(v___x_284_, 0, v___x_303_);
v___x_306_ = v___x_284_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_312_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_282_, v___x_306_, v___x_287_, v___x_301_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_children_282_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_dec_ref(v_todo_297_);
lean_dec_ref(v_e_296_);
return v___y_299_;
}
else
{
lean_object* v_val_308_; lean_object* v_snd_309_; lean_object* v___x_310_; 
v_val_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v___x_307_, 1);
v_snd_309_ = lean_ctor_get(v_val_308_, 1);
lean_inc(v_snd_309_);
lean_dec(v_val_308_);
v___x_310_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_297_, v_e_296_);
v_todo_278_ = v___x_310_;
v_c_279_ = v_snd_309_;
v_result_280_ = v___y_299_;
goto _start;
}
}
}
}
}
}
else
{
lean_del_object(v___x_284_);
lean_dec_ref(v_children_282_);
lean_dec_ref(v_todo_278_);
return v_result_280_;
}
}
else
{
lean_object* v___x_329_; 
lean_del_object(v___x_284_);
lean_dec_ref(v_children_282_);
lean_dec_ref(v_todo_278_);
v___x_329_ = l_Array_append___redArg(v_result_280_, v_vs_281_);
lean_dec_ref(v_vs_281_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_331_, lean_object* v_todo_332_, lean_object* v_c_333_, lean_object* v_result_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_331_, v_todo_332_, v_c_333_, v_result_334_);
lean_dec_ref(v_mctx_331_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_336_, lean_object* v_mctx_337_, lean_object* v_todo_338_, lean_object* v_c_339_, lean_object* v_result_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_337_, v_todo_338_, v_c_339_, v_result_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_342_, lean_object* v_mctx_343_, lean_object* v_todo_344_, lean_object* v_c_345_, lean_object* v_result_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_342_, v_mctx_343_, v_todo_344_, v_c_345_, v_result_346_);
lean_dec_ref(v_mctx_343_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_348_, lean_object* v_as_349_, lean_object* v_k_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_349_, v_k_350_, v_x_351_, v_x_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_355_, lean_object* v_as_356_, lean_object* v_k_357_, lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_355_, v_as_356_, v_k_357_, v_x_358_, v_x_359_, v_x_360_);
lean_dec_ref(v_k_357_);
lean_dec_ref(v_as_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_362_, lean_object* v_vals_363_, lean_object* v_i_364_, lean_object* v_k_365_){
_start:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_array_get_size(v_keys_362_);
v___x_367_ = lean_nat_dec_lt(v_i_364_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec(v_i_364_);
v___x_368_ = lean_box(0);
return v___x_368_;
}
else
{
lean_object* v_k_x27_369_; uint8_t v___x_370_; 
v_k_x27_369_ = lean_array_fget_borrowed(v_keys_362_, v_i_364_);
v___x_370_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_365_, v_k_x27_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_i_364_, v___x_371_);
lean_dec(v_i_364_);
v_i_364_ = v___x_372_;
goto _start;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_array_fget_borrowed(v_vals_363_, v_i_364_);
lean_dec(v_i_364_);
lean_inc(v___x_374_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_376_, lean_object* v_vals_377_, lean_object* v_i_378_, lean_object* v_k_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_376_, v_vals_377_, v_i_378_, v_k_379_);
lean_dec(v_k_379_);
lean_dec_ref(v_vals_377_);
lean_dec_ref(v_keys_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_381_, size_t v_x_382_, lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v_es_384_; lean_object* v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v_j_388_; lean_object* v___x_389_; 
v_es_384_ = lean_ctor_get(v_x_381_, 0);
v___x_385_ = lean_box(2);
v___x_386_ = ((size_t)31ULL);
v___x_387_ = lean_usize_land(v_x_382_, v___x_386_);
v_j_388_ = lean_usize_to_nat(v___x_387_);
v___x_389_ = lean_array_get_borrowed(v___x_385_, v_es_384_, v_j_388_);
lean_dec(v_j_388_);
switch(lean_obj_tag(v___x_389_))
{
case 0:
{
lean_object* v_key_390_; lean_object* v_val_391_; uint8_t v___x_392_; 
v_key_390_ = lean_ctor_get(v___x_389_, 0);
v_val_391_ = lean_ctor_get(v___x_389_, 1);
v___x_392_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_383_, v_key_390_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v___x_394_; 
lean_inc(v_val_391_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v_val_391_);
return v___x_394_;
}
}
case 1:
{
lean_object* v_node_395_; size_t v___x_396_; size_t v___x_397_; 
v_node_395_ = lean_ctor_get(v___x_389_, 0);
v___x_396_ = ((size_t)5ULL);
v___x_397_ = lean_usize_shift_right(v_x_382_, v___x_396_);
v_x_381_ = v_node_395_;
v_x_382_ = v___x_397_;
goto _start;
}
default: 
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
}
}
else
{
lean_object* v_ks_400_; lean_object* v_vs_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_ks_400_ = lean_ctor_get(v_x_381_, 0);
v_vs_401_ = lean_ctor_get(v_x_381_, 1);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_400_, v_vs_401_, v___x_402_, v_x_383_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
size_t v_x_190__boxed_407_; lean_object* v_res_408_; 
v_x_190__boxed_407_ = lean_unbox_usize(v_x_405_);
lean_dec(v_x_405_);
v_res_408_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_404_, v_x_190__boxed_407_, v_x_406_);
lean_dec(v_x_406_);
lean_dec_ref(v_x_404_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
uint64_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_410_);
v___x_412_ = lean_uint64_to_usize(v___x_411_);
v___x_413_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_409_, v___x_412_, v_x_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_414_, v_x_415_);
lean_dec(v_x_415_);
lean_dec_ref(v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_419_, lean_object* v_d_420_, lean_object* v_e_421_){
_start:
{
lean_object* v___y_423_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_box(0);
v___x_433_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_420_, v___x_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(8u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v___y_423_ = v___x_435_;
goto v___jp_422_;
}
else
{
lean_object* v_val_436_; lean_object* v_vs_437_; 
v_val_436_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_433_, 1);
v_vs_437_ = lean_ctor_get(v_val_436_, 0);
lean_inc_ref(v_vs_437_);
lean_dec(v_val_436_);
v___y_423_ = v_vs_437_;
goto v___jp_422_;
}
v___jp_422_:
{
lean_object* v___x_424_; lean_object* v_e_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = l_Lean_Meta_Sym_etaReduce(v_e_421_);
v_e_425_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_419_, v___x_424_);
v___x_426_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_425_);
v___x_427_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_420_, v___x_426_);
lean_dec(v___x_426_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_dec_ref(v_e_425_);
return v___y_423_;
}
else
{
lean_object* v_val_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_val_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_430_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_429_, v_e_425_);
v___x_431_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_419_, v___x_430_, v_val_428_, v___y_423_);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_438_, lean_object* v_d_439_, lean_object* v_e_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_438_, v_d_439_, v_e_440_);
lean_dec_ref(v_e_440_);
lean_dec_ref(v_d_439_);
lean_dec_ref(v_mctx_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_442_, lean_object* v_mctx_443_, lean_object* v_d_444_, lean_object* v_e_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_443_, v_d_444_, v_e_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_447_, lean_object* v_mctx_448_, lean_object* v_d_449_, lean_object* v_e_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_447_, v_mctx_448_, v_d_449_, v_e_450_);
lean_dec_ref(v_e_450_);
lean_dec_ref(v_d_449_);
lean_dec_ref(v_mctx_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_452_, lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_453_, v_x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_456_, v_x_457_, v_x_458_);
lean_dec(v_x_458_);
lean_dec_ref(v_x_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, size_t v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_461_, v_x_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
size_t v_x_296__boxed_469_; lean_object* v_res_470_; 
v_x_296__boxed_469_ = lean_unbox_usize(v_x_467_);
lean_dec(v_x_467_);
v_res_470_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_465_, v_x_466_, v_x_296__boxed_469_, v_x_468_);
lean_dec(v_x_468_);
lean_dec_ref(v_x_466_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_heq_474_, lean_object* v_i_475_, lean_object* v_k_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_472_, v_vals_473_, v_i_475_, v_k_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_478_, lean_object* v_keys_479_, lean_object* v_vals_480_, lean_object* v_heq_481_, lean_object* v_i_482_, lean_object* v_k_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_478_, v_keys_479_, v_vals_480_, v_heq_481_, v_i_482_, v_k_483_);
lean_dec(v_k_483_);
lean_dec_ref(v_vals_480_);
lean_dec_ref(v_keys_479_);
return v_res_484_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_485_, lean_object* v_k_486_){
_start:
{
lean_object* v_k_488_; 
switch(lean_obj_tag(v_k_486_))
{
case 4:
{
lean_object* v_a_492_; lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_505_; 
v_a_492_ = lean_ctor_get(v_k_486_, 0);
v_a_493_ = lean_ctor_get(v_k_486_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_k_486_);
if (v_isSharedCheck_505_ == 0)
{
v___x_495_ = v_k_486_;
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_inc(v_a_492_);
lean_dec(v_k_486_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_zero_497_; uint8_t v_isZero_498_; 
v_zero_497_ = lean_unsigned_to_nat(0u);
v_isZero_498_ = lean_nat_dec_eq(v_a_493_, v_zero_497_);
if (v_isZero_498_ == 0)
{
lean_object* v_one_499_; lean_object* v_n_500_; lean_object* v___x_502_; 
v_one_499_ = lean_unsigned_to_nat(1u);
v_n_500_ = lean_nat_sub(v_a_493_, v_one_499_);
lean_dec(v_a_493_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v_n_500_);
v___x_502_ = v___x_495_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_492_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_n_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
v_k_488_ = v___x_502_;
goto v___jp_487_;
}
}
else
{
uint8_t v___x_504_; 
lean_del_object(v___x_495_);
lean_dec(v_a_493_);
lean_dec(v_a_492_);
v___x_504_ = 0;
return v___x_504_;
}
}
}
case 3:
{
lean_object* v_a_506_; lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_a_506_ = lean_ctor_get(v_k_486_, 0);
v_a_507_ = lean_ctor_get(v_k_486_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_k_486_);
if (v_isSharedCheck_519_ == 0)
{
v___x_509_ = v_k_486_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_inc(v_a_506_);
lean_dec(v_k_486_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_zero_511_; uint8_t v_isZero_512_; 
v_zero_511_ = lean_unsigned_to_nat(0u);
v_isZero_512_ = lean_nat_dec_eq(v_a_507_, v_zero_511_);
if (v_isZero_512_ == 0)
{
lean_object* v_one_513_; lean_object* v_n_514_; lean_object* v___x_516_; 
v_one_513_ = lean_unsigned_to_nat(1u);
v_n_514_ = lean_nat_sub(v_a_507_, v_one_513_);
lean_dec(v_a_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_n_514_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_506_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_n_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v_k_488_ = v___x_516_;
goto v___jp_487_;
}
}
else
{
uint8_t v___x_518_; 
lean_del_object(v___x_509_);
lean_dec(v_a_507_);
lean_dec(v_a_506_);
v___x_518_ = 0;
return v___x_518_;
}
}
}
default: 
{
uint8_t v___x_520_; 
lean_dec(v_k_486_);
v___x_520_ = 0;
return v___x_520_;
}
}
v___jp_487_:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_485_, v_k_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
v_k_486_ = v_k_488_;
goto _start;
}
else
{
uint8_t v___x_491_; 
lean_dec_ref_known(v___x_489_, 1);
lean_dec(v_k_488_);
v___x_491_ = 1;
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_521_, lean_object* v_k_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_521_, v_k_522_);
lean_dec_ref(v_d_521_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_525_, lean_object* v_d_526_, lean_object* v_k_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_526_, v_k_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_529_, lean_object* v_d_530_, lean_object* v_k_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_529_, v_d_530_, v_k_531_);
lean_dec_ref(v_d_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_534_, size_t v_sz_535_, size_t v_i_536_, lean_object* v_bs_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_538_ == 0)
{
lean_dec(v_numExtra_534_);
return v_bs_537_;
}
else
{
lean_object* v_v_539_; lean_object* v___x_540_; lean_object* v_bs_x27_541_; lean_object* v___x_542_; size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; 
v_v_539_ = lean_array_uget(v_bs_537_, v_i_536_);
v___x_540_ = lean_unsigned_to_nat(0u);
v_bs_x27_541_ = lean_array_uset(v_bs_537_, v_i_536_, v___x_540_);
lean_inc(v_numExtra_534_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_v_539_);
lean_ctor_set(v___x_542_, 1, v_numExtra_534_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_536_, v___x_543_);
v___x_545_ = lean_array_uset(v_bs_x27_541_, v_i_536_, v___x_542_);
v_i_536_ = v___x_544_;
v_bs_537_ = v___x_545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_547_, lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_547_, v_sz_boxed_551_, v_i_boxed_552_, v_bs_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_554_, lean_object* v_d_555_, lean_object* v_e_556_, lean_object* v_numExtra_557_, lean_object* v_result_558_){
_start:
{
lean_object* v___x_559_; size_t v_sz_560_; size_t v___x_561_; lean_object* v___x_562_; lean_object* v_result_563_; lean_object* v_e_564_; uint8_t v___x_565_; 
v___x_559_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_554_, v_d_555_, v_e_556_);
v_sz_560_ = lean_array_size(v___x_559_);
v___x_561_ = ((size_t)0ULL);
lean_inc(v_numExtra_557_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_557_, v_sz_560_, v___x_561_, v___x_559_);
v_result_563_ = l_Array_append___redArg(v_result_558_, v___x_562_);
lean_dec_ref(v___x_562_);
v_e_564_ = l_Lean_Expr_consumeMData(v_e_556_);
lean_dec_ref(v_e_556_);
v___x_565_ = l_Lean_Expr_isApp(v_e_564_);
if (v___x_565_ == 0)
{
lean_dec_ref(v_e_564_);
lean_dec(v_numExtra_557_);
return v_result_563_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = l_Lean_Expr_appFn_x21(v_e_564_);
lean_dec_ref(v_e_564_);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_numExtra_557_, v___x_567_);
lean_dec(v_numExtra_557_);
v_e_556_ = v___x_566_;
v_numExtra_557_ = v___x_568_;
v_result_558_ = v_result_563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_570_, lean_object* v_d_571_, lean_object* v_e_572_, lean_object* v_numExtra_573_, lean_object* v_result_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_570_, v_d_571_, v_e_572_, v_numExtra_573_, v_result_574_);
lean_dec_ref(v_d_571_);
lean_dec_ref(v_mctx_570_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_576_, lean_object* v_mctx_577_, lean_object* v_d_578_, lean_object* v_e_579_, lean_object* v_numExtra_580_, lean_object* v_result_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_577_, v_d_578_, v_e_579_, v_numExtra_580_, v_result_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_583_, lean_object* v_mctx_584_, lean_object* v_d_585_, lean_object* v_e_586_, lean_object* v_numExtra_587_, lean_object* v_result_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_583_, v_mctx_584_, v_d_585_, v_e_586_, v_numExtra_587_, v_result_588_);
lean_dec_ref(v_d_585_);
lean_dec_ref(v_mctx_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_590_, lean_object* v_numExtra_591_, size_t v_sz_592_, size_t v_i_593_, lean_object* v_bs_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_591_, v_sz_592_, v_i_593_, v_bs_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_596_, lean_object* v_numExtra_597_, lean_object* v_sz_598_, lean_object* v_i_599_, lean_object* v_bs_600_){
_start:
{
size_t v_sz_boxed_601_; size_t v_i_boxed_602_; lean_object* v_res_603_; 
v_sz_boxed_601_ = lean_unbox_usize(v_sz_598_);
lean_dec(v_sz_598_);
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_596_, v_numExtra_597_, v_sz_boxed_601_, v_i_boxed_602_, v_bs_600_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_604_, size_t v_i_605_, lean_object* v_bs_606_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = lean_usize_dec_lt(v_i_605_, v_sz_604_);
if (v___x_607_ == 0)
{
return v_bs_606_;
}
else
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_bs_x27_610_; lean_object* v___x_611_; size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v_v_608_ = lean_array_uget(v_bs_606_, v_i_605_);
v___x_609_ = lean_unsigned_to_nat(0u);
v_bs_x27_610_ = lean_array_uset(v_bs_606_, v_i_605_, v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v_v_608_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_i_605_, v___x_612_);
v___x_614_ = lean_array_uset(v_bs_x27_610_, v_i_605_, v___x_611_);
v_i_605_ = v___x_613_;
v_bs_606_ = v___x_614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_616_, lean_object* v_i_617_, lean_object* v_bs_618_){
_start:
{
size_t v_sz_boxed_619_; size_t v_i_boxed_620_; lean_object* v_res_621_; 
v_sz_boxed_619_ = lean_unbox_usize(v_sz_616_);
lean_dec(v_sz_616_);
v_i_boxed_620_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_619_, v_i_boxed_620_, v_bs_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_622_, lean_object* v_d_623_, lean_object* v_e_624_){
_start:
{
lean_object* v___x_625_; lean_object* v_e_626_; lean_object* v_e_627_; lean_object* v_result_628_; size_t v_sz_629_; size_t v___x_630_; lean_object* v_result_631_; uint8_t v___x_632_; 
v___x_625_ = l_Lean_Meta_Sym_etaReduce(v_e_624_);
v_e_626_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_622_, v___x_625_);
v_e_627_ = l_Lean_Expr_consumeMData(v_e_626_);
lean_dec_ref(v_e_626_);
v_result_628_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_622_, v_d_623_, v_e_627_);
v_sz_629_ = lean_array_size(v_result_628_);
v___x_630_ = ((size_t)0ULL);
v_result_631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_629_, v___x_630_, v_result_628_);
v___x_632_ = l_Lean_Expr_isApp(v_e_627_);
if (v___x_632_ == 0)
{
lean_dec_ref(v_e_627_);
return v_result_631_;
}
else
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_627_);
v___x_634_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_623_, v___x_633_);
if (v___x_634_ == 0)
{
lean_dec_ref(v_e_627_);
return v_result_631_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = l_Lean_Expr_appFn_x21(v_e_627_);
lean_dec_ref(v_e_627_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_622_, v_d_623_, v___x_635_, v___x_636_, v_result_631_);
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_638_, lean_object* v_d_639_, lean_object* v_e_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_638_, v_d_639_, v_e_640_);
lean_dec_ref(v_e_640_);
lean_dec_ref(v_d_639_);
lean_dec_ref(v_mctx_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_642_, lean_object* v_mctx_643_, lean_object* v_d_644_, lean_object* v_e_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_643_, v_d_644_, v_e_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_647_, lean_object* v_mctx_648_, lean_object* v_d_649_, lean_object* v_e_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_647_, v_mctx_648_, v_d_649_, v_e_650_);
lean_dec_ref(v_e_650_);
lean_dec_ref(v_d_649_);
lean_dec_ref(v_mctx_648_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_652_, size_t v_sz_653_, size_t v_i_654_, lean_object* v_bs_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_653_, v_i_654_, v_bs_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_657_, lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_bs_660_){
_start:
{
size_t v_sz_boxed_661_; size_t v_i_boxed_662_; lean_object* v_res_663_; 
v_sz_boxed_661_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_662_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_657_, v_sz_boxed_661_, v_i_boxed_662_, v_bs_660_);
return v_res_663_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
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
lean_object* initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
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
res = initialize_Lean_Meta_DiscrTree_Basic(builtin);
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
