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
lean_object* v_vs_283_; lean_object* v_children_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_332_; 
v_vs_283_ = lean_ctor_get(v_c_281_, 0);
v_children_284_ = lean_ctor_get(v_c_281_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_c_281_);
if (v_isSharedCheck_332_ == 0)
{
v___x_286_ = v_c_281_;
v_isShared_287_ = v_isSharedCheck_332_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_children_284_);
lean_inc(v_vs_283_);
lean_dec(v_c_281_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_332_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_array_get_size(v_todo_280_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_nat_dec_eq(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v_csize_291_; uint8_t v___x_292_; 
lean_dec_ref(v_vs_283_);
v_csize_291_ = lean_array_get_size(v_children_284_);
v___x_292_ = lean_nat_dec_eq(v_csize_291_, v___x_289_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_e_298_; lean_object* v_todo_299_; lean_object* v___y_301_; lean_object* v_first_315_; uint8_t v___x_316_; 
v___x_293_ = l_Lean_instInhabitedExpr;
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_sub(v___x_288_, v___x_294_);
v___x_296_ = lean_array_get_borrowed(v___x_293_, v_todo_280_, v___x_295_);
lean_dec(v___x_295_);
v___x_297_ = l_Lean_Meta_Sym_etaReduce(v___x_296_);
v_e_298_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_279_, v___x_297_);
v_todo_299_ = lean_array_pop(v_todo_280_);
v_first_315_ = lean_array_fget_borrowed(v_children_284_, v___x_289_);
v___x_316_ = lean_nat_dec_eq(v_csize_291_, v___x_294_);
if (v___x_316_ == 0)
{
lean_object* v_fst_317_; lean_object* v_snd_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_fst_317_ = lean_ctor_get(v_first_315_, 0);
v_snd_318_ = lean_ctor_get(v_first_315_, 1);
v___x_319_ = lean_box(0);
v___x_320_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_317_, v___x_319_);
if (v___x_320_ == 0)
{
v___y_301_ = v_result_282_;
goto v___jp_300_;
}
else
{
lean_object* v___x_321_; 
lean_inc(v_snd_318_);
lean_inc_ref(v_todo_299_);
v___x_321_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_279_, v_todo_299_, v_snd_318_, v_result_282_);
v___y_301_ = v___x_321_;
goto v___jp_300_;
}
}
else
{
lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
lean_inc(v_first_315_);
lean_del_object(v___x_286_);
lean_dec_ref(v_children_284_);
v_fst_322_ = lean_ctor_get(v_first_315_, 0);
lean_inc(v_fst_322_);
v_snd_323_ = lean_ctor_get(v_first_315_, 1);
lean_inc(v_snd_323_);
lean_dec(v_first_315_);
v___x_324_ = lean_box(0);
v___x_325_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_322_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_298_);
v___x_327_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_322_, v___x_326_);
lean_dec(v___x_326_);
lean_dec(v_fst_322_);
if (v___x_327_ == 0)
{
lean_dec(v_snd_323_);
lean_dec_ref(v_todo_299_);
lean_dec_ref(v_e_298_);
return v_result_282_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_299_, v_e_298_);
v_todo_280_ = v___x_328_;
v_c_281_ = v_snd_323_;
goto _start;
}
}
else
{
lean_dec(v_fst_322_);
lean_dec_ref(v_e_298_);
v_todo_280_ = v_todo_299_;
v_c_281_ = v_snd_323_;
goto _start;
}
}
v___jp_300_:
{
uint8_t v___x_302_; 
v___x_302_ = lean_nat_dec_lt(v___x_289_, v_csize_291_);
if (v___x_302_ == 0)
{
lean_dec_ref(v_todo_299_);
lean_dec_ref(v_e_298_);
lean_del_object(v___x_286_);
lean_dec_ref(v_children_284_);
return v___y_301_;
}
else
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_nat_sub(v_csize_291_, v___x_294_);
v___x_304_ = lean_nat_dec_le(v___x_289_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec(v___x_303_);
lean_dec_ref(v_todo_299_);
lean_dec_ref(v_e_298_);
lean_del_object(v___x_286_);
lean_dec_ref(v_children_284_);
return v___y_301_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_298_);
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v___x_306_);
lean_ctor_set(v___x_286_, 0, v___x_305_);
v___x_308_ = v___x_286_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_314_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_284_, v___x_308_, v___x_289_, v___x_303_);
lean_dec_ref(v___x_308_);
lean_dec_ref(v_children_284_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_dec_ref(v_todo_299_);
lean_dec_ref(v_e_298_);
return v___y_301_;
}
else
{
lean_object* v_val_310_; lean_object* v_snd_311_; lean_object* v___x_312_; 
v_val_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v___x_309_, 1);
v_snd_311_ = lean_ctor_get(v_val_310_, 1);
lean_inc(v_snd_311_);
lean_dec(v_val_310_);
v___x_312_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_299_, v_e_298_);
v_todo_280_ = v___x_312_;
v_c_281_ = v_snd_311_;
v_result_282_ = v___y_301_;
goto _start;
}
}
}
}
}
}
else
{
lean_del_object(v___x_286_);
lean_dec_ref(v_children_284_);
lean_dec_ref(v_todo_280_);
return v_result_282_;
}
}
else
{
lean_object* v___x_331_; 
lean_del_object(v___x_286_);
lean_dec_ref(v_children_284_);
lean_dec_ref(v_todo_280_);
v___x_331_ = l_Array_append___redArg(v_result_282_, v_vs_283_);
lean_dec_ref(v_vs_283_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_333_, lean_object* v_todo_334_, lean_object* v_c_335_, lean_object* v_result_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_333_, v_todo_334_, v_c_335_, v_result_336_);
lean_dec_ref(v_mctx_333_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_338_, lean_object* v_mctx_339_, lean_object* v_todo_340_, lean_object* v_c_341_, lean_object* v_result_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_339_, v_todo_340_, v_c_341_, v_result_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_344_, lean_object* v_mctx_345_, lean_object* v_todo_346_, lean_object* v_c_347_, lean_object* v_result_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_344_, v_mctx_345_, v_todo_346_, v_c_347_, v_result_348_);
lean_dec_ref(v_mctx_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_350_, lean_object* v_as_351_, lean_object* v_k_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_351_, v_k_352_, v_x_353_, v_x_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_357_, lean_object* v_as_358_, lean_object* v_k_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_357_, v_as_358_, v_k_359_, v_x_360_, v_x_361_, v_x_362_);
lean_dec_ref(v_k_359_);
lean_dec_ref(v_as_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_i_366_, lean_object* v_k_367_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_keys_364_);
v___x_369_ = lean_nat_dec_lt(v_i_366_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_i_366_);
v___x_370_ = lean_box(0);
return v___x_370_;
}
else
{
lean_object* v_k_x27_371_; uint8_t v___x_372_; 
v_k_x27_371_ = lean_array_fget_borrowed(v_keys_364_, v_i_366_);
v___x_372_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_367_, v_k_x27_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_i_366_, v___x_373_);
lean_dec(v_i_366_);
v_i_366_ = v___x_374_;
goto _start;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_array_fget_borrowed(v_vals_365_, v_i_366_);
lean_dec(v_i_366_);
lean_inc(v___x_376_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_378_, lean_object* v_vals_379_, lean_object* v_i_380_, lean_object* v_k_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_378_, v_vals_379_, v_i_380_, v_k_381_);
lean_dec(v_k_381_);
lean_dec_ref(v_vals_379_);
lean_dec_ref(v_keys_378_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_383_, size_t v_x_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v_es_386_; lean_object* v___x_387_; size_t v___x_388_; size_t v___x_389_; lean_object* v_j_390_; lean_object* v___x_391_; 
v_es_386_ = lean_ctor_get(v_x_383_, 0);
v___x_387_ = lean_box(2);
v___x_388_ = ((size_t)31ULL);
v___x_389_ = lean_usize_land(v_x_384_, v___x_388_);
v_j_390_ = lean_usize_to_nat(v___x_389_);
v___x_391_ = lean_array_get_borrowed(v___x_387_, v_es_386_, v_j_390_);
lean_dec(v_j_390_);
switch(lean_obj_tag(v___x_391_))
{
case 0:
{
lean_object* v_key_392_; lean_object* v_val_393_; uint8_t v___x_394_; 
v_key_392_ = lean_ctor_get(v___x_391_, 0);
v_val_393_ = lean_ctor_get(v___x_391_, 1);
v___x_394_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_385_, v_key_392_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_box(0);
return v___x_395_;
}
else
{
lean_object* v___x_396_; 
lean_inc(v_val_393_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_val_393_);
return v___x_396_;
}
}
case 1:
{
lean_object* v_node_397_; size_t v___x_398_; size_t v___x_399_; 
v_node_397_ = lean_ctor_get(v___x_391_, 0);
v___x_398_ = ((size_t)5ULL);
v___x_399_ = lean_usize_shift_right(v_x_384_, v___x_398_);
v_x_383_ = v_node_397_;
v_x_384_ = v___x_399_;
goto _start;
}
default: 
{
lean_object* v___x_401_; 
v___x_401_ = lean_box(0);
return v___x_401_;
}
}
}
else
{
lean_object* v_ks_402_; lean_object* v_vs_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_ks_402_ = lean_ctor_get(v_x_383_, 0);
v_vs_403_ = lean_ctor_get(v_x_383_, 1);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_402_, v_vs_403_, v___x_404_, v_x_385_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
size_t v_x_192__boxed_409_; lean_object* v_res_410_; 
v_x_192__boxed_409_ = lean_unbox_usize(v_x_407_);
lean_dec(v_x_407_);
v_res_410_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_406_, v_x_192__boxed_409_, v_x_408_);
lean_dec(v_x_408_);
lean_dec_ref(v_x_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint64_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v___x_413_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_412_);
v___x_414_ = lean_uint64_to_usize(v___x_413_);
v___x_415_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_411_, v___x_414_, v_x_412_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_416_, v_x_417_);
lean_dec(v_x_417_);
lean_dec_ref(v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_421_, lean_object* v_d_422_, lean_object* v_e_423_){
_start:
{
lean_object* v___y_425_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_box(0);
v___x_435_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_422_, v___x_434_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(8u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___y_425_ = v___x_437_;
goto v___jp_424_;
}
else
{
lean_object* v_val_438_; lean_object* v_vs_439_; 
v_val_438_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_435_, 1);
v_vs_439_ = lean_ctor_get(v_val_438_, 0);
lean_inc_ref(v_vs_439_);
lean_dec(v_val_438_);
v___y_425_ = v_vs_439_;
goto v___jp_424_;
}
v___jp_424_:
{
lean_object* v___x_426_; lean_object* v_e_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = l_Lean_Meta_Sym_etaReduce(v_e_423_);
v_e_427_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_421_, v___x_426_);
v___x_428_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_427_);
v___x_429_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_422_, v___x_428_);
lean_dec(v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_dec_ref(v_e_427_);
return v___y_425_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_val_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_432_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_431_, v_e_427_);
v___x_433_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_421_, v___x_432_, v_val_430_, v___y_425_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_440_, lean_object* v_d_441_, lean_object* v_e_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_440_, v_d_441_, v_e_442_);
lean_dec_ref(v_e_442_);
lean_dec_ref(v_d_441_);
lean_dec_ref(v_mctx_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_444_, lean_object* v_mctx_445_, lean_object* v_d_446_, lean_object* v_e_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_445_, v_d_446_, v_e_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_449_, lean_object* v_mctx_450_, lean_object* v_d_451_, lean_object* v_e_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_449_, v_mctx_450_, v_d_451_, v_e_452_);
lean_dec_ref(v_e_452_);
lean_dec_ref(v_d_451_);
lean_dec_ref(v_mctx_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_458_, v_x_459_, v_x_460_);
lean_dec(v_x_460_);
lean_dec_ref(v_x_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, size_t v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_463_, v_x_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
size_t v_x_298__boxed_471_; lean_object* v_res_472_; 
v_x_298__boxed_471_ = lean_unbox_usize(v_x_469_);
lean_dec(v_x_469_);
v_res_472_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_467_, v_x_468_, v_x_298__boxed_471_, v_x_470_);
lean_dec(v_x_470_);
lean_dec_ref(v_x_468_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_474_, v_vals_475_, v_i_477_, v_k_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_480_, lean_object* v_keys_481_, lean_object* v_vals_482_, lean_object* v_heq_483_, lean_object* v_i_484_, lean_object* v_k_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_480_, v_keys_481_, v_vals_482_, v_heq_483_, v_i_484_, v_k_485_);
lean_dec(v_k_485_);
lean_dec_ref(v_vals_482_);
lean_dec_ref(v_keys_481_);
return v_res_486_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_487_, lean_object* v_k_488_){
_start:
{
lean_object* v_k_490_; 
switch(lean_obj_tag(v_k_488_))
{
case 4:
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_507_; 
v_a_494_ = lean_ctor_get(v_k_488_, 0);
v_a_495_ = lean_ctor_get(v_k_488_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_k_488_);
if (v_isSharedCheck_507_ == 0)
{
v___x_497_ = v_k_488_;
v_isShared_498_ = v_isSharedCheck_507_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_inc(v_a_494_);
lean_dec(v_k_488_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_507_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_zero_499_; uint8_t v_isZero_500_; 
v_zero_499_ = lean_unsigned_to_nat(0u);
v_isZero_500_ = lean_nat_dec_eq(v_a_495_, v_zero_499_);
if (v_isZero_500_ == 0)
{
lean_object* v_one_501_; lean_object* v_n_502_; lean_object* v___x_504_; 
v_one_501_ = lean_unsigned_to_nat(1u);
v_n_502_ = lean_nat_sub(v_a_495_, v_one_501_);
lean_dec(v_a_495_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v_n_502_);
v___x_504_ = v___x_497_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_n_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v_k_490_ = v___x_504_;
goto v___jp_489_;
}
}
else
{
uint8_t v___x_506_; 
lean_del_object(v___x_497_);
lean_dec(v_a_495_);
lean_dec(v_a_494_);
v___x_506_ = 0;
return v___x_506_;
}
}
}
case 3:
{
lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_521_; 
v_a_508_ = lean_ctor_get(v_k_488_, 0);
v_a_509_ = lean_ctor_get(v_k_488_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_k_488_);
if (v_isSharedCheck_521_ == 0)
{
v___x_511_ = v_k_488_;
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_inc(v_a_508_);
lean_dec(v_k_488_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_zero_513_; uint8_t v_isZero_514_; 
v_zero_513_ = lean_unsigned_to_nat(0u);
v_isZero_514_ = lean_nat_dec_eq(v_a_509_, v_zero_513_);
if (v_isZero_514_ == 0)
{
lean_object* v_one_515_; lean_object* v_n_516_; lean_object* v___x_518_; 
v_one_515_ = lean_unsigned_to_nat(1u);
v_n_516_ = lean_nat_sub(v_a_509_, v_one_515_);
lean_dec(v_a_509_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_n_516_);
v___x_518_ = v___x_511_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_508_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_n_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
v_k_490_ = v___x_518_;
goto v___jp_489_;
}
}
else
{
uint8_t v___x_520_; 
lean_del_object(v___x_511_);
lean_dec(v_a_509_);
lean_dec(v_a_508_);
v___x_520_ = 0;
return v___x_520_;
}
}
}
default: 
{
uint8_t v___x_522_; 
lean_dec(v_k_488_);
v___x_522_ = 0;
return v___x_522_;
}
}
v___jp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_487_, v_k_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
v_k_488_ = v_k_490_;
goto _start;
}
else
{
uint8_t v___x_493_; 
lean_dec_ref_known(v___x_491_, 1);
lean_dec(v_k_490_);
v___x_493_ = 1;
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_523_, lean_object* v_k_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_523_, v_k_524_);
lean_dec_ref(v_d_523_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_527_, lean_object* v_d_528_, lean_object* v_k_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_528_, v_k_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_531_, lean_object* v_d_532_, lean_object* v_k_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_531_, v_d_532_, v_k_533_);
lean_dec_ref(v_d_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_536_, size_t v_sz_537_, size_t v_i_538_, lean_object* v_bs_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_usize_dec_lt(v_i_538_, v_sz_537_);
if (v___x_540_ == 0)
{
lean_dec(v_numExtra_536_);
return v_bs_539_;
}
else
{
lean_object* v_v_541_; lean_object* v___x_542_; lean_object* v_bs_x27_543_; lean_object* v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; 
v_v_541_ = lean_array_uget(v_bs_539_, v_i_538_);
v___x_542_ = lean_unsigned_to_nat(0u);
v_bs_x27_543_ = lean_array_uset(v_bs_539_, v_i_538_, v___x_542_);
lean_inc(v_numExtra_536_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_v_541_);
lean_ctor_set(v___x_544_, 1, v_numExtra_536_);
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_add(v_i_538_, v___x_545_);
v___x_547_ = lean_array_uset(v_bs_x27_543_, v_i_538_, v___x_544_);
v_i_538_ = v___x_546_;
v_bs_539_ = v___x_547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_549_, lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_bs_552_){
_start:
{
size_t v_sz_boxed_553_; size_t v_i_boxed_554_; lean_object* v_res_555_; 
v_sz_boxed_553_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_549_, v_sz_boxed_553_, v_i_boxed_554_, v_bs_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_556_, lean_object* v_d_557_, lean_object* v_e_558_, lean_object* v_numExtra_559_, lean_object* v_result_560_){
_start:
{
lean_object* v___x_561_; size_t v_sz_562_; size_t v___x_563_; lean_object* v___x_564_; lean_object* v_result_565_; lean_object* v_e_566_; uint8_t v___x_567_; 
v___x_561_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_556_, v_d_557_, v_e_558_);
v_sz_562_ = lean_array_size(v___x_561_);
v___x_563_ = ((size_t)0ULL);
lean_inc(v_numExtra_559_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_559_, v_sz_562_, v___x_563_, v___x_561_);
v_result_565_ = l_Array_append___redArg(v_result_560_, v___x_564_);
lean_dec_ref(v___x_564_);
v_e_566_ = l_Lean_Expr_consumeMData(v_e_558_);
lean_dec_ref(v_e_558_);
v___x_567_ = l_Lean_Expr_isApp(v_e_566_);
if (v___x_567_ == 0)
{
lean_dec_ref(v_e_566_);
lean_dec(v_numExtra_559_);
return v_result_565_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_Expr_appFn_x21(v_e_566_);
lean_dec_ref(v_e_566_);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_numExtra_559_, v___x_569_);
lean_dec(v_numExtra_559_);
v_e_558_ = v___x_568_;
v_numExtra_559_ = v___x_570_;
v_result_560_ = v_result_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_572_, lean_object* v_d_573_, lean_object* v_e_574_, lean_object* v_numExtra_575_, lean_object* v_result_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_572_, v_d_573_, v_e_574_, v_numExtra_575_, v_result_576_);
lean_dec_ref(v_d_573_);
lean_dec_ref(v_mctx_572_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_578_, lean_object* v_mctx_579_, lean_object* v_d_580_, lean_object* v_e_581_, lean_object* v_numExtra_582_, lean_object* v_result_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_579_, v_d_580_, v_e_581_, v_numExtra_582_, v_result_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_585_, lean_object* v_mctx_586_, lean_object* v_d_587_, lean_object* v_e_588_, lean_object* v_numExtra_589_, lean_object* v_result_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_585_, v_mctx_586_, v_d_587_, v_e_588_, v_numExtra_589_, v_result_590_);
lean_dec_ref(v_d_587_);
lean_dec_ref(v_mctx_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_592_, lean_object* v_numExtra_593_, size_t v_sz_594_, size_t v_i_595_, lean_object* v_bs_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_593_, v_sz_594_, v_i_595_, v_bs_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_598_, lean_object* v_numExtra_599_, lean_object* v_sz_600_, lean_object* v_i_601_, lean_object* v_bs_602_){
_start:
{
size_t v_sz_boxed_603_; size_t v_i_boxed_604_; lean_object* v_res_605_; 
v_sz_boxed_603_ = lean_unbox_usize(v_sz_600_);
lean_dec(v_sz_600_);
v_i_boxed_604_ = lean_unbox_usize(v_i_601_);
lean_dec(v_i_601_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_598_, v_numExtra_599_, v_sz_boxed_603_, v_i_boxed_604_, v_bs_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_606_, size_t v_i_607_, lean_object* v_bs_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_lt(v_i_607_, v_sz_606_);
if (v___x_609_ == 0)
{
return v_bs_608_;
}
else
{
lean_object* v_v_610_; lean_object* v___x_611_; lean_object* v_bs_x27_612_; lean_object* v___x_613_; size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v_v_610_ = lean_array_uget(v_bs_608_, v_i_607_);
v___x_611_ = lean_unsigned_to_nat(0u);
v_bs_x27_612_ = lean_array_uset(v_bs_608_, v_i_607_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v_v_610_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_607_, v___x_614_);
v___x_616_ = lean_array_uset(v_bs_x27_612_, v_i_607_, v___x_613_);
v_i_607_ = v___x_615_;
v_bs_608_ = v___x_616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_618_, lean_object* v_i_619_, lean_object* v_bs_620_){
_start:
{
size_t v_sz_boxed_621_; size_t v_i_boxed_622_; lean_object* v_res_623_; 
v_sz_boxed_621_ = lean_unbox_usize(v_sz_618_);
lean_dec(v_sz_618_);
v_i_boxed_622_ = lean_unbox_usize(v_i_619_);
lean_dec(v_i_619_);
v_res_623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_621_, v_i_boxed_622_, v_bs_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_624_, lean_object* v_d_625_, lean_object* v_e_626_){
_start:
{
lean_object* v___x_627_; lean_object* v_e_628_; lean_object* v_e_629_; lean_object* v_result_630_; size_t v_sz_631_; size_t v___x_632_; lean_object* v_result_633_; uint8_t v___x_634_; 
v___x_627_ = l_Lean_Meta_Sym_etaReduce(v_e_626_);
v_e_628_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_624_, v___x_627_);
v_e_629_ = l_Lean_Expr_consumeMData(v_e_628_);
lean_dec_ref(v_e_628_);
v_result_630_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_624_, v_d_625_, v_e_629_);
v_sz_631_ = lean_array_size(v_result_630_);
v___x_632_ = ((size_t)0ULL);
v_result_633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_631_, v___x_632_, v_result_630_);
v___x_634_ = l_Lean_Expr_isApp(v_e_629_);
if (v___x_634_ == 0)
{
lean_dec_ref(v_e_629_);
return v_result_633_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_629_);
v___x_636_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_625_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec_ref(v_e_629_);
return v_result_633_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = l_Lean_Expr_appFn_x21(v_e_629_);
lean_dec_ref(v_e_629_);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_624_, v_d_625_, v___x_637_, v___x_638_, v_result_633_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_640_, lean_object* v_d_641_, lean_object* v_e_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_640_, v_d_641_, v_e_642_);
lean_dec_ref(v_e_642_);
lean_dec_ref(v_d_641_);
lean_dec_ref(v_mctx_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_644_, lean_object* v_mctx_645_, lean_object* v_d_646_, lean_object* v_e_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_645_, v_d_646_, v_e_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_649_, lean_object* v_mctx_650_, lean_object* v_d_651_, lean_object* v_e_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_649_, v_mctx_650_, v_d_651_, v_e_652_);
lean_dec_ref(v_e_652_);
lean_dec_ref(v_d_651_);
lean_dec_ref(v_mctx_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_654_, size_t v_sz_655_, size_t v_i_656_, lean_object* v_bs_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_655_, v_i_656_, v_bs_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_659_, lean_object* v_sz_660_, lean_object* v_i_661_, lean_object* v_bs_662_){
_start:
{
size_t v_sz_boxed_663_; size_t v_i_boxed_664_; lean_object* v_res_665_; 
v_sz_boxed_663_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_664_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_659_, v_sz_boxed_663_, v_i_boxed_664_, v_bs_662_);
return v_res_665_;
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
