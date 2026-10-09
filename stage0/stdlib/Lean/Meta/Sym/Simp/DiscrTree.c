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
uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(lean_object* v_infos_1_, lean_object* v_i_2_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1_ = stack[0].m_obj;
lean_object* v_i_2_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(v_infos_1_, v_i_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg___boxed(lean_object* v_infos_9_, lean_object* v_i_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(v_infos_9_, v_i_10_);
lean_dec(v_i_10_);
lean_dec_ref(v_infos_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(lean_object* v_e_13_, lean_object* v_todo_14_){
_start:
{
if (lean_obj_tag(v_e_13_) == 5)
{
lean_object* v_fn_15_; lean_object* v_arg_16_; lean_object* v___x_17_; 
v_fn_15_ = lean_ctor_get(v_e_13_, 0);
lean_inc_ref(v_fn_15_);
v_arg_16_ = lean_ctor_get(v_e_13_, 1);
lean_inc_ref(v_arg_16_);
lean_dec_ref_known(v_e_13_, 2);
v___x_17_ = lean_array_push(v_todo_14_, v_arg_16_);
v_e_13_ = v_fn_15_;
v_todo_14_ = v___x_17_;
goto _start;
}
else
{
lean_dec_ref(v_e_13_);
return v_todo_14_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0(void){
_start:
{
lean_object* v___x_19_; lean_object* v_dummyBVar_20_; 
v___x_19_ = lean_unsigned_to_nat(1000000u);
v_dummyBVar_20_ = l_Lean_Expr_bvar___override(v___x_19_);
return v_dummyBVar_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(lean_object* v_infos_21_, lean_object* v_i_22_, lean_object* v_e_23_, lean_object* v_todo_24_){
_start:
{
if (lean_obj_tag(v_e_23_) == 5)
{
lean_object* v_fn_25_; lean_object* v_arg_26_; uint8_t v___x_27_; 
v_fn_25_ = lean_ctor_get(v_e_23_, 0);
lean_inc_ref(v_fn_25_);
v_arg_26_ = lean_ctor_get(v_e_23_, 1);
lean_inc_ref(v_arg_26_);
lean_dec_ref_known(v_e_23_, 2);
v___x_27_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_ignoreArg(v_infos_21_, v_i_22_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_sub(v_i_22_, v___x_28_);
lean_dec(v_i_22_);
v___x_30_ = lean_array_push(v_todo_24_, v_arg_26_);
v_i_22_ = v___x_29_;
v_e_23_ = v_fn_25_;
v_todo_24_ = v___x_30_;
goto _start;
}
else
{
lean_object* v_dummyBVar_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec_ref(v_arg_26_);
v_dummyBVar_32_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0, &l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___closed__0);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_sub(v_i_22_, v___x_33_);
lean_dec(v_i_22_);
v___x_35_ = lean_array_push(v_todo_24_, v_dummyBVar_32_);
v_i_22_ = v___x_34_;
v_e_23_ = v_fn_25_;
v_todo_24_ = v___x_35_;
goto _start;
}
}
else
{
lean_dec_ref(v_e_23_);
lean_dec(v_i_22_);
return v_todo_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo___boxed(lean_object* v_infos_37_, lean_object* v_i_38_, lean_object* v_e_39_, lean_object* v_todo_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(v_infos_37_, v_i_38_, v_e_39_, v_todo_40_);
lean_dec_ref(v_infos_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(lean_object* v_a_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
else
{
lean_object* v_key_45_; lean_object* v_value_46_; lean_object* v_tail_47_; uint8_t v___x_48_; 
v_key_45_ = lean_ctor_get(v_x_43_, 0);
v_value_46_ = lean_ctor_get(v_x_43_, 1);
v_tail_47_ = lean_ctor_get(v_x_43_, 2);
v___x_48_ = lean_name_eq(v_key_45_, v_a_42_);
if (v___x_48_ == 0)
{
v_x_43_ = v_tail_47_;
goto _start;
}
else
{
lean_object* v___x_50_; 
lean_inc(v_value_46_);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v_value_46_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg___boxed(lean_object* v_a_51_, lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_51_, v_x_52_);
lean_dec(v_x_52_);
lean_dec(v_a_51_);
return v_res_53_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(uint8_t v_root_54_, lean_object* v_fnInfos_55_, lean_object* v_todo_56_, lean_object* v_e_57_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_57_);
if (v___x_61_ == 0)
{
lean_object* v_fn_62_; 
v_fn_62_ = l_Lean_Expr_getAppFn(v_e_57_);
switch(lean_obj_tag(v_fn_62_))
{
case 9:
{
lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec_ref(v_e_57_);
v_a_63_ = lean_ctor_get(v_fn_62_, 0);
lean_inc_ref(v_a_63_);
lean_dec_ref_known(v_fn_62_, 1);
v___x_64_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_64_, 0, v_a_63_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v_todo_56_);
return v___x_65_;
}
case 0:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec_ref_known(v_fn_62_, 1);
lean_dec_ref(v_e_57_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_todo_56_);
return v___x_67_;
}
case 7:
{
lean_object* v_binderType_68_; lean_object* v_body_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref(v_e_57_);
v_binderType_68_ = lean_ctor_get(v_fn_62_, 1);
lean_inc_ref(v_binderType_68_);
v_body_69_ = lean_ctor_get(v_fn_62_, 2);
lean_inc_ref(v_body_69_);
lean_dec_ref_known(v_fn_62_, 3);
v___x_70_ = lean_box(5);
v___x_71_ = lean_array_push(v_todo_56_, v_body_69_);
v___x_72_ = lean_array_push(v___x_71_, v_binderType_68_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_70_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
case 4:
{
lean_object* v_declName_74_; lean_object* v___y_76_; lean_object* v___y_77_; uint8_t v___y_81_; 
v_declName_74_ = lean_ctor_get(v_fn_62_, 0);
lean_inc(v_declName_74_);
lean_dec_ref_known(v_fn_62_, 2);
if (v_root_54_ == 0)
{
goto v___jp_89_;
}
else
{
if (v___x_61_ == 0)
{
v___y_81_ = v___x_61_;
goto v___jp_80_;
}
else
{
goto v___jp_89_;
}
}
v___jp_75_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_78_, 0, v_declName_74_);
lean_ctor_set(v___x_78_, 1, v___y_76_);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___y_77_);
return v___x_79_;
}
v___jp_80_:
{
if (v___y_81_ == 0)
{
lean_object* v_numArgs_82_; lean_object* v___x_83_; 
v_numArgs_82_ = l_Lean_Expr_getAppNumArgs(v_e_57_);
v___x_83_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_declName_74_, v_fnInfos_55_);
if (lean_obj_tag(v___x_83_) == 1)
{
lean_object* v_val_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_val_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_val_84_);
lean_dec_ref_known(v___x_83_, 1);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_sub(v_numArgs_82_, v___x_85_);
v___x_87_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsUsingInfo(v_val_84_, v___x_86_, v_e_57_, v_todo_56_);
lean_dec(v_val_84_);
v___y_76_ = v_numArgs_82_;
v___y_77_ = v___x_87_;
goto v___jp_75_;
}
else
{
lean_object* v___x_88_; 
lean_dec(v___x_83_);
v___x_88_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_57_, v_todo_56_);
v___y_76_ = v_numArgs_82_;
v___y_77_ = v___x_88_;
goto v___jp_75_;
}
}
else
{
lean_dec(v_declName_74_);
lean_dec_ref(v_e_57_);
goto v___jp_58_;
}
}
v___jp_89_:
{
uint8_t v___x_90_; 
lean_inc_ref(v_e_57_);
v___x_90_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_74_, v_e_57_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
lean_inc_ref(v_e_57_);
v___x_91_ = l_Lean_Meta_Sym_isQuasiOffset(v_e_57_);
v___y_81_ = v___x_91_;
goto v___jp_80_;
}
else
{
lean_dec(v_declName_74_);
lean_dec_ref(v_e_57_);
goto v___jp_58_;
}
}
}
case 1:
{
lean_object* v_fvarId_92_; lean_object* v_numArgs_93_; lean_object* v_todo_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_fvarId_92_ = lean_ctor_get(v_fn_62_, 0);
lean_inc(v_fvarId_92_);
lean_dec_ref_known(v_fn_62_, 1);
v_numArgs_93_ = l_Lean_Expr_getAppNumArgs(v_e_57_);
v_todo_94_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushAllArgs(v_e_57_, v_todo_56_);
v___x_95_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_95_, 0, v_fvarId_92_);
lean_ctor_set(v___x_95_, 1, v_numArgs_93_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_todo_94_);
return v___x_96_;
}
default: 
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec_ref(v_fn_62_);
lean_dec_ref(v_e_57_);
v___x_97_ = lean_box(1);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v_todo_56_);
return v___x_98_;
}
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec_ref(v_e_57_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_todo_56_);
return v___x_100_;
}
v___jp_58_:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(0);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v_todo_56_);
return v___x_60_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_root_54_ = stack[0].m_num;
lean_object* v_fnInfos_55_ = stack[1].m_obj;
lean_object* v_todo_56_ = stack[2].m_obj;
lean_object* v_e_57_ = stack[3].m_obj;
lean_object* v_res_101_;
v_res_101_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_54_, v_fnInfos_55_, v_todo_56_, v_e_57_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs___boxed(lean_object* v_root_102_, lean_object* v_fnInfos_103_, lean_object* v_todo_104_, lean_object* v_e_105_){
_start:
{
uint8_t v_root_boxed_106_; lean_object* v_res_107_; 
v_root_boxed_106_ = lean_unbox(v_root_102_);
v_res_107_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_boxed_106_, v_fnInfos_103_, v_todo_104_, v_e_105_);
lean_dec(v_fnInfos_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(lean_object* v_00_u03b2_108_, lean_object* v_a_109_, lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___redArg(v_a_109_, v_x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0___boxed(lean_object* v_00_u03b2_112_, lean_object* v_a_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_AssocList_find_x3f___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs_spec__0(v_00_u03b2_112_, v_a_113_, v_x_114_);
lean_dec(v_x_114_);
lean_dec(v_a_113_);
return v_res_115_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(uint8_t v_root_116_, lean_object* v_fnInfos_117_, lean_object* v_todo_118_, lean_object* v_keys_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_array_get_size(v_todo_118_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v_e_126_; lean_object* v_todo_127_; lean_object* v___x_128_; lean_object* v_fst_129_; lean_object* v_snd_130_; lean_object* v___x_131_; 
v___x_123_ = l_Lean_instInhabitedExpr;
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_sub(v___x_120_, v___x_124_);
v_e_126_ = lean_array_get(v___x_123_, v_todo_118_, v___x_125_);
lean_dec(v___x_125_);
v_todo_127_ = lean_array_pop(v_todo_118_);
v___x_128_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgs(v_root_116_, v_fnInfos_117_, v_todo_127_, v_e_126_);
v_fst_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_fst_129_);
v_snd_130_ = lean_ctor_get(v___x_128_, 1);
lean_inc(v_snd_130_);
lean_dec_ref(v___x_128_);
v___x_131_ = lean_array_push(v_keys_119_, v_fst_129_);
v_root_116_ = v___x_122_;
v_todo_118_ = v_snd_130_;
v_keys_119_ = v___x_131_;
goto _start;
}
else
{
lean_dec_ref(v_todo_118_);
return v_keys_119_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux_0interp(lean_interpreter_value* stack)
{
uint8_t v_root_116_ = stack[0].m_num;
lean_object* v_fnInfos_117_ = stack[1].m_obj;
lean_object* v_todo_118_ = stack[2].m_obj;
lean_object* v_keys_119_ = stack[3].m_obj;
lean_object* v_res_133_;
v_res_133_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v_root_116_, v_fnInfos_117_, v_todo_118_, v_keys_119_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux___boxed(lean_object* v_root_134_, lean_object* v_fnInfos_135_, lean_object* v_todo_136_, lean_object* v_keys_137_){
_start:
{
uint8_t v_root_boxed_138_; lean_object* v_res_139_; 
v_root_boxed_138_ = lean_unbox(v_root_134_);
v_res_139_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v_root_boxed_138_, v_fnInfos_135_, v_todo_136_, v_keys_137_);
lean_dec(v_fnInfos_135_);
return v_res_139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_initCapacity(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_unsigned_to_nat(8u);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(lean_object* v_p_141_){
_start:
{
lean_object* v_pattern_142_; lean_object* v_fnInfos_143_; lean_object* v___x_144_; lean_object* v_todo_145_; uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_pattern_142_ = lean_ctor_get(v_p_141_, 3);
lean_inc_ref(v_pattern_142_);
v_fnInfos_143_ = lean_ctor_get(v_p_141_, 4);
lean_inc(v_fnInfos_143_);
lean_dec_ref(v_p_141_);
v___x_144_ = lean_unsigned_to_nat(8u);
v_todo_145_ = lean_mk_empty_array_with_capacity(v___x_144_);
v___x_146_ = 1;
lean_inc_ref(v_todo_145_);
v___x_147_ = lean_array_push(v_todo_145_, v_pattern_142_);
v___x_148_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_mkPathAux(v___x_146_, v_fnInfos_143_, v___x_147_, v_todo_145_);
lean_dec(v_fnInfos_143_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern___redArg(lean_object* v_inst_149_, lean_object* v_d_150_, lean_object* v_p_151_, lean_object* v_v_152_){
_start:
{
lean_object* v_keys_153_; lean_object* v___x_154_; 
v_keys_153_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_151_);
v___x_154_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(v_inst_149_, v_d_150_, v_keys_153_, v_v_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_insertPattern(lean_object* v_00_u03b1_155_, lean_object* v_inst_156_, lean_object* v_d_157_, lean_object* v_p_158_, lean_object* v_v_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Sym_insertPattern___redArg(v_inst_156_, v_d_157_, v_p_158_, v_v_159_);
return v___x_160_;
}
}
uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_fst_163_; lean_object* v_fst_164_; uint8_t v___x_165_; 
v_fst_163_ = lean_ctor_get(v_a_161_, 0);
v_fst_164_ = lean_ctor_get(v_b_162_, 0);
v___x_165_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_163_, v_fst_164_);
return v___x_165_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_161_ = stack[0].m_obj;
lean_object* v_b_162_ = stack[1].m_obj;
uint8_t v_res_166_;
v_res_166_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_161_, v_b_162_);
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0___boxed(lean_object* v_a_167_, lean_object* v_b_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_167_, v_b_168_);
lean_dec_ref(v_b_168_);
lean_dec_ref(v_a_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(lean_object* v_cs_177_, lean_object* v_k_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_array_get_size(v_cs_177_);
v___x_181_ = lean_nat_dec_lt(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec(v_k_178_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_sub(v___x_180_, v___x_183_);
v___x_185_ = lean_nat_dec_le(v___x_179_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_dec(v___x_184_);
lean_dec(v_k_178_);
v___x_186_ = lean_box(0);
return v___x_186_;
}
else
{
lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___f_187_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_k_178_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_191_ = l_Array_binSearchAux___redArg(v___f_187_, v___x_190_, v_cs_177_, v___x_189_, v___x_179_, v___x_184_);
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___boxed(lean_object* v_cs_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg(v_cs_192_, v_k_193_);
lean_dec_ref(v_cs_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(lean_object* v_00_u03b1_195_, lean_object* v_cs_196_, lean_object* v_k_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = lean_array_get_size(v_cs_196_);
v___x_200_ = lean_nat_dec_lt(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec(v_k_197_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_sub(v___x_199_, v___x_202_);
v___x_204_ = lean_nat_dec_le(v___x_198_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v___x_203_);
lean_dec(v_k_197_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___f_206_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__0));
v___x_207_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v_k_197_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__3));
v___x_210_ = l_Array_binSearchAux___redArg(v___f_206_, v___x_209_, v_cs_196_, v___x_208_, v___x_198_, v___x_203_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___boxed(lean_object* v_00_u03b1_211_, lean_object* v_cs_212_, lean_object* v_k_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f(v_00_u03b1_211_, v_cs_212_, v_k_213_);
lean_dec_ref(v_cs_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(lean_object* v_e_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Expr_getAppFn_x27(v_e_215_);
switch(lean_obj_tag(v___x_216_))
{
case 9:
{
lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_ref(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_218_, 0, v_a_217_);
return v___x_218_;
}
case 4:
{
lean_object* v_declName_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_declName_219_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_declName_219_);
lean_dec_ref_known(v___x_216_, 2);
v___x_220_ = l_Lean_Expr_getAppNumArgs_x27(v_e_215_);
v___x_221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_221_, 0, v_declName_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
case 1:
{
lean_object* v_fvarId_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_fvarId_222_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_fvarId_222_);
lean_dec_ref_known(v___x_216_, 1);
v___x_223_ = l_Lean_Expr_getAppNumArgs_x27(v_e_215_);
v___x_224_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_224_, 0, v_fvarId_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
case 7:
{
lean_object* v___x_225_; 
lean_dec_ref_known(v___x_216_, 3);
v___x_225_ = lean_box(5);
return v___x_225_;
}
default: 
{
lean_object* v___x_226_; 
lean_dec_ref(v___x_216_);
v___x_226_ = lean_box(1);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey___boxed(lean_object* v_e_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_227_);
lean_dec_ref(v_e_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(lean_object* v_mctx_229_, lean_object* v_e_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = l_Lean_Expr_hasExprMVar(v_e_230_);
if (v___x_231_ == 0)
{
return v_e_230_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Expr_getAppFn(v_e_230_);
if (lean_obj_tag(v___x_232_) == 2)
{
lean_object* v_mvarId_233_; lean_object* v___x_234_; 
v_mvarId_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_mvarId_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_229_, v_mvarId_233_);
lean_dec(v_mvarId_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
return v_e_230_;
}
else
{
lean_object* v_val_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v_val_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = l_Lean_Expr_getAppNumArgs(v_e_230_);
v___x_237_ = lean_mk_empty_array_with_capacity(v___x_236_);
lean_dec(v___x_236_);
v___x_238_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_230_, v___x_237_);
v___x_239_ = 0;
v___x_240_ = l_Lean_Expr_betaRev(v_val_235_, v___x_238_, v___x_239_, v___x_239_);
lean_dec_ref(v___x_238_);
v_e_230_ = v___x_240_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_232_);
return v_e_230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars___boxed(lean_object* v_mctx_242_, lean_object* v_e_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_242_, v_e_243_);
lean_dec_ref(v_mctx_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object* v_todo_245_, lean_object* v_e_246_){
_start:
{
switch(lean_obj_tag(v_e_246_))
{
case 5:
{
lean_object* v_fn_247_; lean_object* v_arg_248_; lean_object* v___x_249_; 
v_fn_247_ = lean_ctor_get(v_e_246_, 0);
lean_inc_ref(v_fn_247_);
v_arg_248_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_arg_248_);
lean_dec_ref_known(v_e_246_, 2);
v___x_249_ = lean_array_push(v_todo_245_, v_arg_248_);
v_todo_245_ = v___x_249_;
v_e_246_ = v_fn_247_;
goto _start;
}
case 7:
{
lean_object* v_binderType_251_; lean_object* v_body_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_binderType_251_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_binderType_251_);
v_body_252_ = lean_ctor_get(v_e_246_, 2);
lean_inc_ref(v_body_252_);
lean_dec_ref_known(v_e_246_, 3);
v___x_253_ = lean_array_push(v_todo_245_, v_body_252_);
v___x_254_ = lean_array_push(v___x_253_, v_binderType_251_);
return v___x_254_;
}
case 10:
{
lean_object* v_expr_255_; 
v_expr_255_ = lean_ctor_get(v_e_246_, 1);
lean_inc_ref(v_expr_255_);
lean_dec_ref_known(v_e_246_, 2);
v_e_246_ = v_expr_255_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_246_);
return v_todo_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_as_257_, lean_object* v_k_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_m_263_; lean_object* v_a_264_; uint8_t v___x_265_; 
v___x_261_ = lean_nat_add(v_x_259_, v_x_260_);
v___x_262_ = lean_unsigned_to_nat(1u);
v_m_263_ = lean_nat_shiftr(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
v_a_264_ = lean_array_fget_borrowed(v_as_257_, v_m_263_);
v___x_265_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_264_, v_k_258_);
if (v___x_265_ == 0)
{
uint8_t v___x_266_; 
lean_dec(v_x_260_);
v___x_266_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_258_, v_a_264_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_dec(v_m_263_);
lean_dec(v_x_259_);
lean_inc(v_a_264_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_a_264_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_nat_dec_eq(v_m_263_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_nat_sub(v_m_263_, v___x_262_);
lean_dec(v_m_263_);
v___x_271_ = lean_nat_dec_lt(v___x_270_, v_x_259_);
if (v___x_271_ == 0)
{
v_x_260_ = v___x_270_;
goto _start;
}
else
{
lean_object* v___x_273_; 
lean_dec(v___x_270_);
lean_dec(v_x_259_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
}
else
{
lean_object* v___x_274_; 
lean_dec(v_m_263_);
lean_dec(v_x_259_);
v___x_274_ = lean_box(0);
return v___x_274_;
}
}
}
else
{
lean_object* v___x_275_; uint8_t v___x_276_; 
lean_dec(v_x_259_);
v___x_275_ = lean_nat_add(v_m_263_, v___x_262_);
lean_dec(v_m_263_);
v___x_276_ = lean_nat_dec_le(v___x_275_, v_x_260_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v___x_275_);
lean_dec(v_x_260_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
v_x_259_ = v___x_275_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_279_, lean_object* v_k_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_279_, v_k_280_, v_x_281_, v_x_282_);
lean_dec_ref(v_k_280_);
lean_dec_ref(v_as_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_mctx_284_, lean_object* v_todo_285_, lean_object* v_c_286_, lean_object* v_result_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_c_286_) == 0)
{
lean_object* v_key_289_; lean_object* v_child_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_key_289_ = lean_ctor_get(v_c_286_, 0);
lean_inc(v_key_289_);
v_child_290_ = lean_ctor_get(v_c_286_, 1);
lean_inc_ref(v_child_290_);
lean_dec_ref_known(v_c_286_, 2);
v___x_291_ = lean_array_get_size(v_todo_285_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_nat_dec_eq(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_todo_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_sub(v___x_291_, v___x_294_);
v___x_296_ = lean_array_get(v___x_288_, v_todo_285_, v___x_295_);
lean_dec(v___x_295_);
v_todo_297_ = lean_array_pop(v_todo_285_);
v___x_298_ = lean_box(0);
v___x_299_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_289_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v_e_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_300_ = l_Lean_Meta_Sym_etaReduce(v___x_296_);
lean_dec(v___x_296_);
v_e_301_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_284_, v___x_300_);
v___x_302_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_301_);
v___x_303_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_289_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v_key_289_);
if (v___x_303_ == 0)
{
lean_dec_ref(v_e_301_);
lean_dec_ref(v_todo_297_);
lean_dec_ref(v_child_290_);
return v_result_287_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_297_, v_e_301_);
v_todo_285_ = v___x_304_;
v_c_286_ = v_child_290_;
goto _start;
}
}
else
{
lean_dec(v___x_296_);
lean_dec(v_key_289_);
v_todo_285_ = v_todo_297_;
v_c_286_ = v_child_290_;
goto _start;
}
}
else
{
lean_dec_ref(v_child_290_);
lean_dec(v_key_289_);
lean_dec_ref(v_todo_285_);
return v_result_287_;
}
}
else
{
lean_object* v_vs_307_; lean_object* v_children_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_vs_307_ = lean_ctor_get(v_c_286_, 0);
lean_inc_ref(v_vs_307_);
v_children_308_ = lean_ctor_get(v_c_286_, 1);
lean_inc_ref(v_children_308_);
lean_dec_ref_known(v_c_286_, 2);
v___x_309_ = lean_array_get_size(v_todo_285_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_nat_dec_eq(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v_csize_312_; uint8_t v___x_313_; 
lean_dec_ref(v_vs_307_);
v_csize_312_ = lean_array_get_size(v_children_308_);
v___x_313_ = lean_nat_dec_eq(v_csize_312_, v___x_310_);
if (v___x_313_ == 0)
{
lean_object* v_first_314_; lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_344_; 
v_first_314_ = lean_array_fget(v_children_308_, v___x_310_);
v_fst_315_ = lean_ctor_get(v_first_314_, 0);
v_snd_316_ = lean_ctor_get(v_first_314_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_first_314_);
if (v_isSharedCheck_344_ == 0)
{
v___x_318_ = v_first_314_;
v_isShared_319_ = v_isSharedCheck_344_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_snd_316_);
lean_inc(v_fst_315_);
lean_dec(v_first_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_344_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_e_324_; lean_object* v_todo_325_; lean_object* v___y_327_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_sub(v___x_309_, v___x_320_);
v___x_322_ = lean_array_get_borrowed(v___x_288_, v_todo_285_, v___x_321_);
lean_dec(v___x_321_);
v___x_323_ = l_Lean_Meta_Sym_etaReduce(v___x_322_);
v_e_324_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_284_, v___x_323_);
v_todo_325_ = lean_array_pop(v_todo_285_);
v___x_341_ = lean_box(0);
v___x_342_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_315_, v___x_341_);
lean_dec(v_fst_315_);
if (v___x_342_ == 0)
{
lean_dec(v_snd_316_);
v___y_327_ = v_result_287_;
goto v___jp_326_;
}
else
{
lean_object* v___x_343_; 
lean_inc_ref(v_todo_325_);
v___x_343_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_284_, v_todo_325_, v_snd_316_, v_result_287_);
v___y_327_ = v___x_343_;
goto v___jp_326_;
}
v___jp_326_:
{
uint8_t v___x_328_; 
v___x_328_ = lean_nat_dec_lt(v___x_310_, v_csize_312_);
if (v___x_328_ == 0)
{
lean_dec_ref(v_todo_325_);
lean_dec_ref(v_e_324_);
lean_del_object(v___x_318_);
lean_dec_ref(v_children_308_);
return v___y_327_;
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_nat_sub(v_csize_312_, v___x_320_);
v___x_330_ = lean_nat_dec_le(v___x_310_, v___x_329_);
if (v___x_330_ == 0)
{
lean_dec(v___x_329_);
lean_dec_ref(v_todo_325_);
lean_dec_ref(v_e_324_);
lean_del_object(v___x_318_);
lean_dec_ref(v_children_308_);
return v___y_327_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_331_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_324_);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_332_);
lean_ctor_set(v___x_318_, 0, v___x_331_);
v___x_334_ = v___x_318_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_332_);
v___x_334_ = v_reuseFailAlloc_340_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; 
v___x_335_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_308_, v___x_334_, v___x_310_, v___x_329_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_children_308_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_dec_ref(v_todo_325_);
lean_dec_ref(v_e_324_);
return v___y_327_;
}
else
{
lean_object* v_val_336_; lean_object* v_snd_337_; lean_object* v___x_338_; 
v_val_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v___x_335_, 1);
v_snd_337_ = lean_ctor_get(v_val_336_, 1);
lean_inc(v_snd_337_);
lean_dec(v_val_336_);
v___x_338_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_325_, v_e_324_);
v_todo_285_ = v___x_338_;
v_c_286_ = v_snd_337_;
v_result_287_ = v___y_327_;
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
lean_dec_ref(v_children_308_);
lean_dec_ref(v_todo_285_);
return v_result_287_;
}
}
else
{
lean_object* v___x_345_; 
lean_dec_ref(v_children_308_);
lean_dec_ref(v_todo_285_);
v___x_345_ = l_Array_append___redArg(v_result_287_, v_vs_307_);
lean_dec_ref(v_vs_307_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg___boxed(lean_object* v_mctx_346_, lean_object* v_todo_347_, lean_object* v_c_348_, lean_object* v_result_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_346_, v_todo_347_, v_c_348_, v_result_349_);
lean_dec_ref(v_mctx_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_351_, lean_object* v_mctx_352_, lean_object* v_todo_353_, lean_object* v_c_354_, lean_object* v_result_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_352_, v_todo_353_, v_c_354_, v_result_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___boxed(lean_object* v_00_u03b1_357_, lean_object* v_mctx_358_, lean_object* v_todo_359_, lean_object* v_c_360_, lean_object* v_result_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(v_00_u03b1_357_, v_mctx_358_, v_todo_359_, v_c_360_, v_result_361_);
lean_dec_ref(v_mctx_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_363_, lean_object* v_as_364_, lean_object* v_k_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_364_, v_k_365_, v_x_366_, v_x_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v_as_371_, lean_object* v_k_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_370_, v_as_371_, v_k_372_, v_x_373_, v_x_374_, v_x_375_);
lean_dec_ref(v_k_372_);
lean_dec_ref(v_as_371_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_377_, lean_object* v_vals_378_, lean_object* v_i_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_keys_377_);
v___x_382_ = lean_nat_dec_lt(v_i_379_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_i_379_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v_k_x27_384_; uint8_t v___x_385_; 
v_k_x27_384_ = lean_array_fget_borrowed(v_keys_377_, v_i_379_);
v___x_385_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_380_, v_k_x27_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_i_379_, v___x_386_);
lean_dec(v_i_379_);
v_i_379_ = v___x_387_;
goto _start;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_array_fget_borrowed(v_vals_378_, v_i_379_);
lean_dec(v_i_379_);
lean_inc(v___x_389_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_391_, lean_object* v_vals_392_, lean_object* v_i_393_, lean_object* v_k_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_391_, v_vals_392_, v_i_393_, v_k_394_);
lean_dec(v_k_394_);
lean_dec_ref(v_vals_392_);
lean_dec_ref(v_keys_391_);
return v_res_395_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_396_, size_t v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v_es_399_; lean_object* v___x_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v_j_403_; lean_object* v___x_404_; 
v_es_399_ = lean_ctor_get(v_x_396_, 0);
v___x_400_ = lean_box(2);
v___x_401_ = ((size_t)31ULL);
v___x_402_ = lean_usize_land(v_x_397_, v___x_401_);
v_j_403_ = lean_usize_to_nat(v___x_402_);
v___x_404_ = lean_array_get_borrowed(v___x_400_, v_es_399_, v_j_403_);
lean_dec(v_j_403_);
switch(lean_obj_tag(v___x_404_))
{
case 0:
{
lean_object* v_key_405_; lean_object* v_val_406_; uint8_t v___x_407_; 
v_key_405_ = lean_ctor_get(v___x_404_, 0);
v_val_406_ = lean_ctor_get(v___x_404_, 1);
v___x_407_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_398_, v_key_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
lean_inc(v_val_406_);
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_val_406_);
return v___x_409_;
}
}
case 1:
{
lean_object* v_node_410_; size_t v___x_411_; size_t v___x_412_; 
v_node_410_ = lean_ctor_get(v___x_404_, 0);
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_usize_shift_right(v_x_397_, v___x_411_);
v_x_396_ = v_node_410_;
v_x_397_ = v___x_412_;
goto _start;
}
default: 
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
}
else
{
lean_object* v_ks_415_; lean_object* v_vs_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_ks_415_ = lean_ctor_get(v_x_396_, 0);
v_vs_416_ = lean_ctor_get(v_x_396_, 1);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_415_, v_vs_416_, v___x_417_, v_x_398_);
return v___x_418_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_396_ = stack[0].m_obj;
size_t v_x_397_ = stack[1].m_num;
lean_object* v_x_398_ = stack[2].m_obj;
lean_object* v_res_419_;
v_res_419_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_396_, v_x_397_, v_x_398_);
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
size_t v_x_212__boxed_423_; lean_object* v_res_424_; 
v_x_212__boxed_423_ = lean_unbox_usize(v_x_421_);
lean_dec(v_x_421_);
v_res_424_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_420_, v_x_212__boxed_423_, v_x_422_);
lean_dec(v_x_422_);
lean_dec_ref(v_x_420_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
uint64_t v___x_427_; size_t v___x_428_; lean_object* v___x_429_; 
v___x_427_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_426_);
v___x_428_ = lean_uint64_to_usize(v___x_427_);
v___x_429_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_425_, v___x_428_, v_x_426_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_x_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_mctx_435_, lean_object* v_d_436_, lean_object* v_e_437_){
_start:
{
lean_object* v___y_439_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_box(0);
v___x_449_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_436_, v___x_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(8u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___y_439_ = v___x_451_;
goto v___jp_438_;
}
else
{
lean_object* v_val_452_; 
v_val_452_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v___x_449_, 1);
if (lean_obj_tag(v_val_452_) == 0)
{
lean_object* v___x_453_; 
lean_dec_ref_known(v_val_452_, 2);
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1));
v___y_439_ = v___x_453_;
goto v___jp_438_;
}
else
{
lean_object* v_vs_454_; 
v_vs_454_ = lean_ctor_get(v_val_452_, 0);
lean_inc_ref(v_vs_454_);
lean_dec_ref_known(v_val_452_, 2);
v___y_439_ = v_vs_454_;
goto v___jp_438_;
}
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v_e_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = l_Lean_Meta_Sym_etaReduce(v_e_437_);
v_e_441_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_435_, v___x_440_);
v___x_442_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_441_);
v___x_443_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_436_, v___x_442_);
lean_dec(v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_dec_ref(v_e_441_);
return v___y_439_;
}
else
{
lean_object* v_val_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_val_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_446_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_445_, v_e_441_);
v___x_447_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_mctx_435_, v___x_446_, v_val_444_, v___y_439_);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_mctx_455_, lean_object* v_d_456_, lean_object* v_e_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_455_, v_d_456_, v_e_457_);
lean_dec_ref(v_e_457_);
lean_dec_ref(v_d_456_);
lean_dec_ref(v_mctx_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_459_, lean_object* v_mctx_460_, lean_object* v_d_461_, lean_object* v_e_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_460_, v_d_461_, v_e_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_464_, lean_object* v_mctx_465_, lean_object* v_d_466_, lean_object* v_e_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_464_, v_mctx_465_, v_d_466_, v_e_467_);
lean_dec_ref(v_e_467_);
lean_dec_ref(v_d_466_);
lean_dec_ref(v_mctx_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_470_, v_x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_473_, v_x_474_, v_x_475_);
lean_dec(v_x_475_);
lean_dec_ref(v_x_474_);
return v_res_476_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, size_t v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_478_, v_x_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_478_ = stack[1].m_obj;
size_t v_x_479_ = stack[2].m_num;
lean_object* v_x_480_ = stack[3].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_box(0), v_x_478_, v_x_479_, v_x_480_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
size_t v_x_380__boxed_487_; lean_object* v_res_488_; 
v_x_380__boxed_487_ = lean_unbox_usize(v_x_485_);
lean_dec(v_x_485_);
v_res_488_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_483_, v_x_484_, v_x_380__boxed_487_, v_x_486_);
lean_dec(v_x_486_);
lean_dec_ref(v_x_484_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_489_, lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_heq_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_490_, v_vals_491_, v_i_493_, v_k_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_496_, lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_heq_499_, lean_object* v_i_500_, lean_object* v_k_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_496_, v_keys_497_, v_vals_498_, v_heq_499_, v_i_500_, v_k_501_);
lean_dec(v_k_501_);
lean_dec_ref(v_vals_498_);
lean_dec_ref(v_keys_497_);
return v_res_502_;
}
}
uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_503_, lean_object* v_k_504_){
_start:
{
lean_object* v_k_506_; 
switch(lean_obj_tag(v_k_504_))
{
case 4:
{
lean_object* v_a_510_; lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_523_; 
v_a_510_ = lean_ctor_get(v_k_504_, 0);
v_a_511_ = lean_ctor_get(v_k_504_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_k_504_);
if (v_isSharedCheck_523_ == 0)
{
v___x_513_ = v_k_504_;
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_inc(v_a_510_);
lean_dec(v_k_504_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_523_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_zero_515_; uint8_t v_isZero_516_; 
v_zero_515_ = lean_unsigned_to_nat(0u);
v_isZero_516_ = lean_nat_dec_eq(v_a_511_, v_zero_515_);
if (v_isZero_516_ == 0)
{
lean_object* v_one_517_; lean_object* v_n_518_; lean_object* v___x_520_; 
v_one_517_ = lean_unsigned_to_nat(1u);
v_n_518_ = lean_nat_sub(v_a_511_, v_one_517_);
lean_dec(v_a_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_n_518_);
v___x_520_ = v___x_513_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_510_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_n_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
v_k_506_ = v___x_520_;
goto v___jp_505_;
}
}
else
{
uint8_t v___x_522_; 
lean_del_object(v___x_513_);
lean_dec(v_a_511_);
lean_dec(v_a_510_);
v___x_522_ = 0;
return v___x_522_;
}
}
}
case 3:
{
lean_object* v_a_524_; lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_537_; 
v_a_524_ = lean_ctor_get(v_k_504_, 0);
v_a_525_ = lean_ctor_get(v_k_504_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v_k_504_);
if (v_isSharedCheck_537_ == 0)
{
v___x_527_ = v_k_504_;
v_isShared_528_ = v_isSharedCheck_537_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_inc(v_a_524_);
lean_dec(v_k_504_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_537_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_zero_529_; uint8_t v_isZero_530_; 
v_zero_529_ = lean_unsigned_to_nat(0u);
v_isZero_530_ = lean_nat_dec_eq(v_a_525_, v_zero_529_);
if (v_isZero_530_ == 0)
{
lean_object* v_one_531_; lean_object* v_n_532_; lean_object* v___x_534_; 
v_one_531_ = lean_unsigned_to_nat(1u);
v_n_532_ = lean_nat_sub(v_a_525_, v_one_531_);
lean_dec(v_a_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 1, v_n_532_);
v___x_534_ = v___x_527_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_524_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_n_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
v_k_506_ = v___x_534_;
goto v___jp_505_;
}
}
else
{
uint8_t v___x_536_; 
lean_del_object(v___x_527_);
lean_dec(v_a_525_);
lean_dec(v_a_524_);
v___x_536_ = 0;
return v___x_536_;
}
}
}
default: 
{
uint8_t v___x_538_; 
lean_dec(v_k_504_);
v___x_538_ = 0;
return v___x_538_;
}
}
v___jp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_503_, v_k_506_);
if (lean_obj_tag(v___x_507_) == 0)
{
v_k_504_ = v_k_506_;
goto _start;
}
else
{
uint8_t v___x_509_; 
lean_dec_ref_known(v___x_507_, 1);
lean_dec(v_k_506_);
v___x_509_ = 1;
return v___x_509_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_503_ = stack[0].m_obj;
lean_object* v_k_504_ = stack[1].m_obj;
uint8_t v_res_539_;
v_res_539_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_503_, v_k_504_);
stack->m_num = v_res_539_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_540_, lean_object* v_k_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_540_, v_k_541_);
lean_dec_ref(v_d_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_544_, lean_object* v_d_545_, lean_object* v_k_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_545_, v_k_546_);
return v___x_547_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_545_ = stack[1].m_obj;
lean_object* v_k_546_ = stack[2].m_obj;
uint8_t v_res_548_;
v_res_548_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_box(0), v_d_545_, v_k_546_);
stack->m_num = v_res_548_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_549_, lean_object* v_d_550_, lean_object* v_k_551_){
_start:
{
uint8_t v_res_552_; lean_object* v_r_553_; 
v_res_552_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_549_, v_d_550_, v_k_551_);
lean_dec_ref(v_d_550_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_554_, size_t v_sz_555_, size_t v_i_556_, lean_object* v_bs_557_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_lt(v_i_556_, v_sz_555_);
if (v___x_558_ == 0)
{
lean_dec(v_numExtra_554_);
return v_bs_557_;
}
else
{
lean_object* v_v_559_; lean_object* v___x_560_; lean_object* v_bs_x27_561_; lean_object* v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v_v_559_ = lean_array_uget(v_bs_557_, v_i_556_);
v___x_560_ = lean_unsigned_to_nat(0u);
v_bs_x27_561_ = lean_array_uset(v_bs_557_, v_i_556_, v___x_560_);
lean_inc(v_numExtra_554_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_v_559_);
lean_ctor_set(v___x_562_, 1, v_numExtra_554_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_add(v_i_556_, v___x_563_);
v___x_565_ = lean_array_uset(v_bs_x27_561_, v_i_556_, v___x_562_);
v_i_556_ = v___x_564_;
v_bs_557_ = v___x_565_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numExtra_554_ = stack[0].m_obj;
size_t v_sz_555_ = stack[1].m_num;
size_t v_i_556_ = stack[2].m_num;
lean_object* v_bs_557_ = stack[3].m_obj;
lean_object* v_res_567_;
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_554_, v_sz_555_, v_i_556_, v_bs_557_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_568_, lean_object* v_sz_569_, lean_object* v_i_570_, lean_object* v_bs_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_569_);
lean_dec(v_sz_569_);
v_i_boxed_573_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_568_, v_sz_boxed_572_, v_i_boxed_573_, v_bs_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_mctx_575_, lean_object* v_d_576_, lean_object* v_e_577_, lean_object* v_numExtra_578_, lean_object* v_result_579_){
_start:
{
lean_object* v___x_580_; size_t v_sz_581_; size_t v___x_582_; lean_object* v___x_583_; lean_object* v_result_584_; lean_object* v_e_585_; uint8_t v___x_586_; 
v___x_580_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_575_, v_d_576_, v_e_577_);
v_sz_581_ = lean_array_size(v___x_580_);
v___x_582_ = ((size_t)0ULL);
lean_inc(v_numExtra_578_);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_578_, v_sz_581_, v___x_582_, v___x_580_);
v_result_584_ = l_Array_append___redArg(v_result_579_, v___x_583_);
lean_dec_ref(v___x_583_);
v_e_585_ = l_Lean_Expr_consumeMData(v_e_577_);
lean_dec_ref(v_e_577_);
v___x_586_ = l_Lean_Expr_isApp(v_e_585_);
if (v___x_586_ == 0)
{
lean_dec_ref(v_e_585_);
lean_dec(v_numExtra_578_);
return v_result_584_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = l_Lean_Expr_appFn_x21(v_e_585_);
lean_dec_ref(v_e_585_);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_numExtra_578_, v___x_588_);
lean_dec(v_numExtra_578_);
v_e_577_ = v___x_587_;
v_numExtra_578_ = v___x_589_;
v_result_579_ = v_result_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_mctx_591_, lean_object* v_d_592_, lean_object* v_e_593_, lean_object* v_numExtra_594_, lean_object* v_result_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_591_, v_d_592_, v_e_593_, v_numExtra_594_, v_result_595_);
lean_dec_ref(v_d_592_);
lean_dec_ref(v_mctx_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_597_, lean_object* v_mctx_598_, lean_object* v_d_599_, lean_object* v_e_600_, lean_object* v_numExtra_601_, lean_object* v_result_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_598_, v_d_599_, v_e_600_, v_numExtra_601_, v_result_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_604_, lean_object* v_mctx_605_, lean_object* v_d_606_, lean_object* v_e_607_, lean_object* v_numExtra_608_, lean_object* v_result_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_604_, v_mctx_605_, v_d_606_, v_e_607_, v_numExtra_608_, v_result_609_);
lean_dec_ref(v_d_606_);
lean_dec_ref(v_mctx_605_);
return v_res_610_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_611_, lean_object* v_numExtra_612_, size_t v_sz_613_, size_t v_i_614_, lean_object* v_bs_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_612_, v_sz_613_, v_i_614_, v_bs_615_);
return v___x_616_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_numExtra_612_ = stack[1].m_obj;
size_t v_sz_613_ = stack[2].m_num;
size_t v_i_614_ = stack[3].m_num;
lean_object* v_bs_615_ = stack[4].m_obj;
lean_object* v_res_617_;
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_box(0), v_numExtra_612_, v_sz_613_, v_i_614_, v_bs_615_);
stack->m_obj
 = v_res_617_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_618_, lean_object* v_numExtra_619_, lean_object* v_sz_620_, lean_object* v_i_621_, lean_object* v_bs_622_){
_start:
{
size_t v_sz_boxed_623_; size_t v_i_boxed_624_; lean_object* v_res_625_; 
v_sz_boxed_623_ = lean_unbox_usize(v_sz_620_);
lean_dec(v_sz_620_);
v_i_boxed_624_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_618_, v_numExtra_619_, v_sz_boxed_623_, v_i_boxed_624_, v_bs_622_);
return v_res_625_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_626_, size_t v_i_627_, lean_object* v_bs_628_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = lean_usize_dec_lt(v_i_627_, v_sz_626_);
if (v___x_629_ == 0)
{
return v_bs_628_;
}
else
{
lean_object* v_v_630_; lean_object* v___x_631_; lean_object* v_bs_x27_632_; lean_object* v___x_633_; size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
v_v_630_ = lean_array_uget(v_bs_628_, v_i_627_);
v___x_631_ = lean_unsigned_to_nat(0u);
v_bs_x27_632_ = lean_array_uset(v_bs_628_, v_i_627_, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_v_630_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_i_627_, v___x_634_);
v___x_636_ = lean_array_uset(v_bs_x27_632_, v_i_627_, v___x_633_);
v_i_627_ = v___x_635_;
v_bs_628_ = v___x_636_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_626_ = stack[0].m_num;
size_t v_i_627_ = stack[1].m_num;
lean_object* v_bs_628_ = stack[2].m_obj;
lean_object* v_res_638_;
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_626_, v_i_627_, v_bs_628_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_639_, lean_object* v_i_640_, lean_object* v_bs_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_639_);
lean_dec(v_sz_639_);
v_i_boxed_643_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_642_, v_i_boxed_643_, v_bs_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_mctx_645_, lean_object* v_d_646_, lean_object* v_e_647_){
_start:
{
lean_object* v___x_648_; lean_object* v_e_649_; lean_object* v_e_650_; lean_object* v_result_651_; size_t v_sz_652_; size_t v___x_653_; lean_object* v_result_654_; uint8_t v___x_655_; 
v___x_648_ = l_Lean_Meta_Sym_etaReduce(v_e_647_);
v_e_649_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_resolveAssignedMVars(v_mctx_645_, v___x_648_);
v_e_650_ = l_Lean_Expr_consumeMData(v_e_649_);
lean_dec_ref(v_e_649_);
v_result_651_ = l_Lean_Meta_Sym_getMatch___redArg(v_mctx_645_, v_d_646_, v_e_650_);
v_sz_652_ = lean_array_size(v_result_651_);
v___x_653_ = ((size_t)0ULL);
v_result_654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_652_, v___x_653_, v_result_651_);
v___x_655_ = l_Lean_Expr_isApp(v_e_650_);
if (v___x_655_ == 0)
{
lean_dec_ref(v_e_650_);
return v_result_654_;
}
else
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_650_);
v___x_657_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_646_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec_ref(v_e_650_);
return v_result_654_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_Expr_appFn_x21(v_e_650_);
lean_dec_ref(v_e_650_);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_mctx_645_, v_d_646_, v___x_658_, v___x_659_, v_result_654_);
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_mctx_661_, lean_object* v_d_662_, lean_object* v_e_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_661_, v_d_662_, v_e_663_);
lean_dec_ref(v_e_663_);
lean_dec_ref(v_d_662_);
lean_dec_ref(v_mctx_661_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_665_, lean_object* v_mctx_666_, lean_object* v_d_667_, lean_object* v_e_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_666_, v_d_667_, v_e_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_670_, lean_object* v_mctx_671_, lean_object* v_d_672_, lean_object* v_e_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_670_, v_mctx_671_, v_d_672_, v_e_673_);
lean_dec_ref(v_e_673_);
lean_dec_ref(v_d_672_);
lean_dec_ref(v_mctx_671_);
return v_res_674_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_675_, size_t v_sz_676_, size_t v_i_677_, lean_object* v_bs_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_676_, v_i_677_, v_bs_678_);
return v___x_679_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_676_ = stack[1].m_num;
size_t v_i_677_ = stack[2].m_num;
lean_object* v_bs_678_ = stack[3].m_obj;
lean_object* v_res_680_;
v_res_680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_box(0), v_sz_676_, v_i_677_, v_bs_678_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_681_, lean_object* v_sz_682_, lean_object* v_i_683_, lean_object* v_bs_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_686_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_681_, v_sz_boxed_685_, v_i_boxed_686_, v_bs_684_);
return v_res_687_;
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
