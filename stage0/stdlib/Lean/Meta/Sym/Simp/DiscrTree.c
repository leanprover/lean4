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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_declName_70_; lean_object* v___y_72_; lean_object* v___y_73_; uint8_t v___y_77_; uint8_t v___x_87_; 
v_declName_70_ = lean_ctor_get(v_fn_58_, 0);
lean_inc(v_declName_70_);
lean_dec_ref_known(v_fn_58_, 2);
v___x_87_ = lean_bool_not(v_root_53_);
if (v___x_87_ == 0)
{
v___y_77_ = v___x_87_;
goto v___jp_76_;
}
else
{
uint8_t v___x_88_; 
lean_inc_ref(v_e_56_);
v___x_88_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_70_, v_e_56_);
v___y_77_ = v___x_88_;
goto v___jp_76_;
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
v___x_210_ = l_Lean_Expr_getAppFn(v_e_209_);
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
v___x_214_ = l_Lean_Expr_getAppNumArgs(v_e_209_);
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
v___x_217_ = l_Lean_Expr_getAppNumArgs(v_e_209_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object* v_todo_223_, lean_object* v_e_224_){
_start:
{
switch(lean_obj_tag(v_e_224_))
{
case 5:
{
lean_object* v_fn_225_; lean_object* v_arg_226_; lean_object* v___x_227_; 
v_fn_225_ = lean_ctor_get(v_e_224_, 0);
lean_inc_ref(v_fn_225_);
v_arg_226_ = lean_ctor_get(v_e_224_, 1);
lean_inc_ref(v_arg_226_);
lean_dec_ref_known(v_e_224_, 2);
v___x_227_ = lean_array_push(v_todo_223_, v_arg_226_);
v_todo_223_ = v___x_227_;
v_e_224_ = v_fn_225_;
goto _start;
}
case 7:
{
lean_object* v_binderType_229_; lean_object* v_body_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_binderType_229_ = lean_ctor_get(v_e_224_, 1);
lean_inc_ref(v_binderType_229_);
v_body_230_ = lean_ctor_get(v_e_224_, 2);
lean_inc_ref(v_body_230_);
lean_dec_ref_known(v_e_224_, 3);
v___x_231_ = lean_array_push(v_todo_223_, v_body_230_);
v___x_232_ = lean_array_push(v___x_231_, v_binderType_229_);
return v___x_232_;
}
default: 
{
lean_dec_ref(v_e_224_);
return v_todo_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_as_233_, lean_object* v_k_234_, lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_m_239_; lean_object* v_a_240_; uint8_t v___x_241_; 
v___x_237_ = lean_nat_add(v_x_235_, v_x_236_);
v___x_238_ = lean_unsigned_to_nat(1u);
v_m_239_ = lean_nat_shiftr(v___x_237_, v___x_238_);
lean_dec(v___x_237_);
v_a_240_ = lean_array_fget_borrowed(v_as_233_, v_m_239_);
v___x_241_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_240_, v_k_234_);
if (v___x_241_ == 0)
{
uint8_t v___x_242_; 
lean_dec(v_x_236_);
v___x_242_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_234_, v_a_240_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec(v_m_239_);
lean_dec(v_x_235_);
lean_inc(v_a_240_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_a_240_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v_m_239_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_nat_sub(v_m_239_, v___x_238_);
lean_dec(v_m_239_);
v___x_247_ = lean_nat_dec_lt(v___x_246_, v_x_235_);
if (v___x_247_ == 0)
{
v_x_236_ = v___x_246_;
goto _start;
}
else
{
lean_object* v___x_249_; 
lean_dec(v___x_246_);
lean_dec(v_x_235_);
v___x_249_ = lean_box(0);
return v___x_249_;
}
}
else
{
lean_object* v___x_250_; 
lean_dec(v_m_239_);
lean_dec(v_x_235_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
}
}
else
{
lean_object* v___x_251_; uint8_t v___x_252_; 
lean_dec(v_x_235_);
v___x_251_ = lean_nat_add(v_m_239_, v___x_238_);
lean_dec(v_m_239_);
v___x_252_ = lean_nat_dec_le(v___x_251_, v_x_236_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v___x_251_);
lean_dec(v_x_236_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
v_x_235_ = v___x_251_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_255_, lean_object* v_k_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_255_, v_k_256_, v_x_257_, v_x_258_);
lean_dec_ref(v_k_256_);
lean_dec_ref(v_as_255_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_todo_260_, lean_object* v_c_261_, lean_object* v_result_262_){
_start:
{
lean_object* v_vs_263_; lean_object* v_children_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_311_; 
v_vs_263_ = lean_ctor_get(v_c_261_, 0);
v_children_264_ = lean_ctor_get(v_c_261_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_c_261_);
if (v_isSharedCheck_311_ == 0)
{
v___x_266_ = v_c_261_;
v_isShared_267_ = v_isSharedCheck_311_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_children_264_);
lean_inc(v_vs_263_);
lean_dec(v_c_261_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_311_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = lean_array_get_size(v_todo_260_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_nat_dec_eq(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v_csize_271_; uint8_t v___x_272_; 
lean_dec_ref(v_vs_263_);
v_csize_271_ = lean_array_get_size(v_children_264_);
v___x_272_ = lean_nat_dec_eq(v_csize_271_, v___x_269_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_e_277_; lean_object* v_todo_278_; lean_object* v___y_280_; lean_object* v_first_294_; uint8_t v___x_295_; 
v___x_273_ = l_Lean_instInhabitedExpr;
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_sub(v___x_268_, v___x_274_);
v___x_276_ = lean_array_get_borrowed(v___x_273_, v_todo_260_, v___x_275_);
lean_dec(v___x_275_);
v_e_277_ = l_Lean_Meta_Sym_etaReduce(v___x_276_);
v_todo_278_ = lean_array_pop(v_todo_260_);
v_first_294_ = lean_array_fget_borrowed(v_children_264_, v___x_269_);
v___x_295_ = lean_nat_dec_eq(v_csize_271_, v___x_274_);
if (v___x_295_ == 0)
{
lean_object* v_fst_296_; lean_object* v_snd_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_fst_296_ = lean_ctor_get(v_first_294_, 0);
v_snd_297_ = lean_ctor_get(v_first_294_, 1);
v___x_298_ = lean_box(0);
v___x_299_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_296_, v___x_298_);
if (v___x_299_ == 0)
{
v___y_280_ = v_result_262_;
goto v___jp_279_;
}
else
{
lean_object* v___x_300_; 
lean_inc(v_snd_297_);
lean_inc_ref(v_todo_278_);
v___x_300_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_todo_278_, v_snd_297_, v_result_262_);
v___y_280_ = v___x_300_;
goto v___jp_279_;
}
}
else
{
lean_object* v_fst_301_; lean_object* v_snd_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
lean_inc(v_first_294_);
lean_del_object(v___x_266_);
lean_dec_ref(v_children_264_);
v_fst_301_ = lean_ctor_get(v_first_294_, 0);
lean_inc(v_fst_301_);
v_snd_302_ = lean_ctor_get(v_first_294_, 1);
lean_inc(v_snd_302_);
lean_dec(v_first_294_);
v___x_303_ = lean_box(0);
v___x_304_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_301_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_277_);
v___x_306_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_301_, v___x_305_);
lean_dec(v___x_305_);
lean_dec(v_fst_301_);
if (v___x_306_ == 0)
{
lean_dec(v_snd_302_);
lean_dec_ref(v_todo_278_);
lean_dec_ref(v_e_277_);
return v_result_262_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_278_, v_e_277_);
v_todo_260_ = v___x_307_;
v_c_261_ = v_snd_302_;
goto _start;
}
}
else
{
lean_dec(v_fst_301_);
lean_dec_ref(v_e_277_);
v_todo_260_ = v_todo_278_;
v_c_261_ = v_snd_302_;
goto _start;
}
}
v___jp_279_:
{
uint8_t v___x_281_; 
v___x_281_ = lean_nat_dec_lt(v___x_269_, v_csize_271_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_todo_278_);
lean_dec_ref(v_e_277_);
lean_del_object(v___x_266_);
lean_dec_ref(v_children_264_);
return v___y_280_;
}
else
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_nat_sub(v_csize_271_, v___x_274_);
v___x_283_ = lean_nat_dec_le(v___x_269_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec(v___x_282_);
lean_dec_ref(v_todo_278_);
lean_dec_ref(v_e_277_);
lean_del_object(v___x_266_);
lean_dec_ref(v_children_264_);
return v___y_280_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_284_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_277_);
v___x_285_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2));
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_285_);
lean_ctor_set(v___x_266_, 0, v___x_284_);
v___x_287_ = v___x_266_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_293_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_264_, v___x_287_, v___x_269_, v___x_282_);
lean_dec_ref(v___x_287_);
lean_dec_ref(v_children_264_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_dec_ref(v_todo_278_);
lean_dec_ref(v_e_277_);
return v___y_280_;
}
else
{
lean_object* v_val_289_; lean_object* v_snd_290_; lean_object* v___x_291_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_288_, 1);
v_snd_290_ = lean_ctor_get(v_val_289_, 1);
lean_inc(v_snd_290_);
lean_dec(v_val_289_);
v___x_291_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_278_, v_e_277_);
v_todo_260_ = v___x_291_;
v_c_261_ = v_snd_290_;
v_result_262_ = v___y_280_;
goto _start;
}
}
}
}
}
}
else
{
lean_del_object(v___x_266_);
lean_dec_ref(v_children_264_);
lean_dec_ref(v_todo_260_);
return v_result_262_;
}
}
else
{
lean_object* v___x_310_; 
lean_del_object(v___x_266_);
lean_dec_ref(v_children_264_);
lean_dec_ref(v_todo_260_);
v___x_310_ = l_Array_append___redArg(v_result_262_, v_vs_263_);
lean_dec_ref(v_vs_263_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_312_, lean_object* v_todo_313_, lean_object* v_c_314_, lean_object* v_result_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_todo_313_, v_c_314_, v_result_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_317_, lean_object* v_as_318_, lean_object* v_k_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_318_, v_k_319_, v_x_320_, v_x_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_324_, lean_object* v_as_325_, lean_object* v_k_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_324_, v_as_325_, v_k_326_, v_x_327_, v_x_328_, v_x_329_);
lean_dec_ref(v_k_326_);
lean_dec_ref(v_as_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_331_, lean_object* v_vals_332_, lean_object* v_i_333_, lean_object* v_k_334_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_array_get_size(v_keys_331_);
v___x_336_ = lean_nat_dec_lt(v_i_333_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec(v_i_333_);
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v_k_x27_338_; uint8_t v___x_339_; 
v_k_x27_338_ = lean_array_fget_borrowed(v_keys_331_, v_i_333_);
v___x_339_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_334_, v_k_x27_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_i_333_, v___x_340_);
lean_dec(v_i_333_);
v_i_333_ = v___x_341_;
goto _start;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_array_fget_borrowed(v_vals_332_, v_i_333_);
lean_dec(v_i_333_);
lean_inc(v___x_343_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_345_, lean_object* v_vals_346_, lean_object* v_i_347_, lean_object* v_k_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_345_, v_vals_346_, v_i_347_, v_k_348_);
lean_dec(v_k_348_);
lean_dec_ref(v_vals_346_);
lean_dec_ref(v_keys_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_350_, size_t v_x_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v_es_353_; lean_object* v___x_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v_j_357_; lean_object* v___x_358_; 
v_es_353_ = lean_ctor_get(v_x_350_, 0);
v___x_354_ = lean_box(2);
v___x_355_ = ((size_t)31ULL);
v___x_356_ = lean_usize_land(v_x_351_, v___x_355_);
v_j_357_ = lean_usize_to_nat(v___x_356_);
v___x_358_ = lean_array_get_borrowed(v___x_354_, v_es_353_, v_j_357_);
lean_dec(v_j_357_);
switch(lean_obj_tag(v___x_358_))
{
case 0:
{
lean_object* v_key_359_; lean_object* v_val_360_; uint8_t v___x_361_; 
v_key_359_ = lean_ctor_get(v___x_358_, 0);
v_val_360_ = lean_ctor_get(v___x_358_, 1);
v___x_361_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_352_, v_key_359_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(0);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
lean_inc(v_val_360_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v_val_360_);
return v___x_363_;
}
}
case 1:
{
lean_object* v_node_364_; size_t v___x_365_; size_t v___x_366_; 
v_node_364_ = lean_ctor_get(v___x_358_, 0);
v___x_365_ = ((size_t)5ULL);
v___x_366_ = lean_usize_shift_right(v_x_351_, v___x_365_);
v_x_350_ = v_node_364_;
v_x_351_ = v___x_366_;
goto _start;
}
default: 
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(0);
return v___x_368_;
}
}
}
else
{
lean_object* v_ks_369_; lean_object* v_vs_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_ks_369_ = lean_ctor_get(v_x_350_, 0);
v_vs_370_ = lean_ctor_get(v_x_350_, 1);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_369_, v_vs_370_, v___x_371_, v_x_352_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
size_t v_x_189__boxed_376_; lean_object* v_res_377_; 
v_x_189__boxed_376_ = lean_unbox_usize(v_x_374_);
lean_dec(v_x_374_);
v_res_377_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_373_, v_x_189__boxed_376_, v_x_375_);
lean_dec(v_x_375_);
lean_dec_ref(v_x_373_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
uint64_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_380_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_379_);
v___x_381_ = lean_uint64_to_usize(v___x_380_);
v___x_382_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_378_, v___x_381_, v_x_379_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_383_, v_x_384_);
lean_dec(v_x_384_);
lean_dec_ref(v_x_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_d_388_, lean_object* v_e_389_){
_start:
{
lean_object* v___y_391_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_box(0);
v___x_400_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_388_, v___x_399_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(8u);
v___x_402_ = lean_mk_empty_array_with_capacity(v___x_401_);
v___y_391_ = v___x_402_;
goto v___jp_390_;
}
else
{
lean_object* v_val_403_; lean_object* v_vs_404_; 
v_val_403_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_400_, 1);
v_vs_404_ = lean_ctor_get(v_val_403_, 0);
lean_inc_ref(v_vs_404_);
lean_dec(v_val_403_);
v___y_391_ = v_vs_404_;
goto v___jp_390_;
}
v___jp_390_:
{
lean_object* v_e_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_e_392_ = l_Lean_Meta_Sym_etaReduce(v_e_389_);
v___x_393_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_392_);
v___x_394_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_388_, v___x_393_);
lean_dec(v___x_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_dec_ref(v_e_392_);
return v___y_391_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_val_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_397_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_396_, v_e_392_);
v___x_398_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v___x_397_, v_val_395_, v___y_391_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_d_405_, lean_object* v_e_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_405_, v_e_406_);
lean_dec_ref(v_e_406_);
lean_dec_ref(v_d_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_408_, lean_object* v_d_409_, lean_object* v_e_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_409_, v_e_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_412_, lean_object* v_d_413_, lean_object* v_e_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_412_, v_d_413_, v_e_414_);
lean_dec_ref(v_e_414_);
lean_dec_ref(v_d_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_417_, v_x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_420_, v_x_421_, v_x_422_);
lean_dec(v_x_422_);
lean_dec_ref(v_x_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_424_, lean_object* v_x_425_, size_t v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_425_, v_x_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
size_t v_x_293__boxed_433_; lean_object* v_res_434_; 
v_x_293__boxed_433_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_429_, v_x_430_, v_x_293__boxed_433_, v_x_432_);
lean_dec(v_x_432_);
lean_dec_ref(v_x_430_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_435_, lean_object* v_keys_436_, lean_object* v_vals_437_, lean_object* v_heq_438_, lean_object* v_i_439_, lean_object* v_k_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_436_, v_vals_437_, v_i_439_, v_k_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_442_, lean_object* v_keys_443_, lean_object* v_vals_444_, lean_object* v_heq_445_, lean_object* v_i_446_, lean_object* v_k_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_442_, v_keys_443_, v_vals_444_, v_heq_445_, v_i_446_, v_k_447_);
lean_dec(v_k_447_);
lean_dec_ref(v_vals_444_);
lean_dec_ref(v_keys_443_);
return v_res_448_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_449_, lean_object* v_k_450_){
_start:
{
lean_object* v_k_452_; 
switch(lean_obj_tag(v_k_450_))
{
case 4:
{
lean_object* v_a_456_; lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_469_; 
v_a_456_ = lean_ctor_get(v_k_450_, 0);
v_a_457_ = lean_ctor_get(v_k_450_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_k_450_);
if (v_isSharedCheck_469_ == 0)
{
v___x_459_ = v_k_450_;
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_inc(v_a_456_);
lean_dec(v_k_450_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_zero_461_; uint8_t v_isZero_462_; 
v_zero_461_ = lean_unsigned_to_nat(0u);
v_isZero_462_ = lean_nat_dec_eq(v_a_457_, v_zero_461_);
if (v_isZero_462_ == 0)
{
lean_object* v_one_463_; lean_object* v_n_464_; lean_object* v___x_466_; 
v_one_463_ = lean_unsigned_to_nat(1u);
v_n_464_ = lean_nat_sub(v_a_457_, v_one_463_);
lean_dec(v_a_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_n_464_);
v___x_466_ = v___x_459_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_n_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v_k_452_ = v___x_466_;
goto v___jp_451_;
}
}
else
{
uint8_t v___x_468_; 
lean_del_object(v___x_459_);
lean_dec(v_a_457_);
lean_dec(v_a_456_);
v___x_468_ = 0;
return v___x_468_;
}
}
}
case 3:
{
lean_object* v_a_470_; lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_483_; 
v_a_470_ = lean_ctor_get(v_k_450_, 0);
v_a_471_ = lean_ctor_get(v_k_450_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_k_450_);
if (v_isSharedCheck_483_ == 0)
{
v___x_473_ = v_k_450_;
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_inc(v_a_470_);
lean_dec(v_k_450_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_zero_475_; uint8_t v_isZero_476_; 
v_zero_475_ = lean_unsigned_to_nat(0u);
v_isZero_476_ = lean_nat_dec_eq(v_a_471_, v_zero_475_);
if (v_isZero_476_ == 0)
{
lean_object* v_one_477_; lean_object* v_n_478_; lean_object* v___x_480_; 
v_one_477_ = lean_unsigned_to_nat(1u);
v_n_478_ = lean_nat_sub(v_a_471_, v_one_477_);
lean_dec(v_a_471_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_n_478_);
v___x_480_ = v___x_473_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_470_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_n_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v_k_452_ = v___x_480_;
goto v___jp_451_;
}
}
else
{
uint8_t v___x_482_; 
lean_del_object(v___x_473_);
lean_dec(v_a_471_);
lean_dec(v_a_470_);
v___x_482_ = 0;
return v___x_482_;
}
}
}
default: 
{
uint8_t v___x_484_; 
lean_dec(v_k_450_);
v___x_484_ = 0;
return v___x_484_;
}
}
v___jp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_449_, v_k_452_);
if (lean_obj_tag(v___x_453_) == 0)
{
v_k_450_ = v_k_452_;
goto _start;
}
else
{
uint8_t v___x_455_; 
lean_dec_ref_known(v___x_453_, 1);
lean_dec(v_k_452_);
v___x_455_ = 1;
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_485_, lean_object* v_k_486_){
_start:
{
uint8_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_485_, v_k_486_);
lean_dec_ref(v_d_485_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_489_, lean_object* v_d_490_, lean_object* v_k_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_490_, v_k_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_493_, lean_object* v_d_494_, lean_object* v_k_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_493_, v_d_494_, v_k_495_);
lean_dec_ref(v_d_494_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_498_, size_t v_sz_499_, size_t v_i_500_, lean_object* v_bs_501_){
_start:
{
uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_lt(v_i_500_, v_sz_499_);
if (v___x_502_ == 0)
{
lean_dec(v_numExtra_498_);
return v_bs_501_;
}
else
{
lean_object* v_v_503_; lean_object* v___x_504_; lean_object* v_bs_x27_505_; lean_object* v___x_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v_v_503_ = lean_array_uget(v_bs_501_, v_i_500_);
v___x_504_ = lean_unsigned_to_nat(0u);
v_bs_x27_505_ = lean_array_uset(v_bs_501_, v_i_500_, v___x_504_);
lean_inc(v_numExtra_498_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_v_503_);
lean_ctor_set(v___x_506_, 1, v_numExtra_498_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_500_, v___x_507_);
v___x_509_ = lean_array_uset(v_bs_x27_505_, v_i_500_, v___x_506_);
v_i_500_ = v___x_508_;
v_bs_501_ = v___x_509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_511_, lean_object* v_sz_512_, lean_object* v_i_513_, lean_object* v_bs_514_){
_start:
{
size_t v_sz_boxed_515_; size_t v_i_boxed_516_; lean_object* v_res_517_; 
v_sz_boxed_515_ = lean_unbox_usize(v_sz_512_);
lean_dec(v_sz_512_);
v_i_boxed_516_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_511_, v_sz_boxed_515_, v_i_boxed_516_, v_bs_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_d_518_, lean_object* v_e_519_, lean_object* v_numExtra_520_, lean_object* v_result_521_){
_start:
{
lean_object* v___x_522_; size_t v_sz_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v_result_526_; uint8_t v___x_527_; 
v___x_522_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_518_, v_e_519_);
v_sz_523_ = lean_array_size(v___x_522_);
v___x_524_ = ((size_t)0ULL);
lean_inc(v_numExtra_520_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_520_, v_sz_523_, v___x_524_, v___x_522_);
v_result_526_ = l_Array_append___redArg(v_result_521_, v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = l_Lean_Expr_isApp(v_e_519_);
if (v___x_527_ == 0)
{
lean_dec(v_numExtra_520_);
lean_dec_ref(v_e_519_);
return v_result_526_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = l_Lean_Expr_appFn_x21(v_e_519_);
lean_dec_ref(v_e_519_);
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_add(v_numExtra_520_, v___x_529_);
lean_dec(v_numExtra_520_);
v_e_519_ = v___x_528_;
v_numExtra_520_ = v___x_530_;
v_result_521_ = v_result_526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg___boxed(lean_object* v_d_532_, lean_object* v_e_533_, lean_object* v_numExtra_534_, lean_object* v_result_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_d_532_, v_e_533_, v_numExtra_534_, v_result_535_);
lean_dec_ref(v_d_532_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_537_, lean_object* v_d_538_, lean_object* v_e_539_, lean_object* v_numExtra_540_, lean_object* v_result_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_d_538_, v_e_539_, v_numExtra_540_, v_result_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___boxed(lean_object* v_00_u03b1_543_, lean_object* v_d_544_, lean_object* v_e_545_, lean_object* v_numExtra_546_, lean_object* v_result_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(v_00_u03b1_543_, v_d_544_, v_e_545_, v_numExtra_546_, v_result_547_);
lean_dec_ref(v_d_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(lean_object* v_00_u03b1_549_, lean_object* v_numExtra_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_bs_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_550_, v_sz_551_, v_i_552_, v_bs_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___boxed(lean_object* v_00_u03b1_555_, lean_object* v_numExtra_556_, lean_object* v_sz_557_, lean_object* v_i_558_, lean_object* v_bs_559_){
_start:
{
size_t v_sz_boxed_560_; size_t v_i_boxed_561_; lean_object* v_res_562_; 
v_sz_boxed_560_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_561_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0(v_00_u03b1_555_, v_numExtra_556_, v_sz_boxed_560_, v_i_boxed_561_, v_bs_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(size_t v_sz_563_, size_t v_i_564_, lean_object* v_bs_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_lt(v_i_564_, v_sz_563_);
if (v___x_566_ == 0)
{
return v_bs_565_;
}
else
{
lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_bs_x27_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v_v_567_ = lean_array_uget(v_bs_565_, v_i_564_);
v___x_568_ = lean_unsigned_to_nat(0u);
v_bs_x27_569_ = lean_array_uset(v_bs_565_, v_i_564_, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_v_567_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_564_, v___x_571_);
v___x_573_ = lean_array_uset(v_bs_x27_569_, v_i_564_, v___x_570_);
v_i_564_ = v___x_572_;
v_bs_565_ = v___x_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg___boxed(lean_object* v_sz_575_, lean_object* v_i_576_, lean_object* v_bs_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_575_);
lean_dec(v_sz_575_);
v_i_boxed_579_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_boxed_578_, v_i_boxed_579_, v_bs_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object* v_d_581_, lean_object* v_e_582_){
_start:
{
lean_object* v_e_583_; lean_object* v_result_584_; size_t v_sz_585_; size_t v___x_586_; lean_object* v_result_587_; uint8_t v___x_588_; uint8_t v___x_589_; 
v_e_583_ = l_Lean_Meta_Sym_etaReduce(v_e_582_);
v_result_584_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_581_, v_e_583_);
v_sz_585_ = lean_array_size(v_result_584_);
v___x_586_ = ((size_t)0ULL);
v_result_587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_585_, v___x_586_, v_result_584_);
v___x_588_ = l_Lean_Expr_isApp(v_e_583_);
v___x_589_ = lean_bool_not(v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; uint8_t v___x_591_; uint8_t v___x_592_; 
v___x_590_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_583_);
v___x_591_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_581_, v___x_590_);
v___x_592_ = lean_bool_not(v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = l_Lean_Expr_appFn_x21(v_e_583_);
lean_dec_ref(v_e_583_);
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_d_581_, v___x_593_, v___x_594_, v_result_587_);
return v___x_595_;
}
else
{
lean_dec_ref(v_e_583_);
return v_result_587_;
}
}
else
{
lean_dec_ref(v_e_583_);
return v_result_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_d_596_, lean_object* v_e_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_596_, v_e_597_);
lean_dec_ref(v_e_597_);
lean_dec_ref(v_d_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_599_, lean_object* v_d_600_, lean_object* v_e_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_600_, v_e_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_603_, lean_object* v_d_604_, lean_object* v_e_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_603_, v_d_604_, v_e_605_);
lean_dec_ref(v_e_605_);
lean_dec_ref(v_d_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_607_, size_t v_sz_608_, size_t v_i_609_, lean_object* v_bs_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_608_, v_i_609_, v_bs_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_612_, lean_object* v_sz_613_, lean_object* v_i_614_, lean_object* v_bs_615_){
_start:
{
size_t v_sz_boxed_616_; size_t v_i_boxed_617_; lean_object* v_res_618_; 
v_sz_boxed_616_ = lean_unbox_usize(v_sz_613_);
lean_dec(v_sz_613_);
v_i_boxed_617_ = lean_unbox_usize(v_i_614_);
lean_dec(v_i_614_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_612_, v_sz_boxed_616_, v_i_boxed_617_, v_bs_615_);
return v_res_618_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Offset(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Eta(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
