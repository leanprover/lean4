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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2;
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_e_12_);
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
lean_dec_ref(v_e_22_);
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
lean_dec_ref(v_fn_58_);
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
lean_dec_ref(v_fn_58_);
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
lean_dec_ref(v_fn_58_);
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
lean_dec_ref(v_fn_58_);
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
lean_dec_ref(v___x_78_);
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
lean_dec_ref(v_fn_58_);
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
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__1));
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
return v___x_168_;
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
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2);
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
v___x_200_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2);
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
v___x_209_ = l_Lean_Expr_getAppFn(v_e_208_);
switch(lean_obj_tag(v___x_209_))
{
case 9:
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_a_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_211_, 0, v_a_210_);
return v___x_211_;
}
case 4:
{
lean_object* v_declName_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_declName_212_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_declName_212_);
lean_dec_ref(v___x_209_);
v___x_213_ = l_Lean_Expr_getAppNumArgs(v_e_208_);
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
lean_dec_ref(v___x_209_);
v___x_216_ = l_Lean_Expr_getAppNumArgs(v_e_208_);
v___x_217_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_217_, 0, v_fvarId_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
case 7:
{
lean_object* v___x_218_; 
lean_dec_ref(v___x_209_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(lean_object* v_todo_222_, lean_object* v_e_223_){
_start:
{
switch(lean_obj_tag(v_e_223_))
{
case 5:
{
lean_object* v_fn_224_; lean_object* v_arg_225_; lean_object* v___x_226_; 
v_fn_224_ = lean_ctor_get(v_e_223_, 0);
lean_inc_ref(v_fn_224_);
v_arg_225_ = lean_ctor_get(v_e_223_, 1);
lean_inc_ref(v_arg_225_);
lean_dec_ref(v_e_223_);
v___x_226_ = lean_array_push(v_todo_222_, v_arg_225_);
v_todo_222_ = v___x_226_;
v_e_223_ = v_fn_224_;
goto _start;
}
case 7:
{
lean_object* v_binderType_228_; lean_object* v_body_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_binderType_228_ = lean_ctor_get(v_e_223_, 1);
lean_inc_ref(v_binderType_228_);
v_body_229_ = lean_ctor_get(v_e_223_, 2);
lean_inc_ref(v_body_229_);
lean_dec_ref(v_e_223_);
v___x_230_ = lean_array_push(v_todo_222_, v_body_229_);
v___x_231_ = lean_array_push(v___x_230_, v_binderType_228_);
return v___x_231_;
}
default: 
{
lean_dec_ref(v_e_223_);
return v_todo_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(lean_object* v_as_232_, lean_object* v_k_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_m_238_; lean_object* v_a_239_; uint8_t v___x_240_; 
v___x_236_ = lean_nat_add(v_x_234_, v_x_235_);
v___x_237_ = lean_unsigned_to_nat(1u);
v_m_238_ = lean_nat_shiftr(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
v_a_239_ = lean_array_fget_borrowed(v_as_232_, v_m_238_);
v___x_240_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_a_239_, v_k_233_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; 
lean_dec(v_x_235_);
v___x_241_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___lam__0(v_k_233_, v_a_239_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_dec(v_m_238_);
lean_dec(v_x_234_);
lean_inc(v_a_239_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_a_239_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_nat_dec_eq(v_m_238_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_nat_sub(v_m_238_, v___x_237_);
lean_dec(v_m_238_);
v___x_246_ = lean_nat_dec_lt(v___x_245_, v_x_234_);
if (v___x_246_ == 0)
{
v_x_235_ = v___x_245_;
goto _start;
}
else
{
lean_object* v___x_248_; 
lean_dec(v___x_245_);
lean_dec(v_x_234_);
v___x_248_ = lean_box(0);
return v___x_248_;
}
}
else
{
lean_object* v___x_249_; 
lean_dec(v_m_238_);
lean_dec(v_x_234_);
v___x_249_ = lean_box(0);
return v___x_249_;
}
}
}
else
{
lean_object* v___x_250_; uint8_t v___x_251_; 
lean_dec(v_x_234_);
v___x_250_ = lean_nat_add(v_m_238_, v___x_237_);
lean_dec(v_m_238_);
v___x_251_ = lean_nat_dec_le(v___x_250_, v_x_235_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec(v___x_250_);
lean_dec(v_x_235_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
else
{
v_x_234_ = v___x_250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg___boxed(lean_object* v_as_254_, lean_object* v_k_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_254_, v_k_255_, v_x_256_, v_x_257_);
lean_dec_ref(v_k_255_);
lean_dec_ref(v_as_254_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(lean_object* v_todo_259_, lean_object* v_c_260_, lean_object* v_result_261_){
_start:
{
lean_object* v_vs_262_; lean_object* v_children_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_310_; 
v_vs_262_ = lean_ctor_get(v_c_260_, 0);
v_children_263_ = lean_ctor_get(v_c_260_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_c_260_);
if (v_isSharedCheck_310_ == 0)
{
v___x_265_ = v_c_260_;
v_isShared_266_ = v_isSharedCheck_310_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_children_263_);
lean_inc(v_vs_262_);
lean_dec(v_c_260_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_310_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_267_ = lean_array_get_size(v_todo_259_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_nat_dec_eq(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v_csize_270_; uint8_t v___x_271_; 
lean_dec_ref(v_vs_262_);
v_csize_270_ = lean_array_get_size(v_children_263_);
v___x_271_ = lean_nat_dec_eq(v_csize_270_, v___x_268_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_e_276_; lean_object* v_todo_277_; lean_object* v___y_279_; lean_object* v_first_293_; uint8_t v___x_294_; 
v___x_272_ = l_Lean_instInhabitedExpr;
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_sub(v___x_267_, v___x_273_);
v___x_275_ = lean_array_get_borrowed(v___x_272_, v_todo_259_, v___x_274_);
lean_dec(v___x_274_);
v_e_276_ = l_Lean_Meta_Sym_etaReduce(v___x_275_);
v_todo_277_ = lean_array_pop(v_todo_259_);
v_first_293_ = lean_array_fget_borrowed(v_children_263_, v___x_268_);
v___x_294_ = lean_nat_dec_eq(v_csize_270_, v___x_273_);
if (v___x_294_ == 0)
{
lean_object* v_fst_295_; lean_object* v_snd_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_fst_295_ = lean_ctor_get(v_first_293_, 0);
v_snd_296_ = lean_ctor_get(v_first_293_, 1);
v___x_297_ = lean_box(0);
v___x_298_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_295_, v___x_297_);
if (v___x_298_ == 0)
{
v___y_279_ = v_result_261_;
goto v___jp_278_;
}
else
{
lean_object* v___x_299_; 
lean_inc(v_snd_296_);
lean_inc_ref(v_todo_277_);
v___x_299_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_todo_277_, v_snd_296_, v_result_261_);
v___y_279_ = v___x_299_;
goto v___jp_278_;
}
}
else
{
lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
lean_inc(v_first_293_);
lean_del_object(v___x_265_);
lean_dec_ref(v_children_263_);
v_fst_300_ = lean_ctor_get(v_first_293_, 0);
lean_inc(v_fst_300_);
v_snd_301_ = lean_ctor_get(v_first_293_, 1);
lean_inc(v_snd_301_);
lean_dec(v_first_293_);
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_300_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_276_);
v___x_305_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_300_, v___x_304_);
lean_dec(v___x_304_);
lean_dec(v_fst_300_);
if (v___x_305_ == 0)
{
lean_dec(v_snd_301_);
lean_dec_ref(v_todo_277_);
lean_dec_ref(v_e_276_);
return v_result_261_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_277_, v_e_276_);
v_todo_259_ = v___x_306_;
v_c_260_ = v_snd_301_;
goto _start;
}
}
else
{
lean_dec(v_fst_300_);
lean_dec_ref(v_e_276_);
v_todo_259_ = v_todo_277_;
v_c_260_ = v_snd_301_;
goto _start;
}
}
v___jp_278_:
{
uint8_t v___x_280_; 
v___x_280_ = lean_nat_dec_lt(v___x_268_, v_csize_270_);
if (v___x_280_ == 0)
{
lean_dec_ref(v_todo_277_);
lean_dec_ref(v_e_276_);
lean_del_object(v___x_265_);
lean_dec_ref(v_children_263_);
return v___y_279_;
}
else
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_nat_sub(v_csize_270_, v___x_273_);
v___x_282_ = lean_nat_dec_le(v___x_268_, v___x_281_);
if (v___x_282_ == 0)
{
lean_dec(v___x_281_);
lean_dec_ref(v_todo_277_);
lean_dec_ref(v_e_276_);
lean_del_object(v___x_265_);
lean_dec_ref(v_children_263_);
return v___y_279_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_276_);
v___x_284_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_findKey_x3f___redArg___closed__2);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_284_);
lean_ctor_set(v___x_265_, 0, v___x_283_);
v___x_286_ = v___x_265_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_292_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; 
v___x_287_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_children_263_, v___x_286_, v___x_268_, v___x_281_);
lean_dec_ref(v___x_286_);
lean_dec_ref(v_children_263_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_dec_ref(v_todo_277_);
lean_dec_ref(v_e_276_);
return v___y_279_;
}
else
{
lean_object* v_val_288_; lean_object* v_snd_289_; lean_object* v___x_290_; 
v_val_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_val_288_);
lean_dec_ref(v___x_287_);
v_snd_289_ = lean_ctor_get(v_val_288_, 1);
lean_inc(v_snd_289_);
lean_dec(v_val_288_);
v___x_290_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v_todo_277_, v_e_276_);
v_todo_259_ = v___x_290_;
v_c_260_ = v_snd_289_;
v_result_261_ = v___y_279_;
goto _start;
}
}
}
}
}
}
else
{
lean_del_object(v___x_265_);
lean_dec_ref(v_children_263_);
lean_dec_ref(v_todo_259_);
return v_result_261_;
}
}
else
{
lean_object* v___x_309_; 
lean_del_object(v___x_265_);
lean_dec_ref(v_children_263_);
lean_dec_ref(v_todo_259_);
v___x_309_ = l_Array_append___redArg(v_result_261_, v_vs_262_);
lean_dec_ref(v_vs_262_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop(lean_object* v_00_u03b1_311_, lean_object* v_todo_312_, lean_object* v_c_313_, lean_object* v_result_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v_todo_312_, v_c_313_, v_result_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(lean_object* v_00_u03b1_316_, lean_object* v_as_317_, lean_object* v_k_318_, lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___redArg(v_as_317_, v_k_318_, v_x_319_, v_x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0___boxed(lean_object* v_00_u03b1_323_, lean_object* v_as_324_, lean_object* v_k_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Array_binSearchAux___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop_spec__0(v_00_u03b1_323_, v_as_324_, v_k_325_, v_x_326_, v_x_327_, v_x_328_);
lean_dec_ref(v_k_325_);
lean_dec_ref(v_as_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_330_, lean_object* v_vals_331_, lean_object* v_i_332_, lean_object* v_k_333_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_array_get_size(v_keys_330_);
v___x_335_ = lean_nat_dec_lt(v_i_332_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v_i_332_);
v___x_336_ = lean_box(0);
return v___x_336_;
}
else
{
lean_object* v_k_x27_337_; uint8_t v___x_338_; 
v_k_x27_337_ = lean_array_fget_borrowed(v_keys_330_, v_i_332_);
v___x_338_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_333_, v_k_x27_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_i_332_, v___x_339_);
lean_dec(v_i_332_);
v_i_332_ = v___x_340_;
goto _start;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_array_fget_borrowed(v_vals_331_, v_i_332_);
lean_dec(v_i_332_);
lean_inc(v___x_342_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_344_, lean_object* v_vals_345_, lean_object* v_i_346_, lean_object* v_k_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_344_, v_vals_345_, v_i_346_, v_k_347_);
lean_dec(v_k_347_);
lean_dec_ref(v_vals_345_);
lean_dec_ref(v_keys_344_);
return v_res_348_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_349_; size_t v___x_350_; size_t v___x_351_; 
v___x_349_ = ((size_t)5ULL);
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_shift_left(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; 
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__0);
v___x_354_ = lean_usize_sub(v___x_353_, v___x_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(lean_object* v_x_355_, size_t v_x_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v_es_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_379_; 
v_es_358_ = lean_ctor_get(v_x_355_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_355_);
if (v_isSharedCheck_379_ == 0)
{
v___x_360_ = v_x_355_;
v_isShared_361_ = v_isSharedCheck_379_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_es_358_);
lean_dec(v_x_355_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_379_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v_j_366_; lean_object* v___x_367_; 
v___x_362_ = lean_box(2);
v___x_363_ = ((size_t)5ULL);
v___x_364_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___closed__1);
v___x_365_ = lean_usize_land(v_x_356_, v___x_364_);
v_j_366_ = lean_usize_to_nat(v___x_365_);
v___x_367_ = lean_array_get(v___x_362_, v_es_358_, v_j_366_);
lean_dec(v_j_366_);
lean_dec_ref(v_es_358_);
switch(lean_obj_tag(v___x_367_))
{
case 0:
{
lean_object* v_key_368_; lean_object* v_val_369_; uint8_t v___x_370_; 
v_key_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_key_368_);
v_val_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_val_369_);
lean_dec_ref(v___x_367_);
v___x_370_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_357_, v_key_368_);
lean_dec(v_key_368_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_val_369_);
lean_del_object(v___x_360_);
v___x_371_ = lean_box(0);
return v___x_371_;
}
else
{
lean_object* v___x_373_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 0, v_val_369_);
v___x_373_ = v___x_360_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_val_369_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
case 1:
{
lean_object* v_node_375_; size_t v___x_376_; 
lean_del_object(v___x_360_);
v_node_375_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_node_375_);
lean_dec_ref(v___x_367_);
v___x_376_ = lean_usize_shift_right(v_x_356_, v___x_363_);
v_x_355_ = v_node_375_;
v_x_356_ = v___x_376_;
goto _start;
}
default: 
{
lean_object* v___x_378_; 
lean_del_object(v___x_360_);
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
}
}
else
{
lean_object* v_ks_380_; lean_object* v_vs_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_ks_380_ = lean_ctor_get(v_x_355_, 0);
lean_inc_ref(v_ks_380_);
v_vs_381_ = lean_ctor_get(v_x_355_, 1);
lean_inc_ref(v_vs_381_);
lean_dec_ref(v_x_355_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_ks_380_, v_vs_381_, v___x_382_, v_x_357_);
lean_dec_ref(v_vs_381_);
lean_dec_ref(v_ks_380_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg___boxed(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
size_t v_x_205__boxed_387_; lean_object* v_res_388_; 
v_x_205__boxed_387_ = lean_unbox_usize(v_x_385_);
lean_dec(v_x_385_);
v_res_388_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_384_, v_x_205__boxed_387_, v_x_386_);
lean_dec(v_x_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
uint64_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v___x_391_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_390_);
v___x_392_ = lean_uint64_to_usize(v___x_391_);
v___x_393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_389_, v___x_392_, v_x_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_394_, v_x_395_);
lean_dec(v_x_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object* v_d_399_, lean_object* v_e_400_){
_start:
{
lean_object* v___y_402_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_box(0);
lean_inc_ref(v_d_399_);
v___x_411_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_399_, v___x_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(8u);
v___x_413_ = lean_mk_empty_array_with_capacity(v___x_412_);
v___y_402_ = v___x_413_;
goto v___jp_401_;
}
else
{
lean_object* v_val_414_; lean_object* v_vs_415_; 
v_val_414_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_414_);
lean_dec_ref(v___x_411_);
v_vs_415_ = lean_ctor_get(v_val_414_, 0);
lean_inc_ref(v_vs_415_);
lean_dec(v_val_414_);
v___y_402_ = v_vs_415_;
goto v___jp_401_;
}
v___jp_401_:
{
lean_object* v_e_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_e_403_ = l_Lean_Meta_Sym_etaReduce(v_e_400_);
v___x_404_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_403_);
v___x_405_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_399_, v___x_404_);
lean_dec(v___x_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_dec_ref(v_e_403_);
return v___y_402_;
}
else
{
lean_object* v_val_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_val_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_val_406_);
lean_dec_ref(v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Meta_Sym_getMatch___redArg___closed__0));
v___x_408_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_pushArgsTodo(v___x_407_, v_e_403_);
v___x_409_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchLoop___redArg(v___x_408_, v_val_406_, v___y_402_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___redArg___boxed(lean_object* v_d_416_, lean_object* v_e_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_416_, v_e_417_);
lean_dec_ref(v_e_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch(lean_object* v_00_u03b1_419_, lean_object* v_d_420_, lean_object* v_e_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_420_, v_e_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatch___boxed(lean_object* v_00_u03b1_423_, lean_object* v_d_424_, lean_object* v_e_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_Sym_getMatch(v_00_u03b1_423_, v_d_424_, v_e_425_);
lean_dec_ref(v_e_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_x_428_, v_x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___boxed(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0(v_00_u03b2_431_, v_x_432_, v_x_433_);
lean_dec(v_x_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(lean_object* v_00_u03b2_435_, lean_object* v_x_436_, size_t v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___redArg(v_x_436_, v_x_437_, v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0___boxed(lean_object* v_00_u03b2_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
size_t v_x_327__boxed_444_; lean_object* v_res_445_; 
v_x_327__boxed_444_ = lean_unbox_usize(v_x_442_);
lean_dec(v_x_442_);
v_res_445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0(v_00_u03b2_440_, v_x_441_, v_x_327__boxed_444_, v_x_443_);
lean_dec(v_x_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_446_, lean_object* v_keys_447_, lean_object* v_vals_448_, lean_object* v_heq_449_, lean_object* v_i_450_, lean_object* v_k_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___redArg(v_keys_447_, v_vals_448_, v_i_450_, v_k_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_453_, lean_object* v_keys_454_, lean_object* v_vals_455_, lean_object* v_heq_456_, lean_object* v_i_457_, lean_object* v_k_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0_spec__0_spec__1(v_00_u03b2_453_, v_keys_454_, v_vals_455_, v_heq_456_, v_i_457_, v_k_458_);
lean_dec(v_k_458_);
lean_dec_ref(v_vals_455_);
lean_dec_ref(v_keys_454_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(lean_object* v_d_460_, lean_object* v_k_461_){
_start:
{
lean_object* v_k_463_; 
switch(lean_obj_tag(v_k_461_))
{
case 4:
{
lean_object* v_a_467_; lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_480_; 
v_a_467_ = lean_ctor_get(v_k_461_, 0);
v_a_468_ = lean_ctor_get(v_k_461_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_k_461_);
if (v_isSharedCheck_480_ == 0)
{
v___x_470_ = v_k_461_;
v_isShared_471_ = v_isSharedCheck_480_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_inc(v_a_467_);
lean_dec(v_k_461_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_480_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_zero_472_; uint8_t v_isZero_473_; 
v_zero_472_ = lean_unsigned_to_nat(0u);
v_isZero_473_ = lean_nat_dec_eq(v_a_468_, v_zero_472_);
if (v_isZero_473_ == 0)
{
lean_object* v_one_474_; lean_object* v_n_475_; lean_object* v___x_477_; 
v_one_474_ = lean_unsigned_to_nat(1u);
v_n_475_ = lean_nat_sub(v_a_468_, v_one_474_);
lean_dec(v_a_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_n_475_);
v___x_477_ = v___x_470_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_467_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_n_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v_k_463_ = v___x_477_;
goto v___jp_462_;
}
}
else
{
uint8_t v___x_479_; 
lean_del_object(v___x_470_);
lean_dec(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_d_460_);
v___x_479_ = 0;
return v___x_479_;
}
}
}
case 3:
{
lean_object* v_a_481_; lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_494_; 
v_a_481_ = lean_ctor_get(v_k_461_, 0);
v_a_482_ = lean_ctor_get(v_k_461_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_k_461_);
if (v_isSharedCheck_494_ == 0)
{
v___x_484_ = v_k_461_;
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_inc(v_a_481_);
lean_dec(v_k_461_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_zero_486_; uint8_t v_isZero_487_; 
v_zero_486_ = lean_unsigned_to_nat(0u);
v_isZero_487_ = lean_nat_dec_eq(v_a_482_, v_zero_486_);
if (v_isZero_487_ == 0)
{
lean_object* v_one_488_; lean_object* v_n_489_; lean_object* v___x_491_; 
v_one_488_ = lean_unsigned_to_nat(1u);
v_n_489_ = lean_nat_sub(v_a_482_, v_one_488_);
lean_dec(v_a_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v_n_489_);
v___x_491_ = v___x_484_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_n_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
v_k_463_ = v___x_491_;
goto v___jp_462_;
}
}
else
{
uint8_t v___x_493_; 
lean_del_object(v___x_484_);
lean_dec(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_d_460_);
v___x_493_ = 0;
return v___x_493_;
}
}
}
default: 
{
uint8_t v___x_495_; 
lean_dec(v_k_461_);
lean_dec_ref(v_d_460_);
v___x_495_ = 0;
return v___x_495_;
}
}
v___jp_462_:
{
lean_object* v___x_464_; 
lean_inc_ref(v_d_460_);
v___x_464_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getMatch_spec__0___redArg(v_d_460_, v_k_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
v_k_461_ = v_k_463_;
goto _start;
}
else
{
uint8_t v___x_466_; 
lean_dec_ref(v___x_464_);
lean_dec(v_k_463_);
lean_dec_ref(v_d_460_);
v___x_466_ = 1;
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg___boxed(lean_object* v_d_496_, lean_object* v_k_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_496_, v_k_497_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(lean_object* v_00_u03b1_500_, lean_object* v_d_501_, lean_object* v_k_502_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_501_, v_k_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___boxed(lean_object* v_00_u03b1_504_, lean_object* v_d_505_, lean_object* v_k_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_504_, v_d_505_, v_k_506_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(lean_object* v_numExtra_509_, size_t v_sz_510_, size_t v_i_511_, lean_object* v_bs_512_){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_513_ == 0)
{
lean_dec(v_numExtra_509_);
return v_bs_512_;
}
else
{
lean_object* v_v_514_; lean_object* v___x_515_; lean_object* v_bs_x27_516_; lean_object* v___x_517_; size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v_v_514_ = lean_array_uget(v_bs_512_, v_i_511_);
v___x_515_ = lean_unsigned_to_nat(0u);
v_bs_x27_516_ = lean_array_uset(v_bs_512_, v_i_511_, v___x_515_);
lean_inc(v_numExtra_509_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_v_514_);
lean_ctor_set(v___x_517_, 1, v_numExtra_509_);
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_511_, v___x_518_);
v___x_520_ = lean_array_uset(v_bs_x27_516_, v_i_511_, v___x_517_);
v_i_511_ = v___x_519_;
v_bs_512_ = v___x_520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg___boxed(lean_object* v_numExtra_522_, lean_object* v_sz_523_, lean_object* v_i_524_, lean_object* v_bs_525_){
_start:
{
size_t v_sz_boxed_526_; size_t v_i_boxed_527_; lean_object* v_res_528_; 
v_sz_boxed_526_ = lean_unbox_usize(v_sz_523_);
lean_dec(v_sz_523_);
v_i_boxed_527_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_522_, v_sz_boxed_526_, v_i_boxed_527_, v_bs_525_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(lean_object* v_d_529_, lean_object* v_e_530_, lean_object* v_numExtra_531_, lean_object* v_result_532_){
_start:
{
lean_object* v___x_533_; size_t v_sz_534_; size_t v___x_535_; lean_object* v___x_536_; lean_object* v_result_537_; uint8_t v___x_538_; 
lean_inc_ref(v_d_529_);
v___x_533_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_529_, v_e_530_);
v_sz_534_ = lean_array_size(v___x_533_);
v___x_535_ = ((size_t)0ULL);
lean_inc(v_numExtra_531_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go_spec__0___redArg(v_numExtra_531_, v_sz_534_, v___x_535_, v___x_533_);
v_result_537_ = l_Array_append___redArg(v_result_532_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = l_Lean_Expr_isApp(v_e_530_);
if (v___x_538_ == 0)
{
lean_dec(v_numExtra_531_);
lean_dec_ref(v_e_530_);
lean_dec_ref(v_d_529_);
return v_result_537_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_Expr_appFn_x21(v_e_530_);
lean_dec_ref(v_e_530_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_numExtra_531_, v___x_540_);
lean_dec(v_numExtra_531_);
v_e_530_ = v___x_539_;
v_numExtra_531_ = v___x_541_;
v_result_532_ = v_result_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go(lean_object* v_00_u03b1_543_, lean_object* v_d_544_, lean_object* v_e_545_, lean_object* v_numExtra_546_, lean_object* v_result_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_d_544_, v_e_545_, v_numExtra_546_, v_result_547_);
return v___x_548_;
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
lean_object* v_e_583_; lean_object* v_result_584_; size_t v_sz_585_; size_t v___x_586_; lean_object* v_result_587_; uint8_t v___x_588_; 
v_e_583_ = l_Lean_Meta_Sym_etaReduce(v_e_582_);
lean_inc_ref(v_d_581_);
v_result_584_ = l_Lean_Meta_Sym_getMatch___redArg(v_d_581_, v_e_583_);
v_sz_585_ = lean_array_size(v_result_584_);
v___x_586_ = ((size_t)0ULL);
v_result_587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_585_, v___x_586_, v_result_584_);
v___x_588_ = l_Lean_Expr_isApp(v_e_583_);
if (v___x_588_ == 0)
{
lean_dec_ref(v_e_583_);
lean_dec_ref(v_d_581_);
return v_result_587_;
}
else
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getKey(v_e_583_);
lean_inc_ref(v_d_581_);
v___x_590_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_mayMatchPrefix___redArg(v_d_581_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec_ref(v_e_583_);
lean_dec_ref(v_d_581_);
return v_result_587_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = l_Lean_Expr_appFn_x21(v_e_583_);
lean_dec_ref(v_e_583_);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = l___private_Lean_Meta_Sym_Simp_DiscrTree_0__Lean_Meta_Sym_getMatchWithExtra_go___redArg(v_d_581_, v___x_591_, v___x_592_, v_result_587_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg___boxed(lean_object* v_d_594_, lean_object* v_e_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_594_, v_e_595_);
lean_dec_ref(v_e_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra(lean_object* v_00_u03b1_597_, lean_object* v_d_598_, lean_object* v_e_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_d_598_, v_e_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getMatchWithExtra___boxed(lean_object* v_00_u03b1_601_, lean_object* v_d_602_, lean_object* v_e_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Meta_Sym_getMatchWithExtra(v_00_u03b1_601_, v_d_602_, v_e_603_);
lean_dec_ref(v_e_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(lean_object* v_00_u03b1_605_, size_t v_sz_606_, size_t v_i_607_, lean_object* v_bs_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___redArg(v_sz_606_, v_i_607_, v_bs_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0___boxed(lean_object* v_00_u03b1_610_, lean_object* v_sz_611_, lean_object* v_i_612_, lean_object* v_bs_613_){
_start:
{
size_t v_sz_boxed_614_; size_t v_i_boxed_615_; lean_object* v_res_616_; 
v_sz_boxed_614_ = lean_unbox_usize(v_sz_611_);
lean_dec(v_sz_611_);
v_i_boxed_615_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_getMatchWithExtra_spec__0(v_00_u03b1_610_, v_sz_boxed_614_, v_i_boxed_615_, v_bs_613_);
return v_res_616_;
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
