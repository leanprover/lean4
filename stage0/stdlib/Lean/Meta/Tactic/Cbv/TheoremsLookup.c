// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.TheoremsLookup
// Imports: public import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Match.MatchEqsExt import Lean.Meta.Eqns
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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; size_t v___x_8_; size_t v___x_9_; 
v___x_6_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
lean_inc(v___x_6_);
v___x_7_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_4_, v___x_6_);
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_2_, v___x_8_);
v_i_2_ = v___x_9_;
v_b_4_ = v___x_7_;
goto _start;
}
else
{
return v_b_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0___boxed(lean_object* v_as_11_, lean_object* v_i_12_, lean_object* v_stop_13_, lean_object* v_b_14_){
_start:
{
size_t v_i_boxed_15_; size_t v_stop_boxed_16_; lean_object* v_res_17_; 
v_i_boxed_15_ = lean_unbox_usize(v_i_12_);
lean_dec(v_i_12_);
v_stop_boxed_16_ = lean_unbox_usize(v_stop_13_);
lean_dec(v_stop_13_);
v_res_17_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(v_as_11_, v_i_boxed_15_, v_stop_boxed_16_, v_b_14_);
lean_dec_ref(v_as_11_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(lean_object* v_thms_18_, lean_object* v_toInsert_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_array_get_size(v_toInsert_19_);
v___x_22_ = lean_nat_dec_lt(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
return v_thms_18_;
}
else
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_le(v___x_21_, v___x_21_);
if (v___x_23_ == 0)
{
if (v___x_22_ == 0)
{
return v_thms_18_;
}
else
{
size_t v___x_24_; size_t v___x_25_; lean_object* v___x_26_; 
v___x_24_ = ((size_t)0ULL);
v___x_25_ = lean_usize_of_nat(v___x_21_);
v___x_26_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(v_toInsert_19_, v___x_24_, v___x_25_, v_thms_18_);
return v___x_26_;
}
}
else
{
size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; 
v___x_27_ = ((size_t)0ULL);
v___x_28_ = lean_usize_of_nat(v___x_21_);
v___x_29_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany_spec__0(v_toInsert_19_, v___x_27_, v___x_28_, v_thms_18_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany___boxed(lean_object* v_thms_30_, lean_object* v_toInsert_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v_thms_30_, v_toInsert_31_);
lean_dec_ref(v_toInsert_31_);
return v_res_32_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__0);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__1);
v___x_37_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
lean_ctor_set(v___x_37_, 2, v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_(lean_object* v___x_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed(lean_object* v___x_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_(v___x_43_);
return v_res_45_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_46_; lean_object* v___f_47_; 
v___x_46_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default___closed__2);
v___f_47_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_47_, 0, v___x_46_);
return v___f_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___f_49_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_box(1);
v___x_52_ = l_Lean_registerEnvExtension___redArg(v___f_49_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2____boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_ks_59_; lean_object* v_vs_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_84_; 
v_ks_59_ = lean_ctor_get(v_x_55_, 0);
v_vs_60_ = lean_ctor_get(v_x_55_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_84_ == 0)
{
v___x_62_ = v_x_55_;
v_isShared_63_ = v_isSharedCheck_84_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_vs_60_);
lean_inc(v_ks_59_);
lean_dec(v_x_55_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_84_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_array_get_size(v_ks_59_);
v___x_65_ = lean_nat_dec_lt(v_x_56_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
lean_dec(v_x_56_);
v___x_66_ = lean_array_push(v_ks_59_, v_x_57_);
v___x_67_ = lean_array_push(v_vs_60_, v_x_58_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_67_);
lean_ctor_set(v___x_62_, 0, v___x_66_);
v___x_69_ = v___x_62_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_66_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
else
{
lean_object* v_k_x27_71_; uint8_t v___x_72_; 
v_k_x27_71_ = lean_array_fget_borrowed(v_ks_59_, v_x_56_);
v___x_72_ = lean_name_eq(v_x_57_, v_k_x27_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_74_; 
if (v_isShared_63_ == 0)
{
v___x_74_ = v___x_62_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_ks_59_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_vs_60_);
v___x_74_ = v_reuseFailAlloc_78_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_add(v_x_56_, v___x_75_);
lean_dec(v_x_56_);
v_x_55_ = v___x_74_;
v_x_56_ = v___x_76_;
goto _start;
}
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_79_ = lean_array_fset(v_ks_59_, v_x_56_, v_x_57_);
v___x_80_ = lean_array_fset(v_vs_60_, v_x_56_, v_x_58_);
lean_dec(v_x_56_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_80_);
lean_ctor_set(v___x_62_, 0, v___x_79_);
v___x_82_ = v___x_62_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(lean_object* v_n_85_, lean_object* v_k_86_, lean_object* v_v_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(v_n_85_, v___x_88_, v_k_86_, v_v_87_);
return v___x_89_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_90_; uint64_t v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1723u);
v___x_91_ = lean_uint64_of_nat(v___x_90_);
return v___x_91_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; 
v___x_92_ = ((size_t)5ULL);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_shift_left(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0);
v___x_97_ = lean_usize_sub(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(lean_object* v_x_99_, size_t v_x_100_, size_t v_x_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v_es_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; size_t v___x_108_; lean_object* v_j_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_es_104_ = lean_ctor_get(v_x_99_, 0);
v___x_105_ = ((size_t)5ULL);
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1);
v___x_108_ = lean_usize_land(v_x_100_, v___x_107_);
v_j_109_ = lean_usize_to_nat(v___x_108_);
v___x_110_ = lean_array_get_size(v_es_104_);
v___x_111_ = lean_nat_dec_lt(v_j_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec(v_j_109_);
lean_dec(v_x_103_);
lean_dec(v_x_102_);
return v_x_99_;
}
else
{
lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_148_; 
lean_inc_ref(v_es_104_);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v_x_99_, 0);
lean_dec(v_unused_149_);
v___x_113_ = v_x_99_;
v_isShared_114_ = v_isSharedCheck_148_;
goto v_resetjp_112_;
}
else
{
lean_dec(v_x_99_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_148_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_v_115_; lean_object* v___x_116_; lean_object* v_xs_x27_117_; lean_object* v___y_119_; 
v_v_115_ = lean_array_fget(v_es_104_, v_j_109_);
v___x_116_ = lean_box(0);
v_xs_x27_117_ = lean_array_fset(v_es_104_, v_j_109_, v___x_116_);
switch(lean_obj_tag(v_v_115_))
{
case 0:
{
lean_object* v_key_124_; lean_object* v_val_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_key_124_ = lean_ctor_get(v_v_115_, 0);
v_val_125_ = lean_ctor_get(v_v_115_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_v_115_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v_v_115_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_val_125_);
lean_inc(v_key_124_);
lean_dec(v_v_115_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint8_t v___x_129_; 
v___x_129_ = lean_name_eq(v_x_102_, v_key_124_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_127_);
v___x_130_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_124_, v_val_125_, v_x_102_, v_x_103_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
v___y_119_ = v___x_131_;
goto v___jp_118_;
}
else
{
lean_object* v___x_133_; 
lean_dec(v_val_125_);
lean_dec(v_key_124_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v_x_103_);
lean_ctor_set(v___x_127_, 0, v_x_102_);
v___x_133_ = v___x_127_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_x_102_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_x_103_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v___y_119_ = v___x_133_;
goto v___jp_118_;
}
}
}
}
case 1:
{
lean_object* v_node_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_146_; 
v_node_136_ = lean_ctor_get(v_v_115_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_v_115_);
if (v_isSharedCheck_146_ == 0)
{
v___x_138_ = v_v_115_;
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_node_136_);
lean_dec(v_v_115_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_140_ = lean_usize_shift_right(v_x_100_, v___x_105_);
v___x_141_ = lean_usize_add(v_x_101_, v___x_106_);
v___x_142_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_node_136_, v___x_140_, v___x_141_, v_x_102_, v_x_103_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_142_);
v___x_144_ = v___x_138_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v___y_119_ = v___x_144_;
goto v___jp_118_;
}
}
}
default: 
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_x_102_);
lean_ctor_set(v___x_147_, 1, v_x_103_);
v___y_119_ = v___x_147_;
goto v___jp_118_;
}
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = lean_array_fset(v_xs_x27_117_, v_j_109_, v___y_119_);
lean_dec(v_j_109_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_120_);
v___x_122_ = v___x_113_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
else
{
lean_object* v_ks_150_; lean_object* v_vs_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_171_; 
v_ks_150_ = lean_ctor_get(v_x_99_, 0);
v_vs_151_ = lean_ctor_get(v_x_99_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_171_ == 0)
{
v___x_153_ = v_x_99_;
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_vs_151_);
lean_inc(v_ks_150_);
lean_dec(v_x_99_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_ks_150_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_vs_151_);
v___x_156_ = v_reuseFailAlloc_170_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v_newNode_157_; uint8_t v___y_159_; size_t v___x_165_; uint8_t v___x_166_; 
v_newNode_157_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v___x_156_, v_x_102_, v_x_103_);
v___x_165_ = ((size_t)7ULL);
v___x_166_ = lean_usize_dec_le(v___x_165_, v_x_101_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_167_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_157_);
v___x_168_ = lean_unsigned_to_nat(4u);
v___x_169_ = lean_nat_dec_lt(v___x_167_, v___x_168_);
lean_dec(v___x_167_);
v___y_159_ = v___x_169_;
goto v___jp_158_;
}
else
{
v___y_159_ = v___x_166_;
goto v___jp_158_;
}
v___jp_158_:
{
if (v___y_159_ == 0)
{
lean_object* v_ks_160_; lean_object* v_vs_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_ks_160_ = lean_ctor_get(v_newNode_157_, 0);
lean_inc_ref(v_ks_160_);
v_vs_161_ = lean_ctor_get(v_newNode_157_, 1);
lean_inc_ref(v_vs_161_);
lean_dec_ref(v_newNode_157_);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__2);
v___x_164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_x_101_, v_ks_160_, v_vs_161_, v___x_162_, v___x_163_);
lean_dec_ref(v_vs_161_);
lean_dec_ref(v_ks_160_);
return v___x_164_;
}
else
{
return v_newNode_157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(size_t v_depth_172_, lean_object* v_keys_173_, lean_object* v_vals_174_, lean_object* v_i_175_, lean_object* v_entries_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_array_get_size(v_keys_173_);
v___x_178_ = lean_nat_dec_lt(v_i_175_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec(v_i_175_);
return v_entries_176_;
}
else
{
lean_object* v_k_179_; lean_object* v_v_180_; uint64_t v___y_182_; 
v_k_179_ = lean_array_fget_borrowed(v_keys_173_, v_i_175_);
v_v_180_ = lean_array_fget_borrowed(v_vals_174_, v_i_175_);
if (lean_obj_tag(v_k_179_) == 0)
{
uint64_t v___x_193_; 
v___x_193_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0);
v___y_182_ = v___x_193_;
goto v___jp_181_;
}
else
{
uint64_t v_hash_194_; 
v_hash_194_ = lean_ctor_get_uint64(v_k_179_, sizeof(void*)*2);
v___y_182_ = v_hash_194_;
goto v___jp_181_;
}
v___jp_181_:
{
size_t v_h_183_; size_t v___x_184_; lean_object* v___x_185_; size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v_h_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_h_183_ = lean_uint64_to_usize(v___y_182_);
v___x_184_ = ((size_t)5ULL);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_sub(v_depth_172_, v___x_186_);
v___x_188_ = lean_usize_mul(v___x_184_, v___x_187_);
v_h_189_ = lean_usize_shift_right(v_h_183_, v___x_188_);
v___x_190_ = lean_nat_add(v_i_175_, v___x_185_);
lean_dec(v_i_175_);
lean_inc(v_v_180_);
lean_inc(v_k_179_);
v___x_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_entries_176_, v_h_189_, v_depth_172_, v_k_179_, v_v_180_);
v_i_175_ = v___x_190_;
v_entries_176_ = v___x_191_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_195_, lean_object* v_keys_196_, lean_object* v_vals_197_, lean_object* v_i_198_, lean_object* v_entries_199_){
_start:
{
size_t v_depth_boxed_200_; lean_object* v_res_201_; 
v_depth_boxed_200_ = lean_unbox_usize(v_depth_195_);
lean_dec(v_depth_195_);
v_res_201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_boxed_200_, v_keys_196_, v_vals_197_, v_i_198_, v_entries_199_);
lean_dec_ref(v_vals_197_);
lean_dec_ref(v_keys_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___boxed(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
size_t v_x_2213__boxed_207_; size_t v_x_2214__boxed_208_; lean_object* v_res_209_; 
v_x_2213__boxed_207_ = lean_unbox_usize(v_x_203_);
lean_dec(v_x_203_);
v_x_2214__boxed_208_ = lean_unbox_usize(v_x_204_);
lean_dec(v_x_204_);
v_res_209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_202_, v_x_2213__boxed_207_, v_x_2214__boxed_208_, v_x_205_, v_x_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
uint64_t v___y_214_; 
if (lean_obj_tag(v_x_211_) == 0)
{
uint64_t v___x_218_; 
v___x_218_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0);
v___y_214_ = v___x_218_;
goto v___jp_213_;
}
else
{
uint64_t v_hash_219_; 
v_hash_219_ = lean_ctor_get_uint64(v_x_211_, sizeof(void*)*2);
v___y_214_ = v_hash_219_;
goto v___jp_213_;
}
v___jp_213_:
{
size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_uint64_to_usize(v___y_214_);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_210_, v___x_215_, v___x_216_, v_x_211_, v_x_212_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0(lean_object* v_fnName_220_, lean_object* v___x_221_, lean_object* v_cache_222_){
_start:
{
lean_object* v_eqnTheorems_223_; lean_object* v_unfoldTheorems_224_; lean_object* v_matchTheorems_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_eqnTheorems_223_ = lean_ctor_get(v_cache_222_, 0);
v_unfoldTheorems_224_ = lean_ctor_get(v_cache_222_, 1);
v_matchTheorems_225_ = lean_ctor_get(v_cache_222_, 2);
v_isSharedCheck_233_ = !lean_is_exclusive(v_cache_222_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v_cache_222_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_matchTheorems_225_);
lean_inc(v_unfoldTheorems_224_);
lean_inc(v_eqnTheorems_223_);
lean_dec(v_cache_222_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_eqnTheorems_223_, v_fnName_220_, v___x_221_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_unfoldTheorems_224_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_matchTheorems_225_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(size_t v_sz_234_, size_t v_i_235_, lean_object* v_bs_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = lean_usize_dec_lt(v_i_235_, v_sz_234_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_bs_236_);
return v___x_243_;
}
else
{
lean_object* v_v_244_; lean_object* v___x_245_; 
v_v_244_ = lean_array_uget_borrowed(v_bs_236_, v_i_235_);
lean_inc(v_v_244_);
v___x_245_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_v_244_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; lean_object* v_bs_x27_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v___x_245_);
v___x_247_ = lean_unsigned_to_nat(0u);
v_bs_x27_248_ = lean_array_uset(v_bs_236_, v_i_235_, v___x_247_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_add(v_i_235_, v___x_249_);
v___x_251_ = lean_array_uset(v_bs_x27_248_, v_i_235_, v_a_246_);
v_i_235_ = v___x_250_;
v_bs_236_ = v___x_251_;
goto _start;
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v_bs_236_);
v_a_253_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_245_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_245_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1___boxed(lean_object* v_sz_261_, lean_object* v_i_262_, lean_object* v_bs_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
size_t v_sz_boxed_269_; size_t v_i_boxed_270_; lean_object* v_res_271_; 
v_sz_boxed_269_ = lean_unbox_usize(v_sz_261_);
lean_dec(v_sz_261_);
v_i_boxed_270_ = lean_unbox_usize(v_i_262_);
lean_dec(v_i_262_);
v_res_271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_boxed_269_, v_i_boxed_270_, v_bs_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_272_, lean_object* v_vals_273_, lean_object* v_i_274_, lean_object* v_k_275_){
_start:
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_array_get_size(v_keys_272_);
v___x_277_ = lean_nat_dec_lt(v_i_274_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec(v_i_274_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
lean_object* v_k_x27_279_; uint8_t v___x_280_; 
v_k_x27_279_ = lean_array_fget_borrowed(v_keys_272_, v_i_274_);
v___x_280_ = lean_name_eq(v_k_275_, v_k_x27_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_add(v_i_274_, v___x_281_);
lean_dec(v_i_274_);
v_i_274_ = v___x_282_;
goto _start;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_array_fget_borrowed(v_vals_273_, v_i_274_);
lean_dec(v_i_274_);
lean_inc(v___x_284_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_286_, v_vals_287_, v_i_288_, v_k_289_);
lean_dec(v_k_289_);
lean_dec_ref(v_vals_287_);
lean_dec_ref(v_keys_286_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(lean_object* v_x_291_, size_t v_x_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v_es_294_; lean_object* v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; lean_object* v_j_299_; lean_object* v___x_300_; 
v_es_294_ = lean_ctor_get(v_x_291_, 0);
v___x_295_ = lean_box(2);
v___x_296_ = ((size_t)5ULL);
v___x_297_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__1);
v___x_298_ = lean_usize_land(v_x_292_, v___x_297_);
v_j_299_ = lean_usize_to_nat(v___x_298_);
v___x_300_ = lean_array_get_borrowed(v___x_295_, v_es_294_, v_j_299_);
lean_dec(v_j_299_);
switch(lean_obj_tag(v___x_300_))
{
case 0:
{
lean_object* v_key_301_; lean_object* v_val_302_; uint8_t v___x_303_; 
v_key_301_ = lean_ctor_get(v___x_300_, 0);
v_val_302_ = lean_ctor_get(v___x_300_, 1);
v___x_303_ = lean_name_eq(v_x_293_, v_key_301_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
lean_inc(v_val_302_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_val_302_);
return v___x_305_;
}
}
case 1:
{
lean_object* v_node_306_; size_t v___x_307_; 
v_node_306_ = lean_ctor_get(v___x_300_, 0);
v___x_307_ = lean_usize_shift_right(v_x_292_, v___x_296_);
v_x_291_ = v_node_306_;
v_x_292_ = v___x_307_;
goto _start;
}
default: 
{
lean_object* v___x_309_; 
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
}
else
{
lean_object* v_ks_310_; lean_object* v_vs_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_ks_310_ = lean_ctor_get(v_x_291_, 0);
v_vs_311_ = lean_ctor_get(v_x_291_, 1);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_ks_310_, v_vs_311_, v___x_312_, v_x_293_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg___boxed(lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
size_t v_x_2491__boxed_317_; lean_object* v_res_318_; 
v_x_2491__boxed_317_ = lean_unbox_usize(v_x_315_);
lean_dec(v_x_315_);
v_res_318_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_314_, v_x_2491__boxed_317_, v_x_316_);
lean_dec(v_x_316_);
lean_dec_ref(v_x_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
uint64_t v___y_322_; 
if (lean_obj_tag(v_x_320_) == 0)
{
uint64_t v___x_325_; 
v___x_325_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___closed__0);
v___y_322_ = v___x_325_;
goto v___jp_321_;
}
else
{
uint64_t v_hash_326_; 
v_hash_326_ = lean_ctor_get_uint64(v_x_320_, sizeof(void*)*2);
v___y_322_ = v_hash_326_;
goto v___jp_321_;
}
v___jp_321_:
{
size_t v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_uint64_to_usize(v___y_322_);
v___x_324_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_319_, v___x_323_, v_x_320_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg___boxed(lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_327_, v_x_328_);
lean_dec(v_x_328_);
lean_dec_ref(v_x_327_);
return v_res_329_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_336_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
lean_ctor_set(v___x_336_, 3, v___x_335_);
lean_ctor_set(v___x_336_, 4, v___x_335_);
lean_ctor_set(v___x_336_, 5, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems(lean_object* v_fnName_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v_asyncMode_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v_eqnTheorems_350_; lean_object* v___x_351_; 
v___x_343_ = lean_st_ref_get(v_a_341_);
v_env_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_env_344_);
lean_dec(v___x_343_);
v___x_345_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_346_ = lean_ctor_get(v___x_345_, 2);
v___x_347_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_348_ = lean_box(0);
v___x_349_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_347_, v___x_345_, v_env_344_, v_asyncMode_346_, v___x_348_);
v_eqnTheorems_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc_ref(v_eqnTheorems_350_);
lean_dec(v___x_349_);
v___x_351_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_eqnTheorems_350_, v_fnName_337_);
lean_dec_ref(v_eqnTheorems_350_);
if (lean_obj_tag(v___x_351_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_fnName_337_);
v_val_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_val_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 0);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_val_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v___x_360_; 
lean_dec(v___x_351_);
lean_inc(v_fnName_337_);
v___x_360_ = l_Lean_Meta_getEqnsFor_x3f(v_fnName_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_428_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_428_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_428_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_428_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
if (lean_obj_tag(v_a_361_) == 1)
{
lean_object* v_val_365_; size_t v_sz_366_; size_t v___x_367_; lean_object* v___x_368_; 
lean_del_object(v___x_363_);
v_val_365_ = lean_ctor_get(v_a_361_, 0);
lean_inc(v_val_365_);
lean_dec_ref(v_a_361_);
v_sz_366_ = lean_array_size(v_val_365_);
v___x_367_ = ((size_t)0ULL);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_366_, v___x_367_, v_val_365_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_415_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_415_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_415_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_415_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v_env_374_; lean_object* v_nextMacroScope_375_; lean_object* v_ngen_376_; lean_object* v_auxDeclNGen_377_; lean_object* v_traceState_378_; lean_object* v_messages_379_; lean_object* v_infoState_380_; lean_object* v_snapshotTasks_381_; lean_object* v_newDecls_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_413_; 
v___x_373_ = lean_st_ref_take(v_a_341_);
v_env_374_ = lean_ctor_get(v___x_373_, 0);
v_nextMacroScope_375_ = lean_ctor_get(v___x_373_, 1);
v_ngen_376_ = lean_ctor_get(v___x_373_, 2);
v_auxDeclNGen_377_ = lean_ctor_get(v___x_373_, 3);
v_traceState_378_ = lean_ctor_get(v___x_373_, 4);
v_messages_379_ = lean_ctor_get(v___x_373_, 6);
v_infoState_380_ = lean_ctor_get(v___x_373_, 7);
v_snapshotTasks_381_ = lean_ctor_get(v___x_373_, 8);
v_newDecls_382_ = lean_ctor_get(v___x_373_, 9);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_373_, 5);
lean_dec(v_unused_414_);
v___x_384_ = v___x_373_;
v_isShared_385_ = v_isSharedCheck_413_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_newDecls_382_);
lean_inc(v_snapshotTasks_381_);
lean_inc(v_infoState_380_);
lean_inc(v_messages_379_);
lean_inc(v_traceState_378_);
lean_inc(v_auxDeclNGen_377_);
lean_inc(v_ngen_376_);
lean_inc(v_nextMacroScope_375_);
lean_inc(v_env_374_);
lean_dec(v___x_373_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_413_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_386_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_387_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_386_, v_a_369_);
lean_dec(v_a_369_);
lean_inc_ref(v___x_387_);
v___f_388_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0), 3, 2);
lean_closure_set(v___f_388_, 0, v_fnName_337_);
lean_closure_set(v___f_388_, 1, v___x_387_);
v___x_389_ = l_Lean_EnvExtension_modifyState___redArg(v___x_345_, v_env_374_, v___f_388_, v_asyncMode_346_, v___x_348_);
v___x_390_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 5, v___x_390_);
lean_ctor_set(v___x_384_, 0, v___x_389_);
v___x_392_ = v___x_384_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_nextMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_ngen_376_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_auxDeclNGen_377_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_traceState_378_);
lean_ctor_set(v_reuseFailAlloc_412_, 5, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_412_, 6, v_messages_379_);
lean_ctor_set(v_reuseFailAlloc_412_, 7, v_infoState_380_);
lean_ctor_set(v_reuseFailAlloc_412_, 8, v_snapshotTasks_381_);
lean_ctor_set(v_reuseFailAlloc_412_, 9, v_newDecls_382_);
v___x_392_ = v_reuseFailAlloc_412_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_mctx_395_; lean_object* v_zetaDeltaFVarIds_396_; lean_object* v_postponed_397_; lean_object* v_diag_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_410_; 
v___x_393_ = lean_st_ref_set(v_a_341_, v___x_392_);
v___x_394_ = lean_st_ref_take(v_a_339_);
v_mctx_395_ = lean_ctor_get(v___x_394_, 0);
v_zetaDeltaFVarIds_396_ = lean_ctor_get(v___x_394_, 2);
v_postponed_397_ = lean_ctor_get(v___x_394_, 3);
v_diag_398_ = lean_ctor_get(v___x_394_, 4);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_394_, 1);
lean_dec(v_unused_411_);
v___x_400_ = v___x_394_;
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_diag_398_);
lean_inc(v_postponed_397_);
lean_inc(v_zetaDeltaFVarIds_396_);
lean_inc(v_mctx_395_);
lean_dec(v___x_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_mctx_395_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_zetaDeltaFVarIds_396_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_postponed_397_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_diag_398_);
v___x_404_ = v_reuseFailAlloc_409_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_st_ref_set(v_a_339_, v___x_404_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_387_);
v___x_407_ = v___x_371_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_387_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_fnName_337_);
v_a_416_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_368_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_368_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_426_; 
lean_dec(v_a_361_);
lean_dec(v_fnName_337_);
v___x_424_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_424_);
v___x_426_ = v___x_363_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_fnName_337_);
v_a_429_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_360_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_360_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___boxed(lean_object* v_fnName_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Tactic_Cbv_getEqnTheorems(v_fnName_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(lean_object* v_00_u03b2_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___boxed(lean_object* v_00_u03b2_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(v_00_u03b2_448_, v_x_449_, v_x_450_);
lean_dec(v_x_450_);
lean_dec_ref(v_x_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2(lean_object* v_00_u03b2_452_, lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_x_453_, v_x_454_, v_x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(lean_object* v_00_u03b2_457_, lean_object* v_x_458_, size_t v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_458_, v_x_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___boxed(lean_object* v_00_u03b2_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
size_t v_x_2768__boxed_466_; lean_object* v_res_467_; 
v_x_2768__boxed_466_ = lean_unbox_usize(v_x_464_);
lean_dec(v_x_464_);
v_res_467_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(v_00_u03b2_462_, v_x_463_, v_x_2768__boxed_466_, v_x_465_);
lean_dec(v_x_465_);
lean_dec_ref(v_x_463_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, size_t v_x_470_, size_t v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_469_, v_x_470_, v_x_471_, v_x_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___boxed(lean_object* v_00_u03b2_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
size_t v_x_2779__boxed_481_; size_t v_x_2780__boxed_482_; lean_object* v_res_483_; 
v_x_2779__boxed_481_ = lean_unbox_usize(v_x_477_);
lean_dec(v_x_477_);
v_x_2780__boxed_482_ = lean_unbox_usize(v_x_478_);
lean_dec(v_x_478_);
v_res_483_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(v_00_u03b2_475_, v_x_476_, v_x_2779__boxed_481_, v_x_2780__boxed_482_, v_x_479_, v_x_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_484_, lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_heq_487_, lean_object* v_i_488_, lean_object* v_k_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_485_, v_vals_486_, v_i_488_, v_k_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_491_, lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_heq_494_, lean_object* v_i_495_, lean_object* v_k_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(v_00_u03b2_491_, v_keys_492_, v_vals_493_, v_heq_494_, v_i_495_, v_k_496_);
lean_dec(v_k_496_);
lean_dec_ref(v_vals_493_);
lean_dec_ref(v_keys_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_498_, lean_object* v_n_499_, lean_object* v_k_500_, lean_object* v_v_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v_n_499_, v_k_500_, v_v_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_503_, size_t v_depth_504_, lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_heq_507_, lean_object* v_i_508_, lean_object* v_entries_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_504_, v_keys_505_, v_vals_506_, v_i_508_, v_entries_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_511_, lean_object* v_depth_512_, lean_object* v_keys_513_, lean_object* v_vals_514_, lean_object* v_heq_515_, lean_object* v_i_516_, lean_object* v_entries_517_){
_start:
{
size_t v_depth_boxed_518_; lean_object* v_res_519_; 
v_depth_boxed_518_ = lean_unbox_usize(v_depth_512_);
lean_dec(v_depth_512_);
v_res_519_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(v_00_u03b2_511_, v_depth_boxed_518_, v_keys_513_, v_vals_514_, v_heq_515_, v_i_516_, v_entries_517_);
lean_dec_ref(v_vals_514_);
lean_dec_ref(v_keys_513_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(v_x_521_, v_x_522_, v_x_523_, v_x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0(lean_object* v_fnName_526_, lean_object* v_a_527_, lean_object* v_cache_528_){
_start:
{
lean_object* v_eqnTheorems_529_; lean_object* v_unfoldTheorems_530_; lean_object* v_matchTheorems_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
v_eqnTheorems_529_ = lean_ctor_get(v_cache_528_, 0);
v_unfoldTheorems_530_ = lean_ctor_get(v_cache_528_, 1);
v_matchTheorems_531_ = lean_ctor_get(v_cache_528_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v_cache_528_);
if (v_isSharedCheck_539_ == 0)
{
v___x_533_ = v_cache_528_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_matchTheorems_531_);
lean_inc(v_unfoldTheorems_530_);
lean_inc(v_eqnTheorems_529_);
lean_dec(v_cache_528_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_unfoldTheorems_530_, v_fnName_526_, v_a_527_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_eqnTheorems_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_matchTheorems_531_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0(void){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1);
v___x_546_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
lean_ctor_set(v___x_546_, 3, v___x_545_);
lean_ctor_set(v___x_546_, 4, v___x_545_);
lean_ctor_set(v___x_546_, 5, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(lean_object* v_fnName_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; lean_object* v_env_554_; lean_object* v___x_555_; lean_object* v_asyncMode_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_unfoldTheorems_560_; lean_object* v___x_561_; 
v___x_553_ = lean_st_ref_get(v_a_551_);
v_env_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc_ref(v_env_554_);
lean_dec(v___x_553_);
v___x_555_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_556_ = lean_ctor_get(v___x_555_, 2);
v___x_557_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_558_ = lean_box(0);
v___x_559_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_557_, v___x_555_, v_env_554_, v_asyncMode_556_, v___x_558_);
v_unfoldTheorems_560_ = lean_ctor_get(v___x_559_, 1);
lean_inc_ref(v_unfoldTheorems_560_);
lean_dec(v___x_559_);
v___x_561_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_unfoldTheorems_560_, v_fnName_547_);
lean_dec_ref(v_unfoldTheorems_560_);
if (lean_obj_tag(v___x_561_) == 1)
{
lean_object* v___x_562_; 
lean_dec(v_fnName_547_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
else
{
uint8_t v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_561_);
v___x_563_ = 1;
lean_inc(v_fnName_547_);
v___x_564_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fnName_547_, v___x_563_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_635_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_635_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_635_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_635_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 1)
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_630_; 
lean_del_object(v___x_567_);
v_val_569_ = lean_ctor_get(v_a_565_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_630_ == 0)
{
v___x_571_ = v_a_565_;
v_isShared_572_ = v_isSharedCheck_630_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v_a_565_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_630_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_val_569_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_621_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_621_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_621_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_621_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v_env_579_; lean_object* v_nextMacroScope_580_; lean_object* v_ngen_581_; lean_object* v_auxDeclNGen_582_; lean_object* v_traceState_583_; lean_object* v_messages_584_; lean_object* v_infoState_585_; lean_object* v_snapshotTasks_586_; lean_object* v_newDecls_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_619_; 
v___x_578_ = lean_st_ref_take(v_a_551_);
v_env_579_ = lean_ctor_get(v___x_578_, 0);
v_nextMacroScope_580_ = lean_ctor_get(v___x_578_, 1);
v_ngen_581_ = lean_ctor_get(v___x_578_, 2);
v_auxDeclNGen_582_ = lean_ctor_get(v___x_578_, 3);
v_traceState_583_ = lean_ctor_get(v___x_578_, 4);
v_messages_584_ = lean_ctor_get(v___x_578_, 6);
v_infoState_585_ = lean_ctor_get(v___x_578_, 7);
v_snapshotTasks_586_ = lean_ctor_get(v___x_578_, 8);
v_newDecls_587_ = lean_ctor_get(v___x_578_, 9);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_578_, 5);
lean_dec(v_unused_620_);
v___x_589_ = v___x_578_;
v_isShared_590_ = v_isSharedCheck_619_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_newDecls_587_);
lean_inc(v_snapshotTasks_586_);
lean_inc(v_infoState_585_);
lean_inc(v_messages_584_);
lean_inc(v_traceState_583_);
lean_inc(v_auxDeclNGen_582_);
lean_inc(v_ngen_581_);
lean_inc(v_nextMacroScope_580_);
lean_inc(v_env_579_);
lean_dec(v___x_578_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_619_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
lean_inc(v_a_574_);
v___f_591_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0), 3, 2);
lean_closure_set(v___f_591_, 0, v_fnName_547_);
lean_closure_set(v___f_591_, 1, v_a_574_);
v___x_592_ = l_Lean_EnvExtension_modifyState___redArg(v___x_555_, v_env_579_, v___f_591_, v_asyncMode_556_, v___x_558_);
v___x_593_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 5, v___x_593_);
lean_ctor_set(v___x_589_, 0, v___x_592_);
v___x_595_ = v___x_589_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_nextMacroScope_580_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_ngen_581_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_auxDeclNGen_582_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_traceState_583_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_618_, 6, v_messages_584_);
lean_ctor_set(v_reuseFailAlloc_618_, 7, v_infoState_585_);
lean_ctor_set(v_reuseFailAlloc_618_, 8, v_snapshotTasks_586_);
lean_ctor_set(v_reuseFailAlloc_618_, 9, v_newDecls_587_);
v___x_595_ = v_reuseFailAlloc_618_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_mctx_598_; lean_object* v_zetaDeltaFVarIds_599_; lean_object* v_postponed_600_; lean_object* v_diag_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_616_; 
v___x_596_ = lean_st_ref_set(v_a_551_, v___x_595_);
v___x_597_ = lean_st_ref_take(v_a_549_);
v_mctx_598_ = lean_ctor_get(v___x_597_, 0);
v_zetaDeltaFVarIds_599_ = lean_ctor_get(v___x_597_, 2);
v_postponed_600_ = lean_ctor_get(v___x_597_, 3);
v_diag_601_ = lean_ctor_get(v___x_597_, 4);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_597_, 1);
lean_dec(v_unused_617_);
v___x_603_ = v___x_597_;
v_isShared_604_ = v_isSharedCheck_616_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_diag_601_);
lean_inc(v_postponed_600_);
lean_inc(v_zetaDeltaFVarIds_599_);
lean_inc(v_mctx_598_);
lean_dec(v___x_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_616_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_mctx_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_zetaDeltaFVarIds_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_postponed_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_diag_601_);
v___x_607_ = v_reuseFailAlloc_615_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_st_ref_set(v_a_549_, v___x_607_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_a_574_);
v___x_610_ = v___x_571_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_574_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_610_);
v___x_612_ = v___x_576_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_del_object(v___x_571_);
lean_dec(v_fnName_547_);
v_a_622_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_573_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_573_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_633_; 
lean_dec(v_a_565_);
lean_dec(v_fnName_547_);
v___x_631_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_631_);
v___x_633_ = v___x_567_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_fnName_547_);
v_a_636_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_564_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_564_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___boxed(lean_object* v_fnName_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(v_fnName_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0(lean_object* v_matcherName_651_, lean_object* v___x_652_, lean_object* v_cache_653_){
_start:
{
lean_object* v_eqnTheorems_654_; lean_object* v_unfoldTheorems_655_; lean_object* v_matchTheorems_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_eqnTheorems_654_ = lean_ctor_get(v_cache_653_, 0);
v_unfoldTheorems_655_ = lean_ctor_get(v_cache_653_, 1);
v_matchTheorems_656_ = lean_ctor_get(v_cache_653_, 2);
v_isSharedCheck_664_ = !lean_is_exclusive(v_cache_653_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v_cache_653_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_matchTheorems_656_);
lean_inc(v_unfoldTheorems_655_);
lean_inc(v_eqnTheorems_654_);
lean_dec(v_cache_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_matchTheorems_656_, v_matcherName_651_, v___x_652_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 2, v___x_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_eqnTheorems_654_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_unfoldTheorems_655_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object* v_matcherName_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; lean_object* v_env_672_; lean_object* v___x_673_; lean_object* v_asyncMode_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_matchTheorems_678_; lean_object* v___x_679_; 
v___x_671_ = lean_st_ref_get(v_a_669_);
v_env_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref(v_env_672_);
lean_dec(v___x_671_);
v___x_673_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_674_ = lean_ctor_get(v___x_673_, 2);
v___x_675_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_676_ = lean_box(0);
v___x_677_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_675_, v___x_673_, v_env_672_, v_asyncMode_674_, v___x_676_);
v_matchTheorems_678_ = lean_ctor_get(v___x_677_, 2);
lean_inc_ref(v_matchTheorems_678_);
lean_dec(v___x_677_);
v___x_679_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_matchTheorems_678_, v_matcherName_665_);
lean_dec_ref(v_matchTheorems_678_);
if (lean_obj_tag(v___x_679_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_matcherName_665_);
v_val_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_val_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
else
{
lean_object* v___x_688_; 
lean_dec(v___x_679_);
lean_inc(v_a_669_);
lean_inc_ref(v_a_668_);
lean_inc(v_a_667_);
lean_inc_ref(v_a_666_);
lean_inc(v_matcherName_665_);
v___x_688_ = lean_get_match_equations_for(v_matcherName_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v_eqnNames_690_; size_t v_sz_691_; size_t v___x_692_; lean_object* v___x_693_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___x_688_);
v_eqnNames_690_ = lean_ctor_get(v_a_689_, 0);
lean_inc_ref(v_eqnNames_690_);
lean_dec(v_a_689_);
v_sz_691_ = lean_array_size(v_eqnNames_690_);
v___x_692_ = ((size_t)0ULL);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_691_, v___x_692_, v_eqnNames_690_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_740_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_740_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_740_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_740_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v_env_699_; lean_object* v_nextMacroScope_700_; lean_object* v_ngen_701_; lean_object* v_auxDeclNGen_702_; lean_object* v_traceState_703_; lean_object* v_messages_704_; lean_object* v_infoState_705_; lean_object* v_snapshotTasks_706_; lean_object* v_newDecls_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_738_; 
v___x_698_ = lean_st_ref_take(v_a_669_);
v_env_699_ = lean_ctor_get(v___x_698_, 0);
v_nextMacroScope_700_ = lean_ctor_get(v___x_698_, 1);
v_ngen_701_ = lean_ctor_get(v___x_698_, 2);
v_auxDeclNGen_702_ = lean_ctor_get(v___x_698_, 3);
v_traceState_703_ = lean_ctor_get(v___x_698_, 4);
v_messages_704_ = lean_ctor_get(v___x_698_, 6);
v_infoState_705_ = lean_ctor_get(v___x_698_, 7);
v_snapshotTasks_706_ = lean_ctor_get(v___x_698_, 8);
v_newDecls_707_ = lean_ctor_get(v___x_698_, 9);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_698_, 5);
lean_dec(v_unused_739_);
v___x_709_ = v___x_698_;
v_isShared_710_ = v_isSharedCheck_738_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_newDecls_707_);
lean_inc(v_snapshotTasks_706_);
lean_inc(v_infoState_705_);
lean_inc(v_messages_704_);
lean_inc(v_traceState_703_);
lean_inc(v_auxDeclNGen_702_);
lean_inc(v_ngen_701_);
lean_inc(v_nextMacroScope_700_);
lean_inc(v_env_699_);
lean_dec(v___x_698_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_738_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_711_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_712_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_711_, v_a_694_);
lean_dec(v_a_694_);
lean_inc_ref(v___x_712_);
v___f_713_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0), 3, 2);
lean_closure_set(v___f_713_, 0, v_matcherName_665_);
lean_closure_set(v___f_713_, 1, v___x_712_);
v___x_714_ = l_Lean_EnvExtension_modifyState___redArg(v___x_673_, v_env_699_, v___f_713_, v_asyncMode_674_, v___x_676_);
v___x_715_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 5, v___x_715_);
lean_ctor_set(v___x_709_, 0, v___x_714_);
v___x_717_ = v___x_709_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_nextMacroScope_700_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_ngen_701_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_auxDeclNGen_702_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_traceState_703_);
lean_ctor_set(v_reuseFailAlloc_737_, 5, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_737_, 6, v_messages_704_);
lean_ctor_set(v_reuseFailAlloc_737_, 7, v_infoState_705_);
lean_ctor_set(v_reuseFailAlloc_737_, 8, v_snapshotTasks_706_);
lean_ctor_set(v_reuseFailAlloc_737_, 9, v_newDecls_707_);
v___x_717_ = v_reuseFailAlloc_737_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_mctx_720_; lean_object* v_zetaDeltaFVarIds_721_; lean_object* v_postponed_722_; lean_object* v_diag_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_735_; 
v___x_718_ = lean_st_ref_set(v_a_669_, v___x_717_);
v___x_719_ = lean_st_ref_take(v_a_667_);
v_mctx_720_ = lean_ctor_get(v___x_719_, 0);
v_zetaDeltaFVarIds_721_ = lean_ctor_get(v___x_719_, 2);
v_postponed_722_ = lean_ctor_get(v___x_719_, 3);
v_diag_723_ = lean_ctor_get(v___x_719_, 4);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_719_, 1);
lean_dec(v_unused_736_);
v___x_725_ = v___x_719_;
v_isShared_726_ = v_isSharedCheck_735_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_diag_723_);
lean_inc(v_postponed_722_);
lean_inc(v_zetaDeltaFVarIds_721_);
lean_inc(v_mctx_720_);
lean_dec(v___x_719_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_735_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_mctx_720_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_zetaDeltaFVarIds_721_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_postponed_722_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_diag_723_);
v___x_729_ = v_reuseFailAlloc_734_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_st_ref_set(v_a_667_, v___x_729_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_712_);
v___x_732_ = v___x_696_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_712_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_matcherName_665_);
v_a_741_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_693_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_693_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_matcherName_665_);
v_a_749_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_688_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_688_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___boxed(lean_object* v_matcherName_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_matcherName_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_763_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState);
res = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_TheoremsLookup_3695032707____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
}
#ifdef __cplusplus
}
#endif
