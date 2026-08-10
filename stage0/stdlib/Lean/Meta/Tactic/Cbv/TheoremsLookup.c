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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0;
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(lean_object* v_x_91_, size_t v_x_92_, size_t v_x_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v_es_96_; size_t v___x_97_; size_t v___x_98_; lean_object* v_j_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_es_96_ = lean_ctor_get(v_x_91_, 0);
v___x_97_ = ((size_t)31ULL);
v___x_98_ = lean_usize_land(v_x_92_, v___x_97_);
v_j_99_ = lean_usize_to_nat(v___x_98_);
v___x_100_ = lean_array_get_size(v_es_96_);
v___x_101_ = lean_nat_dec_lt(v_j_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_dec(v_j_99_);
lean_dec(v_x_95_);
lean_dec(v_x_94_);
return v_x_91_;
}
else
{
lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_140_; 
lean_inc_ref(v_es_96_);
v_isSharedCheck_140_ = !lean_is_exclusive(v_x_91_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_x_91_, 0);
lean_dec(v_unused_141_);
v___x_103_ = v_x_91_;
v_isShared_104_ = v_isSharedCheck_140_;
goto v_resetjp_102_;
}
else
{
lean_dec(v_x_91_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_140_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_v_105_; lean_object* v___x_106_; lean_object* v_xs_x27_107_; lean_object* v___y_109_; 
v_v_105_ = lean_array_fget(v_es_96_, v_j_99_);
v___x_106_ = lean_box(0);
v_xs_x27_107_ = lean_array_fset(v_es_96_, v_j_99_, v___x_106_);
switch(lean_obj_tag(v_v_105_))
{
case 0:
{
lean_object* v_key_114_; lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_125_; 
v_key_114_ = lean_ctor_get(v_v_105_, 0);
v_val_115_ = lean_ctor_get(v_v_105_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_v_105_);
if (v_isSharedCheck_125_ == 0)
{
v___x_117_ = v_v_105_;
v_isShared_118_ = v_isSharedCheck_125_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_inc(v_key_114_);
lean_dec(v_v_105_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_125_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
uint8_t v___x_119_; 
v___x_119_ = lean_name_eq(v_x_94_, v_key_114_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_del_object(v___x_117_);
v___x_120_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_114_, v_val_115_, v_x_94_, v_x_95_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
v___y_109_ = v___x_121_;
goto v___jp_108_;
}
else
{
lean_object* v___x_123_; 
lean_dec(v_val_115_);
lean_dec(v_key_114_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_x_95_);
lean_ctor_set(v___x_117_, 0, v_x_94_);
v___x_123_ = v___x_117_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_x_94_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_x_95_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
v___y_109_ = v___x_123_;
goto v___jp_108_;
}
}
}
}
case 1:
{
lean_object* v_node_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_138_; 
v_node_126_ = lean_ctor_get(v_v_105_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v_v_105_);
if (v_isSharedCheck_138_ == 0)
{
v___x_128_ = v_v_105_;
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_node_126_);
lean_dec(v_v_105_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_138_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_130_ = ((size_t)5ULL);
v___x_131_ = lean_usize_shift_right(v_x_92_, v___x_130_);
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_add(v_x_93_, v___x_132_);
v___x_134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_node_126_, v___x_131_, v___x_133_, v_x_94_, v_x_95_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_134_);
v___x_136_ = v___x_128_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v___y_109_ = v___x_136_;
goto v___jp_108_;
}
}
}
default: 
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_x_94_);
lean_ctor_set(v___x_139_, 1, v_x_95_);
v___y_109_ = v___x_139_;
goto v___jp_108_;
}
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_array_fset(v_xs_x27_107_, v_j_99_, v___y_109_);
lean_dec(v_j_99_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_110_);
v___x_112_ = v___x_103_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
else
{
lean_object* v_ks_142_; lean_object* v_vs_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_163_; 
v_ks_142_ = lean_ctor_get(v_x_91_, 0);
v_vs_143_ = lean_ctor_get(v_x_91_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_91_);
if (v_isSharedCheck_163_ == 0)
{
v___x_145_ = v_x_91_;
v_isShared_146_ = v_isSharedCheck_163_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_vs_143_);
lean_inc(v_ks_142_);
lean_dec(v_x_91_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_163_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_ks_142_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_vs_143_);
v___x_148_ = v_reuseFailAlloc_162_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v_newNode_149_; uint8_t v___y_151_; size_t v___x_157_; uint8_t v___x_158_; 
v_newNode_149_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v___x_148_, v_x_94_, v_x_95_);
v___x_157_ = ((size_t)7ULL);
v___x_158_ = lean_usize_dec_le(v___x_157_, v_x_93_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_159_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_149_);
v___x_160_ = lean_unsigned_to_nat(4u);
v___x_161_ = lean_nat_dec_lt(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
v___y_151_ = v___x_161_;
goto v___jp_150_;
}
else
{
v___y_151_ = v___x_158_;
goto v___jp_150_;
}
v___jp_150_:
{
if (v___y_151_ == 0)
{
lean_object* v_ks_152_; lean_object* v_vs_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_ks_152_ = lean_ctor_get(v_newNode_149_, 0);
lean_inc_ref(v_ks_152_);
v_vs_153_ = lean_ctor_get(v_newNode_149_, 1);
lean_inc_ref(v_vs_153_);
lean_dec_ref(v_newNode_149_);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0);
v___x_156_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_x_93_, v_ks_152_, v_vs_153_, v___x_154_, v___x_155_);
lean_dec_ref(v_vs_153_);
lean_dec_ref(v_ks_152_);
return v___x_156_;
}
else
{
return v_newNode_149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(size_t v_depth_164_, lean_object* v_keys_165_, lean_object* v_vals_166_, lean_object* v_i_167_, lean_object* v_entries_168_){
_start:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_array_get_size(v_keys_165_);
v___x_170_ = lean_nat_dec_lt(v_i_167_, v___x_169_);
if (v___x_170_ == 0)
{
lean_dec(v_i_167_);
return v_entries_168_;
}
else
{
lean_object* v_k_171_; lean_object* v_v_172_; uint64_t v___y_174_; 
v_k_171_ = lean_array_fget_borrowed(v_keys_165_, v_i_167_);
v_v_172_ = lean_array_fget_borrowed(v_vals_166_, v_i_167_);
if (lean_obj_tag(v_k_171_) == 0)
{
uint64_t v___x_185_; 
v___x_185_ = 1723ULL;
v___y_174_ = v___x_185_;
goto v___jp_173_;
}
else
{
uint64_t v_hash_186_; 
v_hash_186_ = lean_ctor_get_uint64(v_k_171_, sizeof(void*)*2);
v___y_174_ = v_hash_186_;
goto v___jp_173_;
}
v___jp_173_:
{
size_t v_h_175_; size_t v___x_176_; lean_object* v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v_h_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_h_175_ = lean_uint64_to_usize(v___y_174_);
v___x_176_ = ((size_t)5ULL);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_sub(v_depth_164_, v___x_178_);
v___x_180_ = lean_usize_mul(v___x_176_, v___x_179_);
v_h_181_ = lean_usize_shift_right(v_h_175_, v___x_180_);
v___x_182_ = lean_nat_add(v_i_167_, v___x_177_);
lean_dec(v_i_167_);
lean_inc(v_v_172_);
lean_inc(v_k_171_);
v___x_183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_entries_168_, v_h_181_, v_depth_164_, v_k_171_, v_v_172_);
v_i_167_ = v___x_182_;
v_entries_168_ = v___x_183_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_187_, lean_object* v_keys_188_, lean_object* v_vals_189_, lean_object* v_i_190_, lean_object* v_entries_191_){
_start:
{
size_t v_depth_boxed_192_; lean_object* v_res_193_; 
v_depth_boxed_192_ = lean_unbox_usize(v_depth_187_);
lean_dec(v_depth_187_);
v_res_193_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_boxed_192_, v_keys_188_, v_vals_189_, v_i_190_, v_entries_191_);
lean_dec_ref(v_vals_189_);
lean_dec_ref(v_keys_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___boxed(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v_x_2176__boxed_199_; size_t v_x_2177__boxed_200_; lean_object* v_res_201_; 
v_x_2176__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_x_2177__boxed_200_ = lean_unbox_usize(v_x_196_);
lean_dec(v_x_196_);
v_res_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_194_, v_x_2176__boxed_199_, v_x_2177__boxed_200_, v_x_197_, v_x_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
uint64_t v___y_206_; 
if (lean_obj_tag(v_x_203_) == 0)
{
uint64_t v___x_210_; 
v___x_210_ = 1723ULL;
v___y_206_ = v___x_210_;
goto v___jp_205_;
}
else
{
uint64_t v_hash_211_; 
v_hash_211_ = lean_ctor_get_uint64(v_x_203_, sizeof(void*)*2);
v___y_206_ = v_hash_211_;
goto v___jp_205_;
}
v___jp_205_:
{
size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_uint64_to_usize(v___y_206_);
v___x_208_ = ((size_t)1ULL);
v___x_209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_202_, v___x_207_, v___x_208_, v_x_203_, v_x_204_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0(lean_object* v_fnName_212_, lean_object* v___x_213_, lean_object* v_cache_214_){
_start:
{
lean_object* v_eqnTheorems_215_; lean_object* v_unfoldTheorems_216_; lean_object* v_matchTheorems_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_eqnTheorems_215_ = lean_ctor_get(v_cache_214_, 0);
v_unfoldTheorems_216_ = lean_ctor_get(v_cache_214_, 1);
v_matchTheorems_217_ = lean_ctor_get(v_cache_214_, 2);
v_isSharedCheck_225_ = !lean_is_exclusive(v_cache_214_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v_cache_214_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_matchTheorems_217_);
lean_inc(v_unfoldTheorems_216_);
lean_inc(v_eqnTheorems_215_);
lean_dec(v_cache_214_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_eqnTheorems_215_, v_fnName_212_, v___x_213_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_unfoldTheorems_216_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_matchTheorems_217_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(size_t v_sz_226_, size_t v_i_227_, lean_object* v_bs_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_lt(v_i_227_, v_sz_226_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v_bs_228_);
return v___x_235_;
}
else
{
lean_object* v_v_236_; lean_object* v___x_237_; 
v_v_236_ = lean_array_uget_borrowed(v_bs_228_, v_i_227_);
lean_inc(v_v_236_);
v___x_237_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_v_236_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v_bs_x27_240_; size_t v___x_241_; size_t v___x_242_; lean_object* v___x_243_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = lean_unsigned_to_nat(0u);
v_bs_x27_240_ = lean_array_uset(v_bs_228_, v_i_227_, v___x_239_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_227_, v___x_241_);
v___x_243_ = lean_array_uset(v_bs_x27_240_, v_i_227_, v_a_238_);
v_i_227_ = v___x_242_;
v_bs_228_ = v___x_243_;
goto _start;
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_bs_228_);
v_a_245_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_237_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_237_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1___boxed(lean_object* v_sz_253_, lean_object* v_i_254_, lean_object* v_bs_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
size_t v_sz_boxed_261_; size_t v_i_boxed_262_; lean_object* v_res_263_; 
v_sz_boxed_261_ = lean_unbox_usize(v_sz_253_);
lean_dec(v_sz_253_);
v_i_boxed_262_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_res_263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_boxed_261_, v_i_boxed_262_, v_bs_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_264_, lean_object* v_vals_265_, lean_object* v_i_266_, lean_object* v_k_267_){
_start:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_array_get_size(v_keys_264_);
v___x_269_ = lean_nat_dec_lt(v_i_266_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec(v_i_266_);
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
lean_object* v_k_x27_271_; uint8_t v___x_272_; 
v_k_x27_271_ = lean_array_fget_borrowed(v_keys_264_, v_i_266_);
v___x_272_ = lean_name_eq(v_k_267_, v_k_x27_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_i_266_, v___x_273_);
lean_dec(v_i_266_);
v_i_266_ = v___x_274_;
goto _start;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_array_fget_borrowed(v_vals_265_, v_i_266_);
lean_dec(v_i_266_);
lean_inc(v___x_276_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_278_, lean_object* v_vals_279_, lean_object* v_i_280_, lean_object* v_k_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_278_, v_vals_279_, v_i_280_, v_k_281_);
lean_dec(v_k_281_);
lean_dec_ref(v_vals_279_);
lean_dec_ref(v_keys_278_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(lean_object* v_x_283_, size_t v_x_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_es_286_; lean_object* v___x_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v_j_290_; lean_object* v___x_291_; 
v_es_286_ = lean_ctor_get(v_x_283_, 0);
v___x_287_ = lean_box(2);
v___x_288_ = ((size_t)31ULL);
v___x_289_ = lean_usize_land(v_x_284_, v___x_288_);
v_j_290_ = lean_usize_to_nat(v___x_289_);
v___x_291_ = lean_array_get_borrowed(v___x_287_, v_es_286_, v_j_290_);
lean_dec(v_j_290_);
switch(lean_obj_tag(v___x_291_))
{
case 0:
{
lean_object* v_key_292_; lean_object* v_val_293_; uint8_t v___x_294_; 
v_key_292_ = lean_ctor_get(v___x_291_, 0);
v_val_293_ = lean_ctor_get(v___x_291_, 1);
v___x_294_ = lean_name_eq(v_x_285_, v_key_292_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v___x_296_; 
lean_inc(v_val_293_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v_val_293_);
return v___x_296_;
}
}
case 1:
{
lean_object* v_node_297_; size_t v___x_298_; size_t v___x_299_; 
v_node_297_ = lean_ctor_get(v___x_291_, 0);
v___x_298_ = ((size_t)5ULL);
v___x_299_ = lean_usize_shift_right(v_x_284_, v___x_298_);
v_x_283_ = v_node_297_;
v_x_284_ = v___x_299_;
goto _start;
}
default: 
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
}
else
{
lean_object* v_ks_302_; lean_object* v_vs_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_ks_302_ = lean_ctor_get(v_x_283_, 0);
v_vs_303_ = lean_ctor_get(v_x_283_, 1);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_ks_302_, v_vs_303_, v___x_304_, v_x_285_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg___boxed(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
size_t v_x_2437__boxed_309_; lean_object* v_res_310_; 
v_x_2437__boxed_309_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_res_310_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_306_, v_x_2437__boxed_309_, v_x_308_);
lean_dec(v_x_308_);
lean_dec_ref(v_x_306_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint64_t v___y_314_; 
if (lean_obj_tag(v_x_312_) == 0)
{
uint64_t v___x_317_; 
v___x_317_ = 1723ULL;
v___y_314_ = v___x_317_;
goto v___jp_313_;
}
else
{
uint64_t v_hash_318_; 
v_hash_318_ = lean_ctor_get_uint64(v_x_312_, sizeof(void*)*2);
v___y_314_ = v_hash_318_;
goto v___jp_313_;
}
v___jp_313_:
{
size_t v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_uint64_to_usize(v___y_314_);
v___x_316_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_311_, v___x_315_, v_x_312_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg___boxed(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_319_, v_x_320_);
lean_dec(v_x_320_);
lean_dec_ref(v_x_319_);
return v_res_321_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_328_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
lean_ctor_set(v___x_328_, 2, v___x_327_);
lean_ctor_set(v___x_328_, 3, v___x_327_);
lean_ctor_set(v___x_328_, 4, v___x_327_);
lean_ctor_set(v___x_328_, 5, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems(lean_object* v_fnName_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; lean_object* v_env_336_; lean_object* v___x_337_; lean_object* v_asyncMode_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_eqnTheorems_342_; lean_object* v___x_343_; 
v___x_335_ = lean_st_ref_get(v_a_333_);
v_env_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_ref(v_env_336_);
lean_dec(v___x_335_);
v___x_337_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_338_ = lean_ctor_get(v___x_337_, 2);
v___x_339_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_340_ = lean_box(0);
v___x_341_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_339_, v___x_337_, v_env_336_, v_asyncMode_338_, v___x_340_);
v_eqnTheorems_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc_ref(v_eqnTheorems_342_);
lean_dec(v___x_341_);
v___x_343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_eqnTheorems_342_, v_fnName_329_);
lean_dec_ref(v_eqnTheorems_342_);
if (lean_obj_tag(v___x_343_) == 1)
{
lean_object* v_val_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_fnName_329_);
v_val_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_val_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 0);
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_val_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
lean_object* v___x_352_; 
lean_dec(v___x_343_);
lean_inc(v_fnName_329_);
v___x_352_ = l_Lean_Meta_getEqnsFor_x3f(v_fnName_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_419_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_419_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_419_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_419_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
if (lean_obj_tag(v_a_353_) == 1)
{
lean_object* v_val_357_; size_t v_sz_358_; size_t v___x_359_; lean_object* v___x_360_; 
lean_del_object(v___x_355_);
v_val_357_ = lean_ctor_get(v_a_353_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v_a_353_, 1);
v_sz_358_ = lean_array_size(v_val_357_);
v___x_359_ = ((size_t)0ULL);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_358_, v___x_359_, v_val_357_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_406_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_406_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_406_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_406_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v_nextMacroScope_367_; lean_object* v_ngen_368_; lean_object* v_auxDeclNGen_369_; lean_object* v_traceState_370_; lean_object* v_messages_371_; lean_object* v_infoState_372_; lean_object* v_snapshotTasks_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_404_; 
v___x_365_ = lean_st_ref_take(v_a_333_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
v_nextMacroScope_367_ = lean_ctor_get(v___x_365_, 1);
v_ngen_368_ = lean_ctor_get(v___x_365_, 2);
v_auxDeclNGen_369_ = lean_ctor_get(v___x_365_, 3);
v_traceState_370_ = lean_ctor_get(v___x_365_, 4);
v_messages_371_ = lean_ctor_get(v___x_365_, 6);
v_infoState_372_ = lean_ctor_get(v___x_365_, 7);
v_snapshotTasks_373_ = lean_ctor_get(v___x_365_, 8);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v___x_365_, 5);
lean_dec(v_unused_405_);
v___x_375_ = v___x_365_;
v_isShared_376_ = v_isSharedCheck_404_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_snapshotTasks_373_);
lean_inc(v_infoState_372_);
lean_inc(v_messages_371_);
lean_inc(v_traceState_370_);
lean_inc(v_auxDeclNGen_369_);
lean_inc(v_ngen_368_);
lean_inc(v_nextMacroScope_367_);
lean_inc(v_env_366_);
lean_dec(v___x_365_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_404_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_377_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_378_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_377_, v_a_361_);
lean_dec(v_a_361_);
lean_inc_ref(v___x_378_);
v___f_379_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0), 3, 2);
lean_closure_set(v___f_379_, 0, v_fnName_329_);
lean_closure_set(v___f_379_, 1, v___x_378_);
v___x_380_ = l_Lean_EnvExtension_modifyState___redArg(v___x_337_, v_env_366_, v___f_379_, v_asyncMode_338_, v___x_340_);
v___x_381_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 5, v___x_381_);
lean_ctor_set(v___x_375_, 0, v___x_380_);
v___x_383_ = v___x_375_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_nextMacroScope_367_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_ngen_368_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_auxDeclNGen_369_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v_traceState_370_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_messages_371_);
lean_ctor_set(v_reuseFailAlloc_403_, 7, v_infoState_372_);
lean_ctor_set(v_reuseFailAlloc_403_, 8, v_snapshotTasks_373_);
v___x_383_ = v_reuseFailAlloc_403_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_mctx_386_; lean_object* v_zetaDeltaFVarIds_387_; lean_object* v_postponed_388_; lean_object* v_diag_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_401_; 
v___x_384_ = lean_st_ref_set(v_a_333_, v___x_383_);
v___x_385_ = lean_st_ref_take(v_a_331_);
v_mctx_386_ = lean_ctor_get(v___x_385_, 0);
v_zetaDeltaFVarIds_387_ = lean_ctor_get(v___x_385_, 2);
v_postponed_388_ = lean_ctor_get(v___x_385_, 3);
v_diag_389_ = lean_ctor_get(v___x_385_, 4);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v___x_385_, 1);
lean_dec(v_unused_402_);
v___x_391_ = v___x_385_;
v_isShared_392_ = v_isSharedCheck_401_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_diag_389_);
lean_inc(v_postponed_388_);
lean_inc(v_zetaDeltaFVarIds_387_);
lean_inc(v_mctx_386_);
lean_dec(v___x_385_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_401_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_mctx_386_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_zetaDeltaFVarIds_387_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_postponed_388_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_diag_389_);
v___x_395_ = v_reuseFailAlloc_400_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_st_ref_set(v_a_331_, v___x_395_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_378_);
v___x_398_ = v___x_363_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_378_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_fnName_329_);
v_a_407_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_360_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_360_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec(v_a_353_);
lean_dec(v_fnName_329_);
v___x_415_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_415_);
v___x_417_ = v___x_355_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_fnName_329_);
v_a_420_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_352_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_352_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___boxed(lean_object* v_fnName_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_Tactic_Cbv_getEqnTheorems(v_fnName_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(lean_object* v_00_u03b2_435_, lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___boxed(lean_object* v_00_u03b2_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(v_00_u03b2_439_, v_x_440_, v_x_441_);
lean_dec(v_x_441_);
lean_dec_ref(v_x_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2(lean_object* v_00_u03b2_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_x_444_, v_x_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(lean_object* v_00_u03b2_448_, lean_object* v_x_449_, size_t v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_449_, v_x_450_, v_x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___boxed(lean_object* v_00_u03b2_453_, lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
size_t v_x_2709__boxed_457_; lean_object* v_res_458_; 
v_x_2709__boxed_457_ = lean_unbox_usize(v_x_455_);
lean_dec(v_x_455_);
v_res_458_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(v_00_u03b2_453_, v_x_454_, v_x_2709__boxed_457_, v_x_456_);
lean_dec(v_x_456_);
lean_dec_ref(v_x_454_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, size_t v_x_461_, size_t v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_460_, v_x_461_, v_x_462_, v_x_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___boxed(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
size_t v_x_2720__boxed_472_; size_t v_x_2721__boxed_473_; lean_object* v_res_474_; 
v_x_2720__boxed_472_ = lean_unbox_usize(v_x_468_);
lean_dec(v_x_468_);
v_x_2721__boxed_473_ = lean_unbox_usize(v_x_469_);
lean_dec(v_x_469_);
v_res_474_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(v_00_u03b2_466_, v_x_467_, v_x_2720__boxed_472_, v_x_2721__boxed_473_, v_x_470_, v_x_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_475_, lean_object* v_keys_476_, lean_object* v_vals_477_, lean_object* v_heq_478_, lean_object* v_i_479_, lean_object* v_k_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_476_, v_vals_477_, v_i_479_, v_k_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_heq_485_, lean_object* v_i_486_, lean_object* v_k_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(v_00_u03b2_482_, v_keys_483_, v_vals_484_, v_heq_485_, v_i_486_, v_k_487_);
lean_dec(v_k_487_);
lean_dec_ref(v_vals_484_);
lean_dec_ref(v_keys_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_489_, lean_object* v_n_490_, lean_object* v_k_491_, lean_object* v_v_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v_n_490_, v_k_491_, v_v_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_494_, size_t v_depth_495_, lean_object* v_keys_496_, lean_object* v_vals_497_, lean_object* v_heq_498_, lean_object* v_i_499_, lean_object* v_entries_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_495_, v_keys_496_, v_vals_497_, v_i_499_, v_entries_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_502_, lean_object* v_depth_503_, lean_object* v_keys_504_, lean_object* v_vals_505_, lean_object* v_heq_506_, lean_object* v_i_507_, lean_object* v_entries_508_){
_start:
{
size_t v_depth_boxed_509_; lean_object* v_res_510_; 
v_depth_boxed_509_ = lean_unbox_usize(v_depth_503_);
lean_dec(v_depth_503_);
v_res_510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(v_00_u03b2_502_, v_depth_boxed_509_, v_keys_504_, v_vals_505_, v_heq_506_, v_i_507_, v_entries_508_);
lean_dec_ref(v_vals_505_);
lean_dec_ref(v_keys_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(v_x_512_, v_x_513_, v_x_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0(lean_object* v_fnName_517_, lean_object* v_a_518_, lean_object* v_cache_519_){
_start:
{
lean_object* v_eqnTheorems_520_; lean_object* v_unfoldTheorems_521_; lean_object* v_matchTheorems_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
v_eqnTheorems_520_ = lean_ctor_get(v_cache_519_, 0);
v_unfoldTheorems_521_ = lean_ctor_get(v_cache_519_, 1);
v_matchTheorems_522_ = lean_ctor_get(v_cache_519_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v_cache_519_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v_cache_519_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_matchTheorems_522_);
lean_inc(v_unfoldTheorems_521_);
lean_inc(v_eqnTheorems_520_);
lean_dec(v_cache_519_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_unfoldTheorems_521_, v_fnName_517_, v_a_518_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_eqnTheorems_520_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_matchTheorems_522_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1);
v___x_537_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_ctor_set(v___x_537_, 2, v___x_536_);
lean_ctor_set(v___x_537_, 3, v___x_536_);
lean_ctor_set(v___x_537_, 4, v___x_536_);
lean_ctor_set(v___x_537_, 5, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(lean_object* v_fnName_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_544_; lean_object* v_env_545_; lean_object* v___x_546_; lean_object* v_asyncMode_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_unfoldTheorems_551_; lean_object* v___x_552_; 
v___x_544_ = lean_st_ref_get(v_a_542_);
v_env_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_env_545_);
lean_dec(v___x_544_);
v___x_546_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_547_ = lean_ctor_get(v___x_546_, 2);
v___x_548_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_549_ = lean_box(0);
v___x_550_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_548_, v___x_546_, v_env_545_, v_asyncMode_547_, v___x_549_);
v_unfoldTheorems_551_ = lean_ctor_get(v___x_550_, 1);
lean_inc_ref(v_unfoldTheorems_551_);
lean_dec(v___x_550_);
v___x_552_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_unfoldTheorems_551_, v_fnName_538_);
lean_dec_ref(v_unfoldTheorems_551_);
if (lean_obj_tag(v___x_552_) == 1)
{
lean_object* v___x_553_; 
lean_dec(v_fnName_538_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
else
{
uint8_t v___x_554_; lean_object* v___x_555_; 
lean_dec(v___x_552_);
v___x_554_ = 1;
lean_inc(v_fnName_538_);
v___x_555_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fnName_538_, v___x_554_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_625_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_625_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_625_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_625_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
if (lean_obj_tag(v_a_556_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_620_; 
lean_del_object(v___x_558_);
v_val_560_ = lean_ctor_get(v_a_556_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_620_ == 0)
{
v___x_562_ = v_a_556_;
v_isShared_563_ = v_isSharedCheck_620_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v_a_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_620_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_val_560_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_611_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_611_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_611_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_611_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v_env_570_; lean_object* v_nextMacroScope_571_; lean_object* v_ngen_572_; lean_object* v_auxDeclNGen_573_; lean_object* v_traceState_574_; lean_object* v_messages_575_; lean_object* v_infoState_576_; lean_object* v_snapshotTasks_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_609_; 
v___x_569_ = lean_st_ref_take(v_a_542_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
v_nextMacroScope_571_ = lean_ctor_get(v___x_569_, 1);
v_ngen_572_ = lean_ctor_get(v___x_569_, 2);
v_auxDeclNGen_573_ = lean_ctor_get(v___x_569_, 3);
v_traceState_574_ = lean_ctor_get(v___x_569_, 4);
v_messages_575_ = lean_ctor_get(v___x_569_, 6);
v_infoState_576_ = lean_ctor_get(v___x_569_, 7);
v_snapshotTasks_577_ = lean_ctor_get(v___x_569_, 8);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_569_, 5);
lean_dec(v_unused_610_);
v___x_579_ = v___x_569_;
v_isShared_580_ = v_isSharedCheck_609_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snapshotTasks_577_);
lean_inc(v_infoState_576_);
lean_inc(v_messages_575_);
lean_inc(v_traceState_574_);
lean_inc(v_auxDeclNGen_573_);
lean_inc(v_ngen_572_);
lean_inc(v_nextMacroScope_571_);
lean_inc(v_env_570_);
lean_dec(v___x_569_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_609_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___f_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
lean_inc(v_a_565_);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0), 3, 2);
lean_closure_set(v___f_581_, 0, v_fnName_538_);
lean_closure_set(v___f_581_, 1, v_a_565_);
v___x_582_ = l_Lean_EnvExtension_modifyState___redArg(v___x_546_, v_env_570_, v___f_581_, v_asyncMode_547_, v___x_549_);
v___x_583_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 5, v___x_583_);
lean_ctor_set(v___x_579_, 0, v___x_582_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_571_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_572_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_573_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_traceState_574_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_messages_575_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_infoState_576_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_snapshotTasks_577_);
v___x_585_ = v_reuseFailAlloc_608_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_mctx_588_; lean_object* v_zetaDeltaFVarIds_589_; lean_object* v_postponed_590_; lean_object* v_diag_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_606_; 
v___x_586_ = lean_st_ref_set(v_a_542_, v___x_585_);
v___x_587_ = lean_st_ref_take(v_a_540_);
v_mctx_588_ = lean_ctor_get(v___x_587_, 0);
v_zetaDeltaFVarIds_589_ = lean_ctor_get(v___x_587_, 2);
v_postponed_590_ = lean_ctor_get(v___x_587_, 3);
v_diag_591_ = lean_ctor_get(v___x_587_, 4);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_587_, 1);
lean_dec(v_unused_607_);
v___x_593_ = v___x_587_;
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_diag_591_);
lean_inc(v_postponed_590_);
lean_inc(v_zetaDeltaFVarIds_589_);
lean_inc(v_mctx_588_);
lean_dec(v___x_587_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_mctx_588_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_zetaDeltaFVarIds_589_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_postponed_590_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_diag_591_);
v___x_597_ = v_reuseFailAlloc_605_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_st_ref_set(v_a_540_, v___x_597_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v_a_565_);
v___x_600_ = v___x_562_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_565_);
v___x_600_ = v_reuseFailAlloc_604_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_600_);
v___x_602_ = v___x_567_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
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
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_del_object(v___x_562_);
lean_dec(v_fnName_538_);
v_a_612_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_564_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_564_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_623_; 
lean_dec(v_a_556_);
lean_dec(v_fnName_538_);
v___x_621_ = lean_box(0);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_621_);
v___x_623_ = v___x_558_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_fnName_538_);
v_a_626_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_555_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_555_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___boxed(lean_object* v_fnName_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(v_fnName_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0(lean_object* v_matcherName_641_, lean_object* v___x_642_, lean_object* v_cache_643_){
_start:
{
lean_object* v_eqnTheorems_644_; lean_object* v_unfoldTheorems_645_; lean_object* v_matchTheorems_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_eqnTheorems_644_ = lean_ctor_get(v_cache_643_, 0);
v_unfoldTheorems_645_ = lean_ctor_get(v_cache_643_, 1);
v_matchTheorems_646_ = lean_ctor_get(v_cache_643_, 2);
v_isSharedCheck_654_ = !lean_is_exclusive(v_cache_643_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v_cache_643_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_matchTheorems_646_);
lean_inc(v_unfoldTheorems_645_);
lean_inc(v_eqnTheorems_644_);
lean_dec(v_cache_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_matchTheorems_646_, v_matcherName_641_, v___x_642_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_eqnTheorems_644_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_unfoldTheorems_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object* v_matcherName_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; lean_object* v_env_662_; lean_object* v___x_663_; lean_object* v_asyncMode_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_matchTheorems_668_; lean_object* v___x_669_; 
v___x_661_ = lean_st_ref_get(v_a_659_);
v_env_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_ref(v_env_662_);
lean_dec(v___x_661_);
v___x_663_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_664_ = lean_ctor_get(v___x_663_, 2);
v___x_665_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_666_ = lean_box(0);
v___x_667_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_665_, v___x_663_, v_env_662_, v_asyncMode_664_, v___x_666_);
v_matchTheorems_668_ = lean_ctor_get(v___x_667_, 2);
lean_inc_ref(v_matchTheorems_668_);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_matchTheorems_668_, v_matcherName_655_);
lean_dec_ref(v_matchTheorems_668_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_matcherName_655_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set_tag(v___x_672_, 0);
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_val_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec(v___x_669_);
lean_inc(v_a_659_);
lean_inc_ref(v_a_658_);
lean_inc(v_a_657_);
lean_inc_ref(v_a_656_);
lean_inc(v_matcherName_655_);
v___x_678_ = lean_get_match_equations_for(v_matcherName_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v_eqnNames_680_; size_t v_sz_681_; size_t v___x_682_; lean_object* v___x_683_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
v_eqnNames_680_ = lean_ctor_get(v_a_679_, 0);
lean_inc_ref(v_eqnNames_680_);
lean_dec(v_a_679_);
v_sz_681_ = lean_array_size(v_eqnNames_680_);
v___x_682_ = ((size_t)0ULL);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_681_, v___x_682_, v_eqnNames_680_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_729_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_729_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_729_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_729_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v_env_689_; lean_object* v_nextMacroScope_690_; lean_object* v_ngen_691_; lean_object* v_auxDeclNGen_692_; lean_object* v_traceState_693_; lean_object* v_messages_694_; lean_object* v_infoState_695_; lean_object* v_snapshotTasks_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_727_; 
v___x_688_ = lean_st_ref_take(v_a_659_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
v_nextMacroScope_690_ = lean_ctor_get(v___x_688_, 1);
v_ngen_691_ = lean_ctor_get(v___x_688_, 2);
v_auxDeclNGen_692_ = lean_ctor_get(v___x_688_, 3);
v_traceState_693_ = lean_ctor_get(v___x_688_, 4);
v_messages_694_ = lean_ctor_get(v___x_688_, 6);
v_infoState_695_ = lean_ctor_get(v___x_688_, 7);
v_snapshotTasks_696_ = lean_ctor_get(v___x_688_, 8);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v___x_688_, 5);
lean_dec(v_unused_728_);
v___x_698_ = v___x_688_;
v_isShared_699_ = v_isSharedCheck_727_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snapshotTasks_696_);
lean_inc(v_infoState_695_);
lean_inc(v_messages_694_);
lean_inc(v_traceState_693_);
lean_inc(v_auxDeclNGen_692_);
lean_inc(v_ngen_691_);
lean_inc(v_nextMacroScope_690_);
lean_inc(v_env_689_);
lean_dec(v___x_688_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_727_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___f_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_700_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_701_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_700_, v_a_684_);
lean_dec(v_a_684_);
lean_inc_ref(v___x_701_);
v___f_702_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0), 3, 2);
lean_closure_set(v___f_702_, 0, v_matcherName_655_);
lean_closure_set(v___f_702_, 1, v___x_701_);
v___x_703_ = l_Lean_EnvExtension_modifyState___redArg(v___x_663_, v_env_689_, v___f_702_, v_asyncMode_664_, v___x_666_);
v___x_704_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 5, v___x_704_);
lean_ctor_set(v___x_698_, 0, v___x_703_);
v___x_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_nextMacroScope_690_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_ngen_691_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_auxDeclNGen_692_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_traceState_693_);
lean_ctor_set(v_reuseFailAlloc_726_, 5, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_726_, 6, v_messages_694_);
lean_ctor_set(v_reuseFailAlloc_726_, 7, v_infoState_695_);
lean_ctor_set(v_reuseFailAlloc_726_, 8, v_snapshotTasks_696_);
v___x_706_ = v_reuseFailAlloc_726_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_mctx_709_; lean_object* v_zetaDeltaFVarIds_710_; lean_object* v_postponed_711_; lean_object* v_diag_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_724_; 
v___x_707_ = lean_st_ref_set(v_a_659_, v___x_706_);
v___x_708_ = lean_st_ref_take(v_a_657_);
v_mctx_709_ = lean_ctor_get(v___x_708_, 0);
v_zetaDeltaFVarIds_710_ = lean_ctor_get(v___x_708_, 2);
v_postponed_711_ = lean_ctor_get(v___x_708_, 3);
v_diag_712_ = lean_ctor_get(v___x_708_, 4);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_708_, 1);
lean_dec(v_unused_725_);
v___x_714_ = v___x_708_;
v_isShared_715_ = v_isSharedCheck_724_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_diag_712_);
lean_inc(v_postponed_711_);
lean_inc(v_zetaDeltaFVarIds_710_);
lean_inc(v_mctx_709_);
lean_dec(v___x_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_724_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_mctx_709_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_zetaDeltaFVarIds_710_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_postponed_711_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_diag_712_);
v___x_718_ = v_reuseFailAlloc_723_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_st_ref_set(v_a_657_, v___x_718_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_701_);
v___x_721_ = v___x_686_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_701_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_matcherName_655_);
v_a_730_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_683_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_683_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_matcherName_655_);
v_a_738_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_678_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_678_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___boxed(lean_object* v_matcherName_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_matcherName_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
return v_res_752_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
