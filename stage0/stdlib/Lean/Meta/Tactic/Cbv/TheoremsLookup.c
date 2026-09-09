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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v_ks_142_; lean_object* v_vs_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_161_; 
v_ks_142_ = lean_ctor_get(v_x_91_, 0);
v_vs_143_ = lean_ctor_get(v_x_91_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x_91_);
if (v_isSharedCheck_161_ == 0)
{
v___x_145_ = v_x_91_;
v_isShared_146_ = v_isSharedCheck_161_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_vs_143_);
lean_inc(v_ks_142_);
lean_dec(v_x_91_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_161_;
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
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_ks_142_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_vs_143_);
v___x_148_ = v_reuseFailAlloc_160_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v_newNode_149_; size_t v___x_150_; uint8_t v___x_151_; 
v_newNode_149_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v___x_148_, v_x_94_, v_x_95_);
v___x_150_ = ((size_t)7ULL);
v___x_151_ = lean_usize_dec_le(v___x_150_, v_x_93_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_152_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_149_);
v___x_153_ = lean_unsigned_to_nat(4u);
v___x_154_ = lean_nat_dec_lt(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
if (v___x_154_ == 0)
{
lean_object* v_ks_155_; lean_object* v_vs_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_ks_155_ = lean_ctor_get(v_newNode_149_, 0);
lean_inc_ref(v_ks_155_);
v_vs_156_ = lean_ctor_get(v_newNode_149_, 1);
lean_inc_ref(v_vs_156_);
lean_dec_ref(v_newNode_149_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___closed__0);
v___x_159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_x_93_, v_ks_155_, v_vs_156_, v___x_157_, v___x_158_);
lean_dec_ref(v_vs_156_);
lean_dec_ref(v_ks_155_);
return v___x_159_;
}
else
{
return v_newNode_149_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(size_t v_depth_162_, lean_object* v_keys_163_, lean_object* v_vals_164_, lean_object* v_i_165_, lean_object* v_entries_166_){
_start:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_array_get_size(v_keys_163_);
v___x_168_ = lean_nat_dec_lt(v_i_165_, v___x_167_);
if (v___x_168_ == 0)
{
lean_dec(v_i_165_);
return v_entries_166_;
}
else
{
lean_object* v_k_169_; lean_object* v_v_170_; uint64_t v___y_172_; 
v_k_169_ = lean_array_fget_borrowed(v_keys_163_, v_i_165_);
v_v_170_ = lean_array_fget_borrowed(v_vals_164_, v_i_165_);
if (lean_obj_tag(v_k_169_) == 0)
{
uint64_t v___x_183_; 
v___x_183_ = 1723ULL;
v___y_172_ = v___x_183_;
goto v___jp_171_;
}
else
{
uint64_t v_hash_184_; 
v_hash_184_ = lean_ctor_get_uint64(v_k_169_, sizeof(void*)*2);
v___y_172_ = v_hash_184_;
goto v___jp_171_;
}
v___jp_171_:
{
size_t v_h_173_; size_t v___x_174_; lean_object* v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v_h_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_h_173_ = lean_uint64_to_usize(v___y_172_);
v___x_174_ = ((size_t)5ULL);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_sub(v_depth_162_, v___x_176_);
v___x_178_ = lean_usize_mul(v___x_174_, v___x_177_);
v_h_179_ = lean_usize_shift_right(v_h_173_, v___x_178_);
v___x_180_ = lean_nat_add(v_i_165_, v___x_175_);
lean_dec(v_i_165_);
lean_inc(v_v_170_);
lean_inc(v_k_169_);
v___x_181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_entries_166_, v_h_179_, v_depth_162_, v_k_169_, v_v_170_);
v_i_165_ = v___x_180_;
v_entries_166_ = v___x_181_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_185_, lean_object* v_keys_186_, lean_object* v_vals_187_, lean_object* v_i_188_, lean_object* v_entries_189_){
_start:
{
size_t v_depth_boxed_190_; lean_object* v_res_191_; 
v_depth_boxed_190_ = lean_unbox_usize(v_depth_185_);
lean_dec(v_depth_185_);
v_res_191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_boxed_190_, v_keys_186_, v_vals_187_, v_i_188_, v_entries_189_);
lean_dec_ref(v_vals_187_);
lean_dec_ref(v_keys_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg___boxed(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
size_t v_x_2167__boxed_197_; size_t v_x_2168__boxed_198_; lean_object* v_res_199_; 
v_x_2167__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_x_2168__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_res_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_192_, v_x_2167__boxed_197_, v_x_2168__boxed_198_, v_x_195_, v_x_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint64_t v___y_204_; 
if (lean_obj_tag(v_x_201_) == 0)
{
uint64_t v___x_208_; 
v___x_208_ = 1723ULL;
v___y_204_ = v___x_208_;
goto v___jp_203_;
}
else
{
uint64_t v_hash_209_; 
v_hash_209_ = lean_ctor_get_uint64(v_x_201_, sizeof(void*)*2);
v___y_204_ = v_hash_209_;
goto v___jp_203_;
}
v___jp_203_:
{
size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_uint64_to_usize(v___y_204_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_200_, v___x_205_, v___x_206_, v_x_201_, v_x_202_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0(lean_object* v_fnName_210_, lean_object* v___x_211_, lean_object* v_cache_212_){
_start:
{
lean_object* v_eqnTheorems_213_; lean_object* v_unfoldTheorems_214_; lean_object* v_matchTheorems_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_eqnTheorems_213_ = lean_ctor_get(v_cache_212_, 0);
v_unfoldTheorems_214_ = lean_ctor_get(v_cache_212_, 1);
v_matchTheorems_215_ = lean_ctor_get(v_cache_212_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v_cache_212_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v_cache_212_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_matchTheorems_215_);
lean_inc(v_unfoldTheorems_214_);
lean_inc(v_eqnTheorems_213_);
lean_dec(v_cache_212_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_eqnTheorems_213_, v_fnName_210_, v___x_211_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_unfoldTheorems_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_matchTheorems_215_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(size_t v_sz_224_, size_t v_i_225_, lean_object* v_bs_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_bs_226_);
return v___x_233_;
}
else
{
lean_object* v_v_234_; lean_object* v___x_235_; 
v_v_234_ = lean_array_uget_borrowed(v_bs_226_, v_i_225_);
lean_inc(v_v_234_);
v___x_235_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_v_234_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; lean_object* v_bs_x27_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = lean_unsigned_to_nat(0u);
v_bs_x27_238_ = lean_array_uset(v_bs_226_, v_i_225_, v___x_237_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_225_, v___x_239_);
v___x_241_ = lean_array_uset(v_bs_x27_238_, v_i_225_, v_a_236_);
v_i_225_ = v___x_240_;
v_bs_226_ = v___x_241_;
goto _start;
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_bs_226_);
v_a_243_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_235_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_235_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1___boxed(lean_object* v_sz_251_, lean_object* v_i_252_, lean_object* v_bs_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
size_t v_sz_boxed_259_; size_t v_i_boxed_260_; lean_object* v_res_261_; 
v_sz_boxed_259_ = lean_unbox_usize(v_sz_251_);
lean_dec(v_sz_251_);
v_i_boxed_260_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_boxed_259_, v_i_boxed_260_, v_bs_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_262_, lean_object* v_vals_263_, lean_object* v_i_264_, lean_object* v_k_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_keys_262_);
v___x_267_ = lean_nat_dec_lt(v_i_264_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec(v_i_264_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v_k_x27_269_; uint8_t v___x_270_; 
v_k_x27_269_ = lean_array_fget_borrowed(v_keys_262_, v_i_264_);
v___x_270_ = lean_name_eq(v_k_265_, v_k_x27_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_i_264_, v___x_271_);
lean_dec(v_i_264_);
v_i_264_ = v___x_272_;
goto _start;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_array_fget_borrowed(v_vals_263_, v_i_264_);
lean_dec(v_i_264_);
lean_inc(v___x_274_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_276_, lean_object* v_vals_277_, lean_object* v_i_278_, lean_object* v_k_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_276_, v_vals_277_, v_i_278_, v_k_279_);
lean_dec(v_k_279_);
lean_dec_ref(v_vals_277_);
lean_dec_ref(v_keys_276_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(lean_object* v_x_281_, size_t v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_es_284_; lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v_j_288_; lean_object* v___x_289_; 
v_es_284_ = lean_ctor_get(v_x_281_, 0);
v___x_285_ = lean_box(2);
v___x_286_ = ((size_t)31ULL);
v___x_287_ = lean_usize_land(v_x_282_, v___x_286_);
v_j_288_ = lean_usize_to_nat(v___x_287_);
v___x_289_ = lean_array_get_borrowed(v___x_285_, v_es_284_, v_j_288_);
lean_dec(v_j_288_);
switch(lean_obj_tag(v___x_289_))
{
case 0:
{
lean_object* v_key_290_; lean_object* v_val_291_; uint8_t v___x_292_; 
v_key_290_ = lean_ctor_get(v___x_289_, 0);
v_val_291_ = lean_ctor_get(v___x_289_, 1);
v___x_292_ = lean_name_eq(v_x_283_, v_key_290_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_box(0);
return v___x_293_;
}
else
{
lean_object* v___x_294_; 
lean_inc(v_val_291_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_val_291_);
return v___x_294_;
}
}
case 1:
{
lean_object* v_node_295_; size_t v___x_296_; size_t v___x_297_; 
v_node_295_ = lean_ctor_get(v___x_289_, 0);
v___x_296_ = ((size_t)5ULL);
v___x_297_ = lean_usize_shift_right(v_x_282_, v___x_296_);
v_x_281_ = v_node_295_;
v_x_282_ = v___x_297_;
goto _start;
}
default: 
{
lean_object* v___x_299_; 
v___x_299_ = lean_box(0);
return v___x_299_;
}
}
}
else
{
lean_object* v_ks_300_; lean_object* v_vs_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_ks_300_ = lean_ctor_get(v_x_281_, 0);
v_vs_301_ = lean_ctor_get(v_x_281_, 1);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_ks_300_, v_vs_301_, v___x_302_, v_x_283_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg___boxed(lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
size_t v_x_2424__boxed_307_; lean_object* v_res_308_; 
v_x_2424__boxed_307_ = lean_unbox_usize(v_x_305_);
lean_dec(v_x_305_);
v_res_308_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_304_, v_x_2424__boxed_307_, v_x_306_);
lean_dec(v_x_306_);
lean_dec_ref(v_x_304_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
uint64_t v___y_312_; 
if (lean_obj_tag(v_x_310_) == 0)
{
uint64_t v___x_315_; 
v___x_315_ = 1723ULL;
v___y_312_ = v___x_315_;
goto v___jp_311_;
}
else
{
uint64_t v_hash_316_; 
v_hash_316_ = lean_ctor_get_uint64(v_x_310_, sizeof(void*)*2);
v___y_312_ = v_hash_316_;
goto v___jp_311_;
}
v___jp_311_:
{
size_t v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_uint64_to_usize(v___y_312_);
v___x_314_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_309_, v___x_313_, v_x_310_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_317_, v_x_318_);
lean_dec(v_x_318_);
lean_dec_ref(v_x_317_);
return v_res_319_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0(void){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_326_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
lean_ctor_set(v___x_326_, 4, v___x_325_);
lean_ctor_set(v___x_326_, 5, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems(lean_object* v_fnName_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; lean_object* v_env_334_; lean_object* v___x_335_; lean_object* v_asyncMode_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_eqnTheorems_340_; lean_object* v___x_341_; 
v___x_333_ = lean_st_ref_get(v_a_331_);
v_env_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_ref(v_env_334_);
lean_dec(v___x_333_);
v___x_335_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_336_ = lean_ctor_get(v___x_335_, 2);
v___x_337_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_338_ = lean_box(0);
v___x_339_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_337_, v___x_335_, v_env_334_, v_asyncMode_336_, v___x_338_);
v_eqnTheorems_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc_ref(v_eqnTheorems_340_);
lean_dec(v___x_339_);
v___x_341_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_eqnTheorems_340_, v_fnName_327_);
lean_dec_ref(v_eqnTheorems_340_);
if (lean_obj_tag(v___x_341_) == 1)
{
lean_object* v_val_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_fnName_327_);
v_val_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_val_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 0);
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_val_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v___x_341_);
lean_inc(v_fnName_327_);
v___x_350_ = l_Lean_Meta_getEqnsFor_x3f(v_fnName_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_417_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_417_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_417_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_417_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
if (lean_obj_tag(v_a_351_) == 1)
{
lean_object* v_val_355_; size_t v_sz_356_; size_t v___x_357_; lean_object* v___x_358_; 
lean_del_object(v___x_353_);
v_val_355_ = lean_ctor_get(v_a_351_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v_a_351_, 1);
v_sz_356_ = lean_array_size(v_val_355_);
v___x_357_ = ((size_t)0ULL);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_356_, v___x_357_, v_val_355_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_404_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_404_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_404_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_404_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v_env_364_; lean_object* v_nextMacroScope_365_; lean_object* v_ngen_366_; lean_object* v_auxDeclNGen_367_; lean_object* v_traceState_368_; lean_object* v_messages_369_; lean_object* v_infoState_370_; lean_object* v_snapshotTasks_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_402_; 
v___x_363_ = lean_st_ref_take(v_a_331_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
v_nextMacroScope_365_ = lean_ctor_get(v___x_363_, 1);
v_ngen_366_ = lean_ctor_get(v___x_363_, 2);
v_auxDeclNGen_367_ = lean_ctor_get(v___x_363_, 3);
v_traceState_368_ = lean_ctor_get(v___x_363_, 4);
v_messages_369_ = lean_ctor_get(v___x_363_, 6);
v_infoState_370_ = lean_ctor_get(v___x_363_, 7);
v_snapshotTasks_371_ = lean_ctor_get(v___x_363_, 8);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; 
v_unused_403_ = lean_ctor_get(v___x_363_, 5);
lean_dec(v_unused_403_);
v___x_373_ = v___x_363_;
v_isShared_374_ = v_isSharedCheck_402_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_snapshotTasks_371_);
lean_inc(v_infoState_370_);
lean_inc(v_messages_369_);
lean_inc(v_traceState_368_);
lean_inc(v_auxDeclNGen_367_);
lean_inc(v_ngen_366_);
lean_inc(v_nextMacroScope_365_);
lean_inc(v_env_364_);
lean_dec(v___x_363_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_402_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_375_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_376_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_375_, v_a_359_);
lean_dec(v_a_359_);
lean_inc_ref(v___x_376_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getEqnTheorems___lam__0), 3, 2);
lean_closure_set(v___f_377_, 0, v_fnName_327_);
lean_closure_set(v___f_377_, 1, v___x_376_);
v___x_378_ = l_Lean_EnvExtension_modifyState___redArg(v___x_335_, v_env_364_, v___f_377_, v_asyncMode_336_, v___x_338_);
v___x_379_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 5, v___x_379_);
lean_ctor_set(v___x_373_, 0, v___x_378_);
v___x_381_ = v___x_373_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_nextMacroScope_365_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_ngen_366_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_auxDeclNGen_367_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v_traceState_368_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_messages_369_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_infoState_370_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_snapshotTasks_371_);
v___x_381_ = v_reuseFailAlloc_401_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_mctx_384_; lean_object* v_zetaDeltaFVarIds_385_; lean_object* v_postponed_386_; lean_object* v_diag_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
v___x_382_ = lean_st_ref_put(v_a_331_, v___x_381_);
v___x_383_ = lean_st_ref_take(v_a_329_);
v_mctx_384_ = lean_ctor_get(v___x_383_, 0);
v_zetaDeltaFVarIds_385_ = lean_ctor_get(v___x_383_, 2);
v_postponed_386_ = lean_ctor_get(v___x_383_, 3);
v_diag_387_ = lean_ctor_get(v___x_383_, 4);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_383_, 1);
lean_dec(v_unused_400_);
v___x_389_ = v___x_383_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_diag_387_);
lean_inc(v_postponed_386_);
lean_inc(v_zetaDeltaFVarIds_385_);
lean_inc(v_mctx_384_);
lean_dec(v___x_383_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_mctx_384_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_zetaDeltaFVarIds_385_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_postponed_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_diag_387_);
v___x_393_ = v_reuseFailAlloc_398_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_st_ref_put(v_a_329_, v___x_393_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_376_);
v___x_396_ = v___x_361_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_376_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_fnName_327_);
v_a_405_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_358_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_358_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_415_; 
lean_dec(v_a_351_);
lean_dec(v_fnName_327_);
v___x_413_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_413_);
v___x_415_ = v___x_353_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec(v_fnName_327_);
v_a_418_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_350_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_350_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems___boxed(lean_object* v_fnName_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_Tactic_Cbv_getEqnTheorems(v_fnName_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_x_434_, v_x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___boxed(lean_object* v_00_u03b2_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0(v_00_u03b2_437_, v_x_438_, v_x_439_);
lean_dec(v_x_439_);
lean_dec_ref(v_x_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2(lean_object* v_00_u03b2_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_x_442_, v_x_443_, v_x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(lean_object* v_00_u03b2_446_, lean_object* v_x_447_, size_t v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___redArg(v_x_447_, v_x_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0___boxed(lean_object* v_00_u03b2_451_, lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
size_t v_x_2696__boxed_455_; lean_object* v_res_456_; 
v_x_2696__boxed_455_ = lean_unbox_usize(v_x_453_);
lean_dec(v_x_453_);
v_res_456_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0(v_00_u03b2_451_, v_x_452_, v_x_2696__boxed_455_, v_x_454_);
lean_dec(v_x_454_);
lean_dec_ref(v_x_452_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(lean_object* v_00_u03b2_457_, lean_object* v_x_458_, size_t v_x_459_, size_t v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___redArg(v_x_458_, v_x_459_, v_x_460_, v_x_461_, v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3___boxed(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
size_t v_x_2707__boxed_470_; size_t v_x_2708__boxed_471_; lean_object* v_res_472_; 
v_x_2707__boxed_470_ = lean_unbox_usize(v_x_466_);
lean_dec(v_x_466_);
v_x_2708__boxed_471_ = lean_unbox_usize(v_x_467_);
lean_dec(v_x_467_);
v_res_472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3(v_00_u03b2_464_, v_x_465_, v_x_2707__boxed_470_, v_x_2708__boxed_471_, v_x_468_, v_x_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_473_, lean_object* v_keys_474_, lean_object* v_vals_475_, lean_object* v_heq_476_, lean_object* v_i_477_, lean_object* v_k_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___redArg(v_keys_474_, v_vals_475_, v_i_477_, v_k_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_480_, lean_object* v_keys_481_, lean_object* v_vals_482_, lean_object* v_heq_483_, lean_object* v_i_484_, lean_object* v_k_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0_spec__0_spec__1(v_00_u03b2_480_, v_keys_481_, v_vals_482_, v_heq_483_, v_i_484_, v_k_485_);
lean_dec(v_k_485_);
lean_dec_ref(v_vals_482_);
lean_dec_ref(v_keys_481_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_487_, lean_object* v_n_488_, lean_object* v_k_489_, lean_object* v_v_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5___redArg(v_n_488_, v_k_489_, v_v_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_492_, size_t v_depth_493_, lean_object* v_keys_494_, lean_object* v_vals_495_, lean_object* v_heq_496_, lean_object* v_i_497_, lean_object* v_entries_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___redArg(v_depth_493_, v_keys_494_, v_vals_495_, v_i_497_, v_entries_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_500_, lean_object* v_depth_501_, lean_object* v_keys_502_, lean_object* v_vals_503_, lean_object* v_heq_504_, lean_object* v_i_505_, lean_object* v_entries_506_){
_start:
{
size_t v_depth_boxed_507_; lean_object* v_res_508_; 
v_depth_boxed_507_ = lean_unbox_usize(v_depth_501_);
lean_dec(v_depth_501_);
v_res_508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__6(v_00_u03b2_500_, v_depth_boxed_507_, v_keys_502_, v_vals_503_, v_heq_504_, v_i_505_, v_entries_506_);
lean_dec_ref(v_vals_503_);
lean_dec_ref(v_keys_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2_spec__3_spec__5_spec__6___redArg(v_x_510_, v_x_511_, v_x_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0(lean_object* v_fnName_515_, lean_object* v_a_516_, lean_object* v_cache_517_){
_start:
{
lean_object* v_eqnTheorems_518_; lean_object* v_unfoldTheorems_519_; lean_object* v_matchTheorems_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_eqnTheorems_518_ = lean_ctor_get(v_cache_517_, 0);
v_unfoldTheorems_519_ = lean_ctor_get(v_cache_517_, 1);
v_matchTheorems_520_ = lean_ctor_get(v_cache_517_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v_cache_517_);
if (v_isSharedCheck_528_ == 0)
{
v___x_522_ = v_cache_517_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_matchTheorems_520_);
lean_inc(v_unfoldTheorems_519_);
lean_inc(v_eqnTheorems_518_);
lean_dec(v_cache_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_unfoldTheorems_519_, v_fnName_515_, v_a_516_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_eqnTheorems_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_matchTheorems_520_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__0);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__1);
v___x_535_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_ctor_set(v___x_535_, 2, v___x_534_);
lean_ctor_set(v___x_535_, 3, v___x_534_);
lean_ctor_set(v___x_535_, 4, v___x_534_);
lean_ctor_set(v___x_535_, 5, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(lean_object* v_fnName_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; lean_object* v_env_543_; lean_object* v___x_544_; lean_object* v_asyncMode_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_unfoldTheorems_549_; lean_object* v___x_550_; 
v___x_542_ = lean_st_ref_get(v_a_540_);
v_env_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc_ref(v_env_543_);
lean_dec(v___x_542_);
v___x_544_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_545_ = lean_ctor_get(v___x_544_, 2);
v___x_546_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_547_ = lean_box(0);
v___x_548_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_546_, v___x_544_, v_env_543_, v_asyncMode_545_, v___x_547_);
v_unfoldTheorems_549_ = lean_ctor_get(v___x_548_, 1);
lean_inc_ref(v_unfoldTheorems_549_);
lean_dec(v___x_548_);
v___x_550_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_unfoldTheorems_549_, v_fnName_536_);
lean_dec_ref(v_unfoldTheorems_549_);
if (lean_obj_tag(v___x_550_) == 1)
{
lean_object* v___x_551_; 
lean_dec(v_fnName_536_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
else
{
uint8_t v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_550_);
v___x_552_ = 1;
lean_inc(v_fnName_536_);
v___x_553_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_fnName_536_, v___x_552_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_623_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_623_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_623_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_623_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
if (lean_obj_tag(v_a_554_) == 1)
{
lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_618_; 
lean_del_object(v___x_556_);
v_val_558_ = lean_ctor_get(v_a_554_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_618_ == 0)
{
v___x_560_ = v_a_554_;
v_isShared_561_ = v_isSharedCheck_618_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_dec(v_a_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_618_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_val_558_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_609_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_609_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_609_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_609_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v_env_568_; lean_object* v_nextMacroScope_569_; lean_object* v_ngen_570_; lean_object* v_auxDeclNGen_571_; lean_object* v_traceState_572_; lean_object* v_messages_573_; lean_object* v_infoState_574_; lean_object* v_snapshotTasks_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_607_; 
v___x_567_ = lean_st_ref_take(v_a_540_);
v_env_568_ = lean_ctor_get(v___x_567_, 0);
v_nextMacroScope_569_ = lean_ctor_get(v___x_567_, 1);
v_ngen_570_ = lean_ctor_get(v___x_567_, 2);
v_auxDeclNGen_571_ = lean_ctor_get(v___x_567_, 3);
v_traceState_572_ = lean_ctor_get(v___x_567_, 4);
v_messages_573_ = lean_ctor_get(v___x_567_, 6);
v_infoState_574_ = lean_ctor_get(v___x_567_, 7);
v_snapshotTasks_575_ = lean_ctor_get(v___x_567_, 8);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_567_, 5);
lean_dec(v_unused_608_);
v___x_577_ = v___x_567_;
v_isShared_578_ = v_isSharedCheck_607_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snapshotTasks_575_);
lean_inc(v_infoState_574_);
lean_inc(v_messages_573_);
lean_inc(v_traceState_572_);
lean_inc(v_auxDeclNGen_571_);
lean_inc(v_ngen_570_);
lean_inc(v_nextMacroScope_569_);
lean_inc(v_env_568_);
lean_dec(v___x_567_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_607_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_inc(v_a_563_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___lam__0), 3, 2);
lean_closure_set(v___f_579_, 0, v_fnName_536_);
lean_closure_set(v___f_579_, 1, v_a_563_);
v___x_580_ = l_Lean_EnvExtension_modifyState___redArg(v___x_544_, v_env_568_, v___f_579_, v_asyncMode_545_, v___x_547_);
v___x_581_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__2);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 5, v___x_581_);
lean_ctor_set(v___x_577_, 0, v___x_580_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_nextMacroScope_569_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_ngen_570_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_auxDeclNGen_571_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_traceState_572_);
lean_ctor_set(v_reuseFailAlloc_606_, 5, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_606_, 6, v_messages_573_);
lean_ctor_set(v_reuseFailAlloc_606_, 7, v_infoState_574_);
lean_ctor_set(v_reuseFailAlloc_606_, 8, v_snapshotTasks_575_);
v___x_583_ = v_reuseFailAlloc_606_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_mctx_586_; lean_object* v_zetaDeltaFVarIds_587_; lean_object* v_postponed_588_; lean_object* v_diag_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_604_; 
v___x_584_ = lean_st_ref_put(v_a_540_, v___x_583_);
v___x_585_ = lean_st_ref_take(v_a_538_);
v_mctx_586_ = lean_ctor_get(v___x_585_, 0);
v_zetaDeltaFVarIds_587_ = lean_ctor_get(v___x_585_, 2);
v_postponed_588_ = lean_ctor_get(v___x_585_, 3);
v_diag_589_ = lean_ctor_get(v___x_585_, 4);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___x_585_, 1);
lean_dec(v_unused_605_);
v___x_591_ = v___x_585_;
v_isShared_592_ = v_isSharedCheck_604_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_diag_589_);
lean_inc(v_postponed_588_);
lean_inc(v_zetaDeltaFVarIds_587_);
lean_inc(v_mctx_586_);
lean_dec(v___x_585_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_604_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3, &l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___closed__3);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_mctx_586_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_zetaDeltaFVarIds_587_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_postponed_588_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v_diag_589_);
v___x_595_ = v_reuseFailAlloc_603_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_st_ref_put(v_a_538_, v___x_595_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_a_563_);
v___x_598_ = v___x_560_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_563_);
v___x_598_ = v_reuseFailAlloc_602_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_598_);
v___x_600_ = v___x_565_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
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
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_del_object(v___x_560_);
lean_dec(v_fnName_536_);
v_a_610_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_562_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_562_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec(v_a_554_);
lean_dec(v_fnName_536_);
v___x_619_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_619_);
v___x_621_ = v___x_556_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_fnName_536_);
v_a_624_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_553_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_553_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem___boxed(lean_object* v_fnName_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(v_fnName_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0(lean_object* v_matcherName_639_, lean_object* v___x_640_, lean_object* v_cache_641_){
_start:
{
lean_object* v_eqnTheorems_642_; lean_object* v_unfoldTheorems_643_; lean_object* v_matchTheorems_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
v_eqnTheorems_642_ = lean_ctor_get(v_cache_641_, 0);
v_unfoldTheorems_643_ = lean_ctor_get(v_cache_641_, 1);
v_matchTheorems_644_ = lean_ctor_get(v_cache_641_, 2);
v_isSharedCheck_652_ = !lean_is_exclusive(v_cache_641_);
if (v_isSharedCheck_652_ == 0)
{
v___x_646_ = v_cache_641_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_matchTheorems_644_);
lean_inc(v_unfoldTheorems_643_);
lean_inc(v_eqnTheorems_642_);
lean_dec(v_cache_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__2___redArg(v_matchTheorems_644_, v_matcherName_639_, v___x_640_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 2, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_eqnTheorems_642_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_unfoldTheorems_643_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object* v_matcherName_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v_env_660_; lean_object* v___x_661_; lean_object* v_asyncMode_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_matchTheorems_666_; lean_object* v___x_667_; 
v___x_659_ = lean_st_ref_get(v_a_657_);
v_env_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_env_660_);
lean_dec(v___x_659_);
v___x_661_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Tactic_Cbv_cbvTheoremsLookup;
v_asyncMode_662_ = lean_ctor_get(v___x_661_, 2);
v___x_663_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvTheoremsLookupState_default;
v___x_664_ = lean_box(0);
v___x_665_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_663_, v___x_661_, v_env_660_, v_asyncMode_662_, v___x_664_);
v_matchTheorems_666_ = lean_ctor_get(v___x_665_, 2);
lean_inc_ref(v_matchTheorems_666_);
lean_dec(v___x_665_);
v___x_667_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__0___redArg(v_matchTheorems_666_, v_matcherName_653_);
lean_dec_ref(v_matchTheorems_666_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec(v_matcherName_653_);
v_val_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_val_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 0);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_val_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v___x_676_; 
lean_dec(v___x_667_);
lean_inc(v_a_657_);
lean_inc_ref(v_a_656_);
lean_inc(v_a_655_);
lean_inc_ref(v_a_654_);
lean_inc(v_matcherName_653_);
v___x_676_ = lean_get_match_equations_for(v_matcherName_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v_eqnNames_678_; size_t v_sz_679_; size_t v___x_680_; lean_object* v___x_681_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v_eqnNames_678_ = lean_ctor_get(v_a_677_, 0);
lean_inc_ref(v_eqnNames_678_);
lean_dec(v_a_677_);
v_sz_679_ = lean_array_size(v_eqnNames_678_);
v___x_680_ = ((size_t)0ULL);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_Cbv_getEqnTheorems_spec__1(v_sz_679_, v___x_680_, v_eqnNames_678_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_727_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_727_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_727_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_727_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v_env_687_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_traceState_691_; lean_object* v_messages_692_; lean_object* v_infoState_693_; lean_object* v_snapshotTasks_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_725_; 
v___x_686_ = lean_st_ref_take(v_a_657_);
v_env_687_ = lean_ctor_get(v___x_686_, 0);
v_nextMacroScope_688_ = lean_ctor_get(v___x_686_, 1);
v_ngen_689_ = lean_ctor_get(v___x_686_, 2);
v_auxDeclNGen_690_ = lean_ctor_get(v___x_686_, 3);
v_traceState_691_ = lean_ctor_get(v___x_686_, 4);
v_messages_692_ = lean_ctor_get(v___x_686_, 6);
v_infoState_693_ = lean_ctor_get(v___x_686_, 7);
v_snapshotTasks_694_ = lean_ctor_get(v___x_686_, 8);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v___x_686_, 5);
lean_dec(v_unused_726_);
v___x_696_ = v___x_686_;
v_isShared_697_ = v_isSharedCheck_725_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snapshotTasks_694_);
lean_inc(v_infoState_693_);
lean_inc(v_messages_692_);
lean_inc(v_traceState_691_);
lean_inc(v_auxDeclNGen_690_);
lean_inc(v_ngen_689_);
lean_inc(v_nextMacroScope_688_);
lean_inc(v_env_687_);
lean_dec(v___x_686_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_725_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_698_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__1);
v___x_699_ = l___private_Lean_Meta_Tactic_Cbv_TheoremsLookup_0__Lean_Meta_Sym_Simp_Theorems_insertMany(v___x_698_, v_a_682_);
lean_dec(v_a_682_);
lean_inc_ref(v___x_699_);
v___f_700_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_getMatchTheorems___lam__0), 3, 2);
lean_closure_set(v___f_700_, 0, v_matcherName_653_);
lean_closure_set(v___f_700_, 1, v___x_699_);
v___x_701_ = l_Lean_EnvExtension_modifyState___redArg(v___x_661_, v_env_687_, v___f_700_, v_asyncMode_662_, v___x_664_);
v___x_702_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__2);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 5, v___x_702_);
lean_ctor_set(v___x_696_, 0, v___x_701_);
v___x_704_ = v___x_696_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_nextMacroScope_688_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_ngen_689_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_auxDeclNGen_690_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_traceState_691_);
lean_ctor_set(v_reuseFailAlloc_724_, 5, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_724_, 6, v_messages_692_);
lean_ctor_set(v_reuseFailAlloc_724_, 7, v_infoState_693_);
lean_ctor_set(v_reuseFailAlloc_724_, 8, v_snapshotTasks_694_);
v___x_704_ = v_reuseFailAlloc_724_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_mctx_707_; lean_object* v_zetaDeltaFVarIds_708_; lean_object* v_postponed_709_; lean_object* v_diag_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_722_; 
v___x_705_ = lean_st_ref_put(v_a_657_, v___x_704_);
v___x_706_ = lean_st_ref_take(v_a_655_);
v_mctx_707_ = lean_ctor_get(v___x_706_, 0);
v_zetaDeltaFVarIds_708_ = lean_ctor_get(v___x_706_, 2);
v_postponed_709_ = lean_ctor_get(v___x_706_, 3);
v_diag_710_ = lean_ctor_get(v___x_706_, 4);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_706_, 1);
lean_dec(v_unused_723_);
v___x_712_ = v___x_706_;
v_isShared_713_ = v_isSharedCheck_722_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_diag_710_);
lean_inc(v_postponed_709_);
lean_inc(v_zetaDeltaFVarIds_708_);
lean_inc(v_mctx_707_);
lean_dec(v___x_706_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_722_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3, &l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_getEqnTheorems___closed__3);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_mctx_707_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_zetaDeltaFVarIds_708_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_postponed_709_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_diag_710_);
v___x_716_ = v_reuseFailAlloc_721_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_st_ref_put(v_a_655_, v___x_716_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_699_);
v___x_719_ = v___x_684_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_699_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_matcherName_653_);
v_a_728_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_681_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_681_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_matcherName_653_);
v_a_736_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_676_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_676_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems___boxed(lean_object* v_matcherName_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_matcherName_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_750_;
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
