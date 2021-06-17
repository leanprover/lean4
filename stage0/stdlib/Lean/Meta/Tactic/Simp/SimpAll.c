// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpAll
// Imports: Init Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Util Lean.Meta.Tactic.Simp.Main
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
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__3(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_SimpAll_instInhabitedEntry___closed__1;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpAll_State_entries___default___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__1(lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_erase___at_Lean_Meta_SimpLemmas_eraseCore___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpAll_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1;
lean_object* l_Lean_Meta_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpLemmas_isDeclToUnfold___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_addSimpLemmaEntry_updateLemmaNames___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpAll_main_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpAll_main_match__1(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
lean_object* l_Lean_Meta_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__2(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__1;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Meta_SimpAll_State_modified___default;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry;
lean_object* l_Lean_Meta_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__1;
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpAll_State_entries___default;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(size_t, size_t, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpAll___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static uint64_t _init_l_Lean_Meta_SimpAll_instInhabitedEntry___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__2;
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_instInhabitedEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SimpAll_State_modified___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_State_entries___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpAll_State_entries___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_4 < x_3;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_4);
lean_inc(x_7);
x_22 = l_Lean_Meta_getLocalDecl(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_LocalDecl_userName(x_23);
lean_inc(x_1);
x_26 = l_Std_PersistentHashMap_contains___at_Lean_Meta_SimpLemmas_isDeclToUnfold___spec__1(x_1, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_27 = l_Lean_LocalDecl_fvarId(x_23);
x_28 = l_Lean_LocalDecl_toExpr(x_23);
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
x_30 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_29, x_9, x_10, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_10, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_6, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 2);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_31);
x_41 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_42 = 1;
x_43 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_28);
x_44 = l_Lean_Meta_SimpLemmas_add(x_39, x_41, x_28, x_42, x_43, x_40, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_LocalDecl_type(x_23);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_48 = l_Lean_Meta_instantiateMVars(x_47, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_25);
lean_ctor_set(x_51, 2, x_31);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_28);
x_52 = lean_st_ref_get(x_10, x_50);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_st_ref_take(x_6, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_ctor_get(x_55, 2);
x_60 = lean_array_push(x_58, x_51);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_59, 1);
lean_dec(x_62);
lean_ctor_set(x_59, 1, x_45);
lean_ctor_set(x_55, 1, x_60);
x_63 = lean_st_ref_set(x_6, x_55, x_56);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_65;
x_16 = x_64;
goto block_21;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 2);
x_68 = lean_ctor_get(x_59, 3);
x_69 = lean_ctor_get(x_59, 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_45);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_68);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_55, 2, x_70);
lean_ctor_set(x_55, 1, x_60);
x_71 = lean_st_ref_set(x_6, x_55, x_56);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_73;
x_16 = x_72;
goto block_21;
}
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_74 = lean_ctor_get_uint8(x_55, sizeof(void*)*3);
x_75 = lean_ctor_get(x_55, 0);
x_76 = lean_ctor_get(x_55, 1);
x_77 = lean_ctor_get(x_55, 2);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_55);
x_78 = lean_array_push(x_76, x_51);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 4);
lean_inc(x_82);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 x_83 = x_77;
} else {
 lean_dec_ref(x_77);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 5, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_45);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
x_85 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*3, x_74);
x_86 = lean_st_ref_set(x_6, x_85, x_56);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_88;
x_16 = x_87;
goto block_21;
}
}
else
{
uint8_t x_89; 
lean_dec(x_45);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_48);
if (x_89 == 0)
{
return x_48;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_48, 0);
x_91 = lean_ctor_get(x_48, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_48);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_44);
if (x_93 == 0)
{
return x_44;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_44, 0);
x_95 = lean_ctor_get(x_44, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_44);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_25);
lean_dec(x_23);
x_97 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_97;
x_16 = x_24;
goto block_21;
}
}
else
{
uint8_t x_98; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_22);
if (x_98 == 0)
{
return x_22;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_22, 0);
x_100 = lean_ctor_get(x_22, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_22);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Meta_getNondepPropHyps(x_12, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 4);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_array_get_size(x_14);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = lean_box(0);
x_28 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(x_23, x_14, x_25, x_26, x_27, x_1, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_14);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpLemmas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpLemmas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpLemmas(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = l_Std_PersistentHashMap_erase___at_Lean_Meta_SimpLemmas_eraseCore___spec__1(x_10, x_2);
x_14 = l_Std_PersistentHashMap_erase___at_Lean_Meta_SimpLemmas_eraseCore___spec__1(x_11, x_2);
x_15 = lean_box(0);
x_16 = l_Std_PersistentHashMap_insert___at_Lean_Meta_addSimpLemmaEntry_updateLemmaNames___spec__1(x_12, x_2, x_15);
lean_ctor_set(x_1, 4, x_16);
lean_ctor_set(x_1, 3, x_14);
lean_ctor_set(x_1, 2, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_23 = l_Std_PersistentHashMap_erase___at_Lean_Meta_SimpLemmas_eraseCore___spec__1(x_20, x_2);
x_24 = l_Std_PersistentHashMap_erase___at_Lean_Meta_SimpLemmas_eraseCore___spec__1(x_21, x_2);
x_25 = lean_box(0);
x_26 = l_Std_PersistentHashMap_insert___at_Lean_Meta_addSimpLemmaEntry_updateLemmaNames___spec__1(x_22, x_2, x_25);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_nat_dec_le(x_12, x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_5);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_36 = lean_st_ref_get(x_10, x_11);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_6, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_SimpAll_instInhabitedEntry;
x_43 = lean_array_get(x_42, x_41, x_4);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_10, x_40);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_6, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_get(x_10, x_48);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_get(x_6, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_ctor_get(x_43, 0);
x_59 = lean_ctor_get(x_43, 1);
x_60 = lean_ctor_get(x_43, 2);
x_61 = lean_ctor_get(x_43, 3);
x_62 = lean_ctor_get(x_43, 4);
x_63 = l_Lean_Meta_SimpLemmas_eraseCore___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(x_56, x_60, x_6, x_7, x_8, x_9, x_10, x_54);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_49);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_49, 1);
lean_dec(x_67);
lean_ctor_set(x_49, 1, x_64);
x_68 = lean_st_ref_get(x_10, x_65);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_get(x_6, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_61);
x_74 = l_Lean_Meta_simpStep(x_73, x_62, x_61, x_49, x_7, x_8, x_9, x_10, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3;
lean_ctor_set(x_74, 0, x_78);
x_18 = x_74;
goto block_35;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec(x_74);
x_80 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_18 = x_81;
goto block_35;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_74);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_74, 1);
x_86 = lean_ctor_get(x_74, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_expr_eqv(x_88, x_61);
lean_dec(x_61);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_74);
x_90 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
x_91 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_90, x_9, x_10, x_85);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_get(x_10, x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_6, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 2);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_92);
lean_ctor_set(x_75, 0, x_92);
x_101 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_102 = 1;
x_103 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_87);
x_104 = l_Lean_Meta_SimpLemmas_add(x_100, x_101, x_87, x_102, x_103, x_75, x_7, x_8, x_9, x_10, x_98);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_get(x_10, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_st_ref_take(x_6, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_113 = lean_ctor_get(x_110, 1);
x_114 = lean_ctor_get(x_110, 2);
x_115 = lean_array_get_size(x_113);
x_116 = lean_nat_dec_lt(x_4, x_115);
lean_dec(x_115);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_114, 1);
lean_dec(x_118);
lean_ctor_set(x_114, 1, x_105);
if (x_116 == 0)
{
lean_object* x_119; uint8_t x_120; 
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_87);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_102);
x_119 = lean_st_ref_set(x_6, x_110, x_111);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_dec(x_121);
lean_inc(x_1);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_119, 0, x_122);
x_18 = x_119;
goto block_35;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_dec(x_119);
lean_inc(x_1);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_18 = x_125;
goto block_35;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
x_127 = lean_array_fset(x_113, x_4, x_126);
lean_ctor_set(x_43, 4, x_87);
lean_ctor_set(x_43, 3, x_88);
lean_ctor_set(x_43, 2, x_92);
x_128 = lean_array_fset(x_127, x_4, x_43);
lean_ctor_set(x_110, 1, x_128);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_102);
x_129 = lean_st_ref_set(x_6, x_110, x_111);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 0);
lean_dec(x_131);
lean_inc(x_1);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_129, 0, x_132);
x_18 = x_129;
goto block_35;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
lean_inc(x_1);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_1);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_18 = x_135;
goto block_35;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_114, 0);
x_137 = lean_ctor_get(x_114, 2);
x_138 = lean_ctor_get(x_114, 3);
x_139 = lean_ctor_get(x_114, 4);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_114);
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_105);
lean_ctor_set(x_140, 2, x_137);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_139);
if (x_116 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_87);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
lean_ctor_set(x_110, 2, x_140);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_102);
x_141 = lean_st_ref_set(x_6, x_110, x_111);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
lean_inc(x_1);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_1);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
x_18 = x_145;
goto block_35;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
x_147 = lean_array_fset(x_113, x_4, x_146);
lean_ctor_set(x_43, 4, x_87);
lean_ctor_set(x_43, 3, x_88);
lean_ctor_set(x_43, 2, x_92);
x_148 = lean_array_fset(x_147, x_4, x_43);
lean_ctor_set(x_110, 2, x_140);
lean_ctor_set(x_110, 1, x_148);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_102);
x_149 = lean_st_ref_set(x_6, x_110, x_111);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
lean_inc(x_1);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_1);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
x_18 = x_153;
goto block_35;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_110, 0);
x_155 = lean_ctor_get(x_110, 1);
x_156 = lean_ctor_get(x_110, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_110);
x_157 = lean_array_get_size(x_155);
x_158 = lean_nat_dec_lt(x_4, x_157);
lean_dec(x_157);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_156, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_156, 4);
lean_inc(x_162);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 lean_ctor_release(x_156, 3);
 lean_ctor_release(x_156, 4);
 x_163 = x_156;
} else {
 lean_dec_ref(x_156);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 5, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_159);
lean_ctor_set(x_164, 1, x_105);
lean_ctor_set(x_164, 2, x_160);
lean_ctor_set(x_164, 3, x_161);
lean_ctor_set(x_164, 4, x_162);
if (x_158 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_87);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
x_165 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_165, 0, x_154);
lean_ctor_set(x_165, 1, x_155);
lean_ctor_set(x_165, 2, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*3, x_102);
x_166 = lean_st_ref_set(x_6, x_165, x_111);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
lean_inc(x_1);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_1);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
x_18 = x_170;
goto block_35;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_171 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
x_172 = lean_array_fset(x_155, x_4, x_171);
lean_ctor_set(x_43, 4, x_87);
lean_ctor_set(x_43, 3, x_88);
lean_ctor_set(x_43, 2, x_92);
x_173 = lean_array_fset(x_172, x_4, x_43);
x_174 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_174, 0, x_154);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set(x_174, 2, x_164);
lean_ctor_set_uint8(x_174, sizeof(void*)*3, x_102);
x_175 = lean_st_ref_set(x_6, x_174, x_111);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
lean_inc(x_1);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_1);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
x_18 = x_179;
goto block_35;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_87);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
x_180 = !lean_is_exclusive(x_104);
if (x_180 == 0)
{
x_18 = x_104;
goto block_35;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_104, 0);
x_182 = lean_ctor_get(x_104, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_104);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_18 = x_183;
goto block_35;
}
}
}
else
{
lean_object* x_184; 
lean_dec(x_88);
lean_dec(x_87);
lean_free_object(x_75);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
lean_inc(x_1);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_1);
lean_ctor_set(x_74, 0, x_184);
x_18 = x_74;
goto block_35;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_75, 0);
x_186 = lean_ctor_get(x_74, 1);
lean_inc(x_186);
lean_dec(x_74);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_expr_eqv(x_188, x_61);
lean_dec(x_61);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; 
x_190 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
x_191 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_190, x_9, x_10, x_186);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_st_ref_get(x_10, x_193);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_st_ref_get(x_6, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 2);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
lean_inc(x_192);
lean_ctor_set(x_75, 0, x_192);
x_201 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_202 = 1;
x_203 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_187);
x_204 = l_Lean_Meta_SimpLemmas_add(x_200, x_201, x_187, x_202, x_203, x_75, x_7, x_8, x_9, x_10, x_198);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_st_ref_get(x_10, x_206);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_st_ref_take(x_6, x_208);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 2);
lean_inc(x_214);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 x_215 = x_210;
} else {
 lean_dec_ref(x_210);
 x_215 = lean_box(0);
}
x_216 = lean_array_get_size(x_213);
x_217 = lean_nat_dec_lt(x_4, x_216);
lean_dec(x_216);
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_214, 4);
lean_inc(x_221);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 x_222 = x_214;
} else {
 lean_dec_ref(x_214);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(0, 5, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_205);
lean_ctor_set(x_223, 2, x_219);
lean_ctor_set(x_223, 3, x_220);
lean_ctor_set(x_223, 4, x_221);
if (x_217 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_192);
lean_dec(x_188);
lean_dec(x_187);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
if (lean_is_scalar(x_215)) {
 x_224 = lean_alloc_ctor(0, 3, 1);
} else {
 x_224 = x_215;
}
lean_ctor_set(x_224, 0, x_212);
lean_ctor_set(x_224, 1, x_213);
lean_ctor_set(x_224, 2, x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*3, x_202);
x_225 = lean_st_ref_set(x_6, x_224, x_211);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
lean_inc(x_1);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_1);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
x_18 = x_229;
goto block_35;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_230 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
x_231 = lean_array_fset(x_213, x_4, x_230);
lean_ctor_set(x_43, 4, x_187);
lean_ctor_set(x_43, 3, x_188);
lean_ctor_set(x_43, 2, x_192);
x_232 = lean_array_fset(x_231, x_4, x_43);
if (lean_is_scalar(x_215)) {
 x_233 = lean_alloc_ctor(0, 3, 1);
} else {
 x_233 = x_215;
}
lean_ctor_set(x_233, 0, x_212);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_233, 2, x_223);
lean_ctor_set_uint8(x_233, sizeof(void*)*3, x_202);
x_234 = lean_st_ref_set(x_6, x_233, x_211);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_236 = x_234;
} else {
 lean_dec_ref(x_234);
 x_236 = lean_box(0);
}
lean_inc(x_1);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_1);
if (lean_is_scalar(x_236)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_236;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
x_18 = x_238;
goto block_35;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_192);
lean_dec(x_188);
lean_dec(x_187);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
x_239 = lean_ctor_get(x_204, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_204, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_241 = x_204;
} else {
 lean_dec_ref(x_204);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
x_18 = x_242;
goto block_35;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_188);
lean_dec(x_187);
lean_free_object(x_75);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
lean_inc(x_1);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_1);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_186);
x_18 = x_244;
goto block_35;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_245 = lean_ctor_get(x_75, 0);
lean_inc(x_245);
lean_dec(x_75);
x_246 = lean_ctor_get(x_74, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_247 = x_74;
} else {
 lean_dec_ref(x_74);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
lean_dec(x_245);
x_250 = lean_expr_eqv(x_249, x_61);
lean_dec(x_61);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_247);
x_251 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
x_252 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_251, x_9, x_10, x_246);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_st_ref_get(x_10, x_254);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_257 = lean_st_ref_get(x_6, x_256);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_258, 2);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
lean_inc(x_253);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_253);
x_263 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_264 = 1;
x_265 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_248);
x_266 = l_Lean_Meta_SimpLemmas_add(x_261, x_263, x_248, x_264, x_265, x_262, x_7, x_8, x_9, x_10, x_259);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_st_ref_get(x_10, x_268);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_st_ref_take(x_6, x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 2);
lean_inc(x_276);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 x_277 = x_272;
} else {
 lean_dec_ref(x_272);
 x_277 = lean_box(0);
}
x_278 = lean_array_get_size(x_275);
x_279 = lean_nat_dec_lt(x_4, x_278);
lean_dec(x_278);
x_280 = lean_ctor_get(x_276, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_276, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_276, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_276, 4);
lean_inc(x_283);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 x_284 = x_276;
} else {
 lean_dec_ref(x_276);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(0, 5, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_280);
lean_ctor_set(x_285, 1, x_267);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set(x_285, 4, x_283);
if (x_279 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_253);
lean_dec(x_249);
lean_dec(x_248);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
if (lean_is_scalar(x_277)) {
 x_286 = lean_alloc_ctor(0, 3, 1);
} else {
 x_286 = x_277;
}
lean_ctor_set(x_286, 0, x_274);
lean_ctor_set(x_286, 1, x_275);
lean_ctor_set(x_286, 2, x_285);
lean_ctor_set_uint8(x_286, sizeof(void*)*3, x_264);
x_287 = lean_st_ref_set(x_6, x_286, x_273);
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_289 = x_287;
} else {
 lean_dec_ref(x_287);
 x_289 = lean_box(0);
}
lean_inc(x_1);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_1);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_288);
x_18 = x_291;
goto block_35;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_292 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
x_293 = lean_array_fset(x_275, x_4, x_292);
lean_ctor_set(x_43, 4, x_248);
lean_ctor_set(x_43, 3, x_249);
lean_ctor_set(x_43, 2, x_253);
x_294 = lean_array_fset(x_293, x_4, x_43);
if (lean_is_scalar(x_277)) {
 x_295 = lean_alloc_ctor(0, 3, 1);
} else {
 x_295 = x_277;
}
lean_ctor_set(x_295, 0, x_274);
lean_ctor_set(x_295, 1, x_294);
lean_ctor_set(x_295, 2, x_285);
lean_ctor_set_uint8(x_295, sizeof(void*)*3, x_264);
x_296 = lean_st_ref_set(x_6, x_295, x_273);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_298 = x_296;
} else {
 lean_dec_ref(x_296);
 x_298 = lean_box(0);
}
lean_inc(x_1);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_1);
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_298;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_297);
x_18 = x_300;
goto block_35;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_253);
lean_dec(x_249);
lean_dec(x_248);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
x_301 = lean_ctor_get(x_266, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_266, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_303 = x_266;
} else {
 lean_dec_ref(x_266);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
x_18 = x_304;
goto block_35;
}
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_249);
lean_dec(x_248);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
lean_inc(x_1);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_1);
if (lean_is_scalar(x_247)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_247;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_246);
x_18 = x_306;
goto block_35;
}
}
}
}
else
{
uint8_t x_307; 
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
x_307 = !lean_is_exclusive(x_74);
if (x_307 == 0)
{
x_18 = x_74;
goto block_35;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_74, 0);
x_309 = lean_ctor_get(x_74, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_74);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_18 = x_310;
goto block_35;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_311 = lean_ctor_get(x_49, 0);
x_312 = lean_ctor_get(x_49, 2);
x_313 = lean_ctor_get(x_49, 3);
x_314 = lean_ctor_get(x_49, 4);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_49);
x_315 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_315, 0, x_311);
lean_ctor_set(x_315, 1, x_64);
lean_ctor_set(x_315, 2, x_312);
lean_ctor_set(x_315, 3, x_313);
lean_ctor_set(x_315, 4, x_314);
x_316 = lean_st_ref_get(x_10, x_65);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_318 = lean_st_ref_get(x_6, x_317);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_61);
x_322 = l_Lean_Meta_simpStep(x_321, x_62, x_61, x_315, x_7, x_8, x_9, x_10, x_320);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_325 = x_322;
} else {
 lean_dec_ref(x_322);
 x_325 = lean_box(0);
}
x_326 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3;
if (lean_is_scalar(x_325)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_325;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_324);
x_18 = x_327;
goto block_35;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_328 = lean_ctor_get(x_323, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 x_329 = x_323;
} else {
 lean_dec_ref(x_323);
 x_329 = lean_box(0);
}
x_330 = lean_ctor_get(x_322, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_331 = x_322;
} else {
 lean_dec_ref(x_322);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_328, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_328, 1);
lean_inc(x_333);
lean_dec(x_328);
x_334 = lean_expr_eqv(x_333, x_61);
lean_dec(x_61);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_331);
x_335 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
x_336 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_335, x_9, x_10, x_330);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_st_ref_get(x_10, x_338);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_341 = lean_st_ref_get(x_6, x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_ctor_get(x_342, 2);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec(x_344);
lean_inc(x_337);
if (lean_is_scalar(x_329)) {
 x_346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_346 = x_329;
}
lean_ctor_set(x_346, 0, x_337);
x_347 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_348 = 1;
x_349 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_332);
x_350 = l_Lean_Meta_SimpLemmas_add(x_345, x_347, x_332, x_348, x_349, x_346, x_7, x_8, x_9, x_10, x_343);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_st_ref_get(x_10, x_352);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
lean_dec(x_353);
x_355 = lean_st_ref_take(x_6, x_354);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_ctor_get(x_356, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_356, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_356, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 lean_ctor_release(x_356, 2);
 x_361 = x_356;
} else {
 lean_dec_ref(x_356);
 x_361 = lean_box(0);
}
x_362 = lean_array_get_size(x_359);
x_363 = lean_nat_dec_lt(x_4, x_362);
lean_dec(x_362);
x_364 = lean_ctor_get(x_360, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_360, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_360, 3);
lean_inc(x_366);
x_367 = lean_ctor_get(x_360, 4);
lean_inc(x_367);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 lean_ctor_release(x_360, 2);
 lean_ctor_release(x_360, 3);
 lean_ctor_release(x_360, 4);
 x_368 = x_360;
} else {
 lean_dec_ref(x_360);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(0, 5, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_364);
lean_ctor_set(x_369, 1, x_351);
lean_ctor_set(x_369, 2, x_365);
lean_ctor_set(x_369, 3, x_366);
lean_ctor_set(x_369, 4, x_367);
if (x_363 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_337);
lean_dec(x_333);
lean_dec(x_332);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
if (lean_is_scalar(x_361)) {
 x_370 = lean_alloc_ctor(0, 3, 1);
} else {
 x_370 = x_361;
}
lean_ctor_set(x_370, 0, x_358);
lean_ctor_set(x_370, 1, x_359);
lean_ctor_set(x_370, 2, x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*3, x_348);
x_371 = lean_st_ref_set(x_6, x_370, x_357);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_373 = x_371;
} else {
 lean_dec_ref(x_371);
 x_373 = lean_box(0);
}
lean_inc(x_1);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_1);
if (lean_is_scalar(x_373)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_373;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_372);
x_18 = x_375;
goto block_35;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_376 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
x_377 = lean_array_fset(x_359, x_4, x_376);
lean_ctor_set(x_43, 4, x_332);
lean_ctor_set(x_43, 3, x_333);
lean_ctor_set(x_43, 2, x_337);
x_378 = lean_array_fset(x_377, x_4, x_43);
if (lean_is_scalar(x_361)) {
 x_379 = lean_alloc_ctor(0, 3, 1);
} else {
 x_379 = x_361;
}
lean_ctor_set(x_379, 0, x_358);
lean_ctor_set(x_379, 1, x_378);
lean_ctor_set(x_379, 2, x_369);
lean_ctor_set_uint8(x_379, sizeof(void*)*3, x_348);
x_380 = lean_st_ref_set(x_6, x_379, x_357);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
lean_inc(x_1);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_1);
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_381);
x_18 = x_384;
goto block_35;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_337);
lean_dec(x_333);
lean_dec(x_332);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
x_385 = lean_ctor_get(x_350, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_350, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_387 = x_350;
} else {
 lean_dec_ref(x_350);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
x_18 = x_388;
goto block_35;
}
}
else
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_329);
lean_free_object(x_43);
lean_dec(x_59);
lean_dec(x_58);
lean_inc(x_1);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_1);
if (lean_is_scalar(x_331)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_331;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_330);
x_18 = x_390;
goto block_35;
}
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
x_391 = lean_ctor_get(x_322, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_322, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_393 = x_322;
} else {
 lean_dec_ref(x_322);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
x_18 = x_394;
goto block_35;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_395 = lean_ctor_get(x_43, 0);
x_396 = lean_ctor_get(x_43, 1);
x_397 = lean_ctor_get(x_43, 2);
x_398 = lean_ctor_get(x_43, 3);
x_399 = lean_ctor_get(x_43, 4);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_397);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_43);
x_400 = l_Lean_Meta_SimpLemmas_eraseCore___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(x_56, x_397, x_6, x_7, x_8, x_9, x_10, x_54);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = lean_ctor_get(x_49, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_49, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_49, 3);
lean_inc(x_405);
x_406 = lean_ctor_get(x_49, 4);
lean_inc(x_406);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 lean_ctor_release(x_49, 4);
 x_407 = x_49;
} else {
 lean_dec_ref(x_49);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(0, 5, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_403);
lean_ctor_set(x_408, 1, x_401);
lean_ctor_set(x_408, 2, x_404);
lean_ctor_set(x_408, 3, x_405);
lean_ctor_set(x_408, 4, x_406);
x_409 = lean_st_ref_get(x_10, x_402);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_st_ref_get(x_6, x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
lean_dec(x_412);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_398);
x_415 = l_Lean_Meta_simpStep(x_414, x_399, x_398, x_408, x_7, x_8, x_9, x_10, x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_398);
lean_dec(x_396);
lean_dec(x_395);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_418 = x_415;
} else {
 lean_dec_ref(x_415);
 x_418 = lean_box(0);
}
x_419 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3;
if (lean_is_scalar(x_418)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_418;
}
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_417);
x_18 = x_420;
goto block_35;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; 
x_421 = lean_ctor_get(x_416, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_422 = x_416;
} else {
 lean_dec_ref(x_416);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get(x_415, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_424 = x_415;
} else {
 lean_dec_ref(x_415);
 x_424 = lean_box(0);
}
x_425 = lean_ctor_get(x_421, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_421, 1);
lean_inc(x_426);
lean_dec(x_421);
x_427 = lean_expr_eqv(x_426, x_398);
lean_dec(x_398);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_424);
x_428 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
x_429 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_428, x_9, x_10, x_423);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_st_ref_get(x_10, x_431);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_434 = lean_st_ref_get(x_6, x_433);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_437 = lean_ctor_get(x_435, 2);
lean_inc(x_437);
lean_dec(x_435);
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
lean_dec(x_437);
lean_inc(x_430);
if (lean_is_scalar(x_422)) {
 x_439 = lean_alloc_ctor(1, 1, 0);
} else {
 x_439 = x_422;
}
lean_ctor_set(x_439, 0, x_430);
x_440 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_441 = 1;
x_442 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_425);
x_443 = l_Lean_Meta_SimpLemmas_add(x_438, x_440, x_425, x_441, x_442, x_439, x_7, x_8, x_9, x_10, x_436);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_st_ref_get(x_10, x_445);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_448 = lean_st_ref_take(x_6, x_447);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_ctor_get(x_449, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_449, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_449, 2);
lean_inc(x_453);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 lean_ctor_release(x_449, 2);
 x_454 = x_449;
} else {
 lean_dec_ref(x_449);
 x_454 = lean_box(0);
}
x_455 = lean_array_get_size(x_452);
x_456 = lean_nat_dec_lt(x_4, x_455);
lean_dec(x_455);
x_457 = lean_ctor_get(x_453, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_453, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_453, 3);
lean_inc(x_459);
x_460 = lean_ctor_get(x_453, 4);
lean_inc(x_460);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 lean_ctor_release(x_453, 2);
 lean_ctor_release(x_453, 3);
 lean_ctor_release(x_453, 4);
 x_461 = x_453;
} else {
 lean_dec_ref(x_453);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(0, 5, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_457);
lean_ctor_set(x_462, 1, x_444);
lean_ctor_set(x_462, 2, x_458);
lean_ctor_set(x_462, 3, x_459);
lean_ctor_set(x_462, 4, x_460);
if (x_456 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_430);
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_396);
lean_dec(x_395);
if (lean_is_scalar(x_454)) {
 x_463 = lean_alloc_ctor(0, 3, 1);
} else {
 x_463 = x_454;
}
lean_ctor_set(x_463, 0, x_451);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_462);
lean_ctor_set_uint8(x_463, sizeof(void*)*3, x_441);
x_464 = lean_st_ref_set(x_6, x_463, x_450);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
lean_inc(x_1);
x_467 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_467, 0, x_1);
if (lean_is_scalar(x_466)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_466;
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_465);
x_18 = x_468;
goto block_35;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_469 = l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
x_470 = lean_array_fset(x_452, x_4, x_469);
x_471 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_471, 0, x_395);
lean_ctor_set(x_471, 1, x_396);
lean_ctor_set(x_471, 2, x_430);
lean_ctor_set(x_471, 3, x_426);
lean_ctor_set(x_471, 4, x_425);
x_472 = lean_array_fset(x_470, x_4, x_471);
if (lean_is_scalar(x_454)) {
 x_473 = lean_alloc_ctor(0, 3, 1);
} else {
 x_473 = x_454;
}
lean_ctor_set(x_473, 0, x_451);
lean_ctor_set(x_473, 1, x_472);
lean_ctor_set(x_473, 2, x_462);
lean_ctor_set_uint8(x_473, sizeof(void*)*3, x_441);
x_474 = lean_st_ref_set(x_6, x_473, x_450);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_476 = x_474;
} else {
 lean_dec_ref(x_474);
 x_476 = lean_box(0);
}
lean_inc(x_1);
x_477 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_477, 0, x_1);
if (lean_is_scalar(x_476)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_476;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_475);
x_18 = x_478;
goto block_35;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_430);
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_396);
lean_dec(x_395);
x_479 = lean_ctor_get(x_443, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_443, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_481 = x_443;
} else {
 lean_dec_ref(x_443);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_480);
x_18 = x_482;
goto block_35;
}
}
else
{
lean_object* x_483; lean_object* x_484; 
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_422);
lean_dec(x_396);
lean_dec(x_395);
lean_inc(x_1);
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_1);
if (lean_is_scalar(x_424)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_424;
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_423);
x_18 = x_484;
goto block_35;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_398);
lean_dec(x_396);
lean_dec(x_395);
x_485 = lean_ctor_get(x_415, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_415, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_487 = x_415;
} else {
 lean_dec_ref(x_415);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
x_18 = x_488;
goto block_35;
}
}
block_35:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_nat_add(x_4, x_28);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_29;
x_5 = x_27;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_489; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_5);
lean_ctor_set(x_489, 1, x_11);
return x_489;
}
}
else
{
lean_object* x_490; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_5);
lean_ctor_set(x_490, 1, x_11);
return x_490;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(x_2, x_3, x_4, x_5, x_6, x_21);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_20 = l_Lean_Meta_simpTarget(x_13, x_19, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1;
x_33 = lean_name_eq(x_13, x_31);
lean_dec(x_13);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_st_ref_get(x_6, x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_2, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = 1;
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_41);
x_42 = lean_st_ref_set(x_2, x_37, x_38);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_7(x_32, x_44, x_2, x_3, x_4, x_5, x_6, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_37, 1);
x_47 = lean_ctor_get(x_37, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = 1;
x_49 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_49, 0, x_31);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_48);
x_50 = lean_st_ref_set(x_2, x_49, x_38);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_apply_7(x_32, x_52, x_2, x_3, x_4, x_5, x_6, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_31);
x_54 = lean_box(0);
x_55 = lean_apply_7(x_32, x_54, x_2, x_3, x_4, x_5, x_6, x_30);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_20);
if (x_56 == 0)
{
return x_20;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_20, 0);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_20);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_13);
x_14 = lean_st_ref_set(x_1, x_10, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2(x_26, x_25, x_22, x_23, x_26, x_1, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__2;
x_32 = lean_box(0);
x_33 = lean_apply_7(x_31, x_32, x_1, x_2, x_3, x_4, x_5, x_30);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
x_46 = lean_ctor_get(x_10, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_47);
x_49 = lean_st_ref_set(x_1, x_48, x_11);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_get(x_5, x_50);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_get(x_1, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_array_get_size(x_56);
lean_dec(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_unsigned_to_nat(1u);
lean_inc(x_57);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
x_61 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_62 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2(x_61, x_60, x_57, x_58, x_61, x_1, x_2, x_3, x_4, x_5, x_55);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__2;
x_67 = lean_box(0);
x_68 = lean_apply_7(x_66, x_67, x_1, x_2, x_3, x_4, x_5, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
lean_dec(x_64);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SimpLemmas_eraseCore___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_SimpAll_main_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_SimpAll_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpAll_main_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = 1;
x_15 = x_2 + x_14;
x_16 = x_13;
x_17 = lean_array_uset(x_8, x_2, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Meta_SimpAll_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(x_1, x_2, x_3, x_4, x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_1, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_5, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_1, x_20);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = x_24;
lean_inc(x_28);
x_29 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(x_26, x_27, x_28);
x_30 = x_29;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Meta_assertHypotheses(x_18, x_30, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2(x_26, x_27, x_28);
x_36 = x_35;
x_37 = l_Lean_Meta_tryClearMany(x_34, x_36, x_2, x_3, x_4, x_5, x_33);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_31, 0);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_9, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_9, 0, x_55);
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 1);
lean_inc(x_56);
lean_dec(x_9);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_9);
if (x_59 == 0)
{
return x_9;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_9, 0);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_9);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_7);
if (x_63 == 0)
{
return x_7;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_7, 0);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_7);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_simpAll___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_mk_ref(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_10);
x_12 = l_Lean_Meta_SimpAll_main(x_10, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_5, x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_10, x_16);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_simpAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = 0;
x_9 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_simpAll___lambda__1), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SimpAll_instInhabitedEntry___closed__1 = _init_l_Lean_Meta_SimpAll_instInhabitedEntry___closed__1();
l_Lean_Meta_SimpAll_instInhabitedEntry___closed__2 = _init_l_Lean_Meta_SimpAll_instInhabitedEntry___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpAll_instInhabitedEntry___closed__2);
l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3 = _init_l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3);
l_Lean_Meta_SimpAll_instInhabitedEntry = _init_l_Lean_Meta_SimpAll_instInhabitedEntry();
lean_mark_persistent(l_Lean_Meta_SimpAll_instInhabitedEntry);
l_Lean_Meta_SimpAll_State_modified___default = _init_l_Lean_Meta_SimpAll_State_modified___default();
l_Lean_Meta_SimpAll_State_entries___default___closed__1 = _init_l_Lean_Meta_SimpAll_State_entries___default___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpAll_State_entries___default___closed__1);
l_Lean_Meta_SimpAll_State_entries___default = _init_l_Lean_Meta_SimpAll_State_entries___default();
lean_mark_persistent(l_Lean_Meta_SimpAll_State_entries___default);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__2___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
