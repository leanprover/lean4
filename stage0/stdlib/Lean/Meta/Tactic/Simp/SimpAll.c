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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
static lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_add(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_SimpAll_instInhabitedEntry___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpAll_State_entries___default___closed__1;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1;
lean_object* l_Lean_Meta_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__1;
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
lean_object* l_Lean_Meta_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpAll_State_modified___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry;
lean_object* l_Lean_Meta_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpAll_instInhabitedEntry___closed__3;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_State_entries___default;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(size_t, size_t, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
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
lean_inc(x_25);
lean_inc(x_1);
x_26 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_1, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
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
x_42 = 0;
x_43 = 1;
x_44 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_28);
x_45 = l_Lean_Meta_SimpTheorems_add(x_39, x_41, x_28, x_42, x_43, x_44, x_40, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_LocalDecl_type(x_23);
lean_dec(x_23);
lean_inc(x_8);
x_49 = l_Lean_Meta_instantiateMVars(x_48, x_7, x_8, x_9, x_10, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_25);
lean_ctor_set(x_52, 2, x_31);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 4, x_28);
x_53 = lean_st_ref_get(x_10, x_51);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_take(x_6, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_ctor_get(x_56, 2);
x_61 = lean_array_push(x_59, x_52);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_60, 1);
lean_dec(x_63);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_56, 1, x_61);
x_64 = lean_st_ref_set(x_6, x_56, x_57);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_66;
x_16 = x_65;
goto block_21;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 2);
x_69 = lean_ctor_get(x_60, 3);
x_70 = lean_ctor_get(x_60, 4);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_46);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_56, 2, x_71);
lean_ctor_set(x_56, 1, x_61);
x_72 = lean_st_ref_set(x_6, x_56, x_57);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_74;
x_16 = x_73;
goto block_21;
}
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get_uint8(x_56, sizeof(void*)*3);
x_76 = lean_ctor_get(x_56, 0);
x_77 = lean_ctor_get(x_56, 1);
x_78 = lean_ctor_get(x_56, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_56);
x_79 = lean_array_push(x_77, x_52);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_46);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_79);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_75);
x_87 = lean_st_ref_set(x_6, x_86, x_57);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_89;
x_16 = x_88;
goto block_21;
}
}
else
{
uint8_t x_90; 
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
x_90 = !lean_is_exclusive(x_45);
if (x_90 == 0)
{
return x_45;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_45, 0);
x_92 = lean_ctor_get(x_45, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_45);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_25);
lean_dec(x_23);
x_94 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__3;
x_15 = x_94;
x_16 = x_24;
goto block_21;
}
}
else
{
uint8_t x_95; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__1() {
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
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_6);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_dec(x_2);
x_35 = lean_st_ref_get(x_11, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_7, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_SimpAll_instInhabitedEntry;
x_42 = lean_array_get(x_41, x_40, x_3);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_11, x_39);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_get(x_7, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 2);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_get(x_11, x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_get(x_7, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = !lean_is_exclusive(x_42);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_42, 1);
x_59 = lean_ctor_get(x_42, 2);
x_60 = lean_ctor_get(x_42, 3);
x_61 = lean_ctor_get(x_42, 4);
lean_inc(x_59);
x_62 = l_Lean_Meta_SimpTheorems_eraseCore(x_55, x_59);
x_63 = !lean_is_exclusive(x_48);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_48, 1);
lean_dec(x_64);
lean_ctor_set(x_48, 1, x_62);
x_65 = lean_st_ref_get(x_11, x_53);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_7, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_60);
x_72 = l_Lean_Meta_simpStep(x_70, x_61, x_60, x_48, x_71, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
x_76 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
lean_ctor_set(x_72, 0, x_76);
x_18 = x_72;
goto block_34;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_18 = x_79;
goto block_34;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_72);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_72, 1);
x_84 = lean_ctor_get(x_72, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_expr_eqv(x_86, x_60);
lean_dec(x_60);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_free_object(x_72);
x_88 = lean_st_ref_get(x_11, x_83);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_st_ref_get(x_7, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 2);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_59);
lean_ctor_set(x_73, 0, x_59);
x_95 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_96 = 0;
x_97 = 1;
x_98 = lean_unsigned_to_nat(1000u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_85);
x_99 = l_Lean_Meta_SimpTheorems_add(x_94, x_95, x_85, x_96, x_97, x_98, x_73, x_8, x_9, x_10, x_11, x_92);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_st_ref_get(x_11, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_st_ref_take(x_7, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_105, 1);
x_109 = lean_ctor_get(x_105, 2);
x_110 = lean_array_get_size(x_108);
x_111 = lean_nat_dec_lt(x_3, x_110);
lean_dec(x_110);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_109, 1);
lean_dec(x_113);
lean_ctor_set(x_109, 1, x_100);
if (x_111 == 0)
{
lean_object* x_114; uint8_t x_115; 
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_ctor_set_uint8(x_105, sizeof(void*)*3, x_97);
x_114 = lean_st_ref_set(x_7, x_105, x_106);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
lean_inc(x_1);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_114, 0, x_117);
x_18 = x_114;
goto block_34;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
lean_inc(x_1);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_1);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_18 = x_120;
goto block_34;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_box(0);
x_122 = lean_array_fset(x_108, x_3, x_121);
lean_ctor_set(x_42, 4, x_85);
lean_ctor_set(x_42, 3, x_86);
x_123 = lean_array_fset(x_122, x_3, x_42);
lean_ctor_set(x_105, 1, x_123);
lean_ctor_set_uint8(x_105, sizeof(void*)*3, x_97);
x_124 = lean_st_ref_set(x_7, x_105, x_106);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
lean_dec(x_126);
lean_inc(x_1);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_124, 0, x_127);
x_18 = x_124;
goto block_34;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
lean_inc(x_1);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_1);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_18 = x_130;
goto block_34;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_109, 0);
x_132 = lean_ctor_get(x_109, 2);
x_133 = lean_ctor_get(x_109, 3);
x_134 = lean_ctor_get(x_109, 4);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_109);
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_100);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_133);
lean_ctor_set(x_135, 4, x_134);
if (x_111 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_ctor_set(x_105, 2, x_135);
lean_ctor_set_uint8(x_105, sizeof(void*)*3, x_97);
x_136 = lean_st_ref_set(x_7, x_105, x_106);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
lean_inc(x_1);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_1);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
x_18 = x_140;
goto block_34;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_box(0);
x_142 = lean_array_fset(x_108, x_3, x_141);
lean_ctor_set(x_42, 4, x_85);
lean_ctor_set(x_42, 3, x_86);
x_143 = lean_array_fset(x_142, x_3, x_42);
lean_ctor_set(x_105, 2, x_135);
lean_ctor_set(x_105, 1, x_143);
lean_ctor_set_uint8(x_105, sizeof(void*)*3, x_97);
x_144 = lean_st_ref_set(x_7, x_105, x_106);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
lean_inc(x_1);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_1);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
x_18 = x_148;
goto block_34;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_149 = lean_ctor_get(x_105, 0);
x_150 = lean_ctor_get(x_105, 1);
x_151 = lean_ctor_get(x_105, 2);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_105);
x_152 = lean_array_get_size(x_150);
x_153 = lean_nat_dec_lt(x_3, x_152);
lean_dec(x_152);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 4);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_154);
lean_ctor_set(x_159, 1, x_100);
lean_ctor_set(x_159, 2, x_155);
lean_ctor_set(x_159, 3, x_156);
lean_ctor_set(x_159, 4, x_157);
if (x_153 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_160 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_160, 0, x_149);
lean_ctor_set(x_160, 1, x_150);
lean_ctor_set(x_160, 2, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*3, x_97);
x_161 = lean_st_ref_set(x_7, x_160, x_106);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
lean_inc(x_1);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_1);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
x_18 = x_165;
goto block_34;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_166 = lean_box(0);
x_167 = lean_array_fset(x_150, x_3, x_166);
lean_ctor_set(x_42, 4, x_85);
lean_ctor_set(x_42, 3, x_86);
x_168 = lean_array_fset(x_167, x_3, x_42);
x_169 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_169, 0, x_149);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_159);
lean_ctor_set_uint8(x_169, sizeof(void*)*3, x_97);
x_170 = lean_st_ref_set(x_7, x_169, x_106);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
lean_inc(x_1);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_1);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
x_18 = x_174;
goto block_34;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_175 = !lean_is_exclusive(x_99);
if (x_175 == 0)
{
x_18 = x_99;
goto block_34;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_99, 0);
x_177 = lean_ctor_get(x_99, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_99);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_18 = x_178;
goto block_34;
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_73);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_72, 0, x_179);
x_18 = x_72;
goto block_34;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_180 = lean_ctor_get(x_73, 0);
x_181 = lean_ctor_get(x_72, 1);
lean_inc(x_181);
lean_dec(x_72);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_expr_eqv(x_183, x_60);
lean_dec(x_60);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; 
x_185 = lean_st_ref_get(x_11, x_181);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_st_ref_get(x_7, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 2);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
lean_inc(x_59);
lean_ctor_set(x_73, 0, x_59);
x_192 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_193 = 0;
x_194 = 1;
x_195 = lean_unsigned_to_nat(1000u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_182);
x_196 = l_Lean_Meta_SimpTheorems_add(x_191, x_192, x_182, x_193, x_194, x_195, x_73, x_8, x_9, x_10, x_11, x_189);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_st_ref_get(x_11, x_198);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_st_ref_take(x_7, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 2);
lean_inc(x_206);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 x_207 = x_202;
} else {
 lean_dec_ref(x_202);
 x_207 = lean_box(0);
}
x_208 = lean_array_get_size(x_205);
x_209 = lean_nat_dec_lt(x_3, x_208);
lean_dec(x_208);
x_210 = lean_ctor_get(x_206, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_206, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_206, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_206, 4);
lean_inc(x_213);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 lean_ctor_release(x_206, 4);
 x_214 = x_206;
} else {
 lean_dec_ref(x_206);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(0, 5, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set(x_215, 1, x_197);
lean_ctor_set(x_215, 2, x_211);
lean_ctor_set(x_215, 3, x_212);
lean_ctor_set(x_215, 4, x_213);
if (x_209 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_183);
lean_dec(x_182);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
if (lean_is_scalar(x_207)) {
 x_216 = lean_alloc_ctor(0, 3, 1);
} else {
 x_216 = x_207;
}
lean_ctor_set(x_216, 0, x_204);
lean_ctor_set(x_216, 1, x_205);
lean_ctor_set(x_216, 2, x_215);
lean_ctor_set_uint8(x_216, sizeof(void*)*3, x_194);
x_217 = lean_st_ref_set(x_7, x_216, x_203);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
lean_inc(x_1);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_1);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
x_18 = x_221;
goto block_34;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_222 = lean_box(0);
x_223 = lean_array_fset(x_205, x_3, x_222);
lean_ctor_set(x_42, 4, x_182);
lean_ctor_set(x_42, 3, x_183);
x_224 = lean_array_fset(x_223, x_3, x_42);
if (lean_is_scalar(x_207)) {
 x_225 = lean_alloc_ctor(0, 3, 1);
} else {
 x_225 = x_207;
}
lean_ctor_set(x_225, 0, x_204);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_215);
lean_ctor_set_uint8(x_225, sizeof(void*)*3, x_194);
x_226 = lean_st_ref_set(x_7, x_225, x_203);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
lean_inc(x_1);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_1);
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_228;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
x_18 = x_230;
goto block_34;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_183);
lean_dec(x_182);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_231 = lean_ctor_get(x_196, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_196, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_233 = x_196;
} else {
 lean_dec_ref(x_196);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
x_18 = x_234;
goto block_34;
}
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_183);
lean_dec(x_182);
lean_free_object(x_73);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_1);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_181);
x_18 = x_236;
goto block_34;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_237 = lean_ctor_get(x_73, 0);
lean_inc(x_237);
lean_dec(x_73);
x_238 = lean_ctor_get(x_72, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_239 = x_72;
} else {
 lean_dec_ref(x_72);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
lean_dec(x_237);
x_242 = lean_expr_eqv(x_241, x_60);
lean_dec(x_60);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_239);
x_243 = lean_st_ref_get(x_11, x_238);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_st_ref_get(x_7, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 2);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
lean_inc(x_59);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_59);
x_251 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_252 = 0;
x_253 = 1;
x_254 = lean_unsigned_to_nat(1000u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_240);
x_255 = l_Lean_Meta_SimpTheorems_add(x_249, x_251, x_240, x_252, x_253, x_254, x_250, x_8, x_9, x_10, x_11, x_247);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_st_ref_get(x_11, x_257);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_260 = lean_st_ref_take(x_7, x_259);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 2);
lean_inc(x_265);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_266 = x_261;
} else {
 lean_dec_ref(x_261);
 x_266 = lean_box(0);
}
x_267 = lean_array_get_size(x_264);
x_268 = lean_nat_dec_lt(x_3, x_267);
lean_dec(x_267);
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_265, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_265, 4);
lean_inc(x_272);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 x_273 = x_265;
} else {
 lean_dec_ref(x_265);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_256);
lean_ctor_set(x_274, 2, x_270);
lean_ctor_set(x_274, 3, x_271);
lean_ctor_set(x_274, 4, x_272);
if (x_268 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_241);
lean_dec(x_240);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
if (lean_is_scalar(x_266)) {
 x_275 = lean_alloc_ctor(0, 3, 1);
} else {
 x_275 = x_266;
}
lean_ctor_set(x_275, 0, x_263);
lean_ctor_set(x_275, 1, x_264);
lean_ctor_set(x_275, 2, x_274);
lean_ctor_set_uint8(x_275, sizeof(void*)*3, x_253);
x_276 = lean_st_ref_set(x_7, x_275, x_262);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_278 = x_276;
} else {
 lean_dec_ref(x_276);
 x_278 = lean_box(0);
}
lean_inc(x_1);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_1);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_277);
x_18 = x_280;
goto block_34;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_281 = lean_box(0);
x_282 = lean_array_fset(x_264, x_3, x_281);
lean_ctor_set(x_42, 4, x_240);
lean_ctor_set(x_42, 3, x_241);
x_283 = lean_array_fset(x_282, x_3, x_42);
if (lean_is_scalar(x_266)) {
 x_284 = lean_alloc_ctor(0, 3, 1);
} else {
 x_284 = x_266;
}
lean_ctor_set(x_284, 0, x_263);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_274);
lean_ctor_set_uint8(x_284, sizeof(void*)*3, x_253);
x_285 = lean_st_ref_set(x_7, x_284, x_262);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
lean_inc(x_1);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_1);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
x_18 = x_289;
goto block_34;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_241);
lean_dec(x_240);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_290 = lean_ctor_get(x_255, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_255, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_292 = x_255;
} else {
 lean_dec_ref(x_255);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
x_18 = x_293;
goto block_34;
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_241);
lean_dec(x_240);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_1);
if (lean_is_scalar(x_239)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_239;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_238);
x_18 = x_295;
goto block_34;
}
}
}
}
else
{
uint8_t x_296; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_296 = !lean_is_exclusive(x_72);
if (x_296 == 0)
{
x_18 = x_72;
goto block_34;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_72, 0);
x_298 = lean_ctor_get(x_72, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_72);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_18 = x_299;
goto block_34;
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_300 = lean_ctor_get(x_48, 0);
x_301 = lean_ctor_get(x_48, 2);
x_302 = lean_ctor_get(x_48, 3);
x_303 = lean_ctor_get(x_48, 4);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_48);
x_304 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_62);
lean_ctor_set(x_304, 2, x_301);
lean_ctor_set(x_304, 3, x_302);
lean_ctor_set(x_304, 4, x_303);
x_305 = lean_st_ref_get(x_11, x_53);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_st_ref_get(x_7, x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_60);
x_312 = l_Lean_Meta_simpStep(x_310, x_61, x_60, x_304, x_311, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
x_316 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
if (lean_is_scalar(x_315)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_315;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_314);
x_18 = x_317;
goto block_34;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_318 = lean_ctor_get(x_313, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_319 = x_313;
} else {
 lean_dec_ref(x_313);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get(x_312, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_321 = x_312;
} else {
 lean_dec_ref(x_312);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_318, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_dec(x_318);
x_324 = lean_expr_eqv(x_323, x_60);
lean_dec(x_60);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_321);
x_325 = lean_st_ref_get(x_11, x_320);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_st_ref_get(x_7, x_326);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_ctor_get(x_328, 2);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
lean_inc(x_59);
if (lean_is_scalar(x_319)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_319;
}
lean_ctor_set(x_332, 0, x_59);
x_333 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_334 = 0;
x_335 = 1;
x_336 = lean_unsigned_to_nat(1000u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_322);
x_337 = l_Lean_Meta_SimpTheorems_add(x_331, x_333, x_322, x_334, x_335, x_336, x_332, x_8, x_9, x_10, x_11, x_329);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_st_ref_get(x_11, x_339);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
x_342 = lean_st_ref_take(x_7, x_341);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_343, 2);
lean_inc(x_347);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 x_348 = x_343;
} else {
 lean_dec_ref(x_343);
 x_348 = lean_box(0);
}
x_349 = lean_array_get_size(x_346);
x_350 = lean_nat_dec_lt(x_3, x_349);
lean_dec(x_349);
x_351 = lean_ctor_get(x_347, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_347, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_347, 4);
lean_inc(x_354);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 lean_ctor_release(x_347, 4);
 x_355 = x_347;
} else {
 lean_dec_ref(x_347);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 5, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_338);
lean_ctor_set(x_356, 2, x_352);
lean_ctor_set(x_356, 3, x_353);
lean_ctor_set(x_356, 4, x_354);
if (x_350 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_323);
lean_dec(x_322);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
if (lean_is_scalar(x_348)) {
 x_357 = lean_alloc_ctor(0, 3, 1);
} else {
 x_357 = x_348;
}
lean_ctor_set(x_357, 0, x_345);
lean_ctor_set(x_357, 1, x_346);
lean_ctor_set(x_357, 2, x_356);
lean_ctor_set_uint8(x_357, sizeof(void*)*3, x_335);
x_358 = lean_st_ref_set(x_7, x_357, x_344);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_360 = x_358;
} else {
 lean_dec_ref(x_358);
 x_360 = lean_box(0);
}
lean_inc(x_1);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_1);
if (lean_is_scalar(x_360)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_360;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_359);
x_18 = x_362;
goto block_34;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_363 = lean_box(0);
x_364 = lean_array_fset(x_346, x_3, x_363);
lean_ctor_set(x_42, 4, x_322);
lean_ctor_set(x_42, 3, x_323);
x_365 = lean_array_fset(x_364, x_3, x_42);
if (lean_is_scalar(x_348)) {
 x_366 = lean_alloc_ctor(0, 3, 1);
} else {
 x_366 = x_348;
}
lean_ctor_set(x_366, 0, x_345);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set(x_366, 2, x_356);
lean_ctor_set_uint8(x_366, sizeof(void*)*3, x_335);
x_367 = lean_st_ref_set(x_7, x_366, x_344);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_369 = x_367;
} else {
 lean_dec_ref(x_367);
 x_369 = lean_box(0);
}
lean_inc(x_1);
x_370 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_370, 0, x_1);
if (lean_is_scalar(x_369)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_369;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_368);
x_18 = x_371;
goto block_34;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_323);
lean_dec(x_322);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_372 = lean_ctor_get(x_337, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_337, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_374 = x_337;
} else {
 lean_dec_ref(x_337);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
x_18 = x_375;
goto block_34;
}
}
else
{
lean_object* x_376; lean_object* x_377; 
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_319);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_1);
if (lean_is_scalar(x_321)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_321;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_320);
x_18 = x_377;
goto block_34;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_378 = lean_ctor_get(x_312, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_312, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_380 = x_312;
} else {
 lean_dec_ref(x_312);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
x_18 = x_381;
goto block_34;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_382 = lean_ctor_get(x_42, 0);
x_383 = lean_ctor_get(x_42, 1);
x_384 = lean_ctor_get(x_42, 2);
x_385 = lean_ctor_get(x_42, 3);
x_386 = lean_ctor_get(x_42, 4);
lean_inc(x_386);
lean_inc(x_385);
lean_inc(x_384);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_42);
lean_inc(x_384);
x_387 = l_Lean_Meta_SimpTheorems_eraseCore(x_55, x_384);
x_388 = lean_ctor_get(x_48, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_48, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_48, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_48, 4);
lean_inc(x_391);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_392 = x_48;
} else {
 lean_dec_ref(x_48);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_388);
lean_ctor_set(x_393, 1, x_387);
lean_ctor_set(x_393, 2, x_389);
lean_ctor_set(x_393, 3, x_390);
lean_ctor_set(x_393, 4, x_391);
x_394 = lean_st_ref_get(x_11, x_53);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_396 = lean_st_ref_get(x_7, x_395);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_385);
x_401 = l_Lean_Meta_simpStep(x_399, x_386, x_385, x_393, x_400, x_8, x_9, x_10, x_11, x_398);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
x_405 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_403);
x_18 = x_406;
goto block_34;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_407 = lean_ctor_get(x_402, 0);
lean_inc(x_407);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 x_408 = x_402;
} else {
 lean_dec_ref(x_402);
 x_408 = lean_box(0);
}
x_409 = lean_ctor_get(x_401, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_410 = x_401;
} else {
 lean_dec_ref(x_401);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_407, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_407, 1);
lean_inc(x_412);
lean_dec(x_407);
x_413 = lean_expr_eqv(x_412, x_385);
lean_dec(x_385);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_410);
x_414 = lean_st_ref_get(x_11, x_409);
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_st_ref_get(x_7, x_415);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = lean_ctor_get(x_417, 2);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
lean_inc(x_384);
if (lean_is_scalar(x_408)) {
 x_421 = lean_alloc_ctor(1, 1, 0);
} else {
 x_421 = x_408;
}
lean_ctor_set(x_421, 0, x_384);
x_422 = l_Lean_Meta_SimpAll_State_entries___default___closed__1;
x_423 = 0;
x_424 = 1;
x_425 = lean_unsigned_to_nat(1000u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_411);
x_426 = l_Lean_Meta_SimpTheorems_add(x_420, x_422, x_411, x_423, x_424, x_425, x_421, x_8, x_9, x_10, x_11, x_418);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_st_ref_get(x_11, x_428);
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
lean_dec(x_429);
x_431 = lean_st_ref_take(x_7, x_430);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_432, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 x_437 = x_432;
} else {
 lean_dec_ref(x_432);
 x_437 = lean_box(0);
}
x_438 = lean_array_get_size(x_435);
x_439 = lean_nat_dec_lt(x_3, x_438);
lean_dec(x_438);
x_440 = lean_ctor_get(x_436, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_436, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_436, 3);
lean_inc(x_442);
x_443 = lean_ctor_get(x_436, 4);
lean_inc(x_443);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 lean_ctor_release(x_436, 2);
 lean_ctor_release(x_436, 3);
 lean_ctor_release(x_436, 4);
 x_444 = x_436;
} else {
 lean_dec_ref(x_436);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_440);
lean_ctor_set(x_445, 1, x_427);
lean_ctor_set(x_445, 2, x_441);
lean_ctor_set(x_445, 3, x_442);
lean_ctor_set(x_445, 4, x_443);
if (x_439 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
if (lean_is_scalar(x_437)) {
 x_446 = lean_alloc_ctor(0, 3, 1);
} else {
 x_446 = x_437;
}
lean_ctor_set(x_446, 0, x_434);
lean_ctor_set(x_446, 1, x_435);
lean_ctor_set(x_446, 2, x_445);
lean_ctor_set_uint8(x_446, sizeof(void*)*3, x_424);
x_447 = lean_st_ref_set(x_7, x_446, x_433);
x_448 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_449 = x_447;
} else {
 lean_dec_ref(x_447);
 x_449 = lean_box(0);
}
lean_inc(x_1);
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_1);
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_448);
x_18 = x_451;
goto block_34;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_452 = lean_box(0);
x_453 = lean_array_fset(x_435, x_3, x_452);
x_454 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_454, 0, x_382);
lean_ctor_set(x_454, 1, x_383);
lean_ctor_set(x_454, 2, x_384);
lean_ctor_set(x_454, 3, x_412);
lean_ctor_set(x_454, 4, x_411);
x_455 = lean_array_fset(x_453, x_3, x_454);
if (lean_is_scalar(x_437)) {
 x_456 = lean_alloc_ctor(0, 3, 1);
} else {
 x_456 = x_437;
}
lean_ctor_set(x_456, 0, x_434);
lean_ctor_set(x_456, 1, x_455);
lean_ctor_set(x_456, 2, x_445);
lean_ctor_set_uint8(x_456, sizeof(void*)*3, x_424);
x_457 = lean_st_ref_set(x_7, x_456, x_433);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_459 = x_457;
} else {
 lean_dec_ref(x_457);
 x_459 = lean_box(0);
}
lean_inc(x_1);
x_460 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_460, 0, x_1);
if (lean_is_scalar(x_459)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_459;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_458);
x_18 = x_461;
goto block_34;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
x_462 = lean_ctor_get(x_426, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_426, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_464 = x_426;
} else {
 lean_dec_ref(x_426);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_463);
x_18 = x_465;
goto block_34;
}
}
else
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_408);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
lean_inc(x_1);
x_466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_466, 0, x_1);
if (lean_is_scalar(x_410)) {
 x_467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_467 = x_410;
}
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_409);
x_18 = x_467;
goto block_34;
}
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_382);
x_468 = lean_ctor_get(x_401, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_401, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_470 = x_401;
} else {
 lean_dec_ref(x_401);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
x_18 = x_471;
goto block_34;
}
}
block_34:
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_28;
x_6 = x_27;
x_12 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_472; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_6);
lean_ctor_set(x_472, 1, x_12);
return x_472;
}
}
else
{
lean_object* x_473; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_6);
lean_ctor_set(x_473, 1, x_12);
return x_473;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_3, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_21 = l_Lean_Meta_simpTarget(x_14, x_20, x_1, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
lean_dec(x_22);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1;
x_34 = lean_name_eq(x_14, x_32);
lean_dec(x_14);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_st_ref_get(x_7, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_take(x_3, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = 1;
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_42);
x_43 = lean_st_ref_set(x_3, x_38, x_39);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = lean_apply_7(x_33, x_45, x_3, x_4, x_5, x_6, x_7, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_38, 1);
x_48 = lean_ctor_get(x_38, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_32);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
x_51 = lean_st_ref_set(x_3, x_50, x_39);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = lean_apply_7(x_33, x_53, x_3, x_4, x_5, x_6, x_7, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_32);
x_55 = lean_box(0);
x_56 = lean_apply_7(x_33, x_55, x_3, x_4, x_5, x_6, x_7, x_31);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
return x_21;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_21, 0);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_21);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_22);
x_27 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(x_24, x_22, x_25, x_22, x_26, x_24, x_1, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_22);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(x_23, x_31, x_1, x_2, x_3, x_4, x_5, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_27, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_46);
x_48 = lean_st_ref_set(x_1, x_47, x_11);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_get(x_5, x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_get(x_1, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_get_size(x_55);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1;
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_56);
x_61 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(x_58, x_56, x_59, x_56, x_60, x_58, x_1, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(x_57, x_65, x_1, x_2, x_3, x_4, x_5, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_73 = x_61;
} else {
 lean_dec_ref(x_61);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 4);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpAll_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
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
lean_inc(x_24);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(x_26, x_27, x_24);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Meta_assertHypotheses(x_18, x_28, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2(x_26, x_27, x_24);
x_34 = l_Lean_Meta_tryClearMany(x_32, x_33, x_2, x_3, x_4, x_5, x_31);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_9, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_9, 0, x_52);
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_dec(x_9);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
return x_9;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_7);
if (x_60 == 0)
{
return x_7;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_7);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_simpAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
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
l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
