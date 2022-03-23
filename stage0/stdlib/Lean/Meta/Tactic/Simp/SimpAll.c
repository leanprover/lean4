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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_simpStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_getSimpTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpAll_State_modified___default;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SimpAll_main___spec__1(size_t, size_t, lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; 
x_13 = lean_array_uget(x_1, x_3);
lean_inc(x_6);
x_21 = l_Lean_Meta_getLocalDecl(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_userName(x_22);
lean_inc(x_24);
lean_inc(x_4);
x_25 = l_Lean_Meta_SimpTheoremsArray_isErased(x_4, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = l_Lean_LocalDecl_fvarId(x_22);
x_27 = l_Lean_LocalDecl_toExpr(x_22);
x_28 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___closed__2;
x_29 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_28, x_8, x_9, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_27);
x_33 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_4, x_27, x_32, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_LocalDecl_type(x_22);
lean_dec(x_22);
lean_inc(x_7);
x_37 = l_Lean_Meta_instantiateMVars(x_36, x_6, x_7, x_8, x_9, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_40, 4, x_27);
x_41 = lean_st_ref_get(x_9, x_39);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_take(x_5, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_ctor_get(x_44, 2);
x_49 = lean_array_push(x_47, x_40);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_48, 1);
lean_dec(x_51);
lean_inc(x_34);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_44, 1, x_49);
x_52 = lean_st_ref_set(x_5, x_44, x_45);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_34);
x_14 = x_54;
x_15 = x_53;
goto block_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 2);
x_57 = lean_ctor_get(x_48, 3);
x_58 = lean_ctor_get(x_48, 4);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
lean_inc(x_34);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_34);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_44, 2, x_59);
lean_ctor_set(x_44, 1, x_49);
x_60 = lean_st_ref_set(x_5, x_44, x_45);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_34);
x_14 = x_62;
x_15 = x_61;
goto block_20;
}
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get(x_44, 1);
x_66 = lean_ctor_get(x_44, 2);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_44);
x_67 = lean_array_push(x_65, x_40);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 4);
lean_inc(x_71);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_72 = x_66;
} else {
 lean_dec_ref(x_66);
 x_72 = lean_box(0);
}
lean_inc(x_34);
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 5, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_34);
lean_ctor_set(x_73, 2, x_69);
lean_ctor_set(x_73, 3, x_70);
lean_ctor_set(x_73, 4, x_71);
x_74 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_63);
x_75 = lean_st_ref_set(x_5, x_74, x_45);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_34);
x_14 = x_77;
x_15 = x_76;
goto block_20;
}
}
else
{
uint8_t x_78; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_33, 0);
x_80 = lean_ctor_get(x_33, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_33);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_24);
lean_dec(x_22);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_4);
x_14 = x_82;
x_15 = x_23;
goto block_20;
}
}
else
{
uint8_t x_83; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_21);
if (x_83 == 0)
{
return x_21;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_21, 0);
x_85 = lean_ctor_get(x_21, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_21);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_16;
x_10 = x_15;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
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
x_23 = lean_array_get_size(x_14);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(x_14, x_24, x_25, x_22, x_1, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_14);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_initEntries___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
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
x_62 = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(x_55, x_59);
x_63 = !lean_is_exclusive(x_48);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
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
x_72 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_60);
x_73 = l_Lean_Meta_simpStep(x_70, x_61, x_60, x_48, x_71, x_72, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 0);
lean_dec(x_76);
x_77 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
lean_ctor_set(x_73, 0, x_77);
x_18 = x_73;
goto block_34;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_18 = x_80;
goto block_34;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_74);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_73);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_73, 1);
x_85 = lean_ctor_get(x_73, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_expr_eqv(x_87, x_60);
lean_dec(x_60);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_73);
x_89 = lean_st_ref_get(x_11, x_84);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_st_ref_get(x_7, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 2);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_inc(x_59);
lean_ctor_set(x_74, 0, x_59);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_86);
x_96 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_95, x_86, x_74, x_8, x_9, x_10, x_11, x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_st_ref_get(x_11, x_98);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_st_ref_take(x_7, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_102, 1);
x_106 = lean_ctor_get(x_102, 2);
x_107 = lean_array_get_size(x_105);
x_108 = lean_nat_dec_lt(x_3, x_107);
lean_dec(x_107);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_106, 1);
lean_dec(x_110);
lean_ctor_set(x_106, 1, x_97);
if (x_108 == 0)
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_72);
x_111 = lean_st_ref_set(x_7, x_102, x_103);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_dec(x_113);
lean_inc(x_1);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_111, 0, x_114);
x_18 = x_111;
goto block_34;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
lean_inc(x_1);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_18 = x_117;
goto block_34;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_box(0);
x_119 = lean_array_fset(x_105, x_3, x_118);
lean_ctor_set(x_42, 4, x_86);
lean_ctor_set(x_42, 3, x_87);
x_120 = lean_array_fset(x_119, x_3, x_42);
lean_ctor_set(x_102, 1, x_120);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_72);
x_121 = lean_st_ref_set(x_7, x_102, x_103);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
lean_dec(x_123);
lean_inc(x_1);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_121, 0, x_124);
x_18 = x_121;
goto block_34;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
lean_dec(x_121);
lean_inc(x_1);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_1);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_18 = x_127;
goto block_34;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_106, 0);
x_129 = lean_ctor_get(x_106, 2);
x_130 = lean_ctor_get(x_106, 3);
x_131 = lean_ctor_get(x_106, 4);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_106);
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_97);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set(x_132, 4, x_131);
if (x_108 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_ctor_set(x_102, 2, x_132);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_72);
x_133 = lean_st_ref_set(x_7, x_102, x_103);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
lean_inc(x_1);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_1);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
x_18 = x_137;
goto block_34;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_box(0);
x_139 = lean_array_fset(x_105, x_3, x_138);
lean_ctor_set(x_42, 4, x_86);
lean_ctor_set(x_42, 3, x_87);
x_140 = lean_array_fset(x_139, x_3, x_42);
lean_ctor_set(x_102, 2, x_132);
lean_ctor_set(x_102, 1, x_140);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_72);
x_141 = lean_st_ref_set(x_7, x_102, x_103);
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
goto block_34;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_146 = lean_ctor_get(x_102, 0);
x_147 = lean_ctor_get(x_102, 1);
x_148 = lean_ctor_get(x_102, 2);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_102);
x_149 = lean_array_get_size(x_147);
x_150 = lean_nat_dec_lt(x_3, x_149);
lean_dec(x_149);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_148, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_148, 4);
lean_inc(x_154);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 x_155 = x_148;
} else {
 lean_dec_ref(x_148);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 5, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_97);
lean_ctor_set(x_156, 2, x_152);
lean_ctor_set(x_156, 3, x_153);
lean_ctor_set(x_156, 4, x_154);
if (x_150 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_157 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_157, 0, x_146);
lean_ctor_set(x_157, 1, x_147);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set_uint8(x_157, sizeof(void*)*3, x_72);
x_158 = lean_st_ref_set(x_7, x_157, x_103);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
lean_inc(x_1);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_1);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
x_18 = x_162;
goto block_34;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_163 = lean_box(0);
x_164 = lean_array_fset(x_147, x_3, x_163);
lean_ctor_set(x_42, 4, x_86);
lean_ctor_set(x_42, 3, x_87);
x_165 = lean_array_fset(x_164, x_3, x_42);
x_166 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_166, 0, x_146);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_156);
lean_ctor_set_uint8(x_166, sizeof(void*)*3, x_72);
x_167 = lean_st_ref_set(x_7, x_166, x_103);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
lean_inc(x_1);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_1);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
x_18 = x_171;
goto block_34;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_172 = !lean_is_exclusive(x_96);
if (x_172 == 0)
{
x_18 = x_96;
goto block_34;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_96, 0);
x_174 = lean_ctor_get(x_96, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_96);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_18 = x_175;
goto block_34;
}
}
}
else
{
lean_object* x_176; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_74);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_1);
lean_ctor_set(x_73, 0, x_176);
x_18 = x_73;
goto block_34;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_177 = lean_ctor_get(x_74, 0);
x_178 = lean_ctor_get(x_73, 1);
lean_inc(x_178);
lean_dec(x_73);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_expr_eqv(x_180, x_60);
lean_dec(x_60);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_182 = lean_st_ref_get(x_11, x_178);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_st_ref_get(x_7, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 2);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
lean_inc(x_59);
lean_ctor_set(x_74, 0, x_59);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_179);
x_189 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_188, x_179, x_74, x_8, x_9, x_10, x_11, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_st_ref_get(x_11, x_191);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_st_ref_take(x_7, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 2);
lean_inc(x_199);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 x_200 = x_195;
} else {
 lean_dec_ref(x_195);
 x_200 = lean_box(0);
}
x_201 = lean_array_get_size(x_198);
x_202 = lean_nat_dec_lt(x_3, x_201);
lean_dec(x_201);
x_203 = lean_ctor_get(x_199, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_199, 4);
lean_inc(x_206);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 x_207 = x_199;
} else {
 lean_dec_ref(x_199);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_203);
lean_ctor_set(x_208, 1, x_190);
lean_ctor_set(x_208, 2, x_204);
lean_ctor_set(x_208, 3, x_205);
lean_ctor_set(x_208, 4, x_206);
if (x_202 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_180);
lean_dec(x_179);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
if (lean_is_scalar(x_200)) {
 x_209 = lean_alloc_ctor(0, 3, 1);
} else {
 x_209 = x_200;
}
lean_ctor_set(x_209, 0, x_197);
lean_ctor_set(x_209, 1, x_198);
lean_ctor_set(x_209, 2, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*3, x_72);
x_210 = lean_st_ref_set(x_7, x_209, x_196);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
lean_inc(x_1);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_1);
if (lean_is_scalar(x_212)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_212;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
x_18 = x_214;
goto block_34;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_215 = lean_box(0);
x_216 = lean_array_fset(x_198, x_3, x_215);
lean_ctor_set(x_42, 4, x_179);
lean_ctor_set(x_42, 3, x_180);
x_217 = lean_array_fset(x_216, x_3, x_42);
if (lean_is_scalar(x_200)) {
 x_218 = lean_alloc_ctor(0, 3, 1);
} else {
 x_218 = x_200;
}
lean_ctor_set(x_218, 0, x_197);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_208);
lean_ctor_set_uint8(x_218, sizeof(void*)*3, x_72);
x_219 = lean_st_ref_set(x_7, x_218, x_196);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
lean_inc(x_1);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_1);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_220);
x_18 = x_223;
goto block_34;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_180);
lean_dec(x_179);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_224 = lean_ctor_get(x_189, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_189, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_226 = x_189;
} else {
 lean_dec_ref(x_189);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
x_18 = x_227;
goto block_34;
}
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_180);
lean_dec(x_179);
lean_free_object(x_74);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_1);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_178);
x_18 = x_229;
goto block_34;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_230 = lean_ctor_get(x_74, 0);
lean_inc(x_230);
lean_dec(x_74);
x_231 = lean_ctor_get(x_73, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_232 = x_73;
} else {
 lean_dec_ref(x_73);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_dec(x_230);
x_235 = lean_expr_eqv(x_234, x_60);
lean_dec(x_60);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_232);
x_236 = lean_st_ref_get(x_11, x_231);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_st_ref_get(x_7, x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_239, 2);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
lean_inc(x_59);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_59);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_233);
x_244 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_242, x_233, x_243, x_8, x_9, x_10, x_11, x_240);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_st_ref_get(x_11, x_246);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_st_ref_take(x_7, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_250, 2);
lean_inc(x_254);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 x_255 = x_250;
} else {
 lean_dec_ref(x_250);
 x_255 = lean_box(0);
}
x_256 = lean_array_get_size(x_253);
x_257 = lean_nat_dec_lt(x_3, x_256);
lean_dec(x_256);
x_258 = lean_ctor_get(x_254, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_254, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_254, 3);
lean_inc(x_260);
x_261 = lean_ctor_get(x_254, 4);
lean_inc(x_261);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 lean_ctor_release(x_254, 2);
 lean_ctor_release(x_254, 3);
 lean_ctor_release(x_254, 4);
 x_262 = x_254;
} else {
 lean_dec_ref(x_254);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(0, 5, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set(x_263, 1, x_245);
lean_ctor_set(x_263, 2, x_259);
lean_ctor_set(x_263, 3, x_260);
lean_ctor_set(x_263, 4, x_261);
if (x_257 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_234);
lean_dec(x_233);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
if (lean_is_scalar(x_255)) {
 x_264 = lean_alloc_ctor(0, 3, 1);
} else {
 x_264 = x_255;
}
lean_ctor_set(x_264, 0, x_252);
lean_ctor_set(x_264, 1, x_253);
lean_ctor_set(x_264, 2, x_263);
lean_ctor_set_uint8(x_264, sizeof(void*)*3, x_72);
x_265 = lean_st_ref_set(x_7, x_264, x_251);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
lean_inc(x_1);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_1);
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
x_18 = x_269;
goto block_34;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_270 = lean_box(0);
x_271 = lean_array_fset(x_253, x_3, x_270);
lean_ctor_set(x_42, 4, x_233);
lean_ctor_set(x_42, 3, x_234);
x_272 = lean_array_fset(x_271, x_3, x_42);
if (lean_is_scalar(x_255)) {
 x_273 = lean_alloc_ctor(0, 3, 1);
} else {
 x_273 = x_255;
}
lean_ctor_set(x_273, 0, x_252);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_273, 2, x_263);
lean_ctor_set_uint8(x_273, sizeof(void*)*3, x_72);
x_274 = lean_st_ref_set(x_7, x_273, x_251);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
lean_inc(x_1);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_1);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
x_18 = x_278;
goto block_34;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_234);
lean_dec(x_233);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_279 = lean_ctor_get(x_244, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_244, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_281 = x_244;
} else {
 lean_dec_ref(x_244);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
x_18 = x_282;
goto block_34;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_234);
lean_dec(x_233);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_1);
if (lean_is_scalar(x_232)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_232;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_231);
x_18 = x_284;
goto block_34;
}
}
}
}
else
{
uint8_t x_285; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_285 = !lean_is_exclusive(x_73);
if (x_285 == 0)
{
x_18 = x_73;
goto block_34;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_73, 0);
x_287 = lean_ctor_get(x_73, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_73);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_18 = x_288;
goto block_34;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; 
x_289 = lean_ctor_get(x_48, 0);
x_290 = lean_ctor_get(x_48, 2);
x_291 = lean_ctor_get(x_48, 3);
x_292 = lean_ctor_get(x_48, 4);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_48);
x_293 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_293, 0, x_289);
lean_ctor_set(x_293, 1, x_62);
lean_ctor_set(x_293, 2, x_290);
lean_ctor_set(x_293, 3, x_291);
lean_ctor_set(x_293, 4, x_292);
x_294 = lean_st_ref_get(x_11, x_53);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_st_ref_get(x_7, x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_box(0);
x_301 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_60);
x_302 = l_Lean_Meta_simpStep(x_299, x_61, x_60, x_293, x_300, x_301, x_8, x_9, x_10, x_11, x_298);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
x_306 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
if (lean_is_scalar(x_305)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_305;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_304);
x_18 = x_307;
goto block_34;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_308 = lean_ctor_get(x_303, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_309 = x_303;
} else {
 lean_dec_ref(x_303);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_302, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_311 = x_302;
} else {
 lean_dec_ref(x_302);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_308, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
lean_dec(x_308);
x_314 = lean_expr_eqv(x_313, x_60);
lean_dec(x_60);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_311);
x_315 = lean_st_ref_get(x_11, x_310);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_st_ref_get(x_7, x_316);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_ctor_get(x_318, 2);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
lean_inc(x_59);
if (lean_is_scalar(x_309)) {
 x_322 = lean_alloc_ctor(1, 1, 0);
} else {
 x_322 = x_309;
}
lean_ctor_set(x_322, 0, x_59);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_312);
x_323 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_321, x_312, x_322, x_8, x_9, x_10, x_11, x_319);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_st_ref_get(x_11, x_325);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
lean_dec(x_326);
x_328 = lean_st_ref_take(x_7, x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_329, 2);
lean_inc(x_333);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 lean_ctor_release(x_329, 2);
 x_334 = x_329;
} else {
 lean_dec_ref(x_329);
 x_334 = lean_box(0);
}
x_335 = lean_array_get_size(x_332);
x_336 = lean_nat_dec_lt(x_3, x_335);
lean_dec(x_335);
x_337 = lean_ctor_get(x_333, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_333, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_333, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_333, 4);
lean_inc(x_340);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 lean_ctor_release(x_333, 2);
 lean_ctor_release(x_333, 3);
 lean_ctor_release(x_333, 4);
 x_341 = x_333;
} else {
 lean_dec_ref(x_333);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(0, 5, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_337);
lean_ctor_set(x_342, 1, x_324);
lean_ctor_set(x_342, 2, x_338);
lean_ctor_set(x_342, 3, x_339);
lean_ctor_set(x_342, 4, x_340);
if (x_336 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_313);
lean_dec(x_312);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
if (lean_is_scalar(x_334)) {
 x_343 = lean_alloc_ctor(0, 3, 1);
} else {
 x_343 = x_334;
}
lean_ctor_set(x_343, 0, x_331);
lean_ctor_set(x_343, 1, x_332);
lean_ctor_set(x_343, 2, x_342);
lean_ctor_set_uint8(x_343, sizeof(void*)*3, x_301);
x_344 = lean_st_ref_set(x_7, x_343, x_330);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_346 = x_344;
} else {
 lean_dec_ref(x_344);
 x_346 = lean_box(0);
}
lean_inc(x_1);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_1);
if (lean_is_scalar(x_346)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_346;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_345);
x_18 = x_348;
goto block_34;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_349 = lean_box(0);
x_350 = lean_array_fset(x_332, x_3, x_349);
lean_ctor_set(x_42, 4, x_312);
lean_ctor_set(x_42, 3, x_313);
x_351 = lean_array_fset(x_350, x_3, x_42);
if (lean_is_scalar(x_334)) {
 x_352 = lean_alloc_ctor(0, 3, 1);
} else {
 x_352 = x_334;
}
lean_ctor_set(x_352, 0, x_331);
lean_ctor_set(x_352, 1, x_351);
lean_ctor_set(x_352, 2, x_342);
lean_ctor_set_uint8(x_352, sizeof(void*)*3, x_301);
x_353 = lean_st_ref_set(x_7, x_352, x_330);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_355 = x_353;
} else {
 lean_dec_ref(x_353);
 x_355 = lean_box(0);
}
lean_inc(x_1);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_1);
if (lean_is_scalar(x_355)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_355;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_354);
x_18 = x_357;
goto block_34;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_313);
lean_dec(x_312);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_358 = lean_ctor_get(x_323, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_323, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_360 = x_323;
} else {
 lean_dec_ref(x_323);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
x_18 = x_361;
goto block_34;
}
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_309);
lean_free_object(x_42);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_1);
x_362 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_362, 0, x_1);
if (lean_is_scalar(x_311)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_311;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_310);
x_18 = x_363;
goto block_34;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_free_object(x_42);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_364 = lean_ctor_get(x_302, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_302, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_366 = x_302;
} else {
 lean_dec_ref(x_302);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
x_18 = x_367;
goto block_34;
}
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_368 = lean_ctor_get(x_42, 0);
x_369 = lean_ctor_get(x_42, 1);
x_370 = lean_ctor_get(x_42, 2);
x_371 = lean_ctor_get(x_42, 3);
x_372 = lean_ctor_get(x_42, 4);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_42);
lean_inc(x_370);
x_373 = l_Lean_Meta_SimpTheoremsArray_eraseTheorem(x_55, x_370);
x_374 = lean_ctor_get(x_48, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_48, 2);
lean_inc(x_375);
x_376 = lean_ctor_get(x_48, 3);
lean_inc(x_376);
x_377 = lean_ctor_get(x_48, 4);
lean_inc(x_377);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_378 = x_48;
} else {
 lean_dec_ref(x_48);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 5, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_374);
lean_ctor_set(x_379, 1, x_373);
lean_ctor_set(x_379, 2, x_375);
lean_ctor_set(x_379, 3, x_376);
lean_ctor_set(x_379, 4, x_377);
x_380 = lean_st_ref_get(x_11, x_53);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_382 = lean_st_ref_get(x_7, x_381);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
lean_dec(x_383);
x_386 = lean_box(0);
x_387 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_371);
x_388 = l_Lean_Meta_simpStep(x_385, x_372, x_371, x_379, x_386, x_387, x_8, x_9, x_10, x_11, x_384);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_391 = x_388;
} else {
 lean_dec_ref(x_388);
 x_391 = lean_box(0);
}
x_392 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___spec__1___closed__3;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_390);
x_18 = x_393;
goto block_34;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_394 = lean_ctor_get(x_389, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_395 = x_389;
} else {
 lean_dec_ref(x_389);
 x_395 = lean_box(0);
}
x_396 = lean_ctor_get(x_388, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_397 = x_388;
} else {
 lean_dec_ref(x_388);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_394, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_394, 1);
lean_inc(x_399);
lean_dec(x_394);
x_400 = lean_expr_eqv(x_399, x_371);
lean_dec(x_371);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_397);
x_401 = lean_st_ref_get(x_11, x_396);
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_403 = lean_st_ref_get(x_7, x_402);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = lean_ctor_get(x_404, 2);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
lean_dec(x_406);
lean_inc(x_370);
if (lean_is_scalar(x_395)) {
 x_408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_408 = x_395;
}
lean_ctor_set(x_408, 0, x_370);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_398);
x_409 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_407, x_398, x_408, x_8, x_9, x_10, x_11, x_405);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_st_ref_get(x_11, x_411);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
lean_dec(x_412);
x_414 = lean_st_ref_take(x_7, x_413);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
x_421 = lean_array_get_size(x_418);
x_422 = lean_nat_dec_lt(x_3, x_421);
lean_dec(x_421);
x_423 = lean_ctor_get(x_419, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_419, 2);
lean_inc(x_424);
x_425 = lean_ctor_get(x_419, 3);
lean_inc(x_425);
x_426 = lean_ctor_get(x_419, 4);
lean_inc(x_426);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 lean_ctor_release(x_419, 4);
 x_427 = x_419;
} else {
 lean_dec_ref(x_419);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(0, 5, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_423);
lean_ctor_set(x_428, 1, x_410);
lean_ctor_set(x_428, 2, x_424);
lean_ctor_set(x_428, 3, x_425);
lean_ctor_set(x_428, 4, x_426);
if (x_422 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
if (lean_is_scalar(x_420)) {
 x_429 = lean_alloc_ctor(0, 3, 1);
} else {
 x_429 = x_420;
}
lean_ctor_set(x_429, 0, x_417);
lean_ctor_set(x_429, 1, x_418);
lean_ctor_set(x_429, 2, x_428);
lean_ctor_set_uint8(x_429, sizeof(void*)*3, x_387);
x_430 = lean_st_ref_set(x_7, x_429, x_416);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_432 = x_430;
} else {
 lean_dec_ref(x_430);
 x_432 = lean_box(0);
}
lean_inc(x_1);
x_433 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_433, 0, x_1);
if (lean_is_scalar(x_432)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_432;
}
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_431);
x_18 = x_434;
goto block_34;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_435 = lean_box(0);
x_436 = lean_array_fset(x_418, x_3, x_435);
x_437 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_437, 0, x_368);
lean_ctor_set(x_437, 1, x_369);
lean_ctor_set(x_437, 2, x_370);
lean_ctor_set(x_437, 3, x_399);
lean_ctor_set(x_437, 4, x_398);
x_438 = lean_array_fset(x_436, x_3, x_437);
if (lean_is_scalar(x_420)) {
 x_439 = lean_alloc_ctor(0, 3, 1);
} else {
 x_439 = x_420;
}
lean_ctor_set(x_439, 0, x_417);
lean_ctor_set(x_439, 1, x_438);
lean_ctor_set(x_439, 2, x_428);
lean_ctor_set_uint8(x_439, sizeof(void*)*3, x_387);
x_440 = lean_st_ref_set(x_7, x_439, x_416);
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_442 = x_440;
} else {
 lean_dec_ref(x_440);
 x_442 = lean_box(0);
}
lean_inc(x_1);
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_1);
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_441);
x_18 = x_444;
goto block_34;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
x_445 = lean_ctor_get(x_409, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_409, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_447 = x_409;
} else {
 lean_dec_ref(x_409);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
x_18 = x_448;
goto block_34;
}
}
else
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_395);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_inc(x_1);
x_449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_449, 0, x_1);
if (lean_is_scalar(x_397)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_397;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_396);
x_18 = x_450;
goto block_34;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
x_451 = lean_ctor_get(x_388, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_388, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_453 = x_388;
} else {
 lean_dec_ref(x_388);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
x_18 = x_454;
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
lean_object* x_455; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_6);
lean_ctor_set(x_455, 1, x_12);
return x_455;
}
}
else
{
lean_object* x_456; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_6);
lean_ctor_set(x_456, 1, x_12);
return x_456;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
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
x_21 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_22 = l_Lean_Meta_simpTarget(x_14, x_20, x_1, x_21, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(x_21);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l___private_Lean_Meta_Tactic_Simp_SimpAll_0__Lean_Meta_SimpAll_loop___lambda__2___closed__1;
x_33 = lean_name_eq(x_14, x_31);
lean_dec(x_14);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_st_ref_get(x_7, x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_3, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_21);
x_41 = lean_st_ref_set(x_3, x_37, x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = lean_apply_7(x_32, x_43, x_3, x_4, x_5, x_6, x_7, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_37, 1);
x_46 = lean_ctor_get(x_37, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_21);
x_48 = lean_st_ref_set(x_3, x_47, x_38);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = lean_apply_7(x_32, x_50, x_3, x_4, x_5, x_6, x_7, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_31);
x_52 = lean_box(0);
x_53 = lean_apply_7(x_32, x_52, x_3, x_4, x_5, x_6, x_7, x_30);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
return x_22;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_22, 0);
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_22);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
