// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: Init Lean.Meta.Tactic.Clear
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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__6;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_MVarId_revert___lambda__1___closed__2;
static lean_object* l_Lean_MVarId_revert___lambda__1___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__15;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__14;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__5;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__1;
static lean_object* l_Lean_MVarId_revert___lambda__1___closed__1;
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__2;
static lean_object* l_Lean_MVarId_revert___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__17;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__4;
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__12;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_revert___lambda__2___closed__3;
lean_object* l_Lean_MVarId_setKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__10;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__11;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4;
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__4;
static lean_object* l_Lean_MVarId_revert___lambda__1___closed__3;
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to revert ", 17);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", it is an auxiliary declaration created to represent recursive definitions", 75);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
lean_inc(x_12);
x_13 = l_Lean_FVarId_getDecl(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_isAuxDecl(x_14);
lean_dec(x_14);
if (x_16 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_dec(x_12);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = l_Lean_Expr_fvar___override(x_12);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_26, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__4;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Revert", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("MVarId", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("revert", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__10;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__12;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(27u);
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
x_3 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__14;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
x_3 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__16;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__15;
lean_inc(x_12);
x_17 = l_Lean_Expr_fvarId_x21(x_12, x_16);
lean_inc(x_5);
x_18 = l_Lean_FVarId_getDecl(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_isAuxDecl(x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_array_push(x_15, x_12);
lean_ctor_set(x_4, 1, x_22);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__17;
x_27 = l_Lean_Expr_fvarId_x21(x_12, x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_MVarId_clear(x_14, x_27, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_4, 0, x_29);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_9 = x_30;
goto _start;
}
else
{
uint8_t x_34; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__15;
lean_inc(x_12);
x_45 = l_Lean_Expr_fvarId_x21(x_12, x_44);
lean_inc(x_5);
x_46 = l_Lean_FVarId_getDecl(x_45, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_LocalDecl_isAuxDecl(x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_50 = lean_array_push(x_43, x_12);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_3, x_52);
x_3 = x_53;
x_4 = x_51;
x_9 = x_48;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__17;
x_56 = l_Lean_Expr_fvarId_x21(x_12, x_55);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l_Lean_MVarId_clear(x_42, x_56, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_43);
x_61 = 1;
x_62 = lean_usize_add(x_3, x_61);
x_3 = x_62;
x_4 = x_60;
x_9 = x_59;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = lean_ctor_get(x_46, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_46, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_70 = x_46;
} else {
 lean_dec_ref(x_46);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_Expr_fvarId_x21(x_7, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_15 = lean_array_uset(x_9, x_4, x_12);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
x_3 = l_Lean_MVarId_revert___lambda__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
x_3 = l_Lean_MVarId_revert___lambda__1___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
x_13 = l_Lean_MVarId_revert___lambda__1___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Expr_mvarId_x21(x_12, x_13);
x_15 = l_Lean_MVarId_setTag(x_14, x_1, x_4, x_5, x_6, x_7, x_8);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_array_get_size(x_11);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
x_21 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
x_22 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_20, x_21, x_19, x_2, x_11);
x_23 = l_Lean_MVarId_revert___lambda__1___closed__4;
x_24 = l_Lean_Expr_mvarId_x21(x_12, x_23);
lean_ctor_set(x_3, 1, x_24);
lean_ctor_set(x_3, 0, x_22);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_array_get_size(x_11);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
x_29 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
x_30 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_28, x_29, x_27, x_2, x_11);
x_31 = l_Lean_MVarId_revert___lambda__1___closed__4;
x_32 = l_Lean_Expr_mvarId_x21(x_12, x_31);
lean_ctor_set(x_3, 1, x_32);
lean_ctor_set(x_3, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_3);
x_36 = l_Lean_Expr_getAppFn(x_34);
lean_dec(x_34);
x_37 = l_Lean_MVarId_revert___lambda__1___closed__2;
lean_inc(x_36);
x_38 = l_Lean_Expr_mvarId_x21(x_36, x_37);
x_39 = l_Lean_MVarId_setTag(x_38, x_1, x_4, x_5, x_6, x_7, x_8);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_array_get_size(x_35);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8;
x_45 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13;
x_46 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_44, x_45, x_43, x_2, x_35);
x_47 = l_Lean_MVarId_revert___lambda__1___closed__4;
x_48 = l_Lean_Expr_mvarId_x21(x_36, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_41)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_41;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
return x_50;
}
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to create binder due to failure when reverting variable dependencies", 75);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_revert___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_get_size(x_3);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_5);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(x_3, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_13, x_14, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_collectForwardDeps(x_18, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MVarId_revert___lambda__2___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_get_size(x_20);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(x_20, x_25, x_14, x_23, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_29);
x_31 = l_Lean_MVarId_getTag(x_29, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_46; lean_object* x_59; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
lean_inc(x_29);
x_35 = l_Lean_MVarId_setKind(x_29, x_34, x_5, x_6, x_7, x_8, x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_80 = lean_ctor_get(x_5, 1);
lean_inc(x_80);
x_81 = lean_st_ref_get(x_8, x_36);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_get(x_8, x_83);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_st_ref_get(x_6, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_8, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 2);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_8, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_environment_main_module(x_84);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_80);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = l_Lean_MVarId_revert___lambda__2___closed__2;
x_102 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_102, 0, x_90);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_94);
lean_ctor_set(x_102, 3, x_101);
lean_inc(x_29);
x_103 = l_Lean_MetavarContext_revert(x_30, x_29, x_4, x_99, x_102);
lean_dec(x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 2);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_st_ref_get(x_8, x_97);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_take(x_6, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
lean_ctor_set(x_112, 0, x_106);
x_116 = lean_st_ref_set(x_6, x_112, x_113);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_st_ref_take(x_8, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_119, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_dec(x_123);
lean_ctor_set(x_119, 2, x_108);
lean_ctor_set(x_119, 1, x_107);
x_124 = lean_st_ref_set(x_8, x_119, x_120);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_124, 0);
lean_dec(x_126);
lean_ctor_set(x_124, 0, x_105);
x_59 = x_124;
goto block_79;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_105);
lean_ctor_set(x_128, 1, x_127);
x_59 = x_128;
goto block_79;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_129 = lean_ctor_get(x_119, 0);
x_130 = lean_ctor_get(x_119, 3);
x_131 = lean_ctor_get(x_119, 4);
x_132 = lean_ctor_get(x_119, 5);
x_133 = lean_ctor_get(x_119, 6);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_119);
x_134 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_107);
lean_ctor_set(x_134, 2, x_108);
lean_ctor_set(x_134, 3, x_130);
lean_ctor_set(x_134, 4, x_131);
lean_ctor_set(x_134, 5, x_132);
lean_ctor_set(x_134, 6, x_133);
x_135 = lean_st_ref_set(x_8, x_134, x_120);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_105);
lean_ctor_set(x_138, 1, x_136);
x_59 = x_138;
goto block_79;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_139 = lean_ctor_get(x_112, 1);
x_140 = lean_ctor_get(x_112, 2);
x_141 = lean_ctor_get(x_112, 3);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_112);
x_142 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_142, 0, x_106);
lean_ctor_set(x_142, 1, x_139);
lean_ctor_set(x_142, 2, x_140);
lean_ctor_set(x_142, 3, x_141);
x_143 = lean_st_ref_set(x_6, x_142, x_113);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_st_ref_take(x_8, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 5);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 6);
lean_inc(x_152);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 lean_ctor_release(x_146, 5);
 lean_ctor_release(x_146, 6);
 x_153 = x_146;
} else {
 lean_dec_ref(x_146);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 7, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_107);
lean_ctor_set(x_154, 2, x_108);
lean_ctor_set(x_154, 3, x_149);
lean_ctor_set(x_154, 4, x_150);
lean_ctor_set(x_154, 5, x_151);
lean_ctor_set(x_154, 6, x_152);
x_155 = lean_st_ref_set(x_8, x_154, x_147);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_105);
lean_ctor_set(x_158, 1, x_156);
x_59 = x_158;
goto block_79;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_159 = lean_ctor_get(x_103, 1);
lean_inc(x_159);
lean_dec(x_103);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 2);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_st_ref_get(x_8, x_97);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_take(x_6, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = !lean_is_exclusive(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_169 = lean_ctor_get(x_166, 0);
lean_dec(x_169);
lean_ctor_set(x_166, 0, x_160);
x_170 = lean_st_ref_set(x_6, x_166, x_167);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = lean_st_ref_take(x_8, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = !lean_is_exclusive(x_173);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_173, 2);
lean_dec(x_176);
x_177 = lean_ctor_get(x_173, 1);
lean_dec(x_177);
lean_ctor_set(x_173, 2, x_162);
lean_ctor_set(x_173, 1, x_161);
x_178 = lean_st_ref_set(x_8, x_173, x_174);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_Lean_MVarId_revert___lambda__2___closed__4;
x_181 = l_Lean_throwError___at_Lean_MVarId_revert___spec__4(x_180, x_5, x_6, x_7, x_8, x_179);
x_59 = x_181;
goto block_79;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_182 = lean_ctor_get(x_173, 0);
x_183 = lean_ctor_get(x_173, 3);
x_184 = lean_ctor_get(x_173, 4);
x_185 = lean_ctor_get(x_173, 5);
x_186 = lean_ctor_get(x_173, 6);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_173);
x_187 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_161);
lean_ctor_set(x_187, 2, x_162);
lean_ctor_set(x_187, 3, x_183);
lean_ctor_set(x_187, 4, x_184);
lean_ctor_set(x_187, 5, x_185);
lean_ctor_set(x_187, 6, x_186);
x_188 = lean_st_ref_set(x_8, x_187, x_174);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = l_Lean_MVarId_revert___lambda__2___closed__4;
x_191 = l_Lean_throwError___at_Lean_MVarId_revert___spec__4(x_190, x_5, x_6, x_7, x_8, x_189);
x_59 = x_191;
goto block_79;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_192 = lean_ctor_get(x_166, 1);
x_193 = lean_ctor_get(x_166, 2);
x_194 = lean_ctor_get(x_166, 3);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_166);
x_195 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_195, 0, x_160);
lean_ctor_set(x_195, 1, x_192);
lean_ctor_set(x_195, 2, x_193);
lean_ctor_set(x_195, 3, x_194);
x_196 = lean_st_ref_set(x_6, x_195, x_167);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_st_ref_take(x_8, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 4);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 5);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 6);
lean_inc(x_205);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 lean_ctor_release(x_199, 5);
 lean_ctor_release(x_199, 6);
 x_206 = x_199;
} else {
 lean_dec_ref(x_199);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 7, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_201);
lean_ctor_set(x_207, 1, x_161);
lean_ctor_set(x_207, 2, x_162);
lean_ctor_set(x_207, 3, x_202);
lean_ctor_set(x_207, 4, x_203);
lean_ctor_set(x_207, 5, x_204);
lean_ctor_set(x_207, 6, x_205);
x_208 = lean_st_ref_set(x_8, x_207, x_200);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = l_Lean_MVarId_revert___lambda__2___closed__4;
x_211 = l_Lean_throwError___at_Lean_MVarId_revert___spec__4(x_210, x_5, x_6, x_7, x_8, x_209);
x_59 = x_211;
goto block_79;
}
}
block_45:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MVarId_revert___lambda__1(x_32, x_14, x_38, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_58:
{
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_49);
x_37 = x_46;
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_37 = x_53;
goto block_45;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
x_37 = x_46;
goto block_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_37 = x_57;
goto block_45;
}
}
}
block_79:
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = 2;
x_63 = l_Lean_MVarId_setKind(x_29, x_62, x_5, x_6, x_7, x_8, x_61);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_63, 0, x_66);
x_46 = x_63;
goto block_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_46 = x_70;
goto block_58;
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_dec(x_59);
x_73 = 2;
x_74 = l_Lean_MVarId_setKind(x_29, x_73, x_5, x_6, x_7, x_8, x_72);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_71);
x_46 = x_74;
goto block_58;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
x_46 = x_78;
goto block_58;
}
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_212 = !lean_is_exclusive(x_31);
if (x_212 == 0)
{
return x_31;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_31, 0);
x_214 = lean_ctor_get(x_31, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_31);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_216 = !lean_is_exclusive(x_26);
if (x_216 == 0)
{
return x_26;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_26, 0);
x_218 = lean_ctor_get(x_26, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_26);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_220 = !lean_is_exclusive(x_19);
if (x_220 == 0)
{
return x_19;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_19, 0);
x_222 = lean_ctor_get(x_19, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_19);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_16);
if (x_224 == 0)
{
return x_16;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_16, 0);
x_226 = lean_ctor_get(x_16, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_16);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_10);
if (x_228 == 0)
{
return x_10;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_10, 0);
x_230 = lean_ctor_get(x_10, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_10);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_revert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_MVarId_revert___closed__1;
x_11 = lean_box(x_3);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_revert___lambda__2___boxed), 9, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_11);
x_13 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l_Lean_MVarId_revert___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_MVarId_revert___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_MVarId_revert___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Lean_MVarId_revert___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_MVarId_revert___lambda__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_MVarId_revert(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_revert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_revert(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__8);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__9);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__10);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__11);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__12);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__13);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__14 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__14();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__14);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__15 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__15();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__15);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__16 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__16();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__16);
l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__17 = _init_l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__17();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_MVarId_revert___spec__2___closed__17);
l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_MVarId_revert___spec__3___closed__1);
l_Lean_MVarId_revert___lambda__1___closed__1 = _init_l_Lean_MVarId_revert___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__1___closed__1);
l_Lean_MVarId_revert___lambda__1___closed__2 = _init_l_Lean_MVarId_revert___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__1___closed__2);
l_Lean_MVarId_revert___lambda__1___closed__3 = _init_l_Lean_MVarId_revert___lambda__1___closed__3();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__1___closed__3);
l_Lean_MVarId_revert___lambda__1___closed__4 = _init_l_Lean_MVarId_revert___lambda__1___closed__4();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__1___closed__4);
l_Lean_MVarId_revert___lambda__2___closed__1 = _init_l_Lean_MVarId_revert___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__1);
l_Lean_MVarId_revert___lambda__2___closed__2 = _init_l_Lean_MVarId_revert___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__2);
l_Lean_MVarId_revert___lambda__2___closed__3 = _init_l_Lean_MVarId_revert___lambda__2___closed__3();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__3);
l_Lean_MVarId_revert___lambda__2___closed__4 = _init_l_Lean_MVarId_revert___lambda__2___closed__4();
lean_mark_persistent(l_Lean_MVarId_revert___lambda__2___closed__4);
l_Lean_MVarId_revert___closed__1 = _init_l_Lean_MVarId_revert___closed__1();
lean_mark_persistent(l_Lean_MVarId_revert___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
