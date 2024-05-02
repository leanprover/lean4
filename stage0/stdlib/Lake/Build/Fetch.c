// Lean compiler output
// Module: Lake.Build.Fetch
// Imports: Init Lake.Util.Error Lake.Util.Cycle Lake.Util.EquipT Lake.Build.Info Lake.Build.Store
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
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__3;
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__2;
static lean_object* l_Lake_buildCycleError___rarg___lambda__1___closed__1;
static lean_object* l_Lake_buildCycleError___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__1;
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run_x27(lean_object*);
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__4;
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__6;
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
static lean_object* l_Lake_buildCycleError___rarg___closed__2;
extern lean_object* l_instMonadBaseIO;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_buildCycleError___rarg___closed__1;
lean_object* l_StateT_instMonad___rarg(lean_object*);
static lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildCycleError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildCycleError___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildCycleError___rarg___lambda__1(lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___rarg(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lake_buildCycleError___rarg___closed__3;
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_EStateT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1(lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_3, x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_RecBuildM_run___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_apply_5(x_1, x_5, x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_20 = x_8;
} else {
 lean_dec_ref(x_8);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_33 = x_8;
} else {
 lean_dec_ref(x_8);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RecBuildM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_RecBuildM_run_x27___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_buildCycleError___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  ", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_buildCycleError___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lake_BuildKey_toString(x_1);
x_3 = l_Lake_buildCycleError___rarg___lambda__1___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = l_Lake_buildCycleError___rarg___lambda__1___closed__2;
x_6 = lean_string_append(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_buildCycleError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildCycleError___rarg___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_buildCycleError___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_buildCycleError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("build cycle detected:\n", 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_box(0);
x_4 = l_Lake_buildCycleError___rarg___closed__1;
x_5 = l_List_mapTR_loop___rarg(x_4, x_2, x_3);
x_6 = l_Lake_buildCycleError___rarg___closed__2;
x_7 = l_String_intercalate(x_6, x_5);
x_8 = l_Lake_buildCycleError___rarg___closed__3;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lake_buildCycleError___rarg___lambda__1___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_apply_2(x_1, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_buildCycleError___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lake_BuildKey_toString(x_5);
x_8 = l_Lake_buildCycleError___rarg___lambda__1___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lake_buildCycleError___rarg___lambda__1___closed__2;
x_11 = lean_string_append(x_9, x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lake_BuildKey_toString(x_13);
x_16 = l_Lake_buildCycleError___rarg___lambda__1___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lake_buildCycleError___rarg___lambda__1___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_14;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__2(x_1, x_7);
x_9 = l_Lake_buildCycleError___rarg___closed__2;
x_10 = l_String_intercalate(x_9, x_8);
x_11 = l_Lake_buildCycleError___rarg___closed__3;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lake_buildCycleError___rarg___lambda__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_array_get_size(x_5);
x_18 = lean_array_push(x_5, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadCycleOfBuildKeyRecBuildM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadBaseIO;
x_2 = l_Lake_EStateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__2;
x_2 = l_StateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__3;
x_2 = l_Lake_instMonadCallStackOfCallStackTOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadCycleOfBuildKeyRecBuildM___lambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__4;
x_2 = l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildCycleError___at_Lake_instMonadCycleOfBuildKeyRecBuildM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildInfo_fetch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Error(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Cycle(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_EquipT(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Info(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Store(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Fetch(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Error(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Cycle(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EquipT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Info(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Store(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_buildCycleError___rarg___lambda__1___closed__1 = _init_l_Lake_buildCycleError___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lake_buildCycleError___rarg___lambda__1___closed__1);
l_Lake_buildCycleError___rarg___lambda__1___closed__2 = _init_l_Lake_buildCycleError___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lake_buildCycleError___rarg___lambda__1___closed__2);
l_Lake_buildCycleError___rarg___closed__1 = _init_l_Lake_buildCycleError___rarg___closed__1();
lean_mark_persistent(l_Lake_buildCycleError___rarg___closed__1);
l_Lake_buildCycleError___rarg___closed__2 = _init_l_Lake_buildCycleError___rarg___closed__2();
lean_mark_persistent(l_Lake_buildCycleError___rarg___closed__2);
l_Lake_buildCycleError___rarg___closed__3 = _init_l_Lake_buildCycleError___rarg___closed__3();
lean_mark_persistent(l_Lake_buildCycleError___rarg___closed__3);
l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__1 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__1();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__1);
l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__2 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__2();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__2);
l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__3 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__3();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__3);
l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__4 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__4();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__4);
l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__5 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__5();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__5);
l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__6 = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__6();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildM___closed__6);
l_Lake_instMonadCycleOfBuildKeyRecBuildM = _init_l_Lake_instMonadCycleOfBuildKeyRecBuildM();
lean_mark_persistent(l_Lake_instMonadCycleOfBuildKeyRecBuildM);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
