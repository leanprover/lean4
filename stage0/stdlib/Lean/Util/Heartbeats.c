// Lean compiler output
// Module: Lean.Util.Heartbeats
// Imports: Lean.CoreM
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
lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withHeartbeats___rarg___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_reportOutOfHeartbeats___closed__2;
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats(lean_object*, lean_object*);
static lean_object* l_Lean_reportOutOfHeartbeats___closed__1;
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(uint8_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_nat_sub(x_4, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_withHeartbeats___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_withHeartbeats___rarg___lambda__2), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_withHeartbeats___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_getNumHeartbeats___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_withHeartbeats___rarg___closed__1;
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
lean_inc(x_6);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_withHeartbeats___rarg___lambda__3), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_withHeartbeats___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_withHeartbeats___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 9);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMaxHeartbeats(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 8);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getInitHeartbeats(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_getMaxHeartbeats(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_io_get_num_heartbeats(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_getInitHeartbeats(x_1, x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_nat_sub(x_8, x_12);
lean_dec(x_12);
lean_dec(x_8);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_13);
lean_dec(x_5);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_nat_sub(x_8, x_15);
lean_dec(x_15);
lean_dec(x_8);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_17);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getRemainingHeartbeats(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_io_get_num_heartbeats(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_getInitHeartbeats(x_1, x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_getMaxHeartbeats(x_1, x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_nat_sub(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
x_14 = lean_unsigned_to_nat(100u);
x_15 = lean_nat_mul(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_div(x_15, x_12);
lean_dec(x_12);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_nat_sub(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
x_20 = lean_unsigned_to_nat(100u);
x_21 = lean_nat_mul(x_19, x_20);
lean_dec(x_19);
x_22 = lean_nat_div(x_21, x_17);
lean_dec(x_17);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_heartbeatsPercent(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_373; uint8_t x_374; 
x_373 = 2;
x_374 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_373);
if (x_374 == 0)
{
lean_object* x_375; 
x_375 = lean_box(0);
x_7 = x_375;
goto block_372;
}
else
{
lean_object* x_376; uint8_t x_377; 
lean_inc(x_2);
x_376 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_377 = lean_unbox(x_376);
lean_dec(x_376);
if (x_377 == 0)
{
lean_object* x_378; 
x_378 = lean_box(0);
x_7 = x_378;
goto block_372;
}
else
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_4);
lean_dec(x_2);
x_379 = lean_box(0);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_6);
return x_380;
}
}
block_372:
{
uint8_t x_8; lean_object* x_366; uint8_t x_367; uint8_t x_368; 
lean_dec(x_7);
x_366 = lean_ctor_get(x_4, 2);
lean_inc(x_366);
x_367 = 1;
x_368 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_3, x_367);
if (x_368 == 0)
{
lean_dec(x_366);
x_8 = x_3;
goto block_365;
}
else
{
lean_object* x_369; uint8_t x_370; 
x_369 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__2;
x_370 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_366, x_369);
lean_dec(x_366);
if (x_370 == 0)
{
x_8 = x_3;
goto block_365;
}
else
{
uint8_t x_371; 
x_371 = 2;
x_8 = x_371;
goto block_365;
}
}
block_365:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 7);
lean_inc(x_13);
x_14 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
x_15 = 0;
x_16 = l_Lean_Syntax_getPos_x3f(x_14, x_15);
x_17 = l_Lean_Syntax_getTailPos_x3f(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_FileMap_toPosition(x_10, x_22);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 0, x_12);
x_25 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_20);
x_26 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_27 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_8);
x_28 = lean_st_ref_take(x_5, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_29, 5);
x_33 = l_Lean_PersistentArray_push___rarg(x_32, x_27);
lean_ctor_set(x_29, 5, x_33);
x_34 = lean_st_ref_set(x_5, x_29, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
x_43 = lean_ctor_get(x_29, 2);
x_44 = lean_ctor_get(x_29, 3);
x_45 = lean_ctor_get(x_29, 4);
x_46 = lean_ctor_get(x_29, 5);
x_47 = lean_ctor_get(x_29, 6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_29);
x_48 = l_Lean_PersistentArray_push___rarg(x_46, x_27);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_49, 6, x_47);
x_50 = lean_st_ref_set(x_5, x_49, x_30);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_55 = lean_ctor_get(x_18, 0);
x_56 = lean_ctor_get(x_18, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_18);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_FileMap_toPosition(x_10, x_57);
lean_inc(x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_12);
lean_ctor_set(x_60, 1, x_13);
x_61 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_62 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_63 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_63, 0, x_9);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_63, sizeof(void*)*5 + 1, x_8);
x_64 = lean_st_ref_take(x_5, x_56);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 6);
lean_inc(x_73);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 x_74 = x_65;
} else {
 lean_dec_ref(x_65);
 x_74 = lean_box(0);
}
x_75 = l_Lean_PersistentArray_push___rarg(x_72, x_63);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 7, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_68);
lean_ctor_set(x_76, 2, x_69);
lean_ctor_set(x_76, 3, x_70);
lean_ctor_set(x_76, 4, x_71);
lean_ctor_set(x_76, 5, x_75);
lean_ctor_set(x_76, 6, x_73);
x_77 = lean_st_ref_set(x_5, x_76, x_66);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_17);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_17, 0);
x_84 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_89 = l_Lean_FileMap_toPosition(x_10, x_88);
x_90 = l_Lean_FileMap_toPosition(x_10, x_83);
lean_dec(x_83);
lean_ctor_set(x_17, 0, x_90);
lean_ctor_set(x_84, 1, x_13);
lean_ctor_set(x_84, 0, x_12);
x_91 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_86);
x_92 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_93 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_93, 0, x_9);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 2, x_17);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_93, 4, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_93, sizeof(void*)*5 + 1, x_8);
x_94 = lean_st_ref_take(x_5, x_87);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_95, 5);
x_99 = l_Lean_PersistentArray_push___rarg(x_98, x_93);
lean_ctor_set(x_95, 5, x_99);
x_100 = lean_st_ref_set(x_5, x_95, x_96);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = lean_ctor_get(x_95, 0);
x_108 = lean_ctor_get(x_95, 1);
x_109 = lean_ctor_get(x_95, 2);
x_110 = lean_ctor_get(x_95, 3);
x_111 = lean_ctor_get(x_95, 4);
x_112 = lean_ctor_get(x_95, 5);
x_113 = lean_ctor_get(x_95, 6);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_95);
x_114 = l_Lean_PersistentArray_push___rarg(x_112, x_93);
x_115 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_108);
lean_ctor_set(x_115, 2, x_109);
lean_ctor_set(x_115, 3, x_110);
lean_ctor_set(x_115, 4, x_111);
lean_ctor_set(x_115, 5, x_114);
lean_ctor_set(x_115, 6, x_113);
x_116 = lean_st_ref_set(x_5, x_115, x_96);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_121 = lean_ctor_get(x_84, 0);
x_122 = lean_ctor_get(x_84, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_84);
x_123 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_124 = l_Lean_FileMap_toPosition(x_10, x_123);
x_125 = l_Lean_FileMap_toPosition(x_10, x_83);
lean_dec(x_83);
lean_ctor_set(x_17, 0, x_125);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_12);
lean_ctor_set(x_126, 1, x_13);
x_127 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_121);
x_128 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_129 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_129, 0, x_9);
lean_ctor_set(x_129, 1, x_124);
lean_ctor_set(x_129, 2, x_17);
lean_ctor_set(x_129, 3, x_128);
lean_ctor_set(x_129, 4, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_129, sizeof(void*)*5 + 1, x_8);
x_130 = lean_st_ref_take(x_5, x_122);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_131, 6);
lean_inc(x_139);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 lean_ctor_release(x_131, 6);
 x_140 = x_131;
} else {
 lean_dec_ref(x_131);
 x_140 = lean_box(0);
}
x_141 = l_Lean_PersistentArray_push___rarg(x_138, x_129);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 7, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_133);
lean_ctor_set(x_142, 1, x_134);
lean_ctor_set(x_142, 2, x_135);
lean_ctor_set(x_142, 3, x_136);
lean_ctor_set(x_142, 4, x_137);
lean_ctor_set(x_142, 5, x_141);
lean_ctor_set(x_142, 6, x_139);
x_143 = lean_st_ref_set(x_5, x_142, x_132);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_148 = lean_ctor_get(x_17, 0);
lean_inc(x_148);
lean_dec(x_17);
x_149 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_154 = l_Lean_FileMap_toPosition(x_10, x_153);
x_155 = l_Lean_FileMap_toPosition(x_10, x_148);
lean_dec(x_148);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_12);
lean_ctor_set(x_157, 1, x_13);
x_158 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_160 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_160, 0, x_9);
lean_ctor_set(x_160, 1, x_154);
lean_ctor_set(x_160, 2, x_156);
lean_ctor_set(x_160, 3, x_159);
lean_ctor_set(x_160, 4, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_160, sizeof(void*)*5 + 1, x_8);
x_161 = lean_st_ref_take(x_5, x_151);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 6);
lean_inc(x_170);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 lean_ctor_release(x_162, 5);
 lean_ctor_release(x_162, 6);
 x_171 = x_162;
} else {
 lean_dec_ref(x_162);
 x_171 = lean_box(0);
}
x_172 = l_Lean_PersistentArray_push___rarg(x_169, x_160);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 7, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_164);
lean_ctor_set(x_173, 1, x_165);
lean_ctor_set(x_173, 2, x_166);
lean_ctor_set(x_173, 3, x_167);
lean_ctor_set(x_173, 4, x_168);
lean_ctor_set(x_173, 5, x_172);
lean_ctor_set(x_173, 6, x_170);
x_174 = lean_st_ref_set(x_5, x_173, x_163);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
x_177 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
return x_178;
}
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_16);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_16, 0);
x_181 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_183 = lean_ctor_get(x_181, 0);
x_184 = lean_ctor_get(x_181, 1);
x_185 = l_Lean_FileMap_toPosition(x_10, x_180);
lean_dec(x_180);
lean_inc(x_185);
lean_ctor_set(x_16, 0, x_185);
lean_ctor_set(x_181, 1, x_13);
lean_ctor_set(x_181, 0, x_12);
x_186 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_183);
x_187 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_188 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_188, 0, x_9);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_16);
lean_ctor_set(x_188, 3, x_187);
lean_ctor_set(x_188, 4, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_188, sizeof(void*)*5 + 1, x_8);
x_189 = lean_st_ref_take(x_5, x_184);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = !lean_is_exclusive(x_190);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_193 = lean_ctor_get(x_190, 5);
x_194 = l_Lean_PersistentArray_push___rarg(x_193, x_188);
lean_ctor_set(x_190, 5, x_194);
x_195 = lean_st_ref_set(x_5, x_190, x_191);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_195, 0);
lean_dec(x_197);
x_198 = lean_box(0);
lean_ctor_set(x_195, 0, x_198);
return x_195;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
lean_dec(x_195);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_202 = lean_ctor_get(x_190, 0);
x_203 = lean_ctor_get(x_190, 1);
x_204 = lean_ctor_get(x_190, 2);
x_205 = lean_ctor_get(x_190, 3);
x_206 = lean_ctor_get(x_190, 4);
x_207 = lean_ctor_get(x_190, 5);
x_208 = lean_ctor_get(x_190, 6);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_190);
x_209 = l_Lean_PersistentArray_push___rarg(x_207, x_188);
x_210 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_210, 0, x_202);
lean_ctor_set(x_210, 1, x_203);
lean_ctor_set(x_210, 2, x_204);
lean_ctor_set(x_210, 3, x_205);
lean_ctor_set(x_210, 4, x_206);
lean_ctor_set(x_210, 5, x_209);
lean_ctor_set(x_210, 6, x_208);
x_211 = lean_st_ref_set(x_5, x_210, x_191);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = lean_box(0);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_216 = lean_ctor_get(x_181, 0);
x_217 = lean_ctor_get(x_181, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_181);
x_218 = l_Lean_FileMap_toPosition(x_10, x_180);
lean_dec(x_180);
lean_inc(x_218);
lean_ctor_set(x_16, 0, x_218);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_12);
lean_ctor_set(x_219, 1, x_13);
x_220 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_216);
x_221 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_222 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_222, 0, x_9);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_16);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_222, 4, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_222, sizeof(void*)*5 + 1, x_8);
x_223 = lean_st_ref_take(x_5, x_217);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 3);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 4);
lean_inc(x_230);
x_231 = lean_ctor_get(x_224, 5);
lean_inc(x_231);
x_232 = lean_ctor_get(x_224, 6);
lean_inc(x_232);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 lean_ctor_release(x_224, 3);
 lean_ctor_release(x_224, 4);
 lean_ctor_release(x_224, 5);
 lean_ctor_release(x_224, 6);
 x_233 = x_224;
} else {
 lean_dec_ref(x_224);
 x_233 = lean_box(0);
}
x_234 = l_Lean_PersistentArray_push___rarg(x_231, x_222);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 7, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_226);
lean_ctor_set(x_235, 1, x_227);
lean_ctor_set(x_235, 2, x_228);
lean_ctor_set(x_235, 3, x_229);
lean_ctor_set(x_235, 4, x_230);
lean_ctor_set(x_235, 5, x_234);
lean_ctor_set(x_235, 6, x_232);
x_236 = lean_st_ref_set(x_5, x_235, x_225);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
x_239 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_241 = lean_ctor_get(x_16, 0);
lean_inc(x_241);
lean_dec(x_16);
x_242 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_246 = l_Lean_FileMap_toPosition(x_10, x_241);
lean_dec(x_241);
lean_inc(x_246);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
if (lean_is_scalar(x_245)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_245;
}
lean_ctor_set(x_248, 0, x_12);
lean_ctor_set(x_248, 1, x_13);
x_249 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_243);
x_250 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_251 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_251, 0, x_9);
lean_ctor_set(x_251, 1, x_246);
lean_ctor_set(x_251, 2, x_247);
lean_ctor_set(x_251, 3, x_250);
lean_ctor_set(x_251, 4, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_251, sizeof(void*)*5 + 1, x_8);
x_252 = lean_st_ref_take(x_5, x_244);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 2);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 3);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 4);
lean_inc(x_259);
x_260 = lean_ctor_get(x_253, 5);
lean_inc(x_260);
x_261 = lean_ctor_get(x_253, 6);
lean_inc(x_261);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 lean_ctor_release(x_253, 5);
 lean_ctor_release(x_253, 6);
 x_262 = x_253;
} else {
 lean_dec_ref(x_253);
 x_262 = lean_box(0);
}
x_263 = l_Lean_PersistentArray_push___rarg(x_260, x_251);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 7, 0);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_255);
lean_ctor_set(x_264, 1, x_256);
lean_ctor_set(x_264, 2, x_257);
lean_ctor_set(x_264, 3, x_258);
lean_ctor_set(x_264, 4, x_259);
lean_ctor_set(x_264, 5, x_263);
lean_ctor_set(x_264, 6, x_261);
x_265 = lean_st_ref_set(x_5, x_264, x_254);
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
x_268 = lean_box(0);
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
}
else
{
lean_object* x_270; uint8_t x_271; 
x_270 = lean_ctor_get(x_16, 0);
lean_inc(x_270);
lean_dec(x_16);
x_271 = !lean_is_exclusive(x_17);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_272 = lean_ctor_get(x_17, 0);
x_273 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_275 = lean_ctor_get(x_273, 0);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_10);
x_277 = l_Lean_FileMap_toPosition(x_10, x_270);
lean_dec(x_270);
x_278 = l_Lean_FileMap_toPosition(x_10, x_272);
lean_dec(x_272);
lean_ctor_set(x_17, 0, x_278);
lean_ctor_set(x_273, 1, x_13);
lean_ctor_set(x_273, 0, x_12);
x_279 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_279, 0, x_273);
lean_ctor_set(x_279, 1, x_275);
x_280 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_281 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_281, 0, x_9);
lean_ctor_set(x_281, 1, x_277);
lean_ctor_set(x_281, 2, x_17);
lean_ctor_set(x_281, 3, x_280);
lean_ctor_set(x_281, 4, x_279);
lean_ctor_set_uint8(x_281, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_281, sizeof(void*)*5 + 1, x_8);
x_282 = lean_st_ref_take(x_5, x_276);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = !lean_is_exclusive(x_283);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_286 = lean_ctor_get(x_283, 5);
x_287 = l_Lean_PersistentArray_push___rarg(x_286, x_281);
lean_ctor_set(x_283, 5, x_287);
x_288 = lean_st_ref_set(x_5, x_283, x_284);
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_288, 0);
lean_dec(x_290);
x_291 = lean_box(0);
lean_ctor_set(x_288, 0, x_291);
return x_288;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
lean_dec(x_288);
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_295 = lean_ctor_get(x_283, 0);
x_296 = lean_ctor_get(x_283, 1);
x_297 = lean_ctor_get(x_283, 2);
x_298 = lean_ctor_get(x_283, 3);
x_299 = lean_ctor_get(x_283, 4);
x_300 = lean_ctor_get(x_283, 5);
x_301 = lean_ctor_get(x_283, 6);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_283);
x_302 = l_Lean_PersistentArray_push___rarg(x_300, x_281);
x_303 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_303, 0, x_295);
lean_ctor_set(x_303, 1, x_296);
lean_ctor_set(x_303, 2, x_297);
lean_ctor_set(x_303, 3, x_298);
lean_ctor_set(x_303, 4, x_299);
lean_ctor_set(x_303, 5, x_302);
lean_ctor_set(x_303, 6, x_301);
x_304 = lean_st_ref_set(x_5, x_303, x_284);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_306 = x_304;
} else {
 lean_dec_ref(x_304);
 x_306 = lean_box(0);
}
x_307 = lean_box(0);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_309 = lean_ctor_get(x_273, 0);
x_310 = lean_ctor_get(x_273, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_273);
lean_inc(x_10);
x_311 = l_Lean_FileMap_toPosition(x_10, x_270);
lean_dec(x_270);
x_312 = l_Lean_FileMap_toPosition(x_10, x_272);
lean_dec(x_272);
lean_ctor_set(x_17, 0, x_312);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_12);
lean_ctor_set(x_313, 1, x_13);
x_314 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_309);
x_315 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_316 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_316, 0, x_9);
lean_ctor_set(x_316, 1, x_311);
lean_ctor_set(x_316, 2, x_17);
lean_ctor_set(x_316, 3, x_315);
lean_ctor_set(x_316, 4, x_314);
lean_ctor_set_uint8(x_316, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_316, sizeof(void*)*5 + 1, x_8);
x_317 = lean_st_ref_take(x_5, x_310);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_ctor_get(x_318, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_318, 2);
lean_inc(x_322);
x_323 = lean_ctor_get(x_318, 3);
lean_inc(x_323);
x_324 = lean_ctor_get(x_318, 4);
lean_inc(x_324);
x_325 = lean_ctor_get(x_318, 5);
lean_inc(x_325);
x_326 = lean_ctor_get(x_318, 6);
lean_inc(x_326);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 lean_ctor_release(x_318, 2);
 lean_ctor_release(x_318, 3);
 lean_ctor_release(x_318, 4);
 lean_ctor_release(x_318, 5);
 lean_ctor_release(x_318, 6);
 x_327 = x_318;
} else {
 lean_dec_ref(x_318);
 x_327 = lean_box(0);
}
x_328 = l_Lean_PersistentArray_push___rarg(x_325, x_316);
if (lean_is_scalar(x_327)) {
 x_329 = lean_alloc_ctor(0, 7, 0);
} else {
 x_329 = x_327;
}
lean_ctor_set(x_329, 0, x_320);
lean_ctor_set(x_329, 1, x_321);
lean_ctor_set(x_329, 2, x_322);
lean_ctor_set(x_329, 3, x_323);
lean_ctor_set(x_329, 4, x_324);
lean_ctor_set(x_329, 5, x_328);
lean_ctor_set(x_329, 6, x_326);
x_330 = lean_st_ref_set(x_5, x_329, x_319);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
x_333 = lean_box(0);
if (lean_is_scalar(x_332)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_332;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_331);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_335 = lean_ctor_get(x_17, 0);
lean_inc(x_335);
lean_dec(x_17);
x_336 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_4, x_5, x_6);
lean_dec(x_4);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
lean_inc(x_10);
x_340 = l_Lean_FileMap_toPosition(x_10, x_270);
lean_dec(x_270);
x_341 = l_Lean_FileMap_toPosition(x_10, x_335);
lean_dec(x_335);
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_341);
if (lean_is_scalar(x_339)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_339;
}
lean_ctor_set(x_343, 0, x_12);
lean_ctor_set(x_343, 1, x_13);
x_344 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_337);
x_345 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1;
x_346 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_346, 0, x_9);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set(x_346, 2, x_342);
lean_ctor_set(x_346, 3, x_345);
lean_ctor_set(x_346, 4, x_344);
lean_ctor_set_uint8(x_346, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_346, sizeof(void*)*5 + 1, x_8);
x_347 = lean_st_ref_take(x_5, x_338);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_348, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_348, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_348, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_348, 5);
lean_inc(x_355);
x_356 = lean_ctor_get(x_348, 6);
lean_inc(x_356);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 lean_ctor_release(x_348, 4);
 lean_ctor_release(x_348, 5);
 lean_ctor_release(x_348, 6);
 x_357 = x_348;
} else {
 lean_dec_ref(x_348);
 x_357 = lean_box(0);
}
x_358 = l_Lean_PersistentArray_push___rarg(x_355, x_346);
if (lean_is_scalar(x_357)) {
 x_359 = lean_alloc_ctor(0, 7, 0);
} else {
 x_359 = x_357;
}
lean_ctor_set(x_359, 0, x_350);
lean_ctor_set(x_359, 1, x_351);
lean_ctor_set(x_359, 2, x_352);
lean_ctor_set(x_359, 3, x_353);
lean_ctor_set(x_359, 4, x_354);
lean_ctor_set(x_359, 5, x_358);
lean_ctor_set(x_359, 6, x_356);
x_360 = lean_st_ref_set(x_5, x_359, x_349);
x_361 = lean_ctor_get(x_360, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_362 = x_360;
} else {
 lean_dec_ref(x_360);
 x_362 = lean_box(0);
}
x_363 = lean_box(0);
if (lean_is_scalar(x_362)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_362;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_361);
return x_364;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_reportOutOfHeartbeats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_reportOutOfHeartbeats___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` stopped because it was running out of time.\nYou may get better results using `set_option maxHeartbeats 0`.", 108);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_heartbeatsPercent(x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_nat_dec_le(x_3, x_9);
lean_dec(x_9);
lean_dec(x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_free_object(x_7);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_1, x_13);
x_15 = l_Lean_reportOutOfHeartbeats___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_reportOutOfHeartbeats___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = 0;
x_22 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1(x_2, x_20, x_21, x_4, x_5, x_10);
lean_dec(x_2);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_nat_dec_le(x_3, x_23);
lean_dec(x_23);
lean_dec(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_28 = 1;
x_29 = l_Lean_Name_toString(x_1, x_28);
x_30 = l_Lean_reportOutOfHeartbeats___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_reportOutOfHeartbeats___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = 0;
x_37 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1(x_2, x_35, x_36, x_4, x_5, x_24);
lean_dec(x_2);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_reportOutOfHeartbeats(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Heartbeats(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_withHeartbeats___rarg___closed__1 = _init_l_Lean_withHeartbeats___rarg___closed__1();
lean_mark_persistent(l_Lean_withHeartbeats___rarg___closed__1);
l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1 = _init_l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__1);
l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__2 = _init_l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__2();
lean_mark_persistent(l_Lean_logAt___at_Lean_reportOutOfHeartbeats___spec__1___closed__2);
l_Lean_reportOutOfHeartbeats___closed__1 = _init_l_Lean_reportOutOfHeartbeats___closed__1();
lean_mark_persistent(l_Lean_reportOutOfHeartbeats___closed__1);
l_Lean_reportOutOfHeartbeats___closed__2 = _init_l_Lean_reportOutOfHeartbeats___closed__2();
lean_mark_persistent(l_Lean_reportOutOfHeartbeats___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
