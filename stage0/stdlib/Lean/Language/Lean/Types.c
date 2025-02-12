// Lean compiler output
// Module: Lean.Language.Lean.Types
// Imports: Lean.Language.Basic Lean.Elab.Command
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
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2;
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot(lean_object*);
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(lean_object*);
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1;
lean_object* l_Lean_Language_SnapshotTask_pure___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_push(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_9 = 1;
x_10 = l_Lean_Language_SnapshotTask_map___rarg(x_3, x_8, x_7, x_9);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2;
x_13 = l_Lean_Language_SnapshotTask_map___rarg(x_4, x_12, x_11, x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_mk(x_17);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_19, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_26 = l_Lean_Language_SnapshotTask_map___rarg(x_23, x_25, x_24, x_9);
lean_ctor_set(x_6, 0, x_26);
x_27 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_6, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_32 = l_Lean_Language_SnapshotTask_map___rarg(x_29, x_31, x_30, x_9);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_33, x_18);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_3 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_16 = 1;
x_17 = l_Lean_Language_SnapshotTask_map___rarg(x_13, x_15, x_14, x_16);
lean_ctor_set(x_2, 0, x_17);
x_18 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_19 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_2, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_24 = 1;
x_25 = l_Lean_Language_SnapshotTask_map___rarg(x_21, x_23, x_22, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_28 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_26, x_27);
lean_ctor_set(x_1, 1, x_28);
return x_1;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_31 = x_2;
} else {
 lean_dec_ref(x_2);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_35 = 1;
x_36 = l_Lean_Language_SnapshotTask_map___rarg(x_32, x_34, x_33, x_35);
if (lean_is_scalar(x_31)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_31;
}
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_39 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_37, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_6, x_1);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_9, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_19 = 1;
x_20 = l_Lean_Language_SnapshotTask_map___rarg(x_16, x_18, x_17, x_19);
lean_ctor_set(x_3, 0, x_20);
x_21 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_3, x_1);
lean_ctor_set(x_2, 1, x_21);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_26 = 1;
x_27 = l_Lean_Language_SnapshotTask_map___rarg(x_23, x_25, x_24, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_28, x_1);
lean_ctor_set(x_2, 1, x_29);
return x_2;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_32 = x_3;
} else {
 lean_dec_ref(x_3);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_36 = 1;
x_37 = l_Lean_Language_SnapshotTask_map___rarg(x_33, x_35, x_34, x_36);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_38, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_11 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = 1;
x_14 = l_Lean_Language_SnapshotTask_map___rarg(x_9, x_11, x_12, x_13);
lean_ctor_set(x_2, 0, x_14);
x_15 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_2, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_20 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = 1;
x_23 = l_Lean_Language_SnapshotTask_map___rarg(x_18, x_20, x_21, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_24, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_SnapshotTask_pure___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2;
x_8 = 1;
x_9 = l_Lean_Language_SnapshotTask_map___rarg(x_5, x_7, x_6, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Language_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot);
l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1);
l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1 = _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1);
l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2 = _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
