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
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__1___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1;
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___rarg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__2;
lean_object* l_Lean_Language_SnapshotTask_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(lean_object*);
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1;
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
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__3), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1;
x_10 = 1;
x_11 = l_Lean_Language_SnapshotTask_map___rarg(x_3, x_9, x_7, x_8, x_10);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__2;
x_15 = l_Lean_Language_SnapshotTask_map___rarg(x_4, x_14, x_12, x_13, x_10);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3;
x_19 = l_Lean_Language_SnapshotTask_map___rarg(x_5, x_18, x_16, x_17, x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_mk(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(x_4);
x_8 = l_Lean_Language_SnapshotTask_finished___rarg(x_6, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_12, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_20 = 1;
x_21 = l_Lean_Language_SnapshotTask_map___rarg(x_16, x_19, x_17, x_18, x_20);
lean_ctor_set(x_5, 0, x_21);
x_22 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_5, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_28 = 1;
x_29 = l_Lean_Language_SnapshotTask_map___rarg(x_24, x_27, x_25, x_26, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_30, x_11);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3;
x_8 = 1;
x_9 = l_Lean_Language_SnapshotTask_map___rarg(x_3, x_7, x_5, x_6, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_13, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_22 = l_Lean_Language_SnapshotTask_map___rarg(x_18, x_21, x_19, x_20, x_8);
lean_ctor_set(x_4, 0, x_22);
x_23 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_4, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_30 = l_Lean_Language_SnapshotTask_map___rarg(x_26, x_29, x_27, x_28, x_8);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_31, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Lean_Language_SnapshotTask_map___rarg(x_5, x_1, x_7, x_8, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_array_mk(x_11);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_13, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_22 = l_Lean_Language_SnapshotTask_map___rarg(x_18, x_21, x_19, x_20, x_9);
lean_ctor_set(x_6, 0, x_22);
x_23 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_6, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_30 = l_Lean_Language_SnapshotTask_map___rarg(x_26, x_29, x_27, x_28, x_9);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_31, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3;
x_8 = 1;
x_9 = l_Lean_Language_SnapshotTask_map___rarg(x_3, x_7, x_5, x_6, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_13, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1), 3, 2);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_10);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = l_Lean_Language_SnapshotTask_map___rarg(x_18, x_19, x_20, x_21, x_8);
lean_ctor_set(x_4, 0, x_22);
x_23 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_4, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1), 3, 2);
lean_closure_set(x_27, 0, x_7);
lean_closure_set(x_27, 1, x_10);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = l_Lean_Language_SnapshotTask_map___rarg(x_26, x_27, x_28, x_29, x_8);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___rarg(x_31, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_SnapshotTask_finished___rarg(x_1, x_1);
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
x_2 = lean_ctor_get(x_1, 4);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2;
x_9 = 1;
x_10 = l_Lean_Language_SnapshotTask_map___rarg(x_5, x_8, x_6, x_7, x_9);
return x_10;
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
l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__2 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__2);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__3);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot);
l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1 = _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1);
l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2 = _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
