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
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(lean_object*);
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0;
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0;
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__2(lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0___boxed), 1, 0);
x_14 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0;
x_15 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__2), 1, 0);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Language_SnapshotTask_map___redArg(x_2, x_13, x_7, x_8, x_17);
x_19 = lean_unbox(x_16);
x_20 = l_Lean_Language_SnapshotTask_map___redArg(x_3, x_14, x_9, x_10, x_19);
x_21 = lean_unbox(x_16);
x_22 = l_Lean_Language_SnapshotTask_map___redArg(x_4, x_15, x_11, x_12, x_21);
x_23 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1;
x_24 = lean_array_push(x_23, x_18);
x_25 = lean_array_push(x_24, x_20);
x_26 = lean_array_push(x_25, x_22);
x_27 = lean_array_push(x_26, x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0() {
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
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
x_6 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Language_SnapshotTask_map___redArg(x_17, x_20, x_18, x_19, x_22);
lean_ctor_set(x_5, 0, x_23);
x_6 = x_5;
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Language_SnapshotTask_map___redArg(x_24, x_27, x_25, x_26, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_6 = x_31;
goto block_14;
}
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(x_4);
x_9 = l_Lean_Language_SnapshotTask_finished___redArg(x_7, x_8);
x_10 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0;
x_11 = lean_array_push(x_10, x_9);
x_12 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_6, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
x_6 = x_17;
goto block_16;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0;
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Language_SnapshotTask_map___redArg(x_20, x_23, x_21, x_22, x_25);
lean_ctor_set(x_5, 0, x_26);
x_6 = x_5;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0;
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
x_34 = l_Lean_Language_SnapshotTask_map___redArg(x_28, x_31, x_29, x_30, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_6 = x_35;
goto block_16;
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Language_SnapshotTask_map___redArg(x_4, x_1, x_7, x_8, x_10);
x_12 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0;
x_13 = lean_array_push(x_12, x_11);
x_14 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_6, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___lam__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_box(0);
x_7 = x_18;
goto block_17;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Language_SnapshotTask_map___redArg(x_21, x_2, x_22, x_23, x_25);
lean_ctor_set(x_6, 0, x_26);
x_7 = x_6;
goto block_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_Language_SnapshotTask_map___redArg(x_28, x_2, x_29, x_30, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_7 = x_34;
goto block_17;
}
}
block_17:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Language_SnapshotTask_map___redArg(x_5, x_1, x_8, x_9, x_11);
x_13 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0;
x_14 = lean_array_push(x_13, x_12);
x_15 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_7, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0;
x_2 = l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lam__3), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Language_SnapshotTask_finished___redArg(x_2, x_1);
return x_3;
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
x_3 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
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
x_8 = lean_alloc_closure((void*)(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed), 1, 0);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Language_SnapshotTask_map___redArg(x_5, x_8, x_6, x_7, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lam__0(x_1);
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
l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot___lam__0___closed__0);
l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandResultSnapshot);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__0);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot___closed__0);
l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__0);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot___closed__0);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot);
l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0 = _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__0);
l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot);
l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0 = _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___closed__0);
l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot);
l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0 = _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0();
lean_mark_persistent(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
