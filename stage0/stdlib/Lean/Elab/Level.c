// Lean compiler output
// Module: Lean.Elab.Level
// Imports: Init Lean.Meta.LevelDefEq Lean.Elab.Exception Lean.Elab.Log
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
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__2;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__10;
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___closed__5;
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_MetavarContext_MkBinding_Lean_MetavarContext___instance__7___closed__1;
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__9;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__11;
lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Tactics___hyg_720____closed__3;
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__3;
lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___closed__3;
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___closed__12;
lean_object* l_Lean_Elab_Level_elabLevel_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__1(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__5;
lean_object* l_Lean_Elab_Level_elabLevel_match__2(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3;
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__8;
lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
extern lean_object* l_Lean_identKind;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__2;
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_37____closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___closed__14;
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__3;
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__4;
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__13;
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_2);
x_8 = lean_apply_2(x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_2(x_3, x_10, x_5);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__1;
x_2 = l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__3;
x_2 = l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__5;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_Lean_Elab_Level___instance__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_Lean_Elab_Level___instance__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MetavarContext_MkBinding_Lean_MetavarContext___instance__7___closed__1;
x_2 = l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_Lean_Elab_Level___instance__1___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__2;
x_2 = l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_Lean_Elab_Level___instance__3___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_name_mk_numeral(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_name_mk_numeral(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
lean_inc(x_21);
lean_inc(x_20);
x_23 = lean_name_mk_numeral(x_20, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_21, x_24);
lean_dec(x_21);
if (lean_is_scalar(x_22)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_22;
}
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_9 = l_Lean_MetavarContext_addLevelMVarDecl(x_8, x_7);
lean_ctor_set(x_5, 1, x_9);
x_10 = l_Lean_mkLevelMVar(x_7);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
lean_inc(x_11);
x_14 = l_Lean_MetavarContext_addLevelMVarDecl(x_13, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_mkLevelMVar(x_11);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
lean_inc(x_18);
x_22 = l_Lean_MetavarContext_addLevelMVarDecl(x_20, x_18);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_mkLevelMVar(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Level_mkFreshLevelMVar(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_3 < x_2;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_array_uget(x_9, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkLevelIMax(x_4, x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_3 < x_2;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_array_uget(x_9, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkLevelMax(x_4, x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkLevelParam(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_37____closed__4;
x_2 = l_Lean_Elab_Level_elabLevel___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = l_myMacro____x40_Init_Tactics___hyg_720____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = l_Lean_Level_LevelToFormat_Result_format___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = l_Lean_Level_LevelToFormat_Result_format___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = l_Lean_mkHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = l_Lean_Elab_Level_elabLevel___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected universe level syntax kind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe level ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_elabLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Elab_Level_elabLevel___closed__3;
x_6 = lean_name_eq(x_4, x_5);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_inc(x_9);
lean_ctor_set(x_2, 0, x_10);
if (x_6 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Level_elabLevel___closed__4;
x_12 = lean_name_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Level_elabLevel___closed__5;
x_14 = lean_name_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Level_elabLevel___closed__6;
x_16 = lean_name_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_numLitKind;
x_18 = lean_name_eq(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_identKind;
x_20 = lean_name_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_9);
x_21 = l_Lean_Elab_Level_elabLevel___closed__8;
x_22 = lean_name_eq(x_4, x_21);
lean_dec(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_Elab_Level_elabLevel___closed__11;
x_24 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(x_23, x_2, x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_inc(x_2);
x_27 = l_Lean_Elab_Level_elabLevel(x_26, x_2, x_3);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
lean_dec(x_1);
x_33 = l_Lean_Syntax_isNatLitAux(x_17, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_free_object(x_27);
lean_dec(x_29);
x_34 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_30);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Level_addOffsetAux(x_35, x_29);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
lean_dec(x_1);
x_41 = l_Lean_Syntax_isNatLitAux(x_17, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec(x_37);
x_42 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_38);
lean_dec(x_2);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Level_addOffsetAux(x_43, x_37);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_4);
x_50 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_51 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_50, x_9);
lean_dec(x_9);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = l_Lean_Elab_Level_elabLevel___closed__14;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(x_54, x_2, x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_box(0);
x_61 = l_Lean_Elab_Level_elabLevel___lambda__1(x_50, x_60, x_2, x_3);
lean_dec(x_2);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_9);
lean_dec(x_4);
x_62 = l_Lean_Syntax_isNatLitAux(x_17, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_3);
lean_dec(x_2);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Level_ofNat(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_67 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec(x_2);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_9);
lean_dec(x_4);
x_68 = lean_unsigned_to_nat(1u);
x_69 = l_Lean_Syntax_getArg(x_1, x_68);
lean_dec(x_1);
x_70 = l_Lean_Syntax_getArgs(x_69);
lean_dec(x_69);
x_71 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_70);
lean_inc(x_2);
x_72 = l_Lean_Elab_Level_elabLevel(x_71, x_2, x_3);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; lean_object* x_81; size_t x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_sub(x_75, x_68);
lean_dec(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Array_toSubarray___rarg(x_70, x_77, x_76);
x_79 = lean_ctor_get(x_78, 2);
lean_inc(x_79);
x_80 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
x_82 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_83 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__3(x_78, x_80, x_82, x_73, x_2, x_74);
lean_dec(x_78);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_70);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_72);
if (x_92 == 0)
{
return x_72;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_72, 0);
x_94 = lean_ctor_get(x_72, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_72);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_9);
lean_dec(x_4);
x_96 = lean_unsigned_to_nat(1u);
x_97 = l_Lean_Syntax_getArg(x_1, x_96);
lean_dec(x_1);
x_98 = l_Lean_Syntax_getArgs(x_97);
lean_dec(x_97);
x_99 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_98);
lean_inc(x_2);
x_100 = l_Lean_Elab_Level_elabLevel(x_99, x_2, x_3);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; lean_object* x_109; size_t x_110; lean_object* x_111; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_array_get_size(x_98);
x_104 = lean_nat_sub(x_103, x_96);
lean_dec(x_103);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Array_toSubarray___rarg(x_98, x_105, x_104);
x_107 = lean_ctor_get(x_106, 2);
lean_inc(x_107);
x_108 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_111 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(x_106, x_108, x_110, x_101, x_2, x_102);
lean_dec(x_106);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_111);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_111);
if (x_116 == 0)
{
return x_111;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_111, 0);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_111);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_98);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_100);
if (x_120 == 0)
{
return x_100;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_100, 0);
x_122 = lean_ctor_get(x_100, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_100);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_9);
lean_dec(x_4);
x_124 = lean_unsigned_to_nat(1u);
x_125 = l_Lean_Syntax_getArg(x_1, x_124);
lean_dec(x_1);
x_1 = x_125;
goto _start;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_2, 0);
x_128 = lean_ctor_get(x_2, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_2);
x_129 = l_Lean_replaceRef(x_1, x_127);
lean_dec(x_127);
lean_inc(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
if (x_6 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Elab_Level_elabLevel___closed__4;
x_132 = lean_name_eq(x_4, x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = l_Lean_Elab_Level_elabLevel___closed__5;
x_134 = lean_name_eq(x_4, x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = l_Lean_Elab_Level_elabLevel___closed__6;
x_136 = lean_name_eq(x_4, x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_Lean_numLitKind;
x_138 = lean_name_eq(x_4, x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = l_Lean_identKind;
x_140 = lean_name_eq(x_4, x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
lean_dec(x_128);
x_141 = l_Lean_Elab_Level_elabLevel___closed__8;
x_142 = lean_name_eq(x_4, x_141);
lean_dec(x_4);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_1);
x_143 = l_Lean_Elab_Level_elabLevel___closed__11;
x_144 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(x_143, x_130, x_3);
lean_dec(x_130);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Syntax_getArg(x_1, x_145);
lean_inc(x_130);
x_147 = l_Lean_Elab_Level_elabLevel(x_146, x_130, x_3);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_unsigned_to_nat(2u);
x_152 = l_Lean_Syntax_getArg(x_1, x_151);
lean_dec(x_1);
x_153 = l_Lean_Syntax_isNatLitAux(x_137, x_152);
lean_dec(x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_148);
x_154 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_130, x_149);
lean_dec(x_130);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_130);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Level_addOffsetAux(x_155, x_148);
if (lean_is_scalar(x_150)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_150;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_130);
lean_dec(x_1);
x_158 = lean_ctor_get(x_147, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_147, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_160 = x_147;
} else {
 lean_dec_ref(x_147);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; 
lean_dec(x_4);
x_162 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_163 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_162, x_128);
lean_dec(x_128);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_164, 0, x_162);
x_165 = l_Lean_Elab_Level_elabLevel___closed__14;
x_166 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(x_166, x_130, x_3);
lean_dec(x_130);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_box(0);
x_173 = l_Lean_Elab_Level_elabLevel___lambda__1(x_162, x_172, x_130, x_3);
lean_dec(x_130);
return x_173;
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_128);
lean_dec(x_4);
x_174 = l_Lean_Syntax_isNatLitAux(x_137, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_130, x_3);
lean_dec(x_130);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_130);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l_Lean_Level_ofNat(x_176);
lean_dec(x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_3);
return x_178;
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_128);
lean_dec(x_4);
lean_dec(x_1);
x_179 = l_Lean_Elab_Level_mkFreshLevelMVar(x_130, x_3);
lean_dec(x_130);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_128);
lean_dec(x_4);
x_180 = lean_unsigned_to_nat(1u);
x_181 = l_Lean_Syntax_getArg(x_1, x_180);
lean_dec(x_1);
x_182 = l_Lean_Syntax_getArgs(x_181);
lean_dec(x_181);
x_183 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_182);
lean_inc(x_130);
x_184 = l_Lean_Elab_Level_elabLevel(x_183, x_130, x_3);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; size_t x_192; lean_object* x_193; size_t x_194; lean_object* x_195; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_array_get_size(x_182);
x_188 = lean_nat_sub(x_187, x_180);
lean_dec(x_187);
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_toSubarray___rarg(x_182, x_189, x_188);
x_191 = lean_ctor_get(x_190, 2);
lean_inc(x_191);
x_192 = lean_usize_of_nat(x_191);
lean_dec(x_191);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
x_194 = lean_usize_of_nat(x_193);
lean_dec(x_193);
x_195 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__3(x_190, x_192, x_194, x_185, x_130, x_186);
lean_dec(x_190);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_195, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_182);
lean_dec(x_130);
x_204 = lean_ctor_get(x_184, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_184, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_206 = x_184;
} else {
 lean_dec_ref(x_184);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_128);
lean_dec(x_4);
x_208 = lean_unsigned_to_nat(1u);
x_209 = l_Lean_Syntax_getArg(x_1, x_208);
lean_dec(x_1);
x_210 = l_Lean_Syntax_getArgs(x_209);
lean_dec(x_209);
x_211 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_210);
lean_inc(x_130);
x_212 = l_Lean_Elab_Level_elabLevel(x_211, x_130, x_3);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; size_t x_220; lean_object* x_221; size_t x_222; lean_object* x_223; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_array_get_size(x_210);
x_216 = lean_nat_sub(x_215, x_208);
lean_dec(x_215);
x_217 = lean_unsigned_to_nat(0u);
x_218 = l_Array_toSubarray___rarg(x_210, x_217, x_216);
x_219 = lean_ctor_get(x_218, 2);
lean_inc(x_219);
x_220 = lean_usize_of_nat(x_219);
lean_dec(x_219);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
x_222 = lean_usize_of_nat(x_221);
lean_dec(x_221);
x_223 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(x_218, x_220, x_222, x_213, x_130, x_214);
lean_dec(x_218);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_230 = x_223;
} else {
 lean_dec_ref(x_223);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_210);
lean_dec(x_130);
x_232 = lean_ctor_get(x_212, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_212, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_234 = x_212;
} else {
 lean_dec_ref(x_212);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_128);
lean_dec(x_4);
x_236 = lean_unsigned_to_nat(1u);
x_237 = l_Lean_Syntax_getArg(x_1, x_236);
lean_dec(x_1);
x_1 = x_237;
x_2 = x_130;
goto _start;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__3(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Level_elabLevel___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Level(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__1 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__1);
l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__2 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__2);
l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__3 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__3);
l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__4 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__4);
l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__5 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__1___closed__5);
l_Lean_Elab_Level_Lean_Elab_Level___instance__1 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__1();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__1);
l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__1 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__1);
l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__2 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__2);
l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__3 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__3);
l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__4 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__3___closed__4);
l_Lean_Elab_Level_Lean_Elab_Level___instance__3 = _init_l_Lean_Elab_Level_Lean_Elab_Level___instance__3();
lean_mark_persistent(l_Lean_Elab_Level_Lean_Elab_Level___instance__3);
l_Lean_Elab_Level_elabLevel___closed__1 = _init_l_Lean_Elab_Level_elabLevel___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__1);
l_Lean_Elab_Level_elabLevel___closed__2 = _init_l_Lean_Elab_Level_elabLevel___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__2);
l_Lean_Elab_Level_elabLevel___closed__3 = _init_l_Lean_Elab_Level_elabLevel___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__3);
l_Lean_Elab_Level_elabLevel___closed__4 = _init_l_Lean_Elab_Level_elabLevel___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__4);
l_Lean_Elab_Level_elabLevel___closed__5 = _init_l_Lean_Elab_Level_elabLevel___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__5);
l_Lean_Elab_Level_elabLevel___closed__6 = _init_l_Lean_Elab_Level_elabLevel___closed__6();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__6);
l_Lean_Elab_Level_elabLevel___closed__7 = _init_l_Lean_Elab_Level_elabLevel___closed__7();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__7);
l_Lean_Elab_Level_elabLevel___closed__8 = _init_l_Lean_Elab_Level_elabLevel___closed__8();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__8);
l_Lean_Elab_Level_elabLevel___closed__9 = _init_l_Lean_Elab_Level_elabLevel___closed__9();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__9);
l_Lean_Elab_Level_elabLevel___closed__10 = _init_l_Lean_Elab_Level_elabLevel___closed__10();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__10);
l_Lean_Elab_Level_elabLevel___closed__11 = _init_l_Lean_Elab_Level_elabLevel___closed__11();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__11);
l_Lean_Elab_Level_elabLevel___closed__12 = _init_l_Lean_Elab_Level_elabLevel___closed__12();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__12);
l_Lean_Elab_Level_elabLevel___closed__13 = _init_l_Lean_Elab_Level_elabLevel___closed__13();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__13);
l_Lean_Elab_Level_elabLevel___closed__14 = _init_l_Lean_Elab_Level_elabLevel___closed__14();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
