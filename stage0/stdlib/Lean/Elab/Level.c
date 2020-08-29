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
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__16;
extern lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__7;
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat___main(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__2;
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__6;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__18;
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__15;
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__5;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__14;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__7;
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__1;
lean_object* l_Lean_Level_addOffsetAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__3;
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__2;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__10;
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__9;
lean_object* l_ReaderT_read___at_Lean_Elab_Level_Lean_MonadError___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__17;
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadError;
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
extern lean_object* l_EST_MonadExceptOf___closed__2;
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__4;
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__6;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__13;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__3;
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__3;
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator;
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__5;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__12;
lean_object* l_ReaderT_MonadExceptOf___rarg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__11;
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__1;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__2;
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__8;
lean_object* l_Lean_Elab_Level_elabLevel___main(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_Lean_MonadError___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EST_MonadExceptOf___closed__2;
x_2 = l_ReaderT_MonadExceptOf___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Level_Lean_MonadError___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_MonadError___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_Lean_MonadError___closed__2;
x_2 = l_Lean_Elab_Level_Lean_MonadError___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_MonadError___lambda__2___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_MonadError___lambda__3), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_Lean_MonadError___closed__1;
x_2 = l_Lean_Elab_Level_Lean_MonadError___closed__4;
x_3 = l_Lean_Elab_Level_Lean_MonadError___closed__5;
x_4 = l_Lean_Elab_Level_Lean_MonadError___closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_Lean_MonadError___closed__7;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_Lean_MonadError___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Level_Lean_MonadError___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1;
x_2 = l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__2;
x_2 = l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_Lean_MonadNameGenerator() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__2(x_1, x_2, x_3);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_fget(x_1, x_11);
lean_inc(x_6);
x_13 = l_Lean_Elab_Level_elabLevel___main(x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_mkLevelIMax(x_5, x_15);
x_18 = lean_nat_dec_eq(x_11, x_2);
if (x_18 == 0)
{
lean_free_object(x_13);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_17;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_6);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lean_mkLevelIMax(x_5, x_20);
x_23 = lean_nat_dec_eq(x_11, x_2);
if (x_23 == 0)
{
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_22;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_fget(x_1, x_11);
lean_inc(x_6);
x_13 = l_Lean_Elab_Level_elabLevel___main(x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_mkLevelMax(x_5, x_15);
x_18 = lean_nat_dec_eq(x_11, x_2);
if (x_18 == 0)
{
lean_free_object(x_13);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_17;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_6);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lean_mkLevelMax(x_5, x_20);
x_23 = lean_nat_dec_eq(x_11, x_2);
if (x_23 == 0)
{
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_22;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Elab_Level_elabLevel___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__2;
x_2 = l_Lean_Elab_Level_elabLevel___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__2;
x_2 = l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__2;
x_2 = l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__2;
x_2 = l_Lean_mkHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addLit");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__2;
x_2 = l_Lean_Elab_Level_elabLevel___main___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected universe level syntax kind");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed universe level syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe level ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_elabLevel___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Elab_Level_elabLevel___main___closed__4;
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
x_11 = l_Lean_Elab_Level_elabLevel___main___closed__5;
x_12 = lean_name_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_14 = lean_name_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Level_elabLevel___main___closed__7;
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
x_21 = l_Lean_Elab_Level_elabLevel___main___closed__9;
x_22 = lean_name_eq(x_4, x_21);
lean_dec(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_Elab_Level_elabLevel___main___closed__12;
x_24 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_23, x_2, x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_inc(x_2);
x_27 = l_Lean_Elab_Level_elabLevel___main(x_26, x_2, x_3);
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
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_27);
lean_dec(x_29);
x_34 = l_Lean_Elab_Level_elabLevel___main___closed__15;
x_35 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_34, x_2, x_30);
lean_dec(x_2);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_Level_addOffsetAux___main(x_36, x_29);
lean_ctor_set(x_27, 0, x_37);
return x_27;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_unsigned_to_nat(2u);
x_41 = l_Lean_Syntax_getArg(x_1, x_40);
lean_dec(x_1);
x_42 = l_Lean_Syntax_isNatLitAux(x_17, x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_38);
x_43 = l_Lean_Elab_Level_elabLevel___main___closed__15;
x_44 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_43, x_2, x_39);
lean_dec(x_2);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_Level_addOffsetAux___main(x_45, x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
return x_27;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_27, 0);
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_27);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_4);
x_52 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_53 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_52, x_9);
lean_dec(x_9);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_52);
x_55 = l_Lean_Elab_Level_elabLevel___main___closed__18;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_56, x_2, x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_62 = l_Lean_mkLevelParam(x_52);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_3);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_9);
lean_dec(x_4);
x_64 = l_Lean_Syntax_isNatLitAux(x_17, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_Elab_Level_elabLevel___main___closed__15;
x_66 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_65, x_2, x_3);
lean_dec(x_2);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lean_Level_ofNat___main(x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_3);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_70 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec(x_2);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_9);
lean_dec(x_4);
x_71 = lean_unsigned_to_nat(1u);
x_72 = l_Lean_Syntax_getArg(x_1, x_71);
lean_dec(x_1);
x_73 = l_Lean_Syntax_getArgs(x_72);
lean_dec(x_72);
x_74 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_73);
lean_inc(x_2);
x_75 = l_Lean_Elab_Level_elabLevel___main(x_74, x_2, x_3);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_array_get_size(x_73);
x_79 = lean_nat_sub(x_78, x_71);
x_80 = lean_nat_dec_le(x_79, x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2(x_73, x_81, x_78, lean_box(0), x_76, x_2, x_77);
lean_dec(x_73);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_78);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2(x_73, x_83, x_79, lean_box(0), x_76, x_2, x_77);
lean_dec(x_73);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_73);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_75);
if (x_85 == 0)
{
return x_75;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_75, 0);
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_75);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_9);
lean_dec(x_4);
x_89 = lean_unsigned_to_nat(1u);
x_90 = l_Lean_Syntax_getArg(x_1, x_89);
lean_dec(x_1);
x_91 = l_Lean_Syntax_getArgs(x_90);
lean_dec(x_90);
x_92 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_91);
lean_inc(x_2);
x_93 = l_Lean_Elab_Level_elabLevel___main(x_92, x_2, x_3);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_sub(x_96, x_89);
x_98 = lean_nat_dec_le(x_97, x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_91, x_99, x_96, lean_box(0), x_94, x_2, x_95);
lean_dec(x_91);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_96);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_91, x_101, x_97, lean_box(0), x_94, x_2, x_95);
lean_dec(x_91);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_91);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_93);
if (x_103 == 0)
{
return x_93;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_93, 0);
x_105 = lean_ctor_get(x_93, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_93);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_9);
lean_dec(x_4);
x_107 = lean_unsigned_to_nat(1u);
x_108 = l_Lean_Syntax_getArg(x_1, x_107);
lean_dec(x_1);
x_1 = x_108;
goto _start;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_2, 0);
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_2);
x_112 = l_Lean_replaceRef(x_1, x_110);
lean_dec(x_110);
lean_inc(x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
if (x_6 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = l_Lean_Elab_Level_elabLevel___main___closed__5;
x_115 = lean_name_eq(x_4, x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_117 = lean_name_eq(x_4, x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = l_Lean_Elab_Level_elabLevel___main___closed__7;
x_119 = lean_name_eq(x_4, x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_numLitKind;
x_121 = lean_name_eq(x_4, x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = l_Lean_identKind;
x_123 = lean_name_eq(x_4, x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
lean_dec(x_111);
x_124 = l_Lean_Elab_Level_elabLevel___main___closed__9;
x_125 = lean_name_eq(x_4, x_124);
lean_dec(x_4);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_1);
x_126 = l_Lean_Elab_Level_elabLevel___main___closed__12;
x_127 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_126, x_113, x_3);
lean_dec(x_113);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Lean_Syntax_getArg(x_1, x_128);
lean_inc(x_113);
x_130 = l_Lean_Elab_Level_elabLevel___main(x_129, x_113, x_3);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_unsigned_to_nat(2u);
x_135 = l_Lean_Syntax_getArg(x_1, x_134);
lean_dec(x_1);
x_136 = l_Lean_Syntax_isNatLitAux(x_120, x_135);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_133);
lean_dec(x_131);
x_137 = l_Lean_Elab_Level_elabLevel___main___closed__15;
x_138 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_137, x_113, x_132);
lean_dec(x_113);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_113);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
x_140 = l_Lean_Level_addOffsetAux___main(x_139, x_131);
if (lean_is_scalar(x_133)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_133;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_132);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_113);
lean_dec(x_1);
x_142 = lean_ctor_get(x_130, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_130, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_144 = x_130;
} else {
 lean_dec_ref(x_130);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; uint8_t x_147; 
lean_dec(x_4);
x_146 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_147 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_146, x_111);
lean_dec(x_111);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_148, 0, x_146);
x_149 = l_Lean_Elab_Level_elabLevel___main___closed__18;
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_150, x_113, x_3);
lean_dec(x_113);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_113);
x_156 = l_Lean_mkLevelParam(x_146);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_3);
return x_157;
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_111);
lean_dec(x_4);
x_158 = l_Lean_Syntax_isNatLitAux(x_120, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Lean_Elab_Level_elabLevel___main___closed__15;
x_160 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_159, x_113, x_3);
lean_dec(x_113);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_113);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
lean_dec(x_158);
x_162 = l_Lean_Level_ofNat___main(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_3);
return x_163;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_111);
lean_dec(x_4);
lean_dec(x_1);
x_164 = l_Lean_Elab_Level_mkFreshLevelMVar(x_113, x_3);
lean_dec(x_113);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_111);
lean_dec(x_4);
x_165 = lean_unsigned_to_nat(1u);
x_166 = l_Lean_Syntax_getArg(x_1, x_165);
lean_dec(x_1);
x_167 = l_Lean_Syntax_getArgs(x_166);
lean_dec(x_166);
x_168 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_167);
lean_inc(x_113);
x_169 = l_Lean_Elab_Level_elabLevel___main(x_168, x_113, x_3);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_array_get_size(x_167);
x_173 = lean_nat_sub(x_172, x_165);
x_174 = lean_nat_dec_le(x_173, x_172);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_173);
x_175 = lean_unsigned_to_nat(0u);
x_176 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2(x_167, x_175, x_172, lean_box(0), x_170, x_113, x_171);
lean_dec(x_167);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_172);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2(x_167, x_177, x_173, lean_box(0), x_170, x_113, x_171);
lean_dec(x_167);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_167);
lean_dec(x_113);
x_179 = lean_ctor_get(x_169, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_181 = x_169;
} else {
 lean_dec_ref(x_169);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_111);
lean_dec(x_4);
x_183 = lean_unsigned_to_nat(1u);
x_184 = l_Lean_Syntax_getArg(x_1, x_183);
lean_dec(x_1);
x_185 = l_Lean_Syntax_getArgs(x_184);
lean_dec(x_184);
x_186 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_185);
lean_inc(x_113);
x_187 = l_Lean_Elab_Level_elabLevel___main(x_186, x_113, x_3);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_array_get_size(x_185);
x_191 = lean_nat_sub(x_190, x_183);
x_192 = lean_nat_dec_le(x_191, x_190);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_191);
x_193 = lean_unsigned_to_nat(0u);
x_194 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_185, x_193, x_190, lean_box(0), x_188, x_113, x_189);
lean_dec(x_185);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_190);
x_195 = lean_unsigned_to_nat(0u);
x_196 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_185, x_195, x_191, lean_box(0), x_188, x_113, x_189);
lean_dec(x_185);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_185);
lean_dec(x_113);
x_197 = lean_ctor_get(x_187, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_187, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_199 = x_187;
} else {
 lean_dec_ref(x_187);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_111);
lean_dec(x_4);
x_201 = lean_unsigned_to_nat(1u);
x_202 = l_Lean_Syntax_getArg(x_1, x_201);
lean_dec(x_1);
x_1 = x_202;
x_2 = x_113;
goto _start;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Level_elabLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_elabLevel___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Level(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
l_Lean_Elab_Level_Lean_MonadError___closed__1 = _init_l_Lean_Elab_Level_Lean_MonadError___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError___closed__1);
l_Lean_Elab_Level_Lean_MonadError___closed__2 = _init_l_Lean_Elab_Level_Lean_MonadError___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError___closed__2);
l_Lean_Elab_Level_Lean_MonadError___closed__3 = _init_l_Lean_Elab_Level_Lean_MonadError___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError___closed__3);
l_Lean_Elab_Level_Lean_MonadError___closed__4 = _init_l_Lean_Elab_Level_Lean_MonadError___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError___closed__4);
l_Lean_Elab_Level_Lean_MonadError___closed__5 = _init_l_Lean_Elab_Level_Lean_MonadError___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError___closed__5);
l_Lean_Elab_Level_Lean_MonadError___closed__6 = _init_l_Lean_Elab_Level_Lean_MonadError___closed__6();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError___closed__6);
l_Lean_Elab_Level_Lean_MonadError___closed__7 = _init_l_Lean_Elab_Level_Lean_MonadError___closed__7();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError___closed__7);
l_Lean_Elab_Level_Lean_MonadError = _init_l_Lean_Elab_Level_Lean_MonadError();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadError);
l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__1 = _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__1);
l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__2 = _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__2);
l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__3 = _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__3);
l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__4 = _init_l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__4);
l_Lean_Elab_Level_Lean_MonadNameGenerator = _init_l_Lean_Elab_Level_Lean_MonadNameGenerator();
lean_mark_persistent(l_Lean_Elab_Level_Lean_MonadNameGenerator);
l_Lean_Elab_Level_elabLevel___main___closed__1 = _init_l_Lean_Elab_Level_elabLevel___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__1);
l_Lean_Elab_Level_elabLevel___main___closed__2 = _init_l_Lean_Elab_Level_elabLevel___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__2);
l_Lean_Elab_Level_elabLevel___main___closed__3 = _init_l_Lean_Elab_Level_elabLevel___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__3);
l_Lean_Elab_Level_elabLevel___main___closed__4 = _init_l_Lean_Elab_Level_elabLevel___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__4);
l_Lean_Elab_Level_elabLevel___main___closed__5 = _init_l_Lean_Elab_Level_elabLevel___main___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__5);
l_Lean_Elab_Level_elabLevel___main___closed__6 = _init_l_Lean_Elab_Level_elabLevel___main___closed__6();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__6);
l_Lean_Elab_Level_elabLevel___main___closed__7 = _init_l_Lean_Elab_Level_elabLevel___main___closed__7();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__7);
l_Lean_Elab_Level_elabLevel___main___closed__8 = _init_l_Lean_Elab_Level_elabLevel___main___closed__8();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__8);
l_Lean_Elab_Level_elabLevel___main___closed__9 = _init_l_Lean_Elab_Level_elabLevel___main___closed__9();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__9);
l_Lean_Elab_Level_elabLevel___main___closed__10 = _init_l_Lean_Elab_Level_elabLevel___main___closed__10();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__10);
l_Lean_Elab_Level_elabLevel___main___closed__11 = _init_l_Lean_Elab_Level_elabLevel___main___closed__11();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__11);
l_Lean_Elab_Level_elabLevel___main___closed__12 = _init_l_Lean_Elab_Level_elabLevel___main___closed__12();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__12);
l_Lean_Elab_Level_elabLevel___main___closed__13 = _init_l_Lean_Elab_Level_elabLevel___main___closed__13();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__13);
l_Lean_Elab_Level_elabLevel___main___closed__14 = _init_l_Lean_Elab_Level_elabLevel___main___closed__14();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__14);
l_Lean_Elab_Level_elabLevel___main___closed__15 = _init_l_Lean_Elab_Level_elabLevel___main___closed__15();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__15);
l_Lean_Elab_Level_elabLevel___main___closed__16 = _init_l_Lean_Elab_Level_elabLevel___main___closed__16();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__16);
l_Lean_Elab_Level_elabLevel___main___closed__17 = _init_l_Lean_Elab_Level_elabLevel___main___closed__17();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__17);
l_Lean_Elab_Level_elabLevel___main___closed__18 = _init_l_Lean_Elab_Level_elabLevel___main___closed__18();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___main___closed__18);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
