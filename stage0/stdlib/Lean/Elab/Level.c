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
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
extern lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__7;
lean_object* l_Lean_Elab_Level_Lean_MonadError___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_Lean_MonadError___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_Lean_MonadNameGenerator___closed__3;
lean_object* l_Lean_Elab_Level_Lean_MonadError___closed__3;
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_3, x_1, x_2);
return x_4;
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
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_1 = lean_mk_string("unknown universe level ");
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
lean_object* x_34; 
lean_free_object(x_27);
lean_dec(x_29);
x_34 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(x_2, x_30);
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
x_36 = l_Lean_Level_addOffsetAux___main(x_35, x_29);
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
x_42 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(x_2, x_38);
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
x_44 = l_Lean_Level_addOffsetAux___main(x_43, x_37);
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
x_51 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_50, x_9);
lean_dec(x_9);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = l_Lean_Elab_Level_elabLevel___main___closed__15;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_54, x_2, x_3);
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
lean_dec(x_2);
x_60 = l_Lean_mkLevelParam(x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
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
x_63 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(x_2, x_3);
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
x_65 = l_Lean_Level_ofNat___main(x_64);
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
x_72 = l_Lean_Elab_Level_elabLevel___main(x_71, x_2, x_3);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_sub(x_75, x_68);
x_77 = lean_nat_dec_le(x_76, x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_70, x_78, x_75, lean_box(0), x_73, x_2, x_74);
lean_dec(x_70);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_75);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_70, x_80, x_76, lean_box(0), x_73, x_2, x_74);
lean_dec(x_70);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_70);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_72);
if (x_82 == 0)
{
return x_72;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_72, 0);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_72);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_9);
lean_dec(x_4);
x_86 = lean_unsigned_to_nat(1u);
x_87 = l_Lean_Syntax_getArg(x_1, x_86);
lean_dec(x_1);
x_88 = l_Lean_Syntax_getArgs(x_87);
lean_dec(x_87);
x_89 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_88);
lean_inc(x_2);
x_90 = l_Lean_Elab_Level_elabLevel___main(x_89, x_2, x_3);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_array_get_size(x_88);
x_94 = lean_nat_sub(x_93, x_86);
x_95 = lean_nat_dec_le(x_94, x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4(x_88, x_96, x_93, lean_box(0), x_91, x_2, x_92);
lean_dec(x_88);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_93);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4(x_88, x_98, x_94, lean_box(0), x_91, x_2, x_92);
lean_dec(x_88);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_88);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_90);
if (x_100 == 0)
{
return x_90;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_90, 0);
x_102 = lean_ctor_get(x_90, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_90);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_9);
lean_dec(x_4);
x_104 = lean_unsigned_to_nat(1u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_dec(x_1);
x_1 = x_105;
goto _start;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_2, 0);
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_2);
x_109 = l_Lean_replaceRef(x_1, x_107);
lean_dec(x_107);
lean_inc(x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
if (x_6 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Lean_Elab_Level_elabLevel___main___closed__5;
x_112 = lean_name_eq(x_4, x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_114 = lean_name_eq(x_4, x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = l_Lean_Elab_Level_elabLevel___main___closed__7;
x_116 = lean_name_eq(x_4, x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = l_Lean_numLitKind;
x_118 = lean_name_eq(x_4, x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_identKind;
x_120 = lean_name_eq(x_4, x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
lean_dec(x_108);
x_121 = l_Lean_Elab_Level_elabLevel___main___closed__9;
x_122 = lean_name_eq(x_4, x_121);
lean_dec(x_4);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_1);
x_123 = l_Lean_Elab_Level_elabLevel___main___closed__12;
x_124 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_123, x_110, x_3);
lean_dec(x_110);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Lean_Syntax_getArg(x_1, x_125);
lean_inc(x_110);
x_127 = l_Lean_Elab_Level_elabLevel___main(x_126, x_110, x_3);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_unsigned_to_nat(2u);
x_132 = l_Lean_Syntax_getArg(x_1, x_131);
lean_dec(x_1);
x_133 = l_Lean_Syntax_isNatLitAux(x_117, x_132);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
lean_dec(x_130);
lean_dec(x_128);
x_134 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(x_110, x_129);
lean_dec(x_110);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_110);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Level_addOffsetAux___main(x_135, x_128);
if (lean_is_scalar(x_130)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_130;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_129);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_110);
lean_dec(x_1);
x_138 = lean_ctor_get(x_127, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_127, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_140 = x_127;
} else {
 lean_dec_ref(x_127);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_4);
x_142 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_143 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_142, x_108);
lean_dec(x_108);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_144 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_144, 0, x_142);
x_145 = l_Lean_Elab_Level_elabLevel___main___closed__15;
x_146 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___rarg(x_146, x_110, x_3);
lean_dec(x_110);
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
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_110);
x_152 = l_Lean_mkLevelParam(x_142);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_3);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_108);
lean_dec(x_4);
x_154 = l_Lean_Syntax_isNatLitAux(x_117, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
x_155 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(x_110, x_3);
lean_dec(x_110);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_110);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_Level_ofNat___main(x_156);
lean_dec(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_3);
return x_158;
}
}
}
else
{
lean_object* x_159; 
lean_dec(x_108);
lean_dec(x_4);
lean_dec(x_1);
x_159 = l_Lean_Elab_Level_mkFreshLevelMVar(x_110, x_3);
lean_dec(x_110);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_108);
lean_dec(x_4);
x_160 = lean_unsigned_to_nat(1u);
x_161 = l_Lean_Syntax_getArg(x_1, x_160);
lean_dec(x_1);
x_162 = l_Lean_Syntax_getArgs(x_161);
lean_dec(x_161);
x_163 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_162);
lean_inc(x_110);
x_164 = l_Lean_Elab_Level_elabLevel___main(x_163, x_110, x_3);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_array_get_size(x_162);
x_168 = lean_nat_sub(x_167, x_160);
x_169 = lean_nat_dec_le(x_168, x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_168);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_162, x_170, x_167, lean_box(0), x_165, x_110, x_166);
lean_dec(x_162);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_167);
x_172 = lean_unsigned_to_nat(0u);
x_173 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__3(x_162, x_172, x_168, lean_box(0), x_165, x_110, x_166);
lean_dec(x_162);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_162);
lean_dec(x_110);
x_174 = lean_ctor_get(x_164, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_164, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_176 = x_164;
} else {
 lean_dec_ref(x_164);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_108);
lean_dec(x_4);
x_178 = lean_unsigned_to_nat(1u);
x_179 = l_Lean_Syntax_getArg(x_1, x_178);
lean_dec(x_1);
x_180 = l_Lean_Syntax_getArgs(x_179);
lean_dec(x_179);
x_181 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_180);
lean_inc(x_110);
x_182 = l_Lean_Elab_Level_elabLevel___main(x_181, x_110, x_3);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_array_get_size(x_180);
x_186 = lean_nat_sub(x_185, x_178);
x_187 = lean_nat_dec_le(x_186, x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_186);
x_188 = lean_unsigned_to_nat(0u);
x_189 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4(x_180, x_188, x_185, lean_box(0), x_183, x_110, x_184);
lean_dec(x_180);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_185);
x_190 = lean_unsigned_to_nat(0u);
x_191 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4(x_180, x_190, x_186, lean_box(0), x_183, x_110, x_184);
lean_dec(x_180);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_180);
lean_dec(x_110);
x_192 = lean_ctor_get(x_182, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_182, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_194 = x_182;
} else {
 lean_dec_ref(x_182);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_108);
lean_dec(x_4);
x_196 = lean_unsigned_to_nat(1u);
x_197 = l_Lean_Syntax_getArg(x_1, x_196);
lean_dec(x_1);
x_1 = x_197;
x_2 = x_110;
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
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___main___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
