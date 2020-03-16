// Lean compiler output
// Module: Init.Lean.Elab.Level
// Imports: Init.Lean.Meta.LevelDefEq Init.Lean.Elab.Exception Init.Lean.Elab.Log
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___rarg(lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__9;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__7;
extern lean_object* l_Lean_Parser_Level_num___elambda__1___closed__2;
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Level_elabLevel___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_max___elambda__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat___main(lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Level_elabLevel___main___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__6;
extern lean_object* l_Lean_Parser_Level_imax___elambda__1___closed__1;
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__2;
lean_object* l_Lean_Elab_Level_elabLevel___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__5;
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__6;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Level_elabLevel___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_addOffsetAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__8;
lean_object* l_Lean_Elab_Level_mkFreshId(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__9;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__1;
lean_object* l_Lean_Elab_Level_mkFreshId___rarg(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_ident___elambda__1___closed__1;
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog;
extern lean_object* l_Lean_Parser_Level_hole___elambda__1___closed__1;
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__7;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__5;
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshId___boxed(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__4;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__4;
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Level_elabLevel___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__2;
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__8;
lean_object* l_Lean_Elab_Level_elabLevel___main(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1;
x_2 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1;
x_2 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1;
x_2 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__3;
x_2 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__5;
x_3 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__7;
x_4 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Level_LevelElabM_MonadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_LevelElabM_MonadLog___closed__9;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_mkFreshId___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Level_mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_mkFreshId___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_mkFreshId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Level_mkFreshId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Level_mkFreshId___rarg(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_8 = l_Lean_MetavarContext_addLevelMVarDecl(x_7, x_6);
lean_ctor_set(x_4, 1, x_8);
x_9 = l_Lean_mkLevelMVar(x_6);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_10);
x_13 = l_Lean_MetavarContext_addLevelMVarDecl(x_12, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_mkLevelMVar(x_10);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
lean_inc(x_17);
x_21 = l_Lean_MetavarContext_addLevelMVarDecl(x_19, x_17);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_mkLevelMVar(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_mkFreshLevelMVar___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Level_mkFreshLevelMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Level_elabLevel___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Level_elabLevel___main___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = l_Lean_FileMap_toPosition(x_7, x_8);
x_10 = lean_box(0);
x_11 = l_String_splitAux___main___closed__1;
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_3, 0);
x_17 = l_Lean_FileMap_toPosition(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_String_splitAux___main___closed__1;
lean_inc(x_14);
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_1);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Level_elabLevel___main___spec__3(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Level_elabLevel___main___spec__4(x_1, x_2, x_9, x_4, x_8);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_1 = lean_mk_string("unexpected universe level syntax kind");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed universe level syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe level ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Level_elabLevel___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_elabLevel___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Parser_Level_paren___elambda__1___closed__4;
x_6 = lean_name_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_8 = lean_name_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_10 = lean_name_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Parser_Level_hole___elambda__1___closed__1;
x_12 = lean_name_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Parser_Level_num___elambda__1___closed__2;
x_14 = lean_name_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Level_ident___elambda__1___closed__1;
x_16 = lean_name_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_18 = lean_name_eq(x_4, x_17);
lean_dec(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Elab_Level_elabLevel___main___closed__3;
x_20 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_19, x_2, x_3);
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Elab_Level_elabLevel___main(x_22, x_2, x_3);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_unsigned_to_nat(2u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
x_29 = l_Lean_numLitKind;
x_30 = l_Lean_Syntax_isNatLitAux(x_29, x_28);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_23);
lean_dec(x_25);
x_31 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_32 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_31, x_2, x_26);
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lean_Level_addOffsetAux___main(x_33, x_25);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_unsigned_to_nat(2u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
x_39 = l_Lean_numLitKind;
x_40 = l_Lean_Syntax_isNatLitAux(x_39, x_38);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_41 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_42 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_41, x_2, x_36);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_Level_addOffsetAux___main(x_43, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_4);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Syntax_getIdAt(x_1, x_50);
x_52 = lean_ctor_get(x_2, 3);
x_53 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_55 = l_Lean_Elab_Level_elabLevel___main___closed__9;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__5(x_1, x_56, x_2, x_3);
lean_dec(x_1);
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
lean_dec(x_1);
x_62 = l_Lean_mkLevelParam(x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_3);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_4);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Syntax_getArg(x_1, x_64);
x_66 = l_Lean_numLitKind;
x_67 = l_Lean_Syntax_isNatLitAux(x_66, x_65);
lean_dec(x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_69 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_68, x_2, x_3);
lean_dec(x_1);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_Lean_Level_ofNat___main(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_4);
lean_dec(x_1);
x_73 = l_Lean_Elab_Level_mkFreshLevelMVar___rarg(x_3);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_4);
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_1, x_74);
lean_dec(x_1);
x_76 = l_Lean_Syntax_getArgs(x_75);
lean_dec(x_75);
x_77 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_76);
x_78 = l_Lean_Elab_Level_elabLevel___main(x_77, x_2, x_3);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_array_get_size(x_76);
x_82 = lean_nat_sub(x_81, x_74);
x_83 = lean_nat_dec_le(x_82, x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6(x_76, x_84, x_81, lean_box(0), x_79, x_2, x_80);
lean_dec(x_76);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6(x_76, x_86, x_82, lean_box(0), x_79, x_2, x_80);
lean_dec(x_76);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_76);
x_88 = !lean_is_exclusive(x_78);
if (x_88 == 0)
{
return x_78;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_78, 0);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_78);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
x_92 = lean_unsigned_to_nat(1u);
x_93 = l_Lean_Syntax_getArg(x_1, x_92);
lean_dec(x_1);
x_94 = l_Lean_Syntax_getArgs(x_93);
lean_dec(x_93);
x_95 = l_Array_back___at_Lean_Parser_checkStackTopFn___spec__1(x_94);
x_96 = l_Lean_Elab_Level_elabLevel___main(x_95, x_2, x_3);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_array_get_size(x_94);
x_100 = lean_nat_sub(x_99, x_92);
x_101 = lean_nat_dec_le(x_100, x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
x_102 = lean_unsigned_to_nat(0u);
x_103 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7(x_94, x_102, x_99, lean_box(0), x_97, x_2, x_98);
lean_dec(x_94);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_99);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7(x_94, x_104, x_100, lean_box(0), x_97, x_2, x_98);
lean_dec(x_94);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_94);
x_106 = !lean_is_exclusive(x_96);
if (x_106 == 0)
{
return x_96;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_96, 0);
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_96);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_4);
x_110 = lean_unsigned_to_nat(1u);
x_111 = l_Lean_Syntax_getArg(x_1, x_110);
lean_dec(x_1);
x_1 = x_111;
goto _start;
}
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Level_elabLevel___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Level_elabLevel___main___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Level_elabLevel___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Level_elabLevel___main___spec__4(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Level_elabLevel___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_elabLevel___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_Elab_Level_elabLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_elabLevel(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Init_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Level(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__2 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__2);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__3 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__3);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__4 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__4);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__5 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__5);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__6 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__6);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__7 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__7);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__8 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__8);
l_Lean_Elab_Level_LevelElabM_MonadLog___closed__9 = _init_l_Lean_Elab_Level_LevelElabM_MonadLog___closed__9();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog___closed__9);
l_Lean_Elab_Level_LevelElabM_MonadLog = _init_l_Lean_Elab_Level_LevelElabM_MonadLog();
lean_mark_persistent(l_Lean_Elab_Level_LevelElabM_MonadLog);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
