// Lean compiler output
// Module: Init.Lean.Elab.Level
// Imports: Init.Lean.Meta Init.Lean.Elab.Exception Init.Lean.Elab.Log
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
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___lambda__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_max___elambda__1___closed__1;
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_LevelElabM_MonadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_LevelElabM_MonadLog___closed__1;
uint8_t l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___main___closed__9;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Level_elabLevel___main___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
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
extern lean_object* l_Lean_Parser_Level_paren___elambda__1___closed__3;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_mkLevelIMax(x_5, x_15);
x_18 = lean_nat_dec_eq(x_11, x_2);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Lean_mkLevelIMax(x_5, x_21);
x_24 = lean_nat_dec_eq(x_11, x_2);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_23;
x_7 = x_22;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_11);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_7);
return x_32;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_mkLevelMax(x_5, x_15);
x_18 = lean_nat_dec_eq(x_11, x_2);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Lean_mkLevelMax(x_5, x_21);
x_24 = lean_nat_dec_eq(x_11, x_2);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_23;
x_7 = x_22;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_11);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_7);
return x_32;
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Parser_Level_paren___elambda__1___closed__3;
x_6 = lean_name_eq(x_4, x_5);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_9 = lean_name_eq(x_4, x_8);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_12 = lean_name_eq(x_4, x_11);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_14 = l_Lean_Parser_Level_hole___elambda__1___closed__1;
x_15 = lean_name_eq(x_4, x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_17 = l_Lean_Parser_Level_num___elambda__1___closed__2;
x_18 = lean_name_eq(x_4, x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_20 = l_Lean_Parser_Level_ident___elambda__1___closed__1;
x_21 = lean_name_eq(x_4, x_20);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_23 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_24 = lean_name_eq(x_4, x_23);
lean_dec(x_4);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Elab_Level_elabLevel___main___closed__3;
x_27 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_26, x_2, x_3);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
x_30 = l_Lean_Elab_Level_elabLevel___main(x_29, x_2, x_3);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_unsigned_to_nat(2u);
x_35 = l_Lean_Syntax_getArg(x_1, x_34);
x_36 = l_Lean_numLitKind;
x_37 = l_Lean_Syntax_isNatLitAux(x_36, x_35);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_30);
lean_dec(x_32);
x_38 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_39 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_38, x_2, x_33);
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_Level_addOffsetAux___main(x_40, x_32);
lean_ctor_set(x_30, 0, x_41);
return x_30;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_unsigned_to_nat(2u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
x_46 = l_Lean_numLitKind;
x_47 = l_Lean_Syntax_isNatLitAux(x_46, x_45);
lean_dec(x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
x_48 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_49 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_48, x_2, x_43);
lean_dec(x_1);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Level_addOffsetAux___main(x_50, x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
return x_30;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_30, 0);
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_30);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; 
lean_dec(x_4);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Syntax_getIdAt(x_1, x_57);
x_59 = lean_ctor_get(x_2, 3);
x_60 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(x_58, x_59);
x_61 = l_coeDecidableEq(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_62, 0, x_58);
x_63 = l_Lean_Elab_Level_elabLevel___main___closed__9;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__5(x_1, x_64, x_2, x_3);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_70 = l_Lean_mkLevelParam(x_58);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_3);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_4);
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Syntax_getArg(x_1, x_72);
x_74 = l_Lean_numLitKind;
x_75 = l_Lean_Syntax_isNatLitAux(x_74, x_73);
lean_dec(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_77 = l_Lean_Elab_throwError___at_Lean_Elab_Level_elabLevel___main___spec__1(x_1, x_76, x_2, x_3);
lean_dec(x_1);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l_Lean_Level_ofNat___main(x_78);
lean_dec(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_3);
return x_80;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_4);
lean_dec(x_1);
x_81 = l_Lean_Elab_Level_mkFreshLevelMVar___rarg(x_3);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_4);
x_82 = lean_unsigned_to_nat(1u);
x_83 = l_Lean_Syntax_getArg(x_1, x_82);
lean_dec(x_1);
x_84 = l_Lean_Syntax_getArgs(x_83);
lean_dec(x_83);
x_85 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_84);
x_86 = l_Lean_Elab_Level_elabLevel___main(x_85, x_2, x_3);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_array_get_size(x_84);
x_90 = lean_nat_sub(x_89, x_82);
x_91 = lean_nat_dec_le(x_90, x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
x_92 = lean_unsigned_to_nat(0u);
x_93 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6(x_84, x_92, x_89, lean_box(0), x_87, x_2, x_88);
lean_dec(x_84);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_89);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__6(x_84, x_94, x_90, lean_box(0), x_87, x_2, x_88);
lean_dec(x_84);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_84);
x_96 = !lean_is_exclusive(x_86);
if (x_96 == 0)
{
return x_86;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_86, 0);
x_98 = lean_ctor_get(x_86, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_86);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_4);
x_100 = lean_unsigned_to_nat(1u);
x_101 = l_Lean_Syntax_getArg(x_1, x_100);
lean_dec(x_1);
x_102 = l_Lean_Syntax_getArgs(x_101);
lean_dec(x_101);
x_103 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_102);
x_104 = l_Lean_Elab_Level_elabLevel___main(x_103, x_2, x_3);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_sub(x_107, x_100);
x_109 = lean_nat_dec_le(x_108, x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7(x_102, x_110, x_107, lean_box(0), x_105, x_2, x_106);
lean_dec(x_102);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_107);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l___private_Init_Data_Array_Basic_4__foldrRangeMAux___main___at_Lean_Elab_Level_elabLevel___main___spec__7(x_102, x_112, x_108, lean_box(0), x_105, x_2, x_106);
lean_dec(x_102);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_102);
x_114 = !lean_is_exclusive(x_104);
if (x_114 == 0)
{
return x_104;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_104, 0);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_104);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_4);
x_118 = lean_unsigned_to_nat(1u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
lean_dec(x_1);
x_1 = x_119;
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
lean_object* initialize_Init_Lean_Meta(lean_object*);
lean_object* initialize_Init_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Level(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta(lean_io_mk_world());
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
