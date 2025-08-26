// Lean compiler output
// Module: Lean.Elab.InfoTree.Types
// Imports: Lean.Data.DeclarationRange Lean.Data.OpenDecl Lean.MetavarContext Lean.Environment Lean.Data.Json.Basic Lean.Server.Rpc.Basic Lean.Widget.Types
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedElabInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo;
static lean_object* l_Lean_Elab_instInhabitedFieldInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTermInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoTree;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__2;
static lean_object* l_Lean_Elab_instInhabitedPartialTermInfo___closed__0;
static lean_object* l_Lean_Elab_instInhabitedInfoTree___closed__0;
static lean_object* l_Lean_Elab_instInhabitedInfoTree___closed__1;
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTacticInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPartialTermInfo;
static lean_object* l_Lean_Elab_instInhabitedElabInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoState;
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedInfoState___closed__0;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo___closed__1;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__8;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo___closed__3;
static lean_object* l_Lean_Elab_instInhabitedInfoState___closed__2;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedFieldInfo;
static size_t l_Lean_Elab_instInhabitedTermInfo___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTacticInfo;
static lean_object* l_Lean_Elab_instInhabitedInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedCommandInfo;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfo;
static lean_object* l_Lean_Elab_instInhabitedInfoState___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__9;
static lean_object* l_Lean_Elab_instInhabitedInfoTree___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__5;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo___closed__2;
static lean_object* l_Lean_Elab_instInhabitedInfoTree___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialContextInfo_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_PartialContextInfo_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedElabInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedElabInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedElabInfo___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_instInhabitedTermInfo___closed__4() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_instInhabitedTermInfo___closed__2;
x_4 = l_Lean_Elab_instInhabitedTermInfo___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__5;
x_3 = l_Lean_Elab_instInhabitedTermInfo___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__9;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_instInhabitedTermInfo___closed__6;
x_5 = l_Lean_Elab_instInhabitedElabInfo___closed__0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__6;
x_3 = l_Lean_Elab_instInhabitedElabInfo___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedPartialTermInfo___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedCommandInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedElabInfo___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
default: 
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CompletionInfo_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_CompletionInfo_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__9;
x_3 = l_Lean_Elab_instInhabitedTermInfo___closed__6;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedFieldInfo___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedTacticInfo___closed__2;
x_3 = l_Lean_Elab_instInhabitedElabInfo___closed__0;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__6;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(10u);
return x_12;
}
case 11:
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(11u);
return x_13;
}
case 12:
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(12u);
return x_14;
}
case 13:
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(13u);
return x_15;
}
default: 
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(14u);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Info_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Info_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfo___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_InfoTree_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedInfoTree___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_instInhabitedInfoTree___closed__0;
x_4 = l_Lean_Elab_instInhabitedInfoTree___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instInhabitedInfoTree___closed__2;
x_2 = l_Lean_Elab_instInhabitedInfo___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfoTree___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedInfoState___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_instInhabitedInfoTree___closed__2;
x_2 = l_Lean_Elab_instInhabitedInfoState___closed__1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfoState___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_1, lean_box(0), x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_setInfoState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_setInfoState___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_setInfoState___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Data_DeclarationRange(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedElabInfo___closed__0 = _init_l_Lean_Elab_instInhabitedElabInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedElabInfo___closed__0);
l_Lean_Elab_instInhabitedElabInfo = _init_l_Lean_Elab_instInhabitedElabInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedElabInfo);
l_Lean_Elab_instInhabitedTermInfo___closed__0 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__0);
l_Lean_Elab_instInhabitedTermInfo___closed__1 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__1);
l_Lean_Elab_instInhabitedTermInfo___closed__2 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__2);
l_Lean_Elab_instInhabitedTermInfo___closed__3 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__3);
l_Lean_Elab_instInhabitedTermInfo___closed__4 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__4();
l_Lean_Elab_instInhabitedTermInfo___closed__5 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__5();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__5);
l_Lean_Elab_instInhabitedTermInfo___closed__6 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__6();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__6);
l_Lean_Elab_instInhabitedTermInfo___closed__7 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__7();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__7);
l_Lean_Elab_instInhabitedTermInfo___closed__8 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__8();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__8);
l_Lean_Elab_instInhabitedTermInfo___closed__9 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__9();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__9);
l_Lean_Elab_instInhabitedTermInfo___closed__10 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__10();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__10);
l_Lean_Elab_instInhabitedTermInfo = _init_l_Lean_Elab_instInhabitedTermInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo);
l_Lean_Elab_instInhabitedPartialTermInfo___closed__0 = _init_l_Lean_Elab_instInhabitedPartialTermInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo___closed__0);
l_Lean_Elab_instInhabitedPartialTermInfo = _init_l_Lean_Elab_instInhabitedPartialTermInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo);
l_Lean_Elab_instInhabitedCommandInfo = _init_l_Lean_Elab_instInhabitedCommandInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedCommandInfo);
l_Lean_Elab_instInhabitedFieldInfo___closed__0 = _init_l_Lean_Elab_instInhabitedFieldInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo___closed__0);
l_Lean_Elab_instInhabitedFieldInfo = _init_l_Lean_Elab_instInhabitedFieldInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo);
l_Lean_Elab_instInhabitedTacticInfo___closed__0 = _init_l_Lean_Elab_instInhabitedTacticInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo___closed__0);
l_Lean_Elab_instInhabitedTacticInfo___closed__1 = _init_l_Lean_Elab_instInhabitedTacticInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo___closed__1);
l_Lean_Elab_instInhabitedTacticInfo___closed__2 = _init_l_Lean_Elab_instInhabitedTacticInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo___closed__2);
l_Lean_Elab_instInhabitedTacticInfo___closed__3 = _init_l_Lean_Elab_instInhabitedTacticInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo___closed__3);
l_Lean_Elab_instInhabitedTacticInfo = _init_l_Lean_Elab_instInhabitedTacticInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo);
l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__0 = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__0);
l_Lean_Elab_instInhabitedMacroExpansionInfo = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo);
l_Lean_Elab_instInhabitedInfo___closed__0 = _init_l_Lean_Elab_instInhabitedInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo___closed__0);
l_Lean_Elab_instInhabitedInfo = _init_l_Lean_Elab_instInhabitedInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo);
l_Lean_Elab_instInhabitedInfoTree___closed__0 = _init_l_Lean_Elab_instInhabitedInfoTree___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree___closed__0);
l_Lean_Elab_instInhabitedInfoTree___closed__1 = _init_l_Lean_Elab_instInhabitedInfoTree___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree___closed__1);
l_Lean_Elab_instInhabitedInfoTree___closed__2 = _init_l_Lean_Elab_instInhabitedInfoTree___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree___closed__2);
l_Lean_Elab_instInhabitedInfoTree___closed__3 = _init_l_Lean_Elab_instInhabitedInfoTree___closed__3();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree___closed__3);
l_Lean_Elab_instInhabitedInfoTree = _init_l_Lean_Elab_instInhabitedInfoTree();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree);
l_Lean_Elab_instInhabitedInfoState___closed__0 = _init_l_Lean_Elab_instInhabitedInfoState___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState___closed__0);
l_Lean_Elab_instInhabitedInfoState___closed__1 = _init_l_Lean_Elab_instInhabitedInfoState___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState___closed__1);
l_Lean_Elab_instInhabitedInfoState___closed__2 = _init_l_Lean_Elab_instInhabitedInfoState___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState___closed__2);
l_Lean_Elab_instInhabitedInfoState = _init_l_Lean_Elab_instInhabitedInfoState();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
