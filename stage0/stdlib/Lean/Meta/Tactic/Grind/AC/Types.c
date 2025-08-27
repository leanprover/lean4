// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Types
// Imports: Init.Core Init.Grind.AC Std.Data.HashMap Lean.Expr Lean.Data.PersistentArray Lean.Meta.Tactic.Grind.ExprPtr Lean.Meta.Tactic.Grind.AC.Seq
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
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0;
static size_t l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__1;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedState___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedState___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableSeq__lean;
static lean_object* l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableExpr__lean;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__1;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hashSeq____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstr;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct;
static lean_object* l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AC_EqCnstr_compare(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__5;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_hashSeq____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_14_(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__3;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3_(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedState___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__4;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedState;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedState___closed__1;
lean_object* l_Lean_Grind_AC_Seq_length(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = lean_uint64_of_nat(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = 1;
x_9 = l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3_(x_6);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3_(x_7);
x_12 = lean_uint64_mix_hash(x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3_(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_hashExpr____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_3____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instHashableExpr__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_hashSeq____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_14_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = lean_uint64_of_nat(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = 1;
x_9 = lean_uint64_of_nat(x_6);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = l_Lean_Meta_Grind_AC_hashSeq____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_14_(x_7);
x_12 = lean_uint64_mix_hash(x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hashSeq____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_14____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_AC_hashSeq____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_14_(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_hashSeq____x40_Lean_Meta_Tactic_Grind_AC_Types_3856241489____hygCtx___hyg_14____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instHashableSeq__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(lean_object* x_1) {
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
default: 
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3;
x_2 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__4;
x_3 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AC_EqCnstr_compare(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_Grind_AC_Seq_length(x_3);
x_8 = l_Lean_Grind_AC_Seq_length(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 2;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_4, x_6);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_4, x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 2;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_AC_EqCnstr_compare(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(lean_object* x_1) {
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
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__0;
x_4 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__5;
x_4 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__3;
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_7);
lean_ctor_set(x_9, 6, x_5);
lean_ctor_set(x_9, 7, x_5);
lean_ctor_set(x_9, 8, x_5);
lean_ctor_set(x_9, 9, x_8);
lean_ctor_set(x_9, 10, x_4);
lean_ctor_set(x_9, 11, x_3);
lean_ctor_set(x_9, 12, x_3);
lean_ctor_set(x_9, 13, x_2);
lean_ctor_set(x_9, 14, x_1);
lean_ctor_set(x_9, 15, x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedState___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedState___closed__2;
x_2 = l_Lean_Meta_Grind_AC_instInhabitedState___closed__0;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instInhabitedState___closed__3;
return x_1;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_AC(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExprPtr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExprPtr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0 = _init_l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0);
l_Lean_Meta_Grind_AC_instHashableExpr__lean = _init_l_Lean_Meta_Grind_AC_instHashableExpr__lean();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instHashableExpr__lean);
l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0 = _init_l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0);
l_Lean_Meta_Grind_AC_instHashableSeq__lean = _init_l_Lean_Meta_Grind_AC_instHashableSeq__lean();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instHashableSeq__lean);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0 = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1 = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2 = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3 = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__4 = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__4);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0 = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__1 = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__1);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstr = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr);
l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__0 = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__0);
l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__1 = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__1);
l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__2 = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__2();
l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__3 = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__3);
l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__4 = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__4);
l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__5 = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__5);
l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__6 = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct___closed__6);
l_Lean_Meta_Grind_AC_instInhabitedStruct = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct);
l_Lean_Meta_Grind_AC_instInhabitedState___closed__0 = _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState___closed__0);
l_Lean_Meta_Grind_AC_instInhabitedState___closed__1 = _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState___closed__1);
l_Lean_Meta_Grind_AC_instInhabitedState___closed__2 = _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState___closed__2);
l_Lean_Meta_Grind_AC_instInhabitedState___closed__3 = _init_l_Lean_Meta_Grind_AC_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState___closed__3);
l_Lean_Meta_Grind_AC_instInhabitedState = _init_l_Lean_Meta_Grind_AC_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
