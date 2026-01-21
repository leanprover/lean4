// Lean compiler output
// Module: Init.Data.Nat.Linear
// Imports: public import Init.ByCases public import Init.Data.Prod public import Init.Data.RArray import Init.LawfulBEqTactics
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
uint8_t l_Nat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_monomialToExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_hugeFuel;
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isNonZero(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqPolyCnstr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancel(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instInhabitedExpr_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_Linear_Expr_inc___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_fixedVar;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isValid___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancelAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isZero___boxed(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNonZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm(lean_object*);
static lean_object* l_Nat_Linear_instInhabitedExpr_default___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqExpr_beq___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqExpr;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_Linear_Poly_isNum_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_Linear_instBEqPolyCnstr___closed__0;
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqExpr_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqPolyCnstr;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Nat_Linear_instBEqExpr___closed__0;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqPolyCnstr_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toNormPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_inc(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___redArg(lean_object*, lean_object*);
static lean_object* _init_l_Nat_Linear_fixedVar() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(100000000u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx(lean_object* x_1) {
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
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_Linear_Expr_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_Linear_Expr_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_Linear_Expr_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_num_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_Linear_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_var_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_Linear_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_add_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_Linear_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulL_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_Linear_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_mulR_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_Linear_Expr_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Nat_Linear_instInhabitedExpr_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_Linear_instInhabitedExpr_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Linear_instInhabitedExpr_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Nat_Linear_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Linear_instInhabitedExpr_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqExpr_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_nat_dec_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = l_Nat_Linear_instBEqExpr_beq(x_11, x_13);
if (x_15 == 0)
{
return x_15;
}
else
{
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_nat_dec_eq(x_18, x_20);
if (x_22 == 0)
{
return x_22;
}
else
{
x_1 = x_19;
x_2 = x_21;
goto _start;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
default: 
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = l_Nat_Linear_instBEqExpr_beq(x_25, x_27);
if (x_29 == 0)
{
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_eq(x_26, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqExpr_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_Linear_instBEqExpr_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_Linear_instBEqExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_Linear_instBEqExpr_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_Linear_instBEqExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Linear_instBEqExpr___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Nat_blt(x_2, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc(x_7);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_nat_dec_eq(x_2, x_9);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Nat_Linear_Poly_insert(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_15);
return x_3;
}
else
{
uint8_t x_16; 
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_nat_add(x_1, x_8);
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_19);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_20 = lean_nat_add(x_1, x_8);
lean_dec(x_8);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = lean_nat_dec_eq(x_2, x_9);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Nat_Linear_Poly_insert(x_1, x_2, x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_25 = x_6;
} else {
 lean_dec_ref(x_6);
 x_25 = lean_box(0);
}
x_26 = lean_nat_add(x_1, x_8);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_6, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_6, 0);
lean_dec(x_31);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Nat_Linear_Poly_insert(x_5, x_6, x_2);
x_1 = x_4;
x_2 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Nat_Linear_Poly_norm_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancelAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_8 = l_List_reverse___redArg(x_4);
x_9 = l_List_appendTR___redArg(x_8, x_2);
x_10 = l_List_reverse___redArg(x_5);
x_11 = l_List_appendTR___redArg(x_10, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_13 = l_List_reverse___redArg(x_4);
x_14 = l_List_appendTR___redArg(x_13, x_2);
x_15 = l_List_reverse___redArg(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = l_List_reverse___redArg(x_4);
x_18 = l_List_reverse___redArg(x_5);
x_19 = l_List_appendTR___redArg(x_18, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_1, x_29);
lean_dec(x_1);
x_31 = l_Nat_blt(x_26, x_28);
if (x_31 == 0)
{
uint8_t x_32; 
lean_inc(x_23);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
x_35 = l_Nat_blt(x_28, x_26);
if (x_35 == 0)
{
uint8_t x_36; 
lean_free_object(x_3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_2, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_2, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_22, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_22, 0);
lean_dec(x_41);
x_42 = l_Nat_blt(x_25, x_27);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Nat_blt(x_27, x_25);
if (x_43 == 0)
{
lean_free_object(x_22);
lean_free_object(x_2);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_45; 
x_45 = lean_nat_sub(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_45);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_22);
{
lean_object* _tmp_0 = x_30;
lean_object* _tmp_1 = x_24;
lean_object* _tmp_2 = x_23;
lean_object* _tmp_3 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_47; 
x_47 = lean_nat_sub(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_47);
lean_ctor_set(x_2, 1, x_5);
lean_ctor_set(x_2, 0, x_22);
{
lean_object* _tmp_0 = x_30;
lean_object* _tmp_1 = x_24;
lean_object* _tmp_2 = x_23;
lean_object* _tmp_4 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
x_49 = l_Nat_blt(x_25, x_27);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Nat_blt(x_27, x_25);
if (x_50 == 0)
{
lean_free_object(x_2);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_nat_sub(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_53);
{
lean_object* _tmp_0 = x_30;
lean_object* _tmp_1 = x_24;
lean_object* _tmp_2 = x_23;
lean_object* _tmp_3 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_nat_sub(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_26);
lean_ctor_set(x_2, 1, x_5);
lean_ctor_set(x_2, 0, x_56);
{
lean_object* _tmp_0 = x_30;
lean_object* _tmp_1 = x_24;
lean_object* _tmp_2 = x_23;
lean_object* _tmp_4 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_2);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_58 = x_22;
} else {
 lean_dec_ref(x_22);
 x_58 = lean_box(0);
}
x_59 = l_Nat_blt(x_25, x_27);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Nat_blt(x_27, x_25);
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_nat_sub(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_26);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_4);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
x_4 = x_64;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_nat_sub(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
if (lean_is_scalar(x_58)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_58;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_26);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_5);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
x_5 = x_68;
goto _start;
}
}
}
else
{
lean_ctor_set(x_3, 1, x_5);
{
lean_object* _tmp_0 = x_30;
lean_object* _tmp_2 = x_23;
lean_object* _tmp_4 = x_3;
x_1 = _tmp_0;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
}
else
{
uint8_t x_71; 
lean_dec(x_3);
x_71 = l_Nat_blt(x_28, x_26);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_72 = x_2;
} else {
 lean_dec_ref(x_2);
 x_72 = lean_box(0);
}
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_73 = x_22;
} else {
 lean_dec_ref(x_22);
 x_73 = lean_box(0);
}
x_74 = l_Nat_blt(x_25, x_27);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Nat_blt(x_27, x_25);
if (x_75 == 0)
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_nat_sub(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_26);
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_72;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_4);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
x_4 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_nat_sub(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_26);
if (lean_is_scalar(x_72)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_72;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_5);
x_1 = x_30;
x_2 = x_24;
x_3 = x_23;
x_5 = x_83;
goto _start;
}
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_22);
lean_ctor_set(x_85, 1, x_5);
x_1 = x_30;
x_3 = x_23;
x_5 = x_85;
goto _start;
}
}
}
else
{
uint8_t x_87; 
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_21);
x_87 = !lean_is_exclusive(x_2);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_2, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_2, 0);
lean_dec(x_89);
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_0 = x_30;
lean_object* _tmp_1 = x_24;
lean_object* _tmp_3 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_91; 
lean_dec(x_2);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_21);
lean_ctor_set(x_91, 1, x_4);
x_1 = x_30;
x_2 = x_24;
x_4 = x_91;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Nat_Linear_hugeFuel() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1000000u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1000000u);
x_4 = lean_box(0);
x_5 = l_Nat_Linear_Poly_cancelAux(x_3, x_1, x_2, x_4, x_4);
return x_5;
}
}
static lean_object* _init_l_Nat_Linear_Poly_isNum_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Nat_Linear_Poly_isNum_x3f___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_unsigned_to_nat(100000000u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_Linear_Poly_isNum_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isZero(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Nat_Linear_Poly_isZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isNonZero(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unsigned_to_nat(100000000u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNonZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Nat_Linear_Poly_isNonZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_nat_mul(x_1, x_4);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(100000000u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_dec(x_1);
return x_3;
}
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_16 = l_Nat_Linear_Expr_toPoly_go(x_1, x_15, x_3);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_nat_mul(x_1, x_18);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_19;
goto _start;
}
else
{
lean_dec(x_1);
return x_3;
}
}
default: 
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_nat_mul(x_1, x_25);
lean_dec(x_1);
x_1 = x_28;
x_2 = x_24;
goto _start;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_Linear_Expr_toPoly_go(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = l_Nat_Linear_Expr_toPoly_go(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_Linear_Expr_toPoly(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_Linear_Expr_toPoly(x_1);
x_3 = l_Nat_Linear_Poly_norm(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_Linear_Expr_toNormPoly(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_Linear_Expr_inc___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_inc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_Linear_Expr_inc___closed__0;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_nat_dec_eq(x_13, x_15);
if (x_17 == 0)
{
x_10 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_14, x_16);
x_10 = x_18;
goto block_12;
}
block_12:
{
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_instBEqPolyCnstr_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
if (x_3 == 0)
{
if (x_6 == 0)
{
goto block_11;
}
else
{
return x_3;
}
}
else
{
if (x_6 == 0)
{
return x_6;
}
else
{
goto block_11;
}
}
block_11:
{
uint8_t x_9; 
x_9 = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(x_4, x_7);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(x_5, x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqPolyCnstr_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_Linear_instBEqPolyCnstr_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Nat_Linear_instBEqPolyCnstr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_Linear_instBEqPolyCnstr_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_Linear_instBEqPolyCnstr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Linear_instBEqPolyCnstr___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_box(x_4);
x_11 = lean_box(x_7);
x_12 = lean_apply_6(x_3, x_10, x_5, x_6, x_11, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = lean_box(x_6);
x_13 = lean_box(x_9);
x_14 = lean_apply_6(x_4, x_12, x_7, x_8, x_13, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Nat_Linear_Poly_norm(x_3);
x_6 = l_Nat_Linear_Poly_norm(x_4);
x_7 = l_Nat_Linear_Poly_cancel(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Nat_Linear_Poly_norm(x_11);
x_14 = l_Nat_Linear_Poly_norm(x_12);
x_15 = l_Nat_Linear_Poly_cancel(x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_10);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
if (x_2 == 0)
{
uint8_t x_9; 
x_9 = l_Nat_Linear_Poly_isNonZero(x_3);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Nat_Linear_Poly_isZero(x_4);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = l_Nat_Linear_Poly_isZero(x_3);
if (x_11 == 0)
{
x_5 = x_11;
goto block_8;
}
else
{
uint8_t x_12; 
x_12 = l_Nat_Linear_Poly_isNonZero(x_4);
x_5 = x_12;
goto block_8;
}
}
block_8:
{
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Nat_Linear_Poly_isNonZero(x_3);
if (x_6 == 0)
{
return x_6;
}
else
{
uint8_t x_7; 
x_7 = l_Nat_Linear_Poly_isZero(x_4);
return x_7;
}
}
else
{
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isUnsat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Nat_Linear_PolyCnstr_isUnsat(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Nat_Linear_Poly_isZero(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Nat_Linear_Poly_isZero(x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Nat_Linear_Poly_isZero(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isValid___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Nat_Linear_PolyCnstr_isValid(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Nat_Linear_Expr_toPoly(x_3);
lean_dec_ref(x_3);
x_6 = l_Nat_Linear_Expr_toPoly(x_4);
lean_dec_ref(x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Nat_Linear_Expr_toPoly(x_8);
lean_dec_ref(x_8);
x_11 = l_Nat_Linear_Expr_toPoly(x_9);
lean_dec_ref(x_9);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toNormPoly(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Nat_Linear_Expr_toNormPoly(x_3);
lean_dec_ref(x_3);
x_6 = l_Nat_Linear_Expr_toNormPoly(x_4);
lean_dec_ref(x_4);
x_7 = l_Nat_Linear_Poly_cancel(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Nat_Linear_Expr_toNormPoly(x_11);
lean_dec_ref(x_11);
x_14 = l_Nat_Linear_Expr_toNormPoly(x_12);
lean_dec_ref(x_12);
x_15 = l_Nat_Linear_Poly_cancel(x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_monomialToExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(100000000u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Nat_Linear_monomialToExpr(x_6, x_7);
lean_ctor_set_tag(x_3, 2);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_1);
x_1 = x_3;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Nat_Linear_monomialToExpr(x_10, x_11);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Nat_Linear_instInhabitedExpr_default___closed__0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Nat_Linear_monomialToExpr(x_5, x_6);
x_8 = l_Nat_Linear_Poly_toExpr_go(x_7, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Nat_Linear_Poly_toExpr(x_3);
x_6 = l_Nat_Linear_Poly_toExpr(x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Nat_Linear_Poly_toExpr(x_8);
x_11 = l_Nat_Linear_Poly_toExpr(x_9);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_3(x_3, x_8, x_9, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_apply_6(x_5, x_12, x_13, x_11, x_14, x_15, x_10);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_4, x_2);
return x_7;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_apply_2(x_5, x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_apply_6(x_6, x_13, x_14, x_12, x_15, x_16, x_11);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_2(x_5, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec_ref(x_1);
x_19 = lean_apply_2(x_6, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Nat_elimOffset___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_apply_1(x_1, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_elimOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_1(x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_elimOffset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_elimOffset(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Data_RArray(uint8_t builtin);
lean_object* initialize_Init_LawfulBEqTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_LawfulBEqTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_Linear_fixedVar = _init_l_Nat_Linear_fixedVar();
lean_mark_persistent(l_Nat_Linear_fixedVar);
l_Nat_Linear_instInhabitedExpr_default___closed__0 = _init_l_Nat_Linear_instInhabitedExpr_default___closed__0();
lean_mark_persistent(l_Nat_Linear_instInhabitedExpr_default___closed__0);
l_Nat_Linear_instInhabitedExpr_default = _init_l_Nat_Linear_instInhabitedExpr_default();
lean_mark_persistent(l_Nat_Linear_instInhabitedExpr_default);
l_Nat_Linear_instInhabitedExpr = _init_l_Nat_Linear_instInhabitedExpr();
lean_mark_persistent(l_Nat_Linear_instInhabitedExpr);
l_Nat_Linear_instBEqExpr___closed__0 = _init_l_Nat_Linear_instBEqExpr___closed__0();
lean_mark_persistent(l_Nat_Linear_instBEqExpr___closed__0);
l_Nat_Linear_instBEqExpr = _init_l_Nat_Linear_instBEqExpr();
lean_mark_persistent(l_Nat_Linear_instBEqExpr);
l_Nat_Linear_hugeFuel = _init_l_Nat_Linear_hugeFuel();
lean_mark_persistent(l_Nat_Linear_hugeFuel);
l_Nat_Linear_Poly_isNum_x3f___closed__0 = _init_l_Nat_Linear_Poly_isNum_x3f___closed__0();
lean_mark_persistent(l_Nat_Linear_Poly_isNum_x3f___closed__0);
l_Nat_Linear_Expr_inc___closed__0 = _init_l_Nat_Linear_Expr_inc___closed__0();
lean_mark_persistent(l_Nat_Linear_Expr_inc___closed__0);
l_Nat_Linear_instBEqPolyCnstr___closed__0 = _init_l_Nat_Linear_instBEqPolyCnstr___closed__0();
lean_mark_persistent(l_Nat_Linear_instBEqPolyCnstr___closed__0);
l_Nat_Linear_instBEqPolyCnstr = _init_l_Nat_Linear_instBEqPolyCnstr();
lean_mark_persistent(l_Nat_Linear_instBEqPolyCnstr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
