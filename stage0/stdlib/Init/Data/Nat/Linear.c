// Lean compiler output
// Module: Init.Data.Nat.Linear
// Imports: Init.ByCases Init.Data.Prod Init.Data.RArray
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
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_defaultExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_;
LEAN_EXPORT uint8_t l_List_beq___at___Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancel(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Var_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_Linear_Expr_inc___closed__0;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr(lean_object*);
static lean_object* l_Nat_Linear_defaultExpr___closed__0____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_fixedVar;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_isValid___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_cancelAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Var_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isZero___boxed(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNonZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_Linear_Poly_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_ctorIdx___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93____boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqExpr;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_toNormPoly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_Linear_Poly_isNum_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_Linear_instBEqPolyCnstr___closed__0;
LEAN_EXPORT uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_instBEqPolyCnstr;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_denote___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Nat_Linear_instBEqExpr___closed__0;
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_isNum_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_toNormPoly(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_inc(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_elimOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_Linear_fixedVar() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(100000000u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Var_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(100000000u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RArray_getImpl___redArg(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Var_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Var_denote(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
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
static lean_object* _init_l_Nat_Linear_defaultExpr___closed__0____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_Linear_defaultExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Linear_defaultExpr___closed__0____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_;
return x_1;
}
}
static lean_object* _init_l_Nat_Linear_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_Linear_defaultExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93_(lean_object* x_1, lean_object* x_2) {
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
x_15 = l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93_(x_11, x_13);
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
x_29 = l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93_(x_25, x_27);
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
LEAN_EXPORT lean_object* l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l_Nat_Linear_beqExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_93____boxed), 2, 0);
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
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Nat_Linear_Var_denote(x_1, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Nat_Linear_Expr_denote(x_1, x_6);
x_9 = l_Nat_Linear_Expr_denote(x_1, x_7);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Nat_Linear_Expr_denote(x_1, x_12);
x_14 = lean_nat_mul(x_11, x_13);
lean_dec(x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = l_Nat_Linear_Expr_denote(x_1, x_15);
x_18 = lean_nat_mul(x_17, x_16);
lean_dec(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_denote(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Nat_Linear_Var_denote(x_1, x_7);
x_9 = lean_nat_mul(x_6, x_8);
lean_dec(x_8);
x_10 = l_Nat_Linear_Poly_denote(x_1, x_5);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Poly_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Poly_denote(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
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
lean_object* x_6; lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_14 = l_List_reverse___redArg(x_4);
x_15 = l_List_appendTR___redArg(x_14, x_2);
x_16 = l_List_reverse___redArg(x_5);
x_17 = l_List_appendTR___redArg(x_16, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
x_6 = x_3;
goto block_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_List_reverse___redArg(x_4);
x_20 = l_List_reverse___redArg(x_5);
x_21 = l_List_appendTR___redArg(x_20, x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
x_6 = x_2;
goto block_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_1, x_31);
lean_dec(x_1);
x_33 = l_Nat_blt(x_27, x_30);
if (x_33 == 0)
{
uint8_t x_34; 
lean_inc(x_28);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_3, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_dec(x_36);
x_37 = l_Nat_blt(x_30, x_27);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec_ref(x_2);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_24, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_24, 0);
lean_dec(x_40);
x_41 = l_Nat_blt(x_26, x_29);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Nat_blt(x_29, x_26);
if (x_42 == 0)
{
lean_free_object(x_24);
lean_free_object(x_3);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_1 = x_32;
x_2 = x_25;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_44; 
x_44 = lean_nat_sub(x_26, x_29);
lean_dec(x_29);
lean_dec(x_26);
lean_ctor_set(x_24, 1, x_27);
lean_ctor_set(x_24, 0, x_44);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_0 = x_32;
lean_object* _tmp_1 = x_25;
lean_object* _tmp_2 = x_28;
lean_object* _tmp_3 = x_3;
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
lean_object* x_46; 
x_46 = lean_nat_sub(x_29, x_26);
lean_dec(x_26);
lean_dec(x_29);
lean_ctor_set(x_24, 1, x_27);
lean_ctor_set(x_24, 0, x_46);
lean_ctor_set(x_3, 1, x_5);
{
lean_object* _tmp_0 = x_32;
lean_object* _tmp_1 = x_25;
lean_object* _tmp_2 = x_28;
lean_object* _tmp_4 = x_3;
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
uint8_t x_48; 
lean_dec(x_24);
x_48 = l_Nat_blt(x_26, x_29);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Nat_blt(x_29, x_26);
if (x_49 == 0)
{
lean_free_object(x_3);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_1 = x_32;
x_2 = x_25;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_nat_sub(x_26, x_29);
lean_dec(x_29);
lean_dec(x_26);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_27);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_52);
{
lean_object* _tmp_0 = x_32;
lean_object* _tmp_1 = x_25;
lean_object* _tmp_2 = x_28;
lean_object* _tmp_3 = x_3;
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
lean_object* x_54; lean_object* x_55; 
x_54 = lean_nat_sub(x_29, x_26);
lean_dec(x_26);
lean_dec(x_29);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_27);
lean_ctor_set(x_3, 1, x_5);
lean_ctor_set(x_3, 0, x_55);
{
lean_object* _tmp_0 = x_32;
lean_object* _tmp_1 = x_25;
lean_object* _tmp_2 = x_28;
lean_object* _tmp_4 = x_3;
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
lean_ctor_set(x_3, 1, x_5);
{
lean_object* _tmp_0 = x_32;
lean_object* _tmp_2 = x_28;
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
uint8_t x_58; 
lean_dec(x_3);
x_58 = l_Nat_blt(x_30, x_27);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_59 = x_24;
} else {
 lean_dec_ref(x_24);
 x_59 = lean_box(0);
}
x_60 = l_Nat_blt(x_26, x_29);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Nat_blt(x_29, x_26);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_1 = x_32;
x_2 = x_25;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_nat_sub(x_26, x_29);
lean_dec(x_29);
lean_dec(x_26);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_27);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_4);
x_1 = x_32;
x_2 = x_25;
x_3 = x_28;
x_4 = x_65;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_nat_sub(x_29, x_26);
lean_dec(x_26);
lean_dec(x_29);
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_59;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_27);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_5);
x_1 = x_32;
x_2 = x_25;
x_3 = x_28;
x_5 = x_69;
goto _start;
}
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_24);
lean_ctor_set(x_71, 1, x_5);
x_1 = x_32;
x_3 = x_28;
x_5 = x_71;
goto _start;
}
}
}
else
{
uint8_t x_73; 
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_23);
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_2, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_2, 0);
lean_dec(x_75);
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_0 = x_32;
lean_object* _tmp_1 = x_25;
lean_object* _tmp_3 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_77; 
lean_dec(x_2);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_23);
lean_ctor_set(x_77, 1, x_4);
x_1 = x_32;
x_2 = x_25;
x_4 = x_77;
goto _start;
}
}
}
}
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_List_reverse___redArg(x_4);
x_8 = l_List_appendTR___redArg(x_7, x_6);
x_9 = l_List_reverse___redArg(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
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
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_PolyCnstr_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_Linear_PolyCnstr_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33__spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33_(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_List_beq___at___Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33__spec__0(x_4, x_7);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_List_beq___at___Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33__spec__0(x_5, x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33__spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l_Nat_Linear_beqPolyCnstr____x40_Init_Data_Nat_Linear_2078008046____hygCtx___hyg_33____boxed), 2, 0);
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
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_Linear_ExprCnstr_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
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
x_2 = l_Nat_Linear_defaultExpr___closed__0____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_;
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
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_3(x_3, x_6, x_7, x_5);
return x_8;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_2, x_11, x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_denote_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
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
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_apply_6(x_5, x_12, x_13, x_11, x_15, x_16, x_14);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
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
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, lean_box(0));
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* initialize_Init_ByCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Prod(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ByCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_Linear_fixedVar = _init_l_Nat_Linear_fixedVar();
lean_mark_persistent(l_Nat_Linear_fixedVar);
l_Nat_Linear_defaultExpr___closed__0____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_ = _init_l_Nat_Linear_defaultExpr___closed__0____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_();
lean_mark_persistent(l_Nat_Linear_defaultExpr___closed__0____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_);
l_Nat_Linear_defaultExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_ = _init_l_Nat_Linear_defaultExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_();
lean_mark_persistent(l_Nat_Linear_defaultExpr____x40_Init_Data_Nat_Linear_3091913453____hygCtx___hyg_87_);
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
