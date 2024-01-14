// Lean compiler output
// Module: Lean.ToExpr
// Imports: Init Lean.Expr
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
static lean_object* l_Lean_instToExprProd___rarg___closed__1;
static lean_object* l_Lean_instToExprChar___closed__2;
static lean_object* l_Lean_instToExprBool___closed__4;
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__7;
static lean_object* l_Lean_instToExprList___rarg___closed__3;
static lean_object* l_Lean_instToExprChar___lambda__1___closed__1;
static lean_object* l_Lean_instToExprUnit___lambda__1___closed__2;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__11;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprBool;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__8;
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lambda__1(uint8_t);
static lean_object* l_Lean_instToExprList___rarg___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprArray(lean_object*);
static lean_object* l_Lean_instToExprString___closed__2;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__9;
static lean_object* l_Lean_instToExprLiteral___lambda__1___closed__7;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__7;
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__1;
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_Lean_instToExprUnit___lambda__1___closed__3;
static lean_object* l_Lean_instToExprList___rarg___closed__4;
static lean_object* l_Lean_instToExprString___closed__4;
static lean_object* l_Lean_instToExprProd___rarg___lambda__1___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__1;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToExprLiteral___lambda__1___closed__4;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__3;
static lean_object* l_Lean_instToExprLiteral___lambda__1___closed__1;
static lean_object* l_Lean_instToExprBool___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprString;
static lean_object* l_Lean_instToExprProd___rarg___lambda__1___closed__3;
static lean_object* l_Lean_instToExprList___rarg___closed__7;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7;
lean_object* l_Lean_Expr_lit___override(lean_object*);
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__2;
static lean_object* l_Lean_instToExprProd___rarg___closed__2;
static lean_object* l_Lean_instToExprNat___closed__3;
static lean_object* l_Lean_instToExprList___rarg___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprProd___rarg___lambda__1___closed__5;
static lean_object* l_Lean_instToExprBool___lambda__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Expr_toCtorIfLit___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToExprOption___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprOption___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToExprBool___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lambda__1(lean_object*);
static lean_object* l_Lean_instToExprLiteral___closed__3;
static lean_object* l_Lean_instToExprUnit___lambda__1___closed__1;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__2;
static lean_object* l_Lean_instToExprNat___closed__1;
static lean_object* l_Lean_instToExprChar___closed__4;
static lean_object* l_Lean_instToExprFVarId___closed__3;
static lean_object* l_Lean_instToExprFVarId___closed__2;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToExprBool___lambda__1___closed__5;
static lean_object* l_Lean_instToExprFVarId___closed__4;
static lean_object* l_Lean_instToExprProd___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_instToExprName___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToExprUnit___closed__2;
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_instToExprUnit___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprArray___rarg___lambda__1___closed__2;
static lean_object* l_Lean_instToExprName___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprChar;
LEAN_EXPORT lean_object* l_Lean_instToExprName;
static lean_object* l_Lean_instToExprArray___rarg___closed__1;
static lean_object* l_Lean_instToExprChar___lambda__1___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_toCtorIfLit___closed__6;
static lean_object* l_Lean_instToExprList___rarg___closed__8;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__8;
LEAN_EXPORT lean_object* l_Lean_instToExprList___rarg(lean_object*);
static lean_object* l_Lean_instToExprName___closed__1;
static lean_object* l_Lean_instToExprChar___closed__1;
static lean_object* l_Lean_instToExprProd___rarg___lambda__1___closed__4;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprProd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprNat;
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_instToExprArray___rarg___lambda__1___closed__4;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4;
static lean_object* l_Lean_instToExprUnit___lambda__1___closed__4;
static lean_object* l_Lean_instToExprArray___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprArray___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprLiteral___lambda__1___closed__5;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__9;
static lean_object* l_Lean_instToExprLiteral___lambda__1___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4;
static lean_object* l_Lean_instToExprFVarId___lambda__1___closed__1;
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__3;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8;
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1;
static lean_object* l_Lean_instToExprList___rarg___closed__5;
static lean_object* l_Lean_instToExprBool___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_instToExprProd___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToExprBool___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
static lean_object* l_Lean_instToExprArray___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lambda__1(lean_object*);
static lean_object* l_Lean_instToExprNat___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_toCtorIfLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprList(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprList___rarg___closed__9;
static lean_object* l_Lean_instToExprLiteral___lambda__1___closed__6;
static lean_object* l_Lean_instToExprLiteral___closed__1;
static lean_object* l_Lean_instToExprUnit___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprArray___rarg___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
static lean_object* l_Lean_instToExprFVarId___lambda__1___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUnit;
static lean_object* l_Lean_instToExprChar___lambda__1___closed__2;
static lean_object* l_Lean_instToExprBool___closed__1;
static lean_object* l_Lean_instToExprFVarId___closed__1;
static lean_object* l_Lean_instToExprBool___closed__2;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lambda__1(uint32_t);
static lean_object* l_Lean_instToExprFVarId___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprProd___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__6;
static lean_object* l_Lean_instToExprLiteral___closed__4;
static lean_object* l_Lean_instToExprOption___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_instToExprNat___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object*);
static lean_object* l_Lean_Expr_toCtorIfLit___closed__10;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprOption(lean_object*);
static lean_object* l_Lean_instToExprChar___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprOption___rarg(lean_object*);
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__5;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__5;
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_instToExprLiteral___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprUnit___closed__1;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2;
static lean_object* l_Lean_instToExprNat___closed__4;
static lean_object* l_Lean_Expr_toCtorIfLit___closed__4;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprLiteral___closed__2;
static lean_object* l_Lean_instToExprList___rarg___closed__1;
static lean_object* l_Lean_instToExprString___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Expr_toCtorIfLit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToExprOption___rarg___lambda__1___closed__8;
static lean_object* l_Lean_instToExprArray___rarg___lambda__1___closed__3;
static lean_object* l_Lean_instToExprString___closed__1;
static lean_object* l_Lean_instToExprBool___lambda__1___closed__2;
static lean_object* l_Lean_instToExprString___closed__5;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5;
static lean_object* l_Lean_instToExprChar___lambda__1___closed__4;
static lean_object* l_Lean_instToExprBool___lambda__1___closed__1;
static lean_object* _init_l_Lean_instToExprNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprNat___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprNat___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprNat___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkNatLit), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprNat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprNat___closed__4;
x_2 = l_Lean_instToExprNat___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprNat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprNat___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprBool___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprBool___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprBool___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprBool___lambda__1___closed__1;
x_2 = l_Lean_instToExprBool___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprBool___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprBool___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprBool___lambda__1___closed__1;
x_2 = l_Lean_instToExprBool___lambda__1___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprBool___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lambda__1(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_instToExprBool___lambda__1___closed__4;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_instToExprBool___lambda__1___closed__7;
return x_3;
}
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprBool___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprBool___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprBool___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprBool___closed__3;
x_2 = l_Lean_instToExprBool___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprBool___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprBool___lambda__1(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Char", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprChar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprChar___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprChar___lambda__1___closed__1;
x_2 = l_Lean_instToExprChar___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprChar___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lambda__1(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Lean_mkNatLit(x_2);
x_4 = l_Lean_instToExprChar___lambda__1___closed__4;
x_5 = l_Lean_Expr_app___override(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprChar___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprChar___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprChar___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprChar___closed__3;
x_2 = l_Lean_instToExprChar___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprChar___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprChar___lambda__1(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("String", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprString___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprString___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkStrLit), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprString___closed__4;
x_2 = l_Lean_instToExprString___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprString___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUnit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUnit___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUnit___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_2 = l_Lean_instToExprUnit___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUnit___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprUnit___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToExprUnit___lambda__1___closed__4;
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprUnit___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprUnit___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprUnit___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprUnit___closed__3;
x_2 = l_Lean_instToExprUnit___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUnit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprUnit___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToExprUnit___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_nat_dec_le(x_2, x_6);
lean_dec(x_2);
return x_7;
}
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
default: 
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 0;
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Name", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mkStr", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.ToExpr", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.ToExpr.0.Lean.Name.toExprAux.mkStr", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5;
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6;
x_3 = lean_unsigned_to_nat(63u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Nat_repr(x_2);
x_5 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3;
x_8 = l_Lean_Name_str___override(x_7, x_6);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_8, x_9);
x_11 = l_Array_reverse___rarg(x_3);
x_12 = l_Lean_mkAppN(x_10, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = l_Lean_mkStrLit(x_14);
x_18 = lean_array_push(x_3, x_17);
x_1 = x_13;
x_2 = x_16;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__8;
x_21 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("anonymous", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2;
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("str", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2;
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("num", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2;
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_3);
x_6 = l_Lean_mkStrLit(x_4);
x_7 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6;
x_8 = l_Lean_mkAppB(x_7, x_5, x_6);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_9);
x_12 = l_Lean_mkNatLit(x_10);
x_13 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__9;
x_14 = l_Lean_mkAppB(x_13, x_11, x_12);
return x_14;
}
}
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__1;
x_6 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(x_1, x_2, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_instToExprName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprName___closed__2;
x_2 = l_Lean_instToExprName___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprName___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("none", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprOption___rarg___lambda__1___closed__1;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprOption___rarg___lambda__1___closed__3;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("some", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprOption___rarg___lambda__1___closed__1;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprOption___rarg___lambda__1___closed__7;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = l_Lean_instToExprOption___rarg___lambda__1___closed__5;
x_5 = l_Lean_Expr_app___override(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_1(x_7, x_6);
x_9 = l_Lean_instToExprOption___rarg___lambda__1___closed__8;
x_10 = l_Lean_mkAppB(x_9, x_1, x_8);
return x_10;
}
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprOption___rarg___closed__1;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOption___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_instToExprOption___rarg___lambda__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_Lean_instToExprOption___rarg___closed__2;
x_5 = l_Lean_Expr_app___override(x_4, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprOption___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_1(x_7, x_5);
lean_inc(x_3);
x_9 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg(x_1, x_2, x_3, x_6);
x_10 = l_Lean_mkAppB(x_3, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("List", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nil", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__1;
x_2 = l_Lean_instToExprList___rarg___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__3;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cons", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__1;
x_2 = l_Lean_instToExprList___rarg___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__6;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprList___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprList___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__8;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_instToExprList___rarg___closed__4;
lean_inc(x_2);
x_4 = l_Lean_Expr_app___override(x_3, x_2);
x_5 = l_Lean_instToExprList___rarg___closed__7;
lean_inc(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg___boxed), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
x_8 = l_Lean_instToExprList___rarg___closed__9;
x_9 = l_Lean_Expr_app___override(x_8, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprList___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprArray___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toArray", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprArray___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__1;
x_2 = l_Lean_instToExprArray___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprArray___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprArray___rarg___lambda__1___closed__2;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprArray___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__3;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArray___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_instToExprArray___rarg___lambda__1___closed__4;
lean_inc(x_1);
x_5 = l_Lean_Expr_app___override(x_4, x_1);
x_6 = l_Lean_instToExprList___rarg___closed__7;
lean_inc(x_1);
x_7 = l_Lean_Expr_app___override(x_6, x_1);
x_8 = lean_array_to_list(lean_box(0), x_3);
x_9 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___rarg(x_2, x_5, x_7, x_8);
lean_dec(x_5);
x_10 = l_Lean_instToExprArray___rarg___lambda__1___closed__3;
x_11 = l_Lean_mkAppB(x_10, x_1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_instToExprArray___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Array", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprArray___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprArray___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprArray___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprArray___rarg___closed__2;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_instToExprArray___rarg___lambda__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_Lean_instToExprArray___rarg___closed__3;
x_5 = l_Lean_Expr_app___override(x_4, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprArray___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprProd___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Prod", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprProd___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprProd___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprProd___rarg___lambda__1___closed__1;
x_2 = l_Lean_instToExprProd___rarg___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprProd___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_instToExprOption___rarg___lambda__1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprProd___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprProd___rarg___lambda__1___closed__3;
x_2 = l_Lean_instToExprProd___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProd___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_8, x_6);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_1(x_10, x_7);
x_12 = l_Lean_instToExprProd___rarg___lambda__1___closed__5;
x_13 = l_Lean_mkApp4(x_12, x_3, x_4, x_9, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_instToExprProd___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprProd___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprProd___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprProd___rarg___closed__1;
x_2 = l_Lean_instToExprProd___rarg___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProd___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_instToExprProd___rarg___lambda__1), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
x_6 = l_Lean_instToExprProd___rarg___closed__2;
x_7 = l_Lean_mkAppB(x_6, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instToExprProd___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Literal", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("natVal", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l_Lean_instToExprLiteral___lambda__1___closed__1;
x_3 = l_Lean_instToExprLiteral___lambda__1___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprLiteral___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("strVal", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l_Lean_instToExprLiteral___lambda__1___closed__1;
x_3 = l_Lean_instToExprLiteral___lambda__1___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprLiteral___lambda__1___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Expr_lit___override(x_1);
x_3 = l_Lean_instToExprLiteral___lambda__1___closed__4;
x_4 = l_Lean_Expr_app___override(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_lit___override(x_1);
x_6 = l_Lean_instToExprLiteral___lambda__1___closed__7;
x_7 = l_Lean_Expr_app___override(x_6, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l_Lean_instToExprLiteral___lambda__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprLiteral___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprLiteral___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprLiteral___closed__3;
x_2 = l_Lean_instToExprLiteral___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprLiteral___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FVarId", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l_Lean_instToExprFVarId___lambda__1___closed__1;
x_3 = l_Lean_instToExprProd___rarg___lambda__1___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprFVarId___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_1);
x_3 = l_Lean_instToExprFVarId___lambda__1___closed__3;
x_4 = l_Lean_Expr_app___override(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1;
x_2 = l_Lean_instToExprFVarId___lambda__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprFVarId___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprFVarId___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprFVarId___closed__3;
x_2 = l_Lean_instToExprFVarId___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToExprFVarId___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Expr_toCtorIfLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = lean_uint32_to_nat(x_6);
x_8 = l_Lean_mkNatLit(x_7);
x_9 = l_Lean_instToExprChar___lambda__1___closed__4;
x_10 = l_Lean_Expr_app___override(x_9, x_8);
lean_inc(x_2);
x_11 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Expr_toCtorIfLit___spec__1(x_1, x_2, x_5);
x_12 = l_Lean_mkAppB(x_2, x_10, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprNat___closed__1;
x_2 = l_Lean_Expr_toCtorIfLit___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_toCtorIfLit___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("zero", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprNat___closed__1;
x_2 = l_Lean_Expr_toCtorIfLit___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_toCtorIfLit___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprString___closed__1;
x_2 = l_Lean_instToExprProd___rarg___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_toCtorIfLit___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprChar___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__4;
x_2 = l_Lean_Expr_toCtorIfLit___closed__9;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_toCtorIfLit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instToExprList___rarg___closed__7;
x_2 = l_Lean_Expr_toCtorIfLit___closed__9;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toCtorIfLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_mkRawNatLit(x_7);
x_9 = l_Lean_Expr_toCtorIfLit___closed__3;
x_10 = l_Lean_Expr_app___override(x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = l_Lean_Expr_toCtorIfLit___closed__6;
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_string_data(x_12);
x_14 = l_Lean_Expr_toCtorIfLit___closed__10;
x_15 = l_Lean_Expr_toCtorIfLit___closed__11;
x_16 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Expr_toCtorIfLit___spec__1(x_14, x_15, x_13);
x_17 = l_Lean_Expr_toCtorIfLit___closed__8;
x_18 = l_Lean_Expr_app___override(x_17, x_16);
return x_18;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Expr_toCtorIfLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at_Lean_Expr_toCtorIfLit___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToExprNat___closed__1 = _init_l_Lean_instToExprNat___closed__1();
lean_mark_persistent(l_Lean_instToExprNat___closed__1);
l_Lean_instToExprNat___closed__2 = _init_l_Lean_instToExprNat___closed__2();
lean_mark_persistent(l_Lean_instToExprNat___closed__2);
l_Lean_instToExprNat___closed__3 = _init_l_Lean_instToExprNat___closed__3();
lean_mark_persistent(l_Lean_instToExprNat___closed__3);
l_Lean_instToExprNat___closed__4 = _init_l_Lean_instToExprNat___closed__4();
lean_mark_persistent(l_Lean_instToExprNat___closed__4);
l_Lean_instToExprNat___closed__5 = _init_l_Lean_instToExprNat___closed__5();
lean_mark_persistent(l_Lean_instToExprNat___closed__5);
l_Lean_instToExprNat = _init_l_Lean_instToExprNat();
lean_mark_persistent(l_Lean_instToExprNat);
l_Lean_instToExprBool___lambda__1___closed__1 = _init_l_Lean_instToExprBool___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprBool___lambda__1___closed__1);
l_Lean_instToExprBool___lambda__1___closed__2 = _init_l_Lean_instToExprBool___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprBool___lambda__1___closed__2);
l_Lean_instToExprBool___lambda__1___closed__3 = _init_l_Lean_instToExprBool___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprBool___lambda__1___closed__3);
l_Lean_instToExprBool___lambda__1___closed__4 = _init_l_Lean_instToExprBool___lambda__1___closed__4();
lean_mark_persistent(l_Lean_instToExprBool___lambda__1___closed__4);
l_Lean_instToExprBool___lambda__1___closed__5 = _init_l_Lean_instToExprBool___lambda__1___closed__5();
lean_mark_persistent(l_Lean_instToExprBool___lambda__1___closed__5);
l_Lean_instToExprBool___lambda__1___closed__6 = _init_l_Lean_instToExprBool___lambda__1___closed__6();
lean_mark_persistent(l_Lean_instToExprBool___lambda__1___closed__6);
l_Lean_instToExprBool___lambda__1___closed__7 = _init_l_Lean_instToExprBool___lambda__1___closed__7();
lean_mark_persistent(l_Lean_instToExprBool___lambda__1___closed__7);
l_Lean_instToExprBool___closed__1 = _init_l_Lean_instToExprBool___closed__1();
lean_mark_persistent(l_Lean_instToExprBool___closed__1);
l_Lean_instToExprBool___closed__2 = _init_l_Lean_instToExprBool___closed__2();
lean_mark_persistent(l_Lean_instToExprBool___closed__2);
l_Lean_instToExprBool___closed__3 = _init_l_Lean_instToExprBool___closed__3();
lean_mark_persistent(l_Lean_instToExprBool___closed__3);
l_Lean_instToExprBool___closed__4 = _init_l_Lean_instToExprBool___closed__4();
lean_mark_persistent(l_Lean_instToExprBool___closed__4);
l_Lean_instToExprBool = _init_l_Lean_instToExprBool();
lean_mark_persistent(l_Lean_instToExprBool);
l_Lean_instToExprChar___lambda__1___closed__1 = _init_l_Lean_instToExprChar___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprChar___lambda__1___closed__1);
l_Lean_instToExprChar___lambda__1___closed__2 = _init_l_Lean_instToExprChar___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprChar___lambda__1___closed__2);
l_Lean_instToExprChar___lambda__1___closed__3 = _init_l_Lean_instToExprChar___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprChar___lambda__1___closed__3);
l_Lean_instToExprChar___lambda__1___closed__4 = _init_l_Lean_instToExprChar___lambda__1___closed__4();
lean_mark_persistent(l_Lean_instToExprChar___lambda__1___closed__4);
l_Lean_instToExprChar___closed__1 = _init_l_Lean_instToExprChar___closed__1();
lean_mark_persistent(l_Lean_instToExprChar___closed__1);
l_Lean_instToExprChar___closed__2 = _init_l_Lean_instToExprChar___closed__2();
lean_mark_persistent(l_Lean_instToExprChar___closed__2);
l_Lean_instToExprChar___closed__3 = _init_l_Lean_instToExprChar___closed__3();
lean_mark_persistent(l_Lean_instToExprChar___closed__3);
l_Lean_instToExprChar___closed__4 = _init_l_Lean_instToExprChar___closed__4();
lean_mark_persistent(l_Lean_instToExprChar___closed__4);
l_Lean_instToExprChar = _init_l_Lean_instToExprChar();
lean_mark_persistent(l_Lean_instToExprChar);
l_Lean_instToExprString___closed__1 = _init_l_Lean_instToExprString___closed__1();
lean_mark_persistent(l_Lean_instToExprString___closed__1);
l_Lean_instToExprString___closed__2 = _init_l_Lean_instToExprString___closed__2();
lean_mark_persistent(l_Lean_instToExprString___closed__2);
l_Lean_instToExprString___closed__3 = _init_l_Lean_instToExprString___closed__3();
lean_mark_persistent(l_Lean_instToExprString___closed__3);
l_Lean_instToExprString___closed__4 = _init_l_Lean_instToExprString___closed__4();
lean_mark_persistent(l_Lean_instToExprString___closed__4);
l_Lean_instToExprString___closed__5 = _init_l_Lean_instToExprString___closed__5();
lean_mark_persistent(l_Lean_instToExprString___closed__5);
l_Lean_instToExprString = _init_l_Lean_instToExprString();
lean_mark_persistent(l_Lean_instToExprString);
l_Lean_instToExprUnit___lambda__1___closed__1 = _init_l_Lean_instToExprUnit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprUnit___lambda__1___closed__1);
l_Lean_instToExprUnit___lambda__1___closed__2 = _init_l_Lean_instToExprUnit___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprUnit___lambda__1___closed__2);
l_Lean_instToExprUnit___lambda__1___closed__3 = _init_l_Lean_instToExprUnit___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprUnit___lambda__1___closed__3);
l_Lean_instToExprUnit___lambda__1___closed__4 = _init_l_Lean_instToExprUnit___lambda__1___closed__4();
lean_mark_persistent(l_Lean_instToExprUnit___lambda__1___closed__4);
l_Lean_instToExprUnit___closed__1 = _init_l_Lean_instToExprUnit___closed__1();
lean_mark_persistent(l_Lean_instToExprUnit___closed__1);
l_Lean_instToExprUnit___closed__2 = _init_l_Lean_instToExprUnit___closed__2();
lean_mark_persistent(l_Lean_instToExprUnit___closed__2);
l_Lean_instToExprUnit___closed__3 = _init_l_Lean_instToExprUnit___closed__3();
lean_mark_persistent(l_Lean_instToExprUnit___closed__3);
l_Lean_instToExprUnit___closed__4 = _init_l_Lean_instToExprUnit___closed__4();
lean_mark_persistent(l_Lean_instToExprUnit___closed__4);
l_Lean_instToExprUnit = _init_l_Lean_instToExprUnit();
lean_mark_persistent(l_Lean_instToExprUnit);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__8 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__8();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__8);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__9 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__9();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__9);
l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__1 = _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__1();
lean_mark_persistent(l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__1);
l_Lean_instToExprName___closed__1 = _init_l_Lean_instToExprName___closed__1();
lean_mark_persistent(l_Lean_instToExprName___closed__1);
l_Lean_instToExprName___closed__2 = _init_l_Lean_instToExprName___closed__2();
lean_mark_persistent(l_Lean_instToExprName___closed__2);
l_Lean_instToExprName___closed__3 = _init_l_Lean_instToExprName___closed__3();
lean_mark_persistent(l_Lean_instToExprName___closed__3);
l_Lean_instToExprName = _init_l_Lean_instToExprName();
lean_mark_persistent(l_Lean_instToExprName);
l_Lean_instToExprOption___rarg___lambda__1___closed__1 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__1);
l_Lean_instToExprOption___rarg___lambda__1___closed__2 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__2);
l_Lean_instToExprOption___rarg___lambda__1___closed__3 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__3);
l_Lean_instToExprOption___rarg___lambda__1___closed__4 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__4);
l_Lean_instToExprOption___rarg___lambda__1___closed__5 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__5);
l_Lean_instToExprOption___rarg___lambda__1___closed__6 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__6();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__6);
l_Lean_instToExprOption___rarg___lambda__1___closed__7 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__7();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__7);
l_Lean_instToExprOption___rarg___lambda__1___closed__8 = _init_l_Lean_instToExprOption___rarg___lambda__1___closed__8();
lean_mark_persistent(l_Lean_instToExprOption___rarg___lambda__1___closed__8);
l_Lean_instToExprOption___rarg___closed__1 = _init_l_Lean_instToExprOption___rarg___closed__1();
lean_mark_persistent(l_Lean_instToExprOption___rarg___closed__1);
l_Lean_instToExprOption___rarg___closed__2 = _init_l_Lean_instToExprOption___rarg___closed__2();
lean_mark_persistent(l_Lean_instToExprOption___rarg___closed__2);
l_Lean_instToExprList___rarg___closed__1 = _init_l_Lean_instToExprList___rarg___closed__1();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__1);
l_Lean_instToExprList___rarg___closed__2 = _init_l_Lean_instToExprList___rarg___closed__2();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__2);
l_Lean_instToExprList___rarg___closed__3 = _init_l_Lean_instToExprList___rarg___closed__3();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__3);
l_Lean_instToExprList___rarg___closed__4 = _init_l_Lean_instToExprList___rarg___closed__4();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__4);
l_Lean_instToExprList___rarg___closed__5 = _init_l_Lean_instToExprList___rarg___closed__5();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__5);
l_Lean_instToExprList___rarg___closed__6 = _init_l_Lean_instToExprList___rarg___closed__6();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__6);
l_Lean_instToExprList___rarg___closed__7 = _init_l_Lean_instToExprList___rarg___closed__7();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__7);
l_Lean_instToExprList___rarg___closed__8 = _init_l_Lean_instToExprList___rarg___closed__8();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__8);
l_Lean_instToExprList___rarg___closed__9 = _init_l_Lean_instToExprList___rarg___closed__9();
lean_mark_persistent(l_Lean_instToExprList___rarg___closed__9);
l_Lean_instToExprArray___rarg___lambda__1___closed__1 = _init_l_Lean_instToExprArray___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprArray___rarg___lambda__1___closed__1);
l_Lean_instToExprArray___rarg___lambda__1___closed__2 = _init_l_Lean_instToExprArray___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprArray___rarg___lambda__1___closed__2);
l_Lean_instToExprArray___rarg___lambda__1___closed__3 = _init_l_Lean_instToExprArray___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprArray___rarg___lambda__1___closed__3);
l_Lean_instToExprArray___rarg___lambda__1___closed__4 = _init_l_Lean_instToExprArray___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_instToExprArray___rarg___lambda__1___closed__4);
l_Lean_instToExprArray___rarg___closed__1 = _init_l_Lean_instToExprArray___rarg___closed__1();
lean_mark_persistent(l_Lean_instToExprArray___rarg___closed__1);
l_Lean_instToExprArray___rarg___closed__2 = _init_l_Lean_instToExprArray___rarg___closed__2();
lean_mark_persistent(l_Lean_instToExprArray___rarg___closed__2);
l_Lean_instToExprArray___rarg___closed__3 = _init_l_Lean_instToExprArray___rarg___closed__3();
lean_mark_persistent(l_Lean_instToExprArray___rarg___closed__3);
l_Lean_instToExprProd___rarg___lambda__1___closed__1 = _init_l_Lean_instToExprProd___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprProd___rarg___lambda__1___closed__1);
l_Lean_instToExprProd___rarg___lambda__1___closed__2 = _init_l_Lean_instToExprProd___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprProd___rarg___lambda__1___closed__2);
l_Lean_instToExprProd___rarg___lambda__1___closed__3 = _init_l_Lean_instToExprProd___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprProd___rarg___lambda__1___closed__3);
l_Lean_instToExprProd___rarg___lambda__1___closed__4 = _init_l_Lean_instToExprProd___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_instToExprProd___rarg___lambda__1___closed__4);
l_Lean_instToExprProd___rarg___lambda__1___closed__5 = _init_l_Lean_instToExprProd___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lean_instToExprProd___rarg___lambda__1___closed__5);
l_Lean_instToExprProd___rarg___closed__1 = _init_l_Lean_instToExprProd___rarg___closed__1();
lean_mark_persistent(l_Lean_instToExprProd___rarg___closed__1);
l_Lean_instToExprProd___rarg___closed__2 = _init_l_Lean_instToExprProd___rarg___closed__2();
lean_mark_persistent(l_Lean_instToExprProd___rarg___closed__2);
l_Lean_instToExprLiteral___lambda__1___closed__1 = _init_l_Lean_instToExprLiteral___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprLiteral___lambda__1___closed__1);
l_Lean_instToExprLiteral___lambda__1___closed__2 = _init_l_Lean_instToExprLiteral___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprLiteral___lambda__1___closed__2);
l_Lean_instToExprLiteral___lambda__1___closed__3 = _init_l_Lean_instToExprLiteral___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprLiteral___lambda__1___closed__3);
l_Lean_instToExprLiteral___lambda__1___closed__4 = _init_l_Lean_instToExprLiteral___lambda__1___closed__4();
lean_mark_persistent(l_Lean_instToExprLiteral___lambda__1___closed__4);
l_Lean_instToExprLiteral___lambda__1___closed__5 = _init_l_Lean_instToExprLiteral___lambda__1___closed__5();
lean_mark_persistent(l_Lean_instToExprLiteral___lambda__1___closed__5);
l_Lean_instToExprLiteral___lambda__1___closed__6 = _init_l_Lean_instToExprLiteral___lambda__1___closed__6();
lean_mark_persistent(l_Lean_instToExprLiteral___lambda__1___closed__6);
l_Lean_instToExprLiteral___lambda__1___closed__7 = _init_l_Lean_instToExprLiteral___lambda__1___closed__7();
lean_mark_persistent(l_Lean_instToExprLiteral___lambda__1___closed__7);
l_Lean_instToExprLiteral___closed__1 = _init_l_Lean_instToExprLiteral___closed__1();
lean_mark_persistent(l_Lean_instToExprLiteral___closed__1);
l_Lean_instToExprLiteral___closed__2 = _init_l_Lean_instToExprLiteral___closed__2();
lean_mark_persistent(l_Lean_instToExprLiteral___closed__2);
l_Lean_instToExprLiteral___closed__3 = _init_l_Lean_instToExprLiteral___closed__3();
lean_mark_persistent(l_Lean_instToExprLiteral___closed__3);
l_Lean_instToExprLiteral___closed__4 = _init_l_Lean_instToExprLiteral___closed__4();
lean_mark_persistent(l_Lean_instToExprLiteral___closed__4);
l_Lean_instToExprLiteral = _init_l_Lean_instToExprLiteral();
lean_mark_persistent(l_Lean_instToExprLiteral);
l_Lean_instToExprFVarId___lambda__1___closed__1 = _init_l_Lean_instToExprFVarId___lambda__1___closed__1();
lean_mark_persistent(l_Lean_instToExprFVarId___lambda__1___closed__1);
l_Lean_instToExprFVarId___lambda__1___closed__2 = _init_l_Lean_instToExprFVarId___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instToExprFVarId___lambda__1___closed__2);
l_Lean_instToExprFVarId___lambda__1___closed__3 = _init_l_Lean_instToExprFVarId___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instToExprFVarId___lambda__1___closed__3);
l_Lean_instToExprFVarId___closed__1 = _init_l_Lean_instToExprFVarId___closed__1();
lean_mark_persistent(l_Lean_instToExprFVarId___closed__1);
l_Lean_instToExprFVarId___closed__2 = _init_l_Lean_instToExprFVarId___closed__2();
lean_mark_persistent(l_Lean_instToExprFVarId___closed__2);
l_Lean_instToExprFVarId___closed__3 = _init_l_Lean_instToExprFVarId___closed__3();
lean_mark_persistent(l_Lean_instToExprFVarId___closed__3);
l_Lean_instToExprFVarId___closed__4 = _init_l_Lean_instToExprFVarId___closed__4();
lean_mark_persistent(l_Lean_instToExprFVarId___closed__4);
l_Lean_instToExprFVarId = _init_l_Lean_instToExprFVarId();
lean_mark_persistent(l_Lean_instToExprFVarId);
l_Lean_Expr_toCtorIfLit___closed__1 = _init_l_Lean_Expr_toCtorIfLit___closed__1();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__1);
l_Lean_Expr_toCtorIfLit___closed__2 = _init_l_Lean_Expr_toCtorIfLit___closed__2();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__2);
l_Lean_Expr_toCtorIfLit___closed__3 = _init_l_Lean_Expr_toCtorIfLit___closed__3();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__3);
l_Lean_Expr_toCtorIfLit___closed__4 = _init_l_Lean_Expr_toCtorIfLit___closed__4();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__4);
l_Lean_Expr_toCtorIfLit___closed__5 = _init_l_Lean_Expr_toCtorIfLit___closed__5();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__5);
l_Lean_Expr_toCtorIfLit___closed__6 = _init_l_Lean_Expr_toCtorIfLit___closed__6();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__6);
l_Lean_Expr_toCtorIfLit___closed__7 = _init_l_Lean_Expr_toCtorIfLit___closed__7();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__7);
l_Lean_Expr_toCtorIfLit___closed__8 = _init_l_Lean_Expr_toCtorIfLit___closed__8();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__8);
l_Lean_Expr_toCtorIfLit___closed__9 = _init_l_Lean_Expr_toCtorIfLit___closed__9();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__9);
l_Lean_Expr_toCtorIfLit___closed__10 = _init_l_Lean_Expr_toCtorIfLit___closed__10();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__10);
l_Lean_Expr_toCtorIfLit___closed__11 = _init_l_Lean_Expr_toCtorIfLit___closed__11();
lean_mark_persistent(l_Lean_Expr_toCtorIfLit___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
