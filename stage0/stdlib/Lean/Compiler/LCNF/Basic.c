// Lean compiler output
// Module: Lean.Compiler.LCNF.Basic
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__2;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedParam___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_size_go___spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedParam___closed__1;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCasesCore(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCasesCore___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCode___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___spec__1(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_getCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_size_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isDecl___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDeclCore___rarg(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_size(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDeclCore(lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedParam___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedParam___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Expr_fvar___override(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLetDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedLetDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedLetDecl___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDeclCore___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1;
x_4 = l_Lean_Compiler_LCNF_instInhabitedParam___closed__1;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDeclCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instInhabitedFunDeclCore___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCasesCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam___closed__1;
x_3 = l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCasesCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCasesCore___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedCode___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_getCode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_2);
return x_13;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_16 = lean_ptr_addr(x_2);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Basic", 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateContImp", 68);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1;
x_2 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__2;
x_3 = lean_unsigned_to_nat(88u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
case 1:
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_15 = lean_ptr_addr(x_2);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
else
{
lean_dec(x_12);
lean_dec(x_2);
return x_1;
}
}
case 2:
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_24 = lean_ptr_addr(x_2);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_dec(x_28);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_2);
return x_29;
}
}
else
{
lean_dec(x_21);
lean_dec(x_2);
return x_1;
}
}
default: 
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__4;
x_31 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___spec__1(x_30);
return x_31;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isDecl(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 2:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
default: 
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Code_isDecl(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_size_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_AltCore_getCode(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_10 = l_Lean_Compiler_LCNF_Code_size_go(x_7, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_Code_size_go(x_9, x_2);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 4);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_LCNF_Code_size_go(x_14, x_2);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
case 4:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_19;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_19;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_size_go___spec__1(x_20, x_25, x_26, x_19);
lean_dec(x_20);
return x_27;
}
}
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_size_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Code_size_go___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_Code_size_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_size(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Compiler_LCNF_Code_size_go(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedParam___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedParam___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedParam___closed__1);
l_Lean_Compiler_LCNF_instInhabitedParam___closed__2 = _init_l_Lean_Compiler_LCNF_instInhabitedParam___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedParam___closed__2);
l_Lean_Compiler_LCNF_instInhabitedParam = _init_l_Lean_Compiler_LCNF_instInhabitedParam();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedParam);
l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg___closed__1);
l_Lean_Compiler_LCNF_instInhabitedLetDecl___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedLetDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedLetDecl___closed__1);
l_Lean_Compiler_LCNF_instInhabitedLetDecl = _init_l_Lean_Compiler_LCNF_instInhabitedLetDecl();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedLetDecl);
l_Lean_Compiler_LCNF_instInhabitedCasesCore___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedCasesCore___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCasesCore___closed__1);
l_Lean_Compiler_LCNF_instInhabitedCode___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCode___closed__1);
l_Lean_Compiler_LCNF_instInhabitedCode = _init_l_Lean_Compiler_LCNF_instInhabitedCode();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCode);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__2 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__2);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__3 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__3);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__4 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
