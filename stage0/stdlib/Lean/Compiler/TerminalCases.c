// Lean compiler output
// Module: Lean.Compiler.TerminalCases
// Imports: Init Lean.Meta.Check Lean.Compiler.Util Lean.Compiler.Decl Lean.Compiler.CompilerM
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1;
lean_object* l_Lean_Compiler_Decl_mapValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Compiler_attachJp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Compiler_instMonadLCtxCompilerM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_terminalCases___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkJpDeclIfNotSimple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_1, x_13);
lean_dec(x_1);
x_15 = lean_array_get_size(x_5);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fget(x_5, x_2);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_5, x_2, x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(x_19, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_fset(x_21, x_2, x_23);
x_26 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_26;
x_5 = x_25;
x_9 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_7);
x_9 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1;
lean_inc(x_8);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_8, x_11);
lean_dec(x_8);
lean_inc(x_2);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_10, x_12);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_15);
x_18 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(x_15, x_16, x_15, x_17, x_13, x_3, x_4, x_5, x_6);
lean_dec(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_22 = l_Lean_mkAppN(x_21, x_20);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_26 = l_Lean_mkAppN(x_25, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(x_7, x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Compiler_mkLetUsingScope(x_10, x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_mkLambda(x_6, x_13, x_2, x_3, x_4, x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_6);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_visitLambda___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1;
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_instMonadLCtxCompilerM___spec__2___rarg), 6, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Compiler_withNewScopeImp___rarg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Compiler_mkLetDecl(x_1, x_2, x_6, x_3, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_4, x_13);
x_16 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(x_5, x_15, x_8, x_9, x_10, x_14);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_8 = lean_array_push(x_1, x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(x_2, x_8, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Compiler_mkLetUsingScope(x_10, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___closed__1;
x_16 = lean_array_push(x_15, x_3);
x_17 = l_Lean_Compiler_mkLambda(x_16, x_13, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_12 = lean_expr_instantiate_rev(x_8, x_2);
lean_dec(x_8);
x_13 = lean_expr_instantiate_rev(x_9, x_2);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = l_Lean_Compiler_isCasesApp_x3f(x_13, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_isLambda(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(x_7, x_12, x_11, x_2, x_10, x_13, x_18, x_3, x_4, x_5, x_16);
return x_19;
}
else
{
lean_object* x_20; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(x_13, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(x_7, x_12, x_11, x_2, x_10, x_21, x_23, x_3, x_4, x_5, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec(x_15);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_mkLocalDecl___boxed), 7, 3);
lean_closure_set(x_33, 0, x_7);
lean_closure_set(x_33, 1, x_12);
lean_closure_set(x_33, 2, x_32);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2), 7, 2);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_10);
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_instMonadLCtxCompilerM___spec__2___rarg), 6, 2);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_34);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Compiler_withNewScopeImp___rarg(x_35, x_3, x_4, x_5, x_29);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_5);
lean_inc(x_4);
x_39 = l_Lean_Compiler_mkJpDeclIfNotSimple(x_37, x_3, x_4, x_5, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases(x_30, x_13, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Compiler_attachJp(x_43, x_40, x_3, x_4, x_5, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_36;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_36, 0);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_36);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_14);
if (x_58 == 0)
{
return x_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_14, 0);
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_14);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_62);
x_63 = l_Lean_Compiler_isCasesApp_x3f(x_62, x_4, x_5, x_6);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases(x_70, x_62, x_3, x_4, x_5, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_62);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_63);
if (x_72 == 0)
{
return x_63;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_63, 0);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_63);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_terminalCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_Decl_terminalCases___closed__1;
x_6 = l_Lean_Compiler_Decl_mapValue(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Decl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_TerminalCases(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Decl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___closed__1);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___closed__1);
l_Lean_Compiler_Decl_terminalCases___closed__1 = _init_l_Lean_Compiler_Decl_terminalCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_terminalCases___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
