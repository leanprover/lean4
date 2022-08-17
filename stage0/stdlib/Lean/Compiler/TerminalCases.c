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
lean_object* l_Lean_Compiler_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1;
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__2;
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1;
lean_object* l_Lean_Compiler_Decl_mapValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withoutJp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_Context_jp_x3f___default;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_CasesInfo_updateResultingType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withoutJp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Compiler_mkOptJump(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withJp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withJp(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_terminalCases___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkJpDeclIfNotSimple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Compiler_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withoutJp(lean_object*);
lean_object* l_Lean_Compiler_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withJp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_TerminalCases_Context_jp_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withJp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Compiler_mkJpDeclIfNotSimple(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_apply_5(x_2, x_11, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withJp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_withJp___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withJp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_TerminalCases_withJp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withoutJp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_5(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withoutJp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_withoutJp___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_withoutJp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_TerminalCases_withoutJp___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_dec(x_1);
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_array_fget(x_5, x_2);
x_21 = lean_box(0);
x_22 = lean_array_fset(x_5, x_2, x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_fset(x_22, x_2, x_24);
x_27 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_27;
x_5 = x_26;
x_10 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_11);
x_14 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(x_11, x_12, x_11, x_13, x_3, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Expr_getAppFn(x_2);
x_18 = l_Lean_mkAppN(x_17, x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = l_Lean_Expr_getAppFn(x_2);
x_22 = l_Lean_mkAppN(x_21, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
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
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.TerminalCases", 27);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Compiler.TerminalCases.0.Lean.Compiler.TerminalCases.visitCases", 77);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__2;
x_2 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__3;
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_8);
x_10 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
lean_inc(x_2);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_11, x_13);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_14, x_15, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_st_ref_get(x_6, x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Compiler_InferType_inferType(x_17, x_23, x_5, x_6, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Compiler_CasesInfo_updateResultingType(x_1, x_14, x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_28, x_29, x_3, x_4, x_5, x_6, x_26);
lean_dec(x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__5;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2(x_32, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_14, x_34, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_34);
lean_dec(x_2);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_24);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = l_Lean_Compiler_withNewScopeImp___rarg(x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_visitLambda(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_mkLambda(x_7, x_14, x_3, x_4, x_5, x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_7);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Compiler_withNewScope___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__2(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_13 = l_Lean_Compiler_mkLetDecl(x_1, x_2, x_6, x_3, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_push(x_4, x_14);
x_17 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(x_5, x_16, x_8, x_9, x_10, x_11, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Compiler_mkLocalDecl(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_9 = lean_array_push(x_1, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
x_17 = lean_array_push(x_16, x_3);
x_18 = l_Lean_Compiler_mkLambda(x_17, x_14, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_13 = lean_expr_instantiate_rev(x_9, x_2);
lean_dec(x_9);
x_14 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_15 = l_Lean_Compiler_isCasesApp_x3f(x_14, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_isLambda(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(x_8, x_13, x_12, x_2, x_11, x_14, x_19, x_3, x_4, x_5, x_6, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda), 6, 1);
lean_closure_set(x_21, 0, x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Compiler_TerminalCases_withoutJp___rarg(x_21, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(x_8, x_13, x_12, x_2, x_11, x_23, x_25, x_3, x_4, x_5, x_6, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed), 7, 2);
lean_closure_set(x_33, 0, x_8);
lean_closure_set(x_33, 1, x_13);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3), 8, 2);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_11);
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Compiler_withNewScope___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___spec__2(x_35, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases), 7, 2);
lean_closure_set(x_39, 0, x_32);
lean_closure_set(x_39, 1, x_14);
x_40 = l_Lean_Compiler_TerminalCases_withJp___rarg(x_37, x_39, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_3);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_49);
x_50 = l_Lean_Compiler_isCasesApp_x3f(x_49, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_mkOptJump(x_3, x_49, x_4, x_5, x_6, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases(x_55, x_49, x_3, x_4, x_5, x_6, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_terminalCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Decl_terminalCases___lambda__1), 5, 0);
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
l_Lean_Compiler_TerminalCases_Context_jp_x3f___default = _init_l_Lean_Compiler_TerminalCases_Context_jp_x3f___default();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_Context_jp_x3f___default);
l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1 = _init_l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1);
l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2 = _init_l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2);
l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3 = _init_l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__1);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__2 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__2);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__3 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__3);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__4 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__4);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__5 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitCases___closed__5);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLambda___closed__1);
l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1 = _init_l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_TerminalCases_0__Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1);
l_Lean_Compiler_Decl_terminalCases___closed__1 = _init_l_Lean_Compiler_Decl_terminalCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_terminalCases___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
