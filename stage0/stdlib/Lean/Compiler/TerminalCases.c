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
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__3;
static lean_object* l_Lean_Compiler_TerminalCases_visitLambda___closed__1;
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__1;
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__4;
lean_object* l_Lean_Compiler_isLcCast_x3f(lean_object*);
uint8_t l_Lean_Compiler_compatibleTypes(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_Decl_mapValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_isLcUnreachable(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2;
static lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__1;
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_Context_jp_x3f___default;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__3;
lean_object* l_Lean_Compiler_CasesInfo_updateResultingType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__3;
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2;
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__5;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__2;
static lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLambda___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isSimpleLCNF(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__3;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__5;
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1;
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__1;
static lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__2;
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__2;
uint8_t l_Lean_Expr_isAnyType(lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__4;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__2;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_terminalCases___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitLambda___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Compiler_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isCasesApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__1;
lean_object* l_Lean_Compiler_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__4;
lean_object* l_Lean_Compiler_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_TerminalCases_Context_jp_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_23 = l_Lean_Compiler_TerminalCases_visitLambda(x_20, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1(x_11, x_12, x_11, x_13, x_3, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.TerminalCases", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.TerminalCases.visitCases", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitCases___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_TerminalCases_visitCases___closed__2;
x_2 = l_Lean_Compiler_TerminalCases_visitCases___closed__3;
x_3 = lean_unsigned_to_nat(25u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l_Lean_Compiler_TerminalCases_visitCases___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_8);
x_10 = l_Lean_Compiler_TerminalCases_visitCases___closed__1;
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
x_16 = l_Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_14, x_15, x_3, x_4, x_5, x_6, x_7);
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
x_30 = l_Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_28, x_29, x_3, x_4, x_5, x_6, x_26);
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
x_32 = l_Lean_Compiler_TerminalCases_visitCases___closed__5;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2(x_32, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_14, x_34, x_3, x_4, x_5, x_6, x_35);
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitLambda___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLambda___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = l_Lean_Compiler_withNewScopeImp___rarg(x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_visitLambda(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Compiler_TerminalCases_visitLet(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
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
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLambda___lambda__2), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_TerminalCases_visitLambda___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLambda___spec__2(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__3;
x_3 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__4;
x_4 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_5, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_4, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Compiler_InferType_inferType(x_1, x_12, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 3)
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_13, 1);
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = l_Lean_Expr_isAnyType(x_14);
lean_dec(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_13);
x_25 = l_Lean_indentExpr(x_1);
x_26 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__4;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4(x_29, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_31 = l_Lean_levelOne;
lean_ctor_set(x_13, 0, x_31);
return x_13;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_Expr_isAnyType(x_14);
lean_dec(x_14);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_indentExpr(x_1);
x_35 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__4;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4(x_38, x_2, x_3, x_4, x_5, x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_40 = l_Lean_levelOne;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcCast", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_Compiler_InferType_inferType(x_1, x_13, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_17 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3(x_15, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_2);
x_20 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3(x_2, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2;
x_27 = l_Lean_Expr_const___override(x_26, x_25);
x_28 = l_Lean_mkApp3(x_27, x_15, x_2, x_1);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2;
x_35 = l_Lean_Expr_const___override(x_34, x_33);
x_36 = l_Lean_mkApp3(x_35, x_15, x_2, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcUnreachable", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__2;
x_13 = l_Lean_Expr_const___override(x_12, x_11);
x_14 = l_Lean_Expr_app___override(x_13, x_1);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__2;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
x_21 = l_Lean_Expr_app___override(x_20, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_17 = l_Lean_Compiler_TerminalCases_visitLet(x_5, x_16, x_8, x_9, x_10, x_11, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Compiler_mkLocalDecl(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_9 = lean_array_push(x_1, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Compiler_TerminalCases_visitLet(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
x_17 = lean_array_push(x_16, x_3);
x_18 = lean_expr_abstract(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
x_22 = lean_array_push(x_21, x_3);
x_23 = lean_expr_abstract(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = l_Lean_Compiler_TerminalCases_visitCases(x_1, x_2, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.TerminalCases.visitLet", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_TerminalCases_visitCases___closed__2;
x_2 = l_Lean_Compiler_TerminalCases_visitLet___closed__1;
x_3 = lean_unsigned_to_nat(68u);
x_4 = lean_unsigned_to_nat(46u);
x_5 = l_Lean_Compiler_TerminalCases_visitCases___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_TerminalCases_visitLet___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_20 = l_Lean_Compiler_TerminalCases_visitLet___lambda__1(x_8, x_13, x_12, x_2, x_11, x_14, x_19, x_3, x_4, x_5, x_6, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Compiler_TerminalCases_visitLambda(x_14, x_21, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l_Lean_Compiler_TerminalCases_visitLet___lambda__1(x_8, x_13, x_12, x_2, x_11, x_23, x_25, x_3, x_4, x_5, x_6, x_24);
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
lean_inc(x_13);
lean_inc(x_8);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed), 7, 2);
lean_closure_set(x_33, 0, x_8);
lean_closure_set(x_33, 1, x_13);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__3), 8, 2);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_11);
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLambda___spec__2(x_35, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_37);
x_39 = l_Lean_Compiler_isSimpleLCNF(x_37, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = 0;
x_44 = l_Lean_Expr_lam___override(x_8, x_13, x_37, x_43);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Compiler_mkJpDecl(x_44, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Compiler_TerminalCases_visitLet___lambda__4(x_32, x_14, x_46, x_3, x_4, x_5, x_6, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_dec(x_39);
x_54 = 0;
x_55 = l_Lean_Expr_lam___override(x_8, x_13, x_37, x_54);
x_56 = l_Lean_Compiler_TerminalCases_visitLet___lambda__4(x_32, x_14, x_55, x_3, x_4, x_5, x_6, x_53);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
return x_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_69);
x_70 = l_Lean_Compiler_isCasesApp_x3f(x_69, x_5, x_6, x_7);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
x_78 = lean_st_ref_get(x_6, x_76);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_st_ref_get(x_4, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_77);
x_84 = l_Lean_Compiler_InferType_inferType(x_77, x_83, x_5, x_6, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 7)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 2);
lean_inc(x_88);
lean_dec(x_85);
x_89 = l_Lean_Compiler_isLcUnreachable(x_69);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
x_90 = lean_st_ref_get(x_6, x_86);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_get(x_4, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_69);
x_96 = l_Lean_Compiler_InferType_inferType(x_69, x_95, x_5, x_6, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_87);
x_99 = l_Lean_Compiler_compatibleTypes(x_97, x_87);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_Compiler_isLcCast_x3f(x_69);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Lean_Compiler_TerminalCases_visitLet___closed__4;
lean_inc(x_6);
lean_inc(x_5);
x_102 = l_Lean_Compiler_mkAuxLetDecl(x_69, x_101, x_4, x_5, x_6, x_98);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_6);
lean_inc(x_5);
x_105 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(x_103, x_87, x_3, x_4, x_5, x_6, x_104);
lean_dec(x_3);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Compiler_mkAuxLetDecl(x_106, x_101, x_4, x_5, x_6, x_107);
lean_dec(x_4);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = l_Lean_Expr_app___override(x_77, x_110);
x_112 = l_Lean_Expr_headBeta(x_111);
lean_ctor_set(x_108, 0, x_112);
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
x_115 = l_Lean_Expr_app___override(x_77, x_113);
x_116 = l_Lean_Expr_headBeta(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec(x_77);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
return x_108;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_108, 0);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_108);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_122 = !lean_is_exclusive(x_105);
if (x_122 == 0)
{
return x_105;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_105, 0);
x_124 = lean_ctor_get(x_105, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_105);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_87);
lean_dec(x_77);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = !lean_is_exclusive(x_102);
if (x_126 == 0)
{
return x_102;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_102, 0);
x_128 = lean_ctor_get(x_102, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_102);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_69);
x_130 = lean_ctor_get(x_100, 0);
lean_inc(x_130);
lean_dec(x_100);
lean_inc(x_6);
lean_inc(x_5);
x_131 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(x_130, x_87, x_3, x_4, x_5, x_6, x_98);
lean_dec(x_3);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Compiler_TerminalCases_visitLet___closed__4;
x_135 = l_Lean_Compiler_mkAuxLetDecl(x_132, x_134, x_4, x_5, x_6, x_133);
lean_dec(x_4);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = l_Lean_Expr_app___override(x_77, x_137);
x_139 = l_Lean_Expr_headBeta(x_138);
lean_ctor_set(x_135, 0, x_139);
return x_135;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_135, 0);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_135);
x_142 = l_Lean_Expr_app___override(x_77, x_140);
x_143 = l_Lean_Expr_headBeta(x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
return x_144;
}
}
else
{
uint8_t x_145; 
lean_dec(x_77);
x_145 = !lean_is_exclusive(x_135);
if (x_145 == 0)
{
return x_135;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_135, 0);
x_147 = lean_ctor_get(x_135, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_135);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_149 = !lean_is_exclusive(x_131);
if (x_149 == 0)
{
return x_131;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_131, 0);
x_151 = lean_ctor_get(x_131, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_131);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_87);
lean_dec(x_3);
x_153 = l_Lean_Compiler_TerminalCases_visitLet___closed__4;
x_154 = l_Lean_Compiler_mkAuxLetDecl(x_69, x_153, x_4, x_5, x_6, x_98);
lean_dec(x_4);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = l_Lean_Expr_app___override(x_77, x_156);
x_158 = l_Lean_Expr_headBeta(x_157);
lean_ctor_set(x_154, 0, x_158);
return x_154;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_154, 0);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_154);
x_161 = l_Lean_Expr_app___override(x_77, x_159);
x_162 = l_Lean_Expr_headBeta(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
}
else
{
uint8_t x_164; 
lean_dec(x_77);
x_164 = !lean_is_exclusive(x_154);
if (x_164 == 0)
{
return x_154;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_154, 0);
x_166 = lean_ctor_get(x_154, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_154);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_87);
lean_dec(x_77);
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_168 = !lean_is_exclusive(x_96);
if (x_168 == 0)
{
return x_96;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_96, 0);
x_170 = lean_ctor_get(x_96, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_96);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_87);
lean_dec(x_77);
lean_dec(x_69);
x_172 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5(x_88, x_3, x_4, x_5, x_6, x_86);
lean_dec(x_4);
lean_dec(x_3);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_85);
lean_dec(x_77);
lean_dec(x_69);
x_173 = lean_ctor_get(x_84, 1);
lean_inc(x_173);
lean_dec(x_84);
x_174 = l_Lean_Compiler_TerminalCases_visitLet___closed__2;
x_175 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(x_174, x_3, x_4, x_5, x_6, x_173);
return x_175;
}
}
else
{
uint8_t x_176; 
lean_dec(x_77);
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_84);
if (x_176 == 0)
{
return x_84;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_84, 0);
x_178 = lean_ctor_get(x_84, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_84);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_70, 1);
lean_inc(x_180);
lean_dec(x_70);
x_181 = lean_ctor_get(x_71, 0);
lean_inc(x_181);
lean_dec(x_71);
x_182 = l_Lean_Compiler_TerminalCases_visitCases(x_181, x_69, x_3, x_4, x_5, x_6, x_180);
return x_182;
}
}
else
{
uint8_t x_183; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = !lean_is_exclusive(x_70);
if (x_183 == 0)
{
return x_70;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_70, 0);
x_185 = lean_ctor_get(x_70, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_70);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_TerminalCases_visitLambda___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Compiler_TerminalCases_visitLet___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_TerminalCases_visitLet___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_7 = l_Lean_Compiler_TerminalCases_visitLambda(x_1, x_6, x_2, x_3, x_4, x_5);
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
l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1);
l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2);
l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__3);
l_Lean_Compiler_TerminalCases_visitCases___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__1);
l_Lean_Compiler_TerminalCases_visitCases___closed__2 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__2();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__2);
l_Lean_Compiler_TerminalCases_visitCases___closed__3 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__3();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__3);
l_Lean_Compiler_TerminalCases_visitCases___closed__4 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__4();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__4);
l_Lean_Compiler_TerminalCases_visitCases___closed__5 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__5();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__5);
l_Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLambda___lambda__2___closed__1);
l_Lean_Compiler_TerminalCases_visitLambda___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLambda___closed__1);
l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1);
l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2);
l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__1);
l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2);
l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__3);
l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__4 = _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__4();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__4);
l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__5 = _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__5();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__5);
l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6 = _init_l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6);
l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__1 = _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__1);
l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__2 = _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__2);
l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__3 = _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__3();
lean_mark_persistent(l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__3);
l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__4 = _init_l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__4();
lean_mark_persistent(l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__4);
l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__1 = _init_l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__1);
l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2 = _init_l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2);
l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__1 = _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__1);
l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__2 = _init_l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__2);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1);
l_Lean_Compiler_TerminalCases_visitLet___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitLet___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___closed__1);
l_Lean_Compiler_TerminalCases_visitLet___closed__2 = _init_l_Lean_Compiler_TerminalCases_visitLet___closed__2();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___closed__2);
l_Lean_Compiler_TerminalCases_visitLet___closed__3 = _init_l_Lean_Compiler_TerminalCases_visitLet___closed__3();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___closed__3);
l_Lean_Compiler_TerminalCases_visitLet___closed__4 = _init_l_Lean_Compiler_TerminalCases_visitLet___closed__4();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___closed__4);
l_Lean_Compiler_Decl_terminalCases___closed__1 = _init_l_Lean_Compiler_Decl_terminalCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_terminalCases___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
