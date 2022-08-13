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
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3___closed__1;
lean_object* l_Lean_Compiler_isLcCast_x3f(lean_object*);
uint8_t l_Lean_Compiler_compatibleTypes(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_Decl_mapValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_isLcUnreachable(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2;
static lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___closed__1;
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_Context_jp_x3f___default;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__2;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getLevel___at_Lean_Compiler_TerminalCases_visitLet___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitAlt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__3;
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__5;
static lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__2;
static lean_object* l_Lean_throwError___at_Lean_Compiler_TerminalCases_visitLet___spec__4___closed__5;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__2;
lean_object* l_Lean_Compiler_isSimpleLCNF(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__3;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__1;
static lean_object* l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2___closed__1;
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
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__6;
lean_object* l_Lean_Compiler_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Compiler_mkLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitAlt___closed__1;
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitAlt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = l_Lean_Compiler_withNewScopeImp___rarg(x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_visitBoundedLambda(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Compiler_TerminalCases_visitLet(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_3, x_4, x_5, x_12);
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
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitAlt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitAlt___lambda__2), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitAlt___lambda__1___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_Compiler_TerminalCases_visitAlt___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitAlt___spec__2(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__3;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.TerminalCases", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.TerminalCases.visitLet", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___closed__1;
x_2 = l_Lean_Compiler_TerminalCases_visitLet___closed__2;
x_3 = lean_unsigned_to_nat(78u);
x_4 = lean_unsigned_to_nat(46u);
x_5 = l_Lean_Compiler_TerminalCases_visitLet___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_TerminalCases_visitLet___closed__5;
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
lean_object* x_21; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Compiler_TerminalCases_visitLambda(x_14, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_TerminalCases_visitLet___lambda__1(x_8, x_13, x_12, x_2, x_11, x_22, x_24, x_3, x_4, x_5, x_6, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_8);
x_32 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed), 7, 2);
lean_closure_set(x_32, 0, x_8);
lean_closure_set(x_32, 1, x_13);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__3), 8, 2);
lean_closure_set(x_33, 0, x_2);
lean_closure_set(x_33, 1, x_11);
x_34 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg), 7, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitAlt___spec__2(x_34, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_38 = l_Lean_Compiler_isSimpleLCNF(x_36, x_5, x_6, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = 0;
x_43 = l_Lean_Expr_lam___override(x_8, x_13, x_36, x_42);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Compiler_mkJpDecl(x_43, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_TerminalCases_visitLet___lambda__4(x_31, x_14, x_45, x_3, x_4, x_5, x_6, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_dec(x_38);
x_53 = 0;
x_54 = l_Lean_Expr_lam___override(x_8, x_13, x_36, x_53);
x_55 = l_Lean_Compiler_TerminalCases_visitLet___lambda__4(x_31, x_14, x_54, x_3, x_4, x_5, x_6, x_52);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
return x_35;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_35);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_15);
if (x_64 == 0)
{
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_68);
x_69 = l_Lean_Compiler_isCasesApp_x3f(x_68, x_5, x_6, x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_ctor_get(x_69, 0);
lean_dec(x_73);
x_74 = l_Lean_Expr_isLambda(x_68);
if (x_74 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
else
{
lean_object* x_75; 
lean_free_object(x_69);
x_75 = l_Lean_Compiler_TerminalCases_visitLambda(x_68, x_3, x_4, x_5, x_6, x_72);
return x_75;
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_dec(x_69);
x_77 = l_Lean_Expr_isLambda(x_68);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; 
x_79 = l_Lean_Compiler_TerminalCases_visitLambda(x_68, x_3, x_4, x_5, x_6, x_76);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_69, 1);
lean_inc(x_80);
lean_dec(x_69);
x_81 = lean_ctor_get(x_3, 0);
lean_inc(x_81);
x_82 = lean_st_ref_get(x_6, x_80);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_st_ref_get(x_4, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_81);
x_88 = l_Lean_Compiler_InferType_inferType(x_81, x_87, x_5, x_6, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 7)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 2);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l_Lean_Compiler_isLcUnreachable(x_68);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_92);
x_94 = lean_st_ref_get(x_6, x_90);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_4, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_68);
x_100 = l_Lean_Compiler_InferType_inferType(x_68, x_99, x_5, x_6, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_91);
x_103 = l_Lean_Compiler_compatibleTypes(x_101, x_91);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = l_Lean_Compiler_isLcCast_x3f(x_68);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_Compiler_TerminalCases_visitLet___closed__6;
lean_inc(x_6);
lean_inc(x_5);
x_106 = l_Lean_Compiler_mkAuxLetDecl(x_68, x_105, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_6);
lean_inc(x_5);
x_109 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(x_107, x_91, x_3, x_4, x_5, x_6, x_108);
lean_dec(x_3);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Lean_Compiler_mkAuxLetDecl(x_110, x_105, x_4, x_5, x_6, x_111);
lean_dec(x_4);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = l_Lean_Expr_app___override(x_81, x_114);
x_116 = l_Lean_Expr_headBeta(x_115);
lean_ctor_set(x_112, 0, x_116);
return x_112;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_112, 0);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_112);
x_119 = l_Lean_Expr_app___override(x_81, x_117);
x_120 = l_Lean_Expr_headBeta(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_81);
x_122 = !lean_is_exclusive(x_112);
if (x_122 == 0)
{
return x_112;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_112, 0);
x_124 = lean_ctor_get(x_112, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_112);
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
lean_dec(x_81);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_126 = !lean_is_exclusive(x_109);
if (x_126 == 0)
{
return x_109;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_109, 0);
x_128 = lean_ctor_get(x_109, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_109);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_91);
lean_dec(x_81);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_130 = !lean_is_exclusive(x_106);
if (x_130 == 0)
{
return x_106;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_106, 0);
x_132 = lean_ctor_get(x_106, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_106);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_68);
x_134 = lean_ctor_get(x_104, 0);
lean_inc(x_134);
lean_dec(x_104);
lean_inc(x_6);
lean_inc(x_5);
x_135 = l_Lean_Compiler_mkLcCast___at_Lean_Compiler_TerminalCases_visitLet___spec__2(x_134, x_91, x_3, x_4, x_5, x_6, x_102);
lean_dec(x_3);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Compiler_TerminalCases_visitLet___closed__6;
x_139 = l_Lean_Compiler_mkAuxLetDecl(x_136, x_138, x_4, x_5, x_6, x_137);
lean_dec(x_4);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = l_Lean_Expr_app___override(x_81, x_141);
x_143 = l_Lean_Expr_headBeta(x_142);
lean_ctor_set(x_139, 0, x_143);
return x_139;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_139, 0);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_139);
x_146 = l_Lean_Expr_app___override(x_81, x_144);
x_147 = l_Lean_Expr_headBeta(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
}
else
{
uint8_t x_149; 
lean_dec(x_81);
x_149 = !lean_is_exclusive(x_139);
if (x_149 == 0)
{
return x_139;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_139, 0);
x_151 = lean_ctor_get(x_139, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_139);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_81);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_153 = !lean_is_exclusive(x_135);
if (x_153 == 0)
{
return x_135;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_135, 0);
x_155 = lean_ctor_get(x_135, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_135);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_91);
lean_dec(x_3);
x_157 = l_Lean_Compiler_TerminalCases_visitLet___closed__6;
x_158 = l_Lean_Compiler_mkAuxLetDecl(x_68, x_157, x_4, x_5, x_6, x_102);
lean_dec(x_4);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = l_Lean_Expr_app___override(x_81, x_160);
x_162 = l_Lean_Expr_headBeta(x_161);
lean_ctor_set(x_158, 0, x_162);
return x_158;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_158, 0);
x_164 = lean_ctor_get(x_158, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_158);
x_165 = l_Lean_Expr_app___override(x_81, x_163);
x_166 = l_Lean_Expr_headBeta(x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
}
}
else
{
uint8_t x_168; 
lean_dec(x_81);
x_168 = !lean_is_exclusive(x_158);
if (x_168 == 0)
{
return x_158;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_158, 0);
x_170 = lean_ctor_get(x_158, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_158);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_91);
lean_dec(x_81);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_172 = !lean_is_exclusive(x_100);
if (x_172 == 0)
{
return x_100;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_100, 0);
x_174 = lean_ctor_get(x_100, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_100);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; 
lean_dec(x_91);
lean_dec(x_81);
lean_dec(x_68);
x_176 = l_Lean_Compiler_mkLcUnreachable___at_Lean_Compiler_TerminalCases_visitLet___spec__5(x_92, x_3, x_4, x_5, x_6, x_90);
lean_dec(x_4);
lean_dec(x_3);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_89);
lean_dec(x_81);
lean_dec(x_68);
x_177 = lean_ctor_get(x_88, 1);
lean_inc(x_177);
lean_dec(x_88);
x_178 = l_Lean_Compiler_TerminalCases_visitLet___closed__4;
x_179 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(x_178, x_3, x_4, x_5, x_6, x_177);
return x_179;
}
}
else
{
uint8_t x_180; 
lean_dec(x_81);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_180 = !lean_is_exclusive(x_88);
if (x_180 == 0)
{
return x_88;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_88, 0);
x_182 = lean_ctor_get(x_88, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_88);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_69, 1);
lean_inc(x_184);
lean_dec(x_69);
x_185 = lean_ctor_get(x_70, 0);
lean_inc(x_185);
lean_dec(x_70);
x_186 = l_Lean_Compiler_TerminalCases_visitCases(x_185, x_68, x_3, x_4, x_5, x_6, x_184);
return x_186;
}
}
else
{
uint8_t x_187; 
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = !lean_is_exclusive(x_69);
if (x_187 == 0)
{
return x_69;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_69, 0);
x_189 = lean_ctor_get(x_69, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_69);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_TerminalCases_visitAlt___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitAlt___spec__2(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_17, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_array_fget(x_19, x_20);
x_29 = lean_nat_add(x_20, x_14);
lean_dec(x_20);
lean_ctor_set(x_17, 1, x_29);
x_30 = lean_array_get_size(x_18);
x_31 = lean_nat_dec_lt(x_2, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_28);
x_32 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_array_fget(x_18, x_2);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_18, x_2, x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l_Lean_Compiler_TerminalCases_visitAlt(x_34, x_28, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_fset(x_36, x_2, x_38);
lean_ctor_set(x_5, 1, x_40);
x_41 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_41;
x_10 = x_39;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_17);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_17);
x_47 = lean_array_fget(x_19, x_20);
x_48 = lean_nat_add(x_20, x_14);
lean_dec(x_20);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_21);
x_50 = lean_array_get_size(x_18);
x_51 = lean_nat_dec_lt(x_2, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_47);
lean_ctor_set(x_5, 0, x_49);
x_52 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_52;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_array_fget(x_18, x_2);
x_55 = lean_box(0);
x_56 = lean_array_fset(x_18, x_2, x_55);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_57 = l_Lean_Compiler_TerminalCases_visitAlt(x_54, x_47, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_array_fset(x_56, x_2, x_58);
lean_ctor_set(x_5, 1, x_60);
lean_ctor_set(x_5, 0, x_49);
x_61 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_61;
x_10 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_56);
lean_dec(x_49);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_5, 0);
x_68 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_5);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 2);
lean_inc(x_71);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_10);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
x_76 = lean_array_fget(x_69, x_70);
x_77 = lean_nat_add(x_70, x_14);
lean_dec(x_70);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(0, 3, 0);
} else {
 x_78 = x_75;
}
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_71);
x_79 = lean_array_get_size(x_68);
x_80 = lean_nat_dec_lt(x_2, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_76);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_68);
x_82 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_82;
x_5 = x_81;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_array_fget(x_68, x_2);
x_85 = lean_box(0);
x_86 = lean_array_fset(x_68, x_2, x_85);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_87 = l_Lean_Compiler_TerminalCases_visitAlt(x_84, x_76, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_array_fset(x_86, x_2, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_78);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_92;
x_5 = x_91;
x_10 = x_89;
goto _start;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_86);
lean_dec(x_78);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_5);
lean_ctor_set(x_98, 1, x_10);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_5);
lean_ctor_set(x_99, 1, x_10);
return x_99;
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_toSubarray___rarg(x_10, x_12, x_11);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
lean_dec(x_14);
lean_inc(x_16);
x_19 = l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1(x_16, x_17, x_16, x_18, x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_getAppFn(x_2);
x_24 = l_Lean_mkAppN(x_23, x_22);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_getAppFn(x_2);
x_29 = l_Lean_mkAppN(x_28, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
x_1 = lean_mk_string_from_bytes("Lean.Compiler.TerminalCases.visitCases", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitCases___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___closed__1;
x_2 = l_Lean_Compiler_TerminalCases_visitCases___closed__2;
x_3 = lean_unsigned_to_nat(31u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l_Lean_Compiler_TerminalCases_visitLet___closed__3;
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
x_32 = l_Lean_Compiler_TerminalCases_visitCases___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_TerminalCases_visitAlt___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
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
l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1);
l_Lean_Compiler_TerminalCases_visitAlt___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitAlt___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitAlt___closed__1);
l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1);
l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__2);
l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__3);
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
l_Lean_Compiler_TerminalCases_visitLet___closed__5 = _init_l_Lean_Compiler_TerminalCases_visitLet___closed__5();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___closed__5);
l_Lean_Compiler_TerminalCases_visitLet___closed__6 = _init_l_Lean_Compiler_TerminalCases_visitLet___closed__6();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___closed__6);
l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__1);
l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2 = _init_l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2);
l_Lean_Compiler_TerminalCases_visitCases___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__1);
l_Lean_Compiler_TerminalCases_visitCases___closed__2 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__2();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__2);
l_Lean_Compiler_TerminalCases_visitCases___closed__3 = _init_l_Lean_Compiler_TerminalCases_visitCases___closed__3();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitCases___closed__3);
l_Lean_Compiler_Decl_terminalCases___closed__1 = _init_l_Lean_Compiler_Decl_terminalCases___closed__1();
lean_mark_persistent(l_Lean_Compiler_Decl_terminalCases___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
