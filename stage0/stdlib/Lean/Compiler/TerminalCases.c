// Lean compiler output
// Module: Lean.Compiler.TerminalCases
// Imports: Init Lean.Meta.Check Lean.Compiler.Util Lean.Compiler.Decl
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
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_updateMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__12;
lean_object* l_Lean_Compiler_mkLetUsingScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isLcCast_x3f(lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__16;
lean_object* l_Lean_Compiler_mkJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_isLcUnreachable(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_withNewScopeImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2___closed__2;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__7;
static lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__10;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_Context_jp_x3f___default;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__11;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__19;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLet___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__9;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLetDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getMaxLetVarIdx(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_TerminalCases_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitAlt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__3;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__5;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__2;
lean_object* l_Lean_Compiler_mkLcUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__3;
lean_object* l_Lean_Compiler_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__17;
lean_object* l_Lean_Compiler_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__1;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__15;
static lean_object* l_Lean_Compiler_Decl_terminalCases___closed__2;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__4;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitCases___closed__2;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_Decl_terminalCases___closed__1;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__14;
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___closed__6;
lean_object* l_Lean_Compiler_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Compiler_inferType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkLcCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitLambda___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_TerminalCases_visitCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__6;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLet___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = l_Lean_Compiler_withNewScopeImp___rarg(x_7, x_3, x_4, x_5, x_6);
return x_8;
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
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_3);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_3);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__5;
x_3 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__6;
x_4 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__7;
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
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__9;
x_2 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__11;
x_3 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__12;
x_4 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__15;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__19() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__18;
x_3 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__17;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__8;
x_3 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__16;
x_4 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__19;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_mkLetUsingScope(x_11, x_5, x_6, x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_16 = l_Lean_Compiler_inferType(x_14, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
x_21 = lean_array_push(x_20, x_3);
x_22 = lean_expr_abstract(x_14, x_21);
x_23 = lean_expr_abstract(x_18, x_21);
lean_dec(x_21);
lean_dec(x_18);
x_24 = l_Lean_Expr_hasLooseBVars(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_16);
x_25 = lean_st_ref_get(x_7, x_19);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_5, x_26);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2;
x_33 = l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_31);
x_36 = lean_st_ref_get(x_7, x_29);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20;
x_39 = lean_st_mk_ref(x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_7);
lean_inc(x_40);
x_42 = l_Lean_Meta_isTypeCorrect(x_14, x_35, x_40, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_7, x_44);
lean_dec(x_7);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_get(x_40, x_46);
lean_dec(x_40);
x_48 = lean_unbox(x_43);
lean_dec(x_43);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_22);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_47, 0, x_53);
return x_47;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_22);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_47, 0);
lean_dec(x_60);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_22);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_47, 0, x_63);
return x_47;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = 1;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_7);
x_69 = !lean_is_exclusive(x_42);
if (x_69 == 0)
{
return x_42;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_42, 0);
x_71 = lean_ctor_get(x_42, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_42);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_73 = 0;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_22);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_16, 0, x_75);
return x_16;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_76 = lean_ctor_get(x_16, 0);
x_77 = lean_ctor_get(x_16, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_16);
x_78 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1;
x_79 = lean_array_push(x_78, x_3);
x_80 = lean_expr_abstract(x_14, x_79);
x_81 = lean_expr_abstract(x_76, x_79);
lean_dec(x_79);
lean_dec(x_76);
x_82 = l_Lean_Expr_hasLooseBVars(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_83 = lean_st_ref_get(x_7, x_77);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_st_ref_get(x_5, x_84);
lean_dec(x_5);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_box(0);
x_90 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2;
x_91 = l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set(x_93, 4, x_92);
lean_ctor_set(x_93, 5, x_89);
x_94 = lean_st_ref_get(x_7, x_87);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20;
x_97 = lean_st_mk_ref(x_96, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_7);
lean_inc(x_98);
x_100 = l_Lean_Meta_isTypeCorrect(x_14, x_93, x_98, x_6, x_7, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_st_ref_get(x_7, x_102);
lean_dec(x_7);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_get(x_98, x_104);
lean_dec(x_98);
x_106 = lean_unbox(x_101);
lean_dec(x_101);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = 0;
x_110 = lean_box(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_80);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_114 = x_105;
} else {
 lean_dec_ref(x_105);
 x_114 = lean_box(0);
}
x_115 = 1;
x_116 = lean_box(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_80);
lean_ctor_set(x_117, 1, x_116);
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_98);
lean_dec(x_80);
lean_dec(x_7);
x_119 = lean_ctor_get(x_100, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_100, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_121 = x_100;
} else {
 lean_dec_ref(x_100);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_123 = 0;
x_124 = lean_box(x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_80);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_77);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_127 = !lean_is_exclusive(x_16);
if (x_127 == 0)
{
return x_16;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_16, 0);
x_129 = lean_ctor_get(x_16, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_16);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_131 = !lean_is_exclusive(x_10);
if (x_131 == 0)
{
return x_10;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_10, 0);
x_133 = lean_ctor_get(x_10, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_10);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
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
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(47u);
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
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_13);
lean_inc(x_8);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed), 7, 2);
lean_closure_set(x_33, 0, x_8);
lean_closure_set(x_33, 1, x_13);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__3), 8, 2);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_11);
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg), 7, 2);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLet___spec__2(x_35, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_free_object(x_16);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Lean_Expr_letE___override(x_8, x_13, x_14, x_42, x_12);
lean_ctor_set(x_36, 0, x_43);
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = l_Lean_Expr_letE___override(x_8, x_13, x_14, x_45, x_12);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_ctor_get(x_37, 0);
lean_inc(x_49);
lean_dec(x_37);
x_50 = 0;
x_51 = l_Lean_Expr_lam___override(x_8, x_13, x_49, x_50);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l_Lean_Compiler_mkJpDecl(x_51, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_ctor_set(x_16, 0, x_53);
x_55 = l_Lean_Compiler_TerminalCases_visitCases(x_32, x_14, x_16, x_4, x_5, x_6, x_54);
return x_55;
}
else
{
uint8_t x_56; 
lean_free_object(x_16);
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_16);
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
return x_36;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_36, 0);
x_62 = lean_ctor_get(x_36, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_36);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_16, 0);
lean_inc(x_64);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_8);
x_65 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__2___boxed), 7, 2);
lean_closure_set(x_65, 0, x_8);
lean_closure_set(x_65, 1, x_13);
x_66 = lean_alloc_closure((void*)(l_Lean_Compiler_TerminalCases_visitLet___lambda__3), 8, 2);
lean_closure_set(x_66, 0, x_2);
lean_closure_set(x_66, 1, x_11);
x_67 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_TerminalCases_visitAlt___spec__1___rarg), 7, 2);
lean_closure_set(x_67, 0, x_65);
lean_closure_set(x_67, 1, x_66);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = l_Lean_Compiler_withNewScope___at_Lean_Compiler_TerminalCases_visitLet___spec__2(x_67, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec(x_69);
x_75 = l_Lean_Expr_letE___override(x_8, x_13, x_14, x_74, x_12);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec(x_68);
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
lean_dec(x_69);
x_79 = 0;
x_80 = l_Lean_Expr_lam___override(x_8, x_13, x_78, x_79);
lean_inc(x_6);
lean_inc(x_5);
x_81 = l_Lean_Compiler_mkJpDecl(x_80, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_82);
x_85 = l_Lean_Compiler_TerminalCases_visitCases(x_64, x_14, x_84, x_4, x_5, x_6, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_64);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_64);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = lean_ctor_get(x_68, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_68, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_92 = x_68;
} else {
 lean_dec_ref(x_68);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_15);
if (x_94 == 0)
{
return x_15;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_15, 0);
x_96 = lean_ctor_get(x_15, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_15);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_98);
x_99 = l_Lean_Compiler_isCasesApp_x3f(x_98, x_5, x_6, x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_ctor_get(x_99, 0);
lean_dec(x_103);
x_104 = l_Lean_Expr_isLambda(x_98);
if (x_104 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
else
{
lean_object* x_105; 
lean_free_object(x_99);
x_105 = l_Lean_Compiler_TerminalCases_visitLambda(x_98, x_3, x_4, x_5, x_6, x_102);
return x_105;
}
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = l_Lean_Expr_isLambda(x_98);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; 
x_109 = l_Lean_Compiler_TerminalCases_visitLambda(x_98, x_3, x_4, x_5, x_6, x_106);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_99, 1);
lean_inc(x_110);
lean_dec(x_99);
x_111 = lean_ctor_get(x_3, 0);
lean_inc(x_111);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_111);
x_112 = l_Lean_Compiler_inferType_x27(x_111, x_4, x_5, x_6, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 7)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_3);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Compiler_isLcUnreachable(x_98);
if (x_116 == 0)
{
lean_object* x_117; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_98);
x_117 = l_Lean_Compiler_inferType(x_98, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_115);
x_120 = l_Lean_Compiler_isDefEq(x_118, x_115, x_4, x_5, x_6, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = l_Lean_Compiler_isLcCast_x3f(x_98);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_Compiler_TerminalCases_visitLet___closed__6;
lean_inc(x_6);
lean_inc(x_5);
x_126 = l_Lean_Compiler_mkAuxLetDecl(x_98, x_125, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_6);
lean_inc(x_5);
x_129 = l_Lean_Compiler_mkLcCast(x_127, x_115, x_4, x_5, x_6, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Compiler_mkAuxLetDecl(x_130, x_125, x_4, x_5, x_6, x_131);
lean_dec(x_4);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = l_Lean_Expr_app___override(x_111, x_134);
lean_ctor_set(x_132, 0, x_135);
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_132, 0);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_132);
x_138 = l_Lean_Expr_app___override(x_111, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_111);
x_140 = !lean_is_exclusive(x_132);
if (x_140 == 0)
{
return x_132;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_144 = !lean_is_exclusive(x_129);
if (x_144 == 0)
{
return x_129;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_129, 0);
x_146 = lean_ctor_get(x_129, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_129);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_148 = !lean_is_exclusive(x_126);
if (x_148 == 0)
{
return x_126;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_126, 0);
x_150 = lean_ctor_get(x_126, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_126);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_98);
x_152 = lean_ctor_get(x_124, 0);
lean_inc(x_152);
lean_dec(x_124);
lean_inc(x_6);
lean_inc(x_5);
x_153 = l_Lean_Compiler_mkLcCast(x_152, x_115, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Compiler_TerminalCases_visitLet___closed__6;
x_157 = l_Lean_Compiler_mkAuxLetDecl(x_154, x_156, x_4, x_5, x_6, x_155);
lean_dec(x_4);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = l_Lean_Expr_app___override(x_111, x_159);
lean_ctor_set(x_157, 0, x_160);
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_157, 0);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_157);
x_163 = l_Lean_Expr_app___override(x_111, x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_111);
x_165 = !lean_is_exclusive(x_157);
if (x_165 == 0)
{
return x_157;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_157, 0);
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_157);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_169 = !lean_is_exclusive(x_153);
if (x_169 == 0)
{
return x_153;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_153, 0);
x_171 = lean_ctor_get(x_153, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_153);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_115);
x_173 = lean_ctor_get(x_120, 1);
lean_inc(x_173);
lean_dec(x_120);
x_174 = l_Lean_Compiler_TerminalCases_visitLet___closed__6;
x_175 = l_Lean_Compiler_mkAuxLetDecl(x_98, x_174, x_4, x_5, x_6, x_173);
lean_dec(x_4);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = l_Lean_Expr_app___override(x_111, x_177);
lean_ctor_set(x_175, 0, x_178);
return x_175;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_175, 0);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_175);
x_181 = l_Lean_Expr_app___override(x_111, x_179);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
uint8_t x_183; 
lean_dec(x_111);
x_183 = !lean_is_exclusive(x_175);
if (x_183 == 0)
{
return x_175;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_175, 0);
x_185 = lean_ctor_get(x_175, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_175);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_187 = !lean_is_exclusive(x_120);
if (x_187 == 0)
{
return x_120;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_120, 0);
x_189 = lean_ctor_get(x_120, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_120);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = !lean_is_exclusive(x_117);
if (x_191 == 0)
{
return x_117;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_117, 0);
x_193 = lean_ctor_get(x_117, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_117);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
lean_object* x_195; 
lean_dec(x_111);
lean_dec(x_98);
x_195 = l_Lean_Compiler_mkLcUnreachable(x_115, x_4, x_5, x_6, x_114);
lean_dec(x_4);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_98);
x_196 = lean_ctor_get(x_112, 1);
lean_inc(x_196);
lean_dec(x_112);
x_197 = l_Lean_Compiler_TerminalCases_visitLet___closed__4;
x_198 = l_panic___at_Lean_Compiler_TerminalCases_visitLet___spec__1(x_197, x_3, x_4, x_5, x_6, x_196);
return x_198;
}
}
else
{
uint8_t x_199; 
lean_dec(x_111);
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_112);
if (x_199 == 0)
{
return x_112;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_112, 0);
x_201 = lean_ctor_get(x_112, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_112);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_99, 1);
lean_inc(x_203);
lean_dec(x_99);
x_204 = lean_ctor_get(x_100, 0);
lean_inc(x_204);
lean_dec(x_100);
x_205 = l_Lean_Compiler_TerminalCases_visitCases(x_204, x_98, x_3, x_4, x_5, x_6, x_203);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = !lean_is_exclusive(x_99);
if (x_206 == 0)
{
return x_99;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_99, 0);
x_208 = lean_ctor_get(x_99, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_99);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
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
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_toSubarray___rarg(x_10, x_12, x_11);
x_14 = lean_ctor_get(x_1, 2);
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
x_3 = lean_unsigned_to_nat(30u);
x_4 = lean_unsigned_to_nat(43u);
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
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Compiler_inferType_x27(x_17, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_6, x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_4, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2;
x_30 = l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_8);
lean_ctor_set(x_31, 5, x_28);
x_32 = lean_st_ref_get(x_6, x_26);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20;
x_35 = lean_st_mk_ref(x_34, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_38 = l_Lean_Compiler_updateMotive(x_1, x_14, x_21, x_31, x_36, x_5, x_6, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_6, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_get(x_36, x_42);
lean_dec(x_36);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_39, x_45, x_3, x_4, x_5, x_6, x_44);
lean_dec(x_2);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_38);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_19);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_dec(x_18);
x_52 = l_Lean_Compiler_TerminalCases_visitCases___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_53 = l_panic___at_Lean_Compiler_TerminalCases_visitCases___spec__2(x_52, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Compiler_TerminalCases_visitCases___lambda__1(x_1, x_2, x_14, x_54, x_3, x_4, x_5, x_6, x_55);
lean_dec(x_54);
lean_dec(x_2);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
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
static lean_object* _init_l_Lean_Compiler_Decl_terminalCases___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_Decl_terminalCases___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_Decl_terminalCases___closed__1;
x_2 = l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__19;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Decl_terminalCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_9 = l_Lean_Compiler_getMaxLetVarIdx(x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_Compiler_Decl_terminalCases___closed__2;
x_16 = l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
x_18 = lean_st_ref_get(x_3, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_mk_ref(x_17, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_21);
x_23 = l_Lean_Compiler_TerminalCases_visitLambda(x_8, x_12, x_21, x_2, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_3, x_25);
lean_dec(x_3);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_21, x_27);
lean_dec(x_21);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_1, 2, x_24);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_1, 2, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_21);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_43);
x_44 = l_Lean_Compiler_getMaxLetVarIdx(x_43, x_2, x_3, x_4);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_45, x_48);
lean_dec(x_45);
x_50 = l_Lean_Compiler_Decl_terminalCases___closed__2;
x_51 = l_Lean_Compiler_TerminalCases_visitAlt___lambda__2___closed__1;
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_49);
x_53 = lean_st_ref_get(x_3, x_46);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_mk_ref(x_52, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_3);
lean_inc(x_56);
x_58 = l_Lean_Compiler_TerminalCases_visitLambda(x_43, x_47, x_56, x_2, x_3, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_get(x_3, x_60);
lean_dec(x_3);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_get(x_56, x_62);
lean_dec(x_56);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_41);
lean_ctor_set(x_66, 1, x_42);
lean_ctor_set(x_66, 2, x_59);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_56);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_3);
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_58, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_70 = x_58;
} else {
 lean_dec_ref(x_58);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_ctor_get(x_44, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_44, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_74 = x_44;
} else {
 lean_dec_ref(x_44);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Decl(uint8_t builtin, lean_object*);
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
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__1);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__2);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__3 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__3);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__4);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__5 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__5);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__6 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__6);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__7 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__7);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__8 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__8);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__9 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__9);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__10 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__10);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__11 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__11);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__12 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__12);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__13 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__13);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__14 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__14);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__15 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__15);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__16 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__16();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__16);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__17 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__17();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__17);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__18 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__18();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__18);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__19 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__19();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__19);
l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20 = _init_l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20();
lean_mark_persistent(l_Lean_Compiler_TerminalCases_visitLet___lambda__3___closed__20);
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
l_Lean_Compiler_Decl_terminalCases___closed__2 = _init_l_Lean_Compiler_Decl_terminalCases___closed__2();
lean_mark_persistent(l_Lean_Compiler_Decl_terminalCases___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
