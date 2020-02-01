// Lean compiler output
// Module: Init.Lean.Elab.DoNotation
// Imports: Init.Lean.Elab.Term Init.Lean.Elab.TermBinders Init.Lean.Elab.Quotation
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_Term_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_6__expandLiftMethod(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_3__getDoElems(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_do___elambda__1___closed__1;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
extern lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_10__mkBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3;
lean_object* l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_decLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_8__ensureDoElemType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeInst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_3__getDoElems___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_do___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_Stats_toString___closed__5;
lean_object* l_Array_back___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ProcessedDoElem_inhabited;
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_8__ensureDoElemType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_12__processDoElems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
extern lean_object* l_Lean_Elab_Term_elabLetDecl___closed__4;
extern lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__4;
extern lean_object* l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__11;
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__3;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Init_Lean_Elab_DoNotation_10__mkBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
uint8_t l_Lean_Expr_isMVar(lean_object*);
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_13__regTraceClasses(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3;
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
extern lean_object* l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
extern lean_object* l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2;
extern lean_object* l_Lean_Parser_Term_doLet___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4;
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractMonad(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Id");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hasBind");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
x_2 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_getLevel(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
lean_inc(x_9);
x_11 = l_Lean_mkConst(x_10, x_9);
x_12 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4;
x_13 = l_Lean_mkConst(x_12, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
lean_inc(x_18);
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4;
x_22 = l_Lean_mkConst(x_21, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid do notation, expected type is not available");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3;
x_6 = l_Lean_Elab_Term_throwError___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 9);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_23 = lean_ctor_get(x_7, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 2;
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 6, x_25);
x_26 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_10);
lean_ctor_set(x_26, 2, x_11);
lean_ctor_set(x_26, 3, x_12);
lean_ctor_set(x_26, 4, x_13);
lean_ctor_set(x_26, 5, x_14);
lean_ctor_set(x_26, 6, x_15);
lean_ctor_set(x_26, 7, x_16);
lean_ctor_set(x_26, 8, x_17);
lean_ctor_set(x_26, 9, x_18);
lean_ctor_set_uint8(x_26, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*10 + 2, x_22);
x_27 = l_Lean_Elab_Term_whnf(x_1, x_9, x_26, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_52; uint8_t x_53; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_52 = l_Lean_Expr_getAppFn___main(x_28);
x_53 = l_Lean_Expr_isMVar(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
x_30 = x_29;
goto block_51;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_28);
x_54 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3;
x_55 = l_Lean_Elab_Term_throwError___rarg(x_1, x_54, x_3, x_29);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
block_51:
{
if (lean_obj_tag(x_28) == 5)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_31);
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_35 = l_Lean_Elab_Term_mkAppM(x_1, x_34, x_33, x_3, x_30);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_3);
x_38 = l_Lean_Elab_Term_synthesizeInst(x_1, x_36, x_3, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_28);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_31);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_31);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
x_50 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_30);
return x_50;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_8, 0);
x_65 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_66 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_67 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
x_68 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_69 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 4);
x_70 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 5);
lean_inc(x_64);
lean_dec(x_8);
x_71 = 2;
x_72 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_65);
lean_ctor_set_uint8(x_72, sizeof(void*)*1 + 1, x_66);
lean_ctor_set_uint8(x_72, sizeof(void*)*1 + 2, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*1 + 3, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*1 + 4, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*1 + 5, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1 + 6, x_71);
lean_ctor_set(x_7, 0, x_72);
x_73 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_73, 0, x_7);
lean_ctor_set(x_73, 1, x_10);
lean_ctor_set(x_73, 2, x_11);
lean_ctor_set(x_73, 3, x_12);
lean_ctor_set(x_73, 4, x_13);
lean_ctor_set(x_73, 5, x_14);
lean_ctor_set(x_73, 6, x_15);
lean_ctor_set(x_73, 7, x_16);
lean_ctor_set(x_73, 8, x_17);
lean_ctor_set(x_73, 9, x_18);
lean_ctor_set_uint8(x_73, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_73, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_73, sizeof(void*)*10 + 2, x_22);
x_74 = l_Lean_Elab_Term_whnf(x_1, x_9, x_73, x_4);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_97; uint8_t x_98; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_97 = l_Lean_Expr_getAppFn___main(x_75);
x_98 = l_Lean_Expr_isMVar(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
x_77 = x_76;
goto block_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_75);
x_99 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3;
x_100 = l_Lean_Elab_Term_throwError___rarg(x_1, x_99, x_3, x_76);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
block_96:
{
if (lean_obj_tag(x_75) == 5)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_78);
x_80 = lean_array_push(x_79, x_78);
x_81 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_82 = l_Lean_Elab_Term_mkAppM(x_1, x_81, x_80, x_3, x_77);
lean_dec(x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_3);
x_85 = l_Lean_Elab_Term_synthesizeInst(x_1, x_83, x_3, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_3);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_86);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_78);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_75, x_3, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_78);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_dec(x_82);
x_94 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_75, x_3, x_93);
return x_94;
}
}
else
{
lean_object* x_95; 
x_95 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_75, x_3, x_77);
return x_95;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_3);
x_105 = lean_ctor_get(x_74, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_74, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_107 = x_74;
} else {
 lean_dec_ref(x_74);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_109 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_110 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_111 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_112 = lean_ctor_get(x_7, 1);
x_113 = lean_ctor_get(x_7, 2);
x_114 = lean_ctor_get(x_7, 3);
x_115 = lean_ctor_get(x_7, 4);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_7);
x_116 = lean_ctor_get(x_8, 0);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_118 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_119 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
x_120 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_121 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 4);
x_122 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_123 = x_8;
} else {
 lean_dec_ref(x_8);
 x_123 = lean_box(0);
}
x_124 = 2;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 1, 7);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_117);
lean_ctor_set_uint8(x_125, sizeof(void*)*1 + 1, x_118);
lean_ctor_set_uint8(x_125, sizeof(void*)*1 + 2, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*1 + 3, x_120);
lean_ctor_set_uint8(x_125, sizeof(void*)*1 + 4, x_121);
lean_ctor_set_uint8(x_125, sizeof(void*)*1 + 5, x_122);
lean_ctor_set_uint8(x_125, sizeof(void*)*1 + 6, x_124);
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_112);
lean_ctor_set(x_126, 2, x_113);
lean_ctor_set(x_126, 3, x_114);
lean_ctor_set(x_126, 4, x_115);
x_127 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_10);
lean_ctor_set(x_127, 2, x_11);
lean_ctor_set(x_127, 3, x_12);
lean_ctor_set(x_127, 4, x_13);
lean_ctor_set(x_127, 5, x_14);
lean_ctor_set(x_127, 6, x_15);
lean_ctor_set(x_127, 7, x_16);
lean_ctor_set(x_127, 8, x_17);
lean_ctor_set(x_127, 9, x_18);
lean_ctor_set_uint8(x_127, sizeof(void*)*10, x_109);
lean_ctor_set_uint8(x_127, sizeof(void*)*10 + 1, x_110);
lean_ctor_set_uint8(x_127, sizeof(void*)*10 + 2, x_111);
x_128 = l_Lean_Elab_Term_whnf(x_1, x_9, x_127, x_4);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_151; uint8_t x_152; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_151 = l_Lean_Expr_getAppFn___main(x_129);
x_152 = l_Lean_Expr_isMVar(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
x_131 = x_130;
goto block_150;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_129);
x_153 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3;
x_154 = l_Lean_Elab_Term_throwError___rarg(x_1, x_153, x_3, x_130);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
block_150:
{
if (lean_obj_tag(x_129) == 5)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_132);
x_134 = lean_array_push(x_133, x_132);
x_135 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_136 = l_Lean_Elab_Term_mkAppM(x_1, x_135, x_134, x_3, x_131);
lean_dec(x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_3);
x_139 = l_Lean_Elab_Term_synthesizeInst(x_1, x_137, x_3, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_129);
lean_dec(x_3);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_132);
lean_ctor_set(x_143, 1, x_140);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_132);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_dec(x_139);
x_146 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_129, x_3, x_145);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_132);
x_147 = lean_ctor_get(x_136, 1);
lean_inc(x_147);
lean_dec(x_136);
x_148 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_129, x_3, x_147);
return x_148;
}
}
else
{
lean_object* x_149; 
x_149 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_129, x_3, x_131);
return x_149;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_3);
x_159 = lean_ctor_get(x_128, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_128, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_161 = x_128;
} else {
 lean_dec_ref(x_128);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_3__getDoElems(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
lean_inc(x_3);
x_4 = l_Lean_Syntax_getKind(x_3);
x_5 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_3__getDoElems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_7 = lean_name_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(x_3, x_3, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_2;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_array_fget(x_2, x_1);
x_13 = lean_box(0);
x_14 = x_13;
x_15 = lean_array_fset(x_2, x_1, x_14);
lean_inc(x_4);
lean_inc(x_12);
x_16 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_12, x_3, x_4, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_19;
lean_dec(x_12);
x_24 = lean_array_fset(x_15, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_3 = x_20;
x_5 = x_18;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("←");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_8 = lean_name_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_13 = lean_name_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(x_14, x_6, x_2, x_3, x_4);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_17, 0, x_1);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_5);
x_30 = l_Lean_Syntax_inhabited;
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_array_get(x_30, x_6, x_31);
lean_dec(x_6);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_4, 5);
x_35 = lean_nat_add(x_34, x_31);
lean_ctor_set(x_4, 5, x_35);
x_36 = !lean_is_exclusive(x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_3, 9);
lean_dec(x_37);
lean_ctor_set(x_3, 9, x_34);
lean_inc(x_3);
x_38 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_32, x_2, x_3, x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
x_44 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Term_getMainModule___rarg(x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_52 = l_Lean_addMacroScope(x_48, x_51, x_45);
x_53 = lean_box(0);
x_54 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_53);
x_56 = l_Array_empty___closed__1;
x_57 = lean_array_push(x_56, x_55);
x_58 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_59 = lean_array_push(x_57, x_58);
x_60 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_61 = lean_array_push(x_59, x_60);
x_62 = lean_array_push(x_61, x_42);
x_63 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_63);
x_64 = lean_array_push(x_56, x_1);
x_65 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_66 = lean_array_push(x_64, x_65);
x_67 = lean_box(0);
x_68 = lean_array_push(x_66, x_67);
x_69 = l_Lean_nullKind___closed__2;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_72 = lean_array_push(x_71, x_70);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_7);
lean_ctor_set(x_73, 1, x_72);
x_74 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_73);
lean_dec(x_73);
x_75 = lean_array_pop(x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_75, x_75, x_76, x_43);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_49);
lean_dec(x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Elab_Term_getMainModule___rarg(x_80);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = l_Lean_addMacroScope(x_83, x_51, x_79);
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_50);
lean_ctor_set(x_85, 1, x_54);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_53);
x_86 = lean_array_push(x_56, x_85);
x_87 = lean_array_push(x_86, x_58);
x_88 = l_Lean_mkTermIdFromIdent___closed__2;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_39, 1, x_77);
lean_ctor_set(x_39, 0, x_89);
lean_ctor_set(x_81, 0, x_39);
return x_81;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_81, 0);
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_81);
x_92 = l_Lean_addMacroScope(x_90, x_51, x_79);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_50);
lean_ctor_set(x_93, 1, x_54);
lean_ctor_set(x_93, 2, x_92);
lean_ctor_set(x_93, 3, x_53);
x_94 = lean_array_push(x_56, x_93);
x_95 = lean_array_push(x_94, x_58);
x_96 = l_Lean_mkTermIdFromIdent___closed__2;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_39, 1, x_77);
lean_ctor_set(x_39, 0, x_97);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_39);
lean_ctor_set(x_98, 1, x_91);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_99 = lean_ctor_get(x_39, 0);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_39);
x_101 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_40);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Elab_Term_getMainModule___rarg(x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_box(0);
x_108 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_109 = l_Lean_addMacroScope(x_105, x_108, x_102);
x_110 = lean_box(0);
x_111 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_110);
x_113 = l_Array_empty___closed__1;
x_114 = lean_array_push(x_113, x_112);
x_115 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_116 = lean_array_push(x_114, x_115);
x_117 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_118 = lean_array_push(x_116, x_117);
x_119 = lean_array_push(x_118, x_99);
x_120 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_119);
lean_ctor_set(x_1, 0, x_120);
x_121 = lean_array_push(x_113, x_1);
x_122 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_123 = lean_array_push(x_121, x_122);
x_124 = lean_box(0);
x_125 = lean_array_push(x_123, x_124);
x_126 = l_Lean_nullKind___closed__2;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_129 = lean_array_push(x_128, x_127);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_7);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_130);
lean_dec(x_130);
x_132 = lean_array_pop(x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_132, x_132, x_133, x_100);
lean_dec(x_132);
x_135 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_106);
lean_dec(x_3);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Elab_Term_getMainModule___rarg(x_137);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = l_Lean_addMacroScope(x_139, x_108, x_136);
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_107);
lean_ctor_set(x_143, 1, x_111);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_110);
x_144 = lean_array_push(x_113, x_143);
x_145 = lean_array_push(x_144, x_115);
x_146 = l_Lean_mkTermIdFromIdent___closed__2;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_134);
if (lean_is_scalar(x_141)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_141;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_140);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_150 = lean_ctor_get(x_3, 0);
x_151 = lean_ctor_get(x_3, 1);
x_152 = lean_ctor_get(x_3, 2);
x_153 = lean_ctor_get(x_3, 3);
x_154 = lean_ctor_get(x_3, 4);
x_155 = lean_ctor_get(x_3, 5);
x_156 = lean_ctor_get(x_3, 6);
x_157 = lean_ctor_get(x_3, 7);
x_158 = lean_ctor_get(x_3, 8);
x_159 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_160 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_161 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_3);
x_162 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_162, 0, x_150);
lean_ctor_set(x_162, 1, x_151);
lean_ctor_set(x_162, 2, x_152);
lean_ctor_set(x_162, 3, x_153);
lean_ctor_set(x_162, 4, x_154);
lean_ctor_set(x_162, 5, x_155);
lean_ctor_set(x_162, 6, x_156);
lean_ctor_set(x_162, 7, x_157);
lean_ctor_set(x_162, 8, x_158);
lean_ctor_set(x_162, 9, x_34);
lean_ctor_set_uint8(x_162, sizeof(void*)*10, x_159);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 1, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*10 + 2, x_161);
lean_inc(x_162);
x_163 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_32, x_2, x_162, x_4);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = l_Lean_Elab_Term_getCurrMacroScope(x_162, x_165);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Elab_Term_getMainModule___rarg(x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_box(0);
x_176 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_177 = l_Lean_addMacroScope(x_173, x_176, x_170);
x_178 = lean_box(0);
x_179 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_180 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_180, 2, x_177);
lean_ctor_set(x_180, 3, x_178);
x_181 = l_Array_empty___closed__1;
x_182 = lean_array_push(x_181, x_180);
x_183 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_184 = lean_array_push(x_182, x_183);
x_185 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_186 = lean_array_push(x_184, x_185);
x_187 = lean_array_push(x_186, x_166);
x_188 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_187);
lean_ctor_set(x_1, 0, x_188);
x_189 = lean_array_push(x_181, x_1);
x_190 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_191 = lean_array_push(x_189, x_190);
x_192 = lean_box(0);
x_193 = lean_array_push(x_191, x_192);
x_194 = l_Lean_nullKind___closed__2;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_197 = lean_array_push(x_196, x_195);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_7);
lean_ctor_set(x_198, 1, x_197);
x_199 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_198);
lean_dec(x_198);
x_200 = lean_array_pop(x_199);
x_201 = lean_unsigned_to_nat(0u);
x_202 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_200, x_200, x_201, x_167);
lean_dec(x_200);
x_203 = l_Lean_Elab_Term_getCurrMacroScope(x_162, x_174);
lean_dec(x_162);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_Lean_Elab_Term_getMainModule___rarg(x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = l_Lean_addMacroScope(x_207, x_176, x_204);
x_211 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_211, 0, x_175);
lean_ctor_set(x_211, 1, x_179);
lean_ctor_set(x_211, 2, x_210);
lean_ctor_set(x_211, 3, x_178);
x_212 = lean_array_push(x_181, x_211);
x_213 = lean_array_push(x_212, x_183);
x_214 = l_Lean_mkTermIdFromIdent___closed__2;
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
if (lean_is_scalar(x_168)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_168;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_202);
if (lean_is_scalar(x_209)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_209;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_208);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_218 = lean_ctor_get(x_4, 0);
x_219 = lean_ctor_get(x_4, 1);
x_220 = lean_ctor_get(x_4, 2);
x_221 = lean_ctor_get(x_4, 3);
x_222 = lean_ctor_get(x_4, 4);
x_223 = lean_ctor_get(x_4, 5);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_4);
x_224 = lean_nat_add(x_223, x_31);
x_225 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_225, 0, x_218);
lean_ctor_set(x_225, 1, x_219);
lean_ctor_set(x_225, 2, x_220);
lean_ctor_set(x_225, 3, x_221);
lean_ctor_set(x_225, 4, x_222);
lean_ctor_set(x_225, 5, x_224);
x_226 = lean_ctor_get(x_3, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_3, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_3, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_3, 3);
lean_inc(x_229);
x_230 = lean_ctor_get(x_3, 4);
lean_inc(x_230);
x_231 = lean_ctor_get(x_3, 5);
lean_inc(x_231);
x_232 = lean_ctor_get(x_3, 6);
lean_inc(x_232);
x_233 = lean_ctor_get(x_3, 7);
lean_inc(x_233);
x_234 = lean_ctor_get(x_3, 8);
lean_inc(x_234);
x_235 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_236 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_237 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 x_238 = x_3;
} else {
 lean_dec_ref(x_3);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 10, 3);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_226);
lean_ctor_set(x_239, 1, x_227);
lean_ctor_set(x_239, 2, x_228);
lean_ctor_set(x_239, 3, x_229);
lean_ctor_set(x_239, 4, x_230);
lean_ctor_set(x_239, 5, x_231);
lean_ctor_set(x_239, 6, x_232);
lean_ctor_set(x_239, 7, x_233);
lean_ctor_set(x_239, 8, x_234);
lean_ctor_set(x_239, 9, x_223);
lean_ctor_set_uint8(x_239, sizeof(void*)*10, x_235);
lean_ctor_set_uint8(x_239, sizeof(void*)*10 + 1, x_236);
lean_ctor_set_uint8(x_239, sizeof(void*)*10 + 2, x_237);
lean_inc(x_239);
x_240 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_32, x_2, x_239, x_225);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = l_Lean_Elab_Term_getCurrMacroScope(x_239, x_242);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_Elab_Term_getMainModule___rarg(x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_box(0);
x_253 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_254 = l_Lean_addMacroScope(x_250, x_253, x_247);
x_255 = lean_box(0);
x_256 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_257 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set(x_257, 2, x_254);
lean_ctor_set(x_257, 3, x_255);
x_258 = l_Array_empty___closed__1;
x_259 = lean_array_push(x_258, x_257);
x_260 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_261 = lean_array_push(x_259, x_260);
x_262 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_263 = lean_array_push(x_261, x_262);
x_264 = lean_array_push(x_263, x_243);
x_265 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_264);
lean_ctor_set(x_1, 0, x_265);
x_266 = lean_array_push(x_258, x_1);
x_267 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_268 = lean_array_push(x_266, x_267);
x_269 = lean_box(0);
x_270 = lean_array_push(x_268, x_269);
x_271 = l_Lean_nullKind___closed__2;
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
x_273 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_274 = lean_array_push(x_273, x_272);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_7);
lean_ctor_set(x_275, 1, x_274);
x_276 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_275);
lean_dec(x_275);
x_277 = lean_array_pop(x_276);
x_278 = lean_unsigned_to_nat(0u);
x_279 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_277, x_277, x_278, x_244);
lean_dec(x_277);
x_280 = l_Lean_Elab_Term_getCurrMacroScope(x_239, x_251);
lean_dec(x_239);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_Elab_Term_getMainModule___rarg(x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_286 = x_283;
} else {
 lean_dec_ref(x_283);
 x_286 = lean_box(0);
}
x_287 = l_Lean_addMacroScope(x_284, x_253, x_281);
x_288 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_288, 0, x_252);
lean_ctor_set(x_288, 1, x_256);
lean_ctor_set(x_288, 2, x_287);
lean_ctor_set(x_288, 3, x_255);
x_289 = lean_array_push(x_258, x_288);
x_290 = lean_array_push(x_289, x_260);
x_291 = l_Lean_mkTermIdFromIdent___closed__2;
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
if (lean_is_scalar(x_245)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_245;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_279);
if (lean_is_scalar(x_286)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_286;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_285);
return x_294;
}
}
}
else
{
lean_object* x_295; uint8_t x_296; 
lean_dec(x_1);
x_295 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_296 = lean_name_eq(x_5, x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_297 = lean_unsigned_to_nat(0u);
x_298 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(x_297, x_6, x_2, x_3, x_4);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_299, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_299, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_304 = x_299;
} else {
 lean_dec_ref(x_299);
 x_304 = lean_box(0);
}
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_5);
lean_ctor_set(x_305, 1, x_302);
if (lean_is_scalar(x_304)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_304;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_303);
if (lean_is_scalar(x_301)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_301;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_300);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; uint8_t x_330; uint8_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_5);
x_308 = l_Lean_Syntax_inhabited;
x_309 = lean_unsigned_to_nat(1u);
x_310 = lean_array_get(x_308, x_6, x_309);
lean_dec(x_6);
x_311 = lean_ctor_get(x_4, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_4, 1);
lean_inc(x_312);
x_313 = lean_ctor_get(x_4, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_4, 3);
lean_inc(x_314);
x_315 = lean_ctor_get(x_4, 4);
lean_inc(x_315);
x_316 = lean_ctor_get(x_4, 5);
lean_inc(x_316);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_317 = x_4;
} else {
 lean_dec_ref(x_4);
 x_317 = lean_box(0);
}
x_318 = lean_nat_add(x_316, x_309);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 6, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_311);
lean_ctor_set(x_319, 1, x_312);
lean_ctor_set(x_319, 2, x_313);
lean_ctor_set(x_319, 3, x_314);
lean_ctor_set(x_319, 4, x_315);
lean_ctor_set(x_319, 5, x_318);
x_320 = lean_ctor_get(x_3, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_3, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_3, 2);
lean_inc(x_322);
x_323 = lean_ctor_get(x_3, 3);
lean_inc(x_323);
x_324 = lean_ctor_get(x_3, 4);
lean_inc(x_324);
x_325 = lean_ctor_get(x_3, 5);
lean_inc(x_325);
x_326 = lean_ctor_get(x_3, 6);
lean_inc(x_326);
x_327 = lean_ctor_get(x_3, 7);
lean_inc(x_327);
x_328 = lean_ctor_get(x_3, 8);
lean_inc(x_328);
x_329 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_330 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_331 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 x_332 = x_3;
} else {
 lean_dec_ref(x_3);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 10, 3);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_320);
lean_ctor_set(x_333, 1, x_321);
lean_ctor_set(x_333, 2, x_322);
lean_ctor_set(x_333, 3, x_323);
lean_ctor_set(x_333, 4, x_324);
lean_ctor_set(x_333, 5, x_325);
lean_ctor_set(x_333, 6, x_326);
lean_ctor_set(x_333, 7, x_327);
lean_ctor_set(x_333, 8, x_328);
lean_ctor_set(x_333, 9, x_316);
lean_ctor_set_uint8(x_333, sizeof(void*)*10, x_329);
lean_ctor_set_uint8(x_333, sizeof(void*)*10 + 1, x_330);
lean_ctor_set_uint8(x_333, sizeof(void*)*10 + 2, x_331);
lean_inc(x_333);
x_334 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_310, x_2, x_333, x_319);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_339 = x_335;
} else {
 lean_dec_ref(x_335);
 x_339 = lean_box(0);
}
x_340 = l_Lean_Elab_Term_getCurrMacroScope(x_333, x_336);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = l_Lean_Elab_Term_getMainModule___rarg(x_342);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_box(0);
x_347 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_348 = l_Lean_addMacroScope(x_344, x_347, x_341);
x_349 = lean_box(0);
x_350 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_351 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_351, 0, x_346);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set(x_351, 2, x_348);
lean_ctor_set(x_351, 3, x_349);
x_352 = l_Array_empty___closed__1;
x_353 = lean_array_push(x_352, x_351);
x_354 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_355 = lean_array_push(x_353, x_354);
x_356 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_357 = lean_array_push(x_355, x_356);
x_358 = lean_array_push(x_357, x_337);
x_359 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
x_361 = lean_array_push(x_352, x_360);
x_362 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_363 = lean_array_push(x_361, x_362);
x_364 = lean_box(0);
x_365 = lean_array_push(x_363, x_364);
x_366 = l_Lean_nullKind___closed__2;
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_368 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_369 = lean_array_push(x_368, x_367);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_7);
lean_ctor_set(x_370, 1, x_369);
x_371 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_370);
lean_dec(x_370);
x_372 = lean_array_pop(x_371);
x_373 = lean_unsigned_to_nat(0u);
x_374 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_372, x_372, x_373, x_338);
lean_dec(x_372);
x_375 = l_Lean_Elab_Term_getCurrMacroScope(x_333, x_345);
lean_dec(x_333);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = l_Lean_Elab_Term_getMainModule___rarg(x_377);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_381 = x_378;
} else {
 lean_dec_ref(x_378);
 x_381 = lean_box(0);
}
x_382 = l_Lean_addMacroScope(x_379, x_347, x_376);
x_383 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_383, 0, x_346);
lean_ctor_set(x_383, 1, x_350);
lean_ctor_set(x_383, 2, x_382);
lean_ctor_set(x_383, 3, x_349);
x_384 = lean_array_push(x_352, x_383);
x_385 = lean_array_push(x_384, x_354);
x_386 = l_Lean_mkTermIdFromIdent___closed__2;
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_385);
if (lean_is_scalar(x_339)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_339;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_374);
if (lean_is_scalar(x_381)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_381;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_380);
return x_389;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_1);
lean_ctor_set(x_390, 1, x_2);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_4);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_3);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_1);
lean_ctor_set(x_392, 1, x_2);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_4);
return x_393;
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_6__expandLiftMethod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_1, x_7, x_2, x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_addParenHeuristic___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_PersistentHashMap_Stats_toString___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__4;
x_2 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_getMainModule___rarg(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_empty___closed__1;
x_17 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_15, x_16);
lean_dec(x_2);
x_18 = l_Lean_nullKind___closed__2;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_21 = lean_array_push(x_20, x_19);
x_22 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_23 = lean_array_push(x_21, x_22);
x_24 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_empty___closed__1;
x_34 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_32, x_33);
lean_dec(x_2);
x_35 = l_Lean_nullKind___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_38 = lean_array_push(x_37, x_36);
x_39 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_40 = lean_array_push(x_38, x_39);
x_41 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_44 = lean_array_push(x_43, x_42);
x_45 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_31);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
lean_inc(x_49);
x_50 = l___private_Init_Lean_Elab_DoNotation_6__expandLiftMethod(x_49, x_4, x_5);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
lean_inc(x_49);
x_54 = l_Lean_Syntax_getKind(x_49);
x_55 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_56 = lean_name_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_58 = lean_name_eq(x_54, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_53);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_6, x_59);
lean_dec(x_6);
x_61 = lean_nat_dec_lt(x_3, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
lean_dec(x_49);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_add(x_3, x_62);
lean_dec(x_3);
x_3 = x_63;
x_5 = x_52;
goto _start;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_66 = lean_name_eq(x_54, x_65);
lean_dec(x_54);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_49);
x_67 = lean_unsigned_to_nat(2u);
x_68 = lean_nat_add(x_3, x_67);
lean_dec(x_3);
x_3 = x_68;
x_5 = x_52;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Syntax_getArg(x_49, x_70);
lean_dec(x_49);
x_72 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_52);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Term_getMainModule___rarg(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_box(0);
x_79 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_80 = l_Lean_addMacroScope(x_76, x_79, x_73);
x_81 = lean_box(0);
x_82 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_81);
x_84 = l_Array_empty___closed__1;
x_85 = lean_array_push(x_84, x_83);
x_86 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_87 = lean_array_push(x_85, x_86);
x_88 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_89 = lean_array_push(x_87, x_88);
x_90 = lean_array_push(x_89, x_71);
x_91 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_push(x_84, x_92);
x_94 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_95 = lean_array_push(x_93, x_94);
x_96 = lean_box(0);
x_97 = lean_array_push(x_95, x_96);
x_98 = l_Lean_nullKind___closed__2;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_101 = lean_array_push(x_100, x_99);
x_102 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_103);
lean_dec(x_103);
x_105 = l_Lean_Syntax_inhabited;
x_106 = lean_array_get(x_105, x_104, x_70);
lean_dec(x_104);
x_107 = lean_array_set(x_2, x_3, x_106);
x_108 = lean_unsigned_to_nat(2u);
x_109 = lean_nat_add(x_3, x_108);
lean_dec(x_3);
x_110 = 1;
x_1 = x_110;
x_2 = x_107;
x_3 = x_109;
x_5 = x_77;
goto _start;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_54);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Lean_Syntax_getArg(x_49, x_112);
x_114 = lean_unsigned_to_nat(2u);
x_115 = l_Lean_Syntax_getArg(x_49, x_114);
x_116 = lean_unsigned_to_nat(3u);
x_117 = l_Lean_Syntax_getArg(x_49, x_116);
lean_dec(x_49);
x_118 = lean_nat_add(x_3, x_114);
x_119 = l_Array_extract___rarg(x_2, x_118, x_6);
lean_dec(x_6);
x_120 = lean_array_get_size(x_119);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_dec_eq(x_120, x_121);
lean_dec(x_120);
if (x_122 == 0)
{
uint8_t x_123; 
lean_dec(x_53);
x_123 = !lean_is_exclusive(x_52);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_52, 5);
x_125 = lean_nat_add(x_124, x_121);
lean_ctor_set(x_52, 5, x_125);
x_126 = !lean_is_exclusive(x_4);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_183; 
x_127 = lean_ctor_get(x_4, 9);
lean_dec(x_127);
lean_ctor_set(x_4, 9, x_124);
x_128 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_52);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = l_Lean_Elab_Term_getMainModule___rarg(x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_box(0);
x_134 = l_Array_empty___closed__1;
x_135 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_119, x_119, x_112, x_134);
lean_dec(x_119);
x_136 = l_Lean_nullKind___closed__2;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_139 = lean_array_push(x_138, x_137);
x_140 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_141 = lean_array_push(x_139, x_140);
x_142 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_145 = lean_array_push(x_144, x_143);
x_146 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_183 = l_Lean_Syntax_isNone(x_117);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_184 = l_Lean_Syntax_getArg(x_117, x_121);
lean_dec(x_117);
x_185 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_131);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Elab_Term_getMainModule___rarg(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_192 = l_Lean_addMacroScope(x_189, x_191, x_186);
x_193 = lean_box(0);
x_194 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_195 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_195, 0, x_133);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_192);
lean_ctor_set(x_195, 3, x_193);
x_196 = lean_array_push(x_134, x_195);
x_197 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_198 = lean_array_push(x_196, x_197);
x_199 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_198);
x_200 = lean_array_push(x_198, x_199);
x_201 = lean_array_push(x_200, x_115);
x_202 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_array_push(x_134, x_203);
x_205 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_206 = lean_array_push(x_204, x_205);
x_207 = l_Lean_mkTermIdFromIdent___closed__2;
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_198);
x_209 = lean_array_push(x_134, x_208);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_136);
lean_ctor_set(x_210, 1, x_209);
x_211 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_212 = lean_array_push(x_211, x_210);
x_213 = lean_array_push(x_212, x_197);
x_214 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_215 = lean_array_push(x_213, x_214);
x_216 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_217 = lean_array_push(x_215, x_216);
x_218 = lean_array_push(x_134, x_113);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_136);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_array_push(x_134, x_219);
x_221 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_222 = lean_array_push(x_220, x_221);
x_223 = lean_array_push(x_222, x_147);
x_224 = l_Lean_Parser_Term_matchAlt___closed__2;
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
x_226 = lean_array_push(x_134, x_225);
x_227 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_228 = lean_array_push(x_226, x_227);
x_229 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5;
x_230 = lean_array_push(x_229, x_184);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_224);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_array_push(x_228, x_231);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_136);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_array_push(x_217, x_233);
x_235 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = lean_array_push(x_134, x_236);
x_238 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
x_240 = lean_array_push(x_206, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_136);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_push(x_144, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_146);
lean_ctor_set(x_243, 1, x_242);
x_148 = x_243;
x_149 = x_190;
goto block_182;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_117);
x_244 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_131);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_Elab_Term_getMainModule___rarg(x_246);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_251 = l_Lean_addMacroScope(x_248, x_250, x_245);
x_252 = lean_box(0);
x_253 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_254 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_254, 0, x_133);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set(x_254, 2, x_251);
lean_ctor_set(x_254, 3, x_252);
x_255 = lean_array_push(x_134, x_254);
x_256 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_257 = lean_array_push(x_255, x_256);
x_258 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_257);
x_259 = lean_array_push(x_257, x_258);
x_260 = lean_array_push(x_259, x_115);
x_261 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = lean_array_push(x_134, x_262);
x_264 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_265 = lean_array_push(x_263, x_264);
x_266 = l_Lean_mkTermIdFromIdent___closed__2;
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_257);
x_268 = lean_array_push(x_134, x_267);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_136);
lean_ctor_set(x_269, 1, x_268);
x_270 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_271 = lean_array_push(x_270, x_269);
x_272 = lean_array_push(x_271, x_256);
x_273 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_274 = lean_array_push(x_272, x_273);
x_275 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_276 = lean_array_push(x_274, x_275);
x_277 = lean_array_push(x_134, x_113);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_136);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_array_push(x_134, x_278);
x_280 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_281 = lean_array_push(x_279, x_280);
x_282 = lean_array_push(x_281, x_147);
x_283 = l_Lean_Parser_Term_matchAlt___closed__2;
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
x_285 = lean_array_push(x_134, x_284);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_136);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_array_push(x_276, x_286);
x_288 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
x_290 = lean_array_push(x_134, x_289);
x_291 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_290);
x_293 = lean_array_push(x_265, x_292);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_136);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_array_push(x_144, x_294);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_146);
lean_ctor_set(x_296, 1, x_295);
x_148 = x_296;
x_149 = x_249;
goto block_182;
}
block_182:
{
uint8_t x_150; 
x_150 = lean_nat_dec_eq(x_3, x_112);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_132);
x_151 = l_Array_extract___rarg(x_2, x_112, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_152 = l_Lean_mkOptionalNode___closed__2;
x_153 = lean_array_push(x_152, x_148);
x_154 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_array_push(x_151, x_155);
x_157 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_149);
lean_dec(x_4);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = l_Lean_Elab_Term_getMainModule___rarg(x_158);
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_161 = lean_ctor_get(x_159, 0);
lean_dec(x_161);
x_162 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_156, x_156, x_112, x_134);
lean_dec(x_156);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_136);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_array_push(x_138, x_163);
x_165 = lean_array_push(x_164, x_140);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_142);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_push(x_144, x_166);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_146);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_159, 0, x_169);
return x_159;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_170 = lean_ctor_get(x_159, 1);
lean_inc(x_170);
lean_dec(x_159);
x_171 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_156, x_156, x_112, x_134);
lean_dec(x_156);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_136);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_push(x_138, x_172);
x_174 = lean_array_push(x_173, x_140);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_142);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_push(x_144, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_146);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_170);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_148);
if (lean_is_scalar(x_132)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_132;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_149);
return x_181;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_356; 
x_297 = lean_ctor_get(x_4, 0);
x_298 = lean_ctor_get(x_4, 1);
x_299 = lean_ctor_get(x_4, 2);
x_300 = lean_ctor_get(x_4, 3);
x_301 = lean_ctor_get(x_4, 4);
x_302 = lean_ctor_get(x_4, 5);
x_303 = lean_ctor_get(x_4, 6);
x_304 = lean_ctor_get(x_4, 7);
x_305 = lean_ctor_get(x_4, 8);
x_306 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_307 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_308 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_4);
x_309 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_309, 0, x_297);
lean_ctor_set(x_309, 1, x_298);
lean_ctor_set(x_309, 2, x_299);
lean_ctor_set(x_309, 3, x_300);
lean_ctor_set(x_309, 4, x_301);
lean_ctor_set(x_309, 5, x_302);
lean_ctor_set(x_309, 6, x_303);
lean_ctor_set(x_309, 7, x_304);
lean_ctor_set(x_309, 8, x_305);
lean_ctor_set(x_309, 9, x_124);
lean_ctor_set_uint8(x_309, sizeof(void*)*10, x_306);
lean_ctor_set_uint8(x_309, sizeof(void*)*10 + 1, x_307);
lean_ctor_set_uint8(x_309, sizeof(void*)*10 + 2, x_308);
x_310 = l_Lean_Elab_Term_getCurrMacroScope(x_309, x_52);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_312 = l_Lean_Elab_Term_getMainModule___rarg(x_311);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_314 = x_312;
} else {
 lean_dec_ref(x_312);
 x_314 = lean_box(0);
}
x_315 = lean_box(0);
x_316 = l_Array_empty___closed__1;
x_317 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_119, x_119, x_112, x_316);
lean_dec(x_119);
x_318 = l_Lean_nullKind___closed__2;
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
x_320 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_321 = lean_array_push(x_320, x_319);
x_322 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_323 = lean_array_push(x_321, x_322);
x_324 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_327 = lean_array_push(x_326, x_325);
x_328 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_356 = l_Lean_Syntax_isNone(x_117);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_357 = l_Lean_Syntax_getArg(x_117, x_121);
lean_dec(x_117);
x_358 = l_Lean_Elab_Term_getCurrMacroScope(x_309, x_313);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = l_Lean_Elab_Term_getMainModule___rarg(x_360);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_365 = l_Lean_addMacroScope(x_362, x_364, x_359);
x_366 = lean_box(0);
x_367 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_368 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_368, 0, x_315);
lean_ctor_set(x_368, 1, x_367);
lean_ctor_set(x_368, 2, x_365);
lean_ctor_set(x_368, 3, x_366);
x_369 = lean_array_push(x_316, x_368);
x_370 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_371 = lean_array_push(x_369, x_370);
x_372 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_371);
x_373 = lean_array_push(x_371, x_372);
x_374 = lean_array_push(x_373, x_115);
x_375 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
x_377 = lean_array_push(x_316, x_376);
x_378 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_379 = lean_array_push(x_377, x_378);
x_380 = l_Lean_mkTermIdFromIdent___closed__2;
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_371);
x_382 = lean_array_push(x_316, x_381);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_318);
lean_ctor_set(x_383, 1, x_382);
x_384 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_385 = lean_array_push(x_384, x_383);
x_386 = lean_array_push(x_385, x_370);
x_387 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_388 = lean_array_push(x_386, x_387);
x_389 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_390 = lean_array_push(x_388, x_389);
x_391 = lean_array_push(x_316, x_113);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_318);
lean_ctor_set(x_392, 1, x_391);
x_393 = lean_array_push(x_316, x_392);
x_394 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_395 = lean_array_push(x_393, x_394);
x_396 = lean_array_push(x_395, x_329);
x_397 = l_Lean_Parser_Term_matchAlt___closed__2;
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_396);
x_399 = lean_array_push(x_316, x_398);
x_400 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_401 = lean_array_push(x_399, x_400);
x_402 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5;
x_403 = lean_array_push(x_402, x_357);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_397);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_array_push(x_401, x_404);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_318);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_array_push(x_390, x_406);
x_408 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
x_410 = lean_array_push(x_316, x_409);
x_411 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_410);
x_413 = lean_array_push(x_379, x_412);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_318);
lean_ctor_set(x_414, 1, x_413);
x_415 = lean_array_push(x_326, x_414);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_328);
lean_ctor_set(x_416, 1, x_415);
x_330 = x_416;
x_331 = x_363;
goto block_355;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_117);
x_417 = l_Lean_Elab_Term_getCurrMacroScope(x_309, x_313);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_Elab_Term_getMainModule___rarg(x_419);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_424 = l_Lean_addMacroScope(x_421, x_423, x_418);
x_425 = lean_box(0);
x_426 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_427 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_427, 0, x_315);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_427, 2, x_424);
lean_ctor_set(x_427, 3, x_425);
x_428 = lean_array_push(x_316, x_427);
x_429 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_430 = lean_array_push(x_428, x_429);
x_431 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_430);
x_432 = lean_array_push(x_430, x_431);
x_433 = lean_array_push(x_432, x_115);
x_434 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_433);
x_436 = lean_array_push(x_316, x_435);
x_437 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_438 = lean_array_push(x_436, x_437);
x_439 = l_Lean_mkTermIdFromIdent___closed__2;
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_430);
x_441 = lean_array_push(x_316, x_440);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_318);
lean_ctor_set(x_442, 1, x_441);
x_443 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_444 = lean_array_push(x_443, x_442);
x_445 = lean_array_push(x_444, x_429);
x_446 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_447 = lean_array_push(x_445, x_446);
x_448 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_449 = lean_array_push(x_447, x_448);
x_450 = lean_array_push(x_316, x_113);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_318);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_array_push(x_316, x_451);
x_453 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_454 = lean_array_push(x_452, x_453);
x_455 = lean_array_push(x_454, x_329);
x_456 = l_Lean_Parser_Term_matchAlt___closed__2;
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_455);
x_458 = lean_array_push(x_316, x_457);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_318);
lean_ctor_set(x_459, 1, x_458);
x_460 = lean_array_push(x_449, x_459);
x_461 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_460);
x_463 = lean_array_push(x_316, x_462);
x_464 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = lean_array_push(x_438, x_465);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_318);
lean_ctor_set(x_467, 1, x_466);
x_468 = lean_array_push(x_326, x_467);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_328);
lean_ctor_set(x_469, 1, x_468);
x_330 = x_469;
x_331 = x_422;
goto block_355;
}
block_355:
{
uint8_t x_332; 
x_332 = lean_nat_dec_eq(x_3, x_112);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_314);
x_333 = l_Array_extract___rarg(x_2, x_112, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_334 = l_Lean_mkOptionalNode___closed__2;
x_335 = lean_array_push(x_334, x_330);
x_336 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_array_push(x_333, x_337);
x_339 = l_Lean_Elab_Term_getCurrMacroScope(x_309, x_331);
lean_dec(x_309);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_341 = l_Lean_Elab_Term_getMainModule___rarg(x_340);
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_343 = x_341;
} else {
 lean_dec_ref(x_341);
 x_343 = lean_box(0);
}
x_344 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_338, x_338, x_112, x_316);
lean_dec(x_338);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_318);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_array_push(x_320, x_345);
x_347 = lean_array_push(x_346, x_322);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_324);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_array_push(x_326, x_348);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_328);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_350);
if (lean_is_scalar(x_343)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_343;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_342);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_309);
lean_dec(x_3);
lean_dec(x_2);
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_330);
if (lean_is_scalar(x_314)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_314;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_331);
return x_354;
}
}
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; uint8_t x_488; uint8_t x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_538; 
x_470 = lean_ctor_get(x_52, 0);
x_471 = lean_ctor_get(x_52, 1);
x_472 = lean_ctor_get(x_52, 2);
x_473 = lean_ctor_get(x_52, 3);
x_474 = lean_ctor_get(x_52, 4);
x_475 = lean_ctor_get(x_52, 5);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_inc(x_472);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_52);
x_476 = lean_nat_add(x_475, x_121);
x_477 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_477, 0, x_470);
lean_ctor_set(x_477, 1, x_471);
lean_ctor_set(x_477, 2, x_472);
lean_ctor_set(x_477, 3, x_473);
lean_ctor_set(x_477, 4, x_474);
lean_ctor_set(x_477, 5, x_476);
x_478 = lean_ctor_get(x_4, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_4, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_4, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_4, 3);
lean_inc(x_481);
x_482 = lean_ctor_get(x_4, 4);
lean_inc(x_482);
x_483 = lean_ctor_get(x_4, 5);
lean_inc(x_483);
x_484 = lean_ctor_get(x_4, 6);
lean_inc(x_484);
x_485 = lean_ctor_get(x_4, 7);
lean_inc(x_485);
x_486 = lean_ctor_get(x_4, 8);
lean_inc(x_486);
x_487 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_488 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_489 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_490 = x_4;
} else {
 lean_dec_ref(x_4);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(0, 10, 3);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_478);
lean_ctor_set(x_491, 1, x_479);
lean_ctor_set(x_491, 2, x_480);
lean_ctor_set(x_491, 3, x_481);
lean_ctor_set(x_491, 4, x_482);
lean_ctor_set(x_491, 5, x_483);
lean_ctor_set(x_491, 6, x_484);
lean_ctor_set(x_491, 7, x_485);
lean_ctor_set(x_491, 8, x_486);
lean_ctor_set(x_491, 9, x_475);
lean_ctor_set_uint8(x_491, sizeof(void*)*10, x_487);
lean_ctor_set_uint8(x_491, sizeof(void*)*10 + 1, x_488);
lean_ctor_set_uint8(x_491, sizeof(void*)*10 + 2, x_489);
x_492 = l_Lean_Elab_Term_getCurrMacroScope(x_491, x_477);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
x_494 = l_Lean_Elab_Term_getMainModule___rarg(x_493);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
x_497 = lean_box(0);
x_498 = l_Array_empty___closed__1;
x_499 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_119, x_119, x_112, x_498);
lean_dec(x_119);
x_500 = l_Lean_nullKind___closed__2;
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_499);
x_502 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_503 = lean_array_push(x_502, x_501);
x_504 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_505 = lean_array_push(x_503, x_504);
x_506 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_505);
x_508 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_509 = lean_array_push(x_508, x_507);
x_510 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_509);
x_538 = l_Lean_Syntax_isNone(x_117);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_539 = l_Lean_Syntax_getArg(x_117, x_121);
lean_dec(x_117);
x_540 = l_Lean_Elab_Term_getCurrMacroScope(x_491, x_495);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_543 = l_Lean_Elab_Term_getMainModule___rarg(x_542);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_547 = l_Lean_addMacroScope(x_544, x_546, x_541);
x_548 = lean_box(0);
x_549 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_550 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_550, 0, x_497);
lean_ctor_set(x_550, 1, x_549);
lean_ctor_set(x_550, 2, x_547);
lean_ctor_set(x_550, 3, x_548);
x_551 = lean_array_push(x_498, x_550);
x_552 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_553 = lean_array_push(x_551, x_552);
x_554 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_553);
x_555 = lean_array_push(x_553, x_554);
x_556 = lean_array_push(x_555, x_115);
x_557 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_556);
x_559 = lean_array_push(x_498, x_558);
x_560 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_561 = lean_array_push(x_559, x_560);
x_562 = l_Lean_mkTermIdFromIdent___closed__2;
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_553);
x_564 = lean_array_push(x_498, x_563);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_500);
lean_ctor_set(x_565, 1, x_564);
x_566 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_567 = lean_array_push(x_566, x_565);
x_568 = lean_array_push(x_567, x_552);
x_569 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_570 = lean_array_push(x_568, x_569);
x_571 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_572 = lean_array_push(x_570, x_571);
x_573 = lean_array_push(x_498, x_113);
x_574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_574, 0, x_500);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_array_push(x_498, x_574);
x_576 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_577 = lean_array_push(x_575, x_576);
x_578 = lean_array_push(x_577, x_511);
x_579 = l_Lean_Parser_Term_matchAlt___closed__2;
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_578);
x_581 = lean_array_push(x_498, x_580);
x_582 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_583 = lean_array_push(x_581, x_582);
x_584 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5;
x_585 = lean_array_push(x_584, x_539);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_579);
lean_ctor_set(x_586, 1, x_585);
x_587 = lean_array_push(x_583, x_586);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_500);
lean_ctor_set(x_588, 1, x_587);
x_589 = lean_array_push(x_572, x_588);
x_590 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
x_592 = lean_array_push(x_498, x_591);
x_593 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_592);
x_595 = lean_array_push(x_561, x_594);
x_596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_596, 0, x_500);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_array_push(x_508, x_596);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_510);
lean_ctor_set(x_598, 1, x_597);
x_512 = x_598;
x_513 = x_545;
goto block_537;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_117);
x_599 = l_Lean_Elab_Term_getCurrMacroScope(x_491, x_495);
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = l_Lean_Elab_Term_getMainModule___rarg(x_601);
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_606 = l_Lean_addMacroScope(x_603, x_605, x_600);
x_607 = lean_box(0);
x_608 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_609 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_609, 0, x_497);
lean_ctor_set(x_609, 1, x_608);
lean_ctor_set(x_609, 2, x_606);
lean_ctor_set(x_609, 3, x_607);
x_610 = lean_array_push(x_498, x_609);
x_611 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_612 = lean_array_push(x_610, x_611);
x_613 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_612);
x_614 = lean_array_push(x_612, x_613);
x_615 = lean_array_push(x_614, x_115);
x_616 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_615);
x_618 = lean_array_push(x_498, x_617);
x_619 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_620 = lean_array_push(x_618, x_619);
x_621 = l_Lean_mkTermIdFromIdent___closed__2;
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_612);
x_623 = lean_array_push(x_498, x_622);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_500);
lean_ctor_set(x_624, 1, x_623);
x_625 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_626 = lean_array_push(x_625, x_624);
x_627 = lean_array_push(x_626, x_611);
x_628 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_629 = lean_array_push(x_627, x_628);
x_630 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_631 = lean_array_push(x_629, x_630);
x_632 = lean_array_push(x_498, x_113);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_500);
lean_ctor_set(x_633, 1, x_632);
x_634 = lean_array_push(x_498, x_633);
x_635 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_636 = lean_array_push(x_634, x_635);
x_637 = lean_array_push(x_636, x_511);
x_638 = l_Lean_Parser_Term_matchAlt___closed__2;
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_637);
x_640 = lean_array_push(x_498, x_639);
x_641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_641, 0, x_500);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_array_push(x_631, x_641);
x_643 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_642);
x_645 = lean_array_push(x_498, x_644);
x_646 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_645);
x_648 = lean_array_push(x_620, x_647);
x_649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_649, 0, x_500);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_array_push(x_508, x_649);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_510);
lean_ctor_set(x_651, 1, x_650);
x_512 = x_651;
x_513 = x_604;
goto block_537;
}
block_537:
{
uint8_t x_514; 
x_514 = lean_nat_dec_eq(x_3, x_112);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_496);
x_515 = l_Array_extract___rarg(x_2, x_112, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_516 = l_Lean_mkOptionalNode___closed__2;
x_517 = lean_array_push(x_516, x_512);
x_518 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_517);
x_520 = lean_array_push(x_515, x_519);
x_521 = l_Lean_Elab_Term_getCurrMacroScope(x_491, x_513);
lean_dec(x_491);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
lean_dec(x_521);
x_523 = l_Lean_Elab_Term_getMainModule___rarg(x_522);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_525 = x_523;
} else {
 lean_dec_ref(x_523);
 x_525 = lean_box(0);
}
x_526 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_520, x_520, x_112, x_498);
lean_dec(x_520);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_500);
lean_ctor_set(x_527, 1, x_526);
x_528 = lean_array_push(x_502, x_527);
x_529 = lean_array_push(x_528, x_504);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_506);
lean_ctor_set(x_530, 1, x_529);
x_531 = lean_array_push(x_508, x_530);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_510);
lean_ctor_set(x_532, 1, x_531);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
if (lean_is_scalar(x_525)) {
 x_534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_534 = x_525;
}
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_524);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; 
lean_dec(x_491);
lean_dec(x_3);
lean_dec(x_2);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_512);
if (lean_is_scalar(x_496)) {
 x_536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_536 = x_496;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_513);
return x_536;
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_652 = l_Lean_Syntax_inhabited;
x_653 = lean_array_get(x_652, x_119, x_112);
lean_dec(x_119);
x_654 = l_Lean_Syntax_getArg(x_653, x_112);
lean_dec(x_653);
x_655 = !lean_is_exclusive(x_52);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; uint8_t x_658; 
x_656 = lean_ctor_get(x_52, 5);
x_657 = lean_nat_add(x_656, x_121);
lean_ctor_set(x_52, 5, x_657);
x_658 = !lean_is_exclusive(x_4);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; uint8_t x_709; 
x_659 = lean_ctor_get(x_4, 9);
lean_dec(x_659);
lean_ctor_set(x_4, 9, x_656);
x_709 = l_Lean_Syntax_isNone(x_117);
if (x_709 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_710 = l_Lean_Syntax_getArg(x_117, x_121);
lean_dec(x_117);
x_711 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_52);
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
x_714 = l_Lean_Elab_Term_getMainModule___rarg(x_713);
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
x_717 = lean_box(0);
x_718 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_719 = l_Lean_addMacroScope(x_715, x_718, x_712);
x_720 = lean_box(0);
x_721 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_722 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_722, 0, x_717);
lean_ctor_set(x_722, 1, x_721);
lean_ctor_set(x_722, 2, x_719);
lean_ctor_set(x_722, 3, x_720);
x_723 = l_Array_empty___closed__1;
x_724 = lean_array_push(x_723, x_722);
x_725 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_726 = lean_array_push(x_724, x_725);
x_727 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_726);
x_728 = lean_array_push(x_726, x_727);
x_729 = lean_array_push(x_728, x_115);
x_730 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_729);
x_732 = lean_array_push(x_723, x_731);
x_733 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_734 = lean_array_push(x_732, x_733);
x_735 = l_Lean_mkTermIdFromIdent___closed__2;
x_736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_726);
x_737 = lean_array_push(x_723, x_736);
x_738 = l_Lean_nullKind___closed__2;
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_737);
x_740 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_741 = lean_array_push(x_740, x_739);
x_742 = lean_array_push(x_741, x_725);
x_743 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_744 = lean_array_push(x_742, x_743);
x_745 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_746 = lean_array_push(x_744, x_745);
x_747 = lean_array_push(x_723, x_113);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_738);
lean_ctor_set(x_748, 1, x_747);
x_749 = lean_array_push(x_723, x_748);
x_750 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_751 = lean_array_push(x_749, x_750);
x_752 = lean_array_push(x_751, x_654);
x_753 = l_Lean_Parser_Term_matchAlt___closed__2;
x_754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_752);
x_755 = lean_array_push(x_723, x_754);
x_756 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_757 = lean_array_push(x_755, x_756);
x_758 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5;
x_759 = lean_array_push(x_758, x_710);
x_760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_760, 0, x_753);
lean_ctor_set(x_760, 1, x_759);
x_761 = lean_array_push(x_757, x_760);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_738);
lean_ctor_set(x_762, 1, x_761);
x_763 = lean_array_push(x_746, x_762);
x_764 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_763);
x_766 = lean_array_push(x_723, x_765);
x_767 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_766);
x_769 = lean_array_push(x_734, x_768);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_738);
lean_ctor_set(x_770, 1, x_769);
x_771 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_772 = lean_array_push(x_771, x_770);
x_773 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_772);
x_660 = x_774;
x_661 = x_716;
goto block_708;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_117);
x_775 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_52);
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = l_Lean_Elab_Term_getMainModule___rarg(x_777);
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
lean_dec(x_778);
x_781 = lean_box(0);
x_782 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_783 = l_Lean_addMacroScope(x_779, x_782, x_776);
x_784 = lean_box(0);
x_785 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_786 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_786, 0, x_781);
lean_ctor_set(x_786, 1, x_785);
lean_ctor_set(x_786, 2, x_783);
lean_ctor_set(x_786, 3, x_784);
x_787 = l_Array_empty___closed__1;
x_788 = lean_array_push(x_787, x_786);
x_789 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_790 = lean_array_push(x_788, x_789);
x_791 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_790);
x_792 = lean_array_push(x_790, x_791);
x_793 = lean_array_push(x_792, x_115);
x_794 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_795 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_793);
x_796 = lean_array_push(x_787, x_795);
x_797 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_798 = lean_array_push(x_796, x_797);
x_799 = l_Lean_mkTermIdFromIdent___closed__2;
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_790);
x_801 = lean_array_push(x_787, x_800);
x_802 = l_Lean_nullKind___closed__2;
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_801);
x_804 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_805 = lean_array_push(x_804, x_803);
x_806 = lean_array_push(x_805, x_789);
x_807 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_808 = lean_array_push(x_806, x_807);
x_809 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_810 = lean_array_push(x_808, x_809);
x_811 = lean_array_push(x_787, x_113);
x_812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_812, 0, x_802);
lean_ctor_set(x_812, 1, x_811);
x_813 = lean_array_push(x_787, x_812);
x_814 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_815 = lean_array_push(x_813, x_814);
x_816 = lean_array_push(x_815, x_654);
x_817 = l_Lean_Parser_Term_matchAlt___closed__2;
x_818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
x_819 = lean_array_push(x_787, x_818);
x_820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_820, 0, x_802);
lean_ctor_set(x_820, 1, x_819);
x_821 = lean_array_push(x_810, x_820);
x_822 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_821);
x_824 = lean_array_push(x_787, x_823);
x_825 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_826 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_826, 0, x_825);
lean_ctor_set(x_826, 1, x_824);
x_827 = lean_array_push(x_798, x_826);
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_802);
lean_ctor_set(x_828, 1, x_827);
x_829 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_830 = lean_array_push(x_829, x_828);
x_831 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_831);
lean_ctor_set(x_832, 1, x_830);
x_660 = x_832;
x_661 = x_780;
goto block_708;
}
block_708:
{
uint8_t x_662; 
x_662 = lean_nat_dec_eq(x_3, x_112);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; 
lean_dec(x_53);
x_663 = l_Array_extract___rarg(x_2, x_112, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_664 = l_Lean_mkOptionalNode___closed__2;
x_665 = lean_array_push(x_664, x_660);
x_666 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_665);
x_668 = lean_array_push(x_663, x_667);
x_669 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_661);
lean_dec(x_4);
x_670 = lean_ctor_get(x_669, 1);
lean_inc(x_670);
lean_dec(x_669);
x_671 = l_Lean_Elab_Term_getMainModule___rarg(x_670);
x_672 = !lean_is_exclusive(x_671);
if (x_672 == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_673 = lean_ctor_get(x_671, 0);
lean_dec(x_673);
x_674 = l_Array_empty___closed__1;
x_675 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_668, x_668, x_112, x_674);
lean_dec(x_668);
x_676 = l_Lean_nullKind___closed__2;
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_675);
x_678 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_679 = lean_array_push(x_678, x_677);
x_680 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_681 = lean_array_push(x_679, x_680);
x_682 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_681);
x_684 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_685 = lean_array_push(x_684, x_683);
x_686 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_685);
x_688 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_671, 0, x_688);
return x_671;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_689 = lean_ctor_get(x_671, 1);
lean_inc(x_689);
lean_dec(x_671);
x_690 = l_Array_empty___closed__1;
x_691 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_668, x_668, x_112, x_690);
lean_dec(x_668);
x_692 = l_Lean_nullKind___closed__2;
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_692);
lean_ctor_set(x_693, 1, x_691);
x_694 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_695 = lean_array_push(x_694, x_693);
x_696 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_697 = lean_array_push(x_695, x_696);
x_698 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_697);
x_700 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_701 = lean_array_push(x_700, x_699);
x_702 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
x_704 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_704, 0, x_703);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_689);
return x_705;
}
}
else
{
lean_object* x_706; lean_object* x_707; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_706 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_706, 0, x_660);
if (lean_is_scalar(x_53)) {
 x_707 = lean_alloc_ctor(0, 2, 0);
} else {
 x_707 = x_53;
}
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_661);
return x_707;
}
}
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; uint8_t x_843; uint8_t x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_879; 
x_833 = lean_ctor_get(x_4, 0);
x_834 = lean_ctor_get(x_4, 1);
x_835 = lean_ctor_get(x_4, 2);
x_836 = lean_ctor_get(x_4, 3);
x_837 = lean_ctor_get(x_4, 4);
x_838 = lean_ctor_get(x_4, 5);
x_839 = lean_ctor_get(x_4, 6);
x_840 = lean_ctor_get(x_4, 7);
x_841 = lean_ctor_get(x_4, 8);
x_842 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_843 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_844 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
lean_inc(x_841);
lean_inc(x_840);
lean_inc(x_839);
lean_inc(x_838);
lean_inc(x_837);
lean_inc(x_836);
lean_inc(x_835);
lean_inc(x_834);
lean_inc(x_833);
lean_dec(x_4);
x_845 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_845, 0, x_833);
lean_ctor_set(x_845, 1, x_834);
lean_ctor_set(x_845, 2, x_835);
lean_ctor_set(x_845, 3, x_836);
lean_ctor_set(x_845, 4, x_837);
lean_ctor_set(x_845, 5, x_838);
lean_ctor_set(x_845, 6, x_839);
lean_ctor_set(x_845, 7, x_840);
lean_ctor_set(x_845, 8, x_841);
lean_ctor_set(x_845, 9, x_656);
lean_ctor_set_uint8(x_845, sizeof(void*)*10, x_842);
lean_ctor_set_uint8(x_845, sizeof(void*)*10 + 1, x_843);
lean_ctor_set_uint8(x_845, sizeof(void*)*10 + 2, x_844);
x_879 = l_Lean_Syntax_isNone(x_117);
if (x_879 == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_880 = l_Lean_Syntax_getArg(x_117, x_121);
lean_dec(x_117);
x_881 = l_Lean_Elab_Term_getCurrMacroScope(x_845, x_52);
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_884 = l_Lean_Elab_Term_getMainModule___rarg(x_883);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = lean_box(0);
x_888 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_889 = l_Lean_addMacroScope(x_885, x_888, x_882);
x_890 = lean_box(0);
x_891 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_892 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_892, 0, x_887);
lean_ctor_set(x_892, 1, x_891);
lean_ctor_set(x_892, 2, x_889);
lean_ctor_set(x_892, 3, x_890);
x_893 = l_Array_empty___closed__1;
x_894 = lean_array_push(x_893, x_892);
x_895 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_896 = lean_array_push(x_894, x_895);
x_897 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_896);
x_898 = lean_array_push(x_896, x_897);
x_899 = lean_array_push(x_898, x_115);
x_900 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_901, 0, x_900);
lean_ctor_set(x_901, 1, x_899);
x_902 = lean_array_push(x_893, x_901);
x_903 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_904 = lean_array_push(x_902, x_903);
x_905 = l_Lean_mkTermIdFromIdent___closed__2;
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_896);
x_907 = lean_array_push(x_893, x_906);
x_908 = l_Lean_nullKind___closed__2;
x_909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_909, 0, x_908);
lean_ctor_set(x_909, 1, x_907);
x_910 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_911 = lean_array_push(x_910, x_909);
x_912 = lean_array_push(x_911, x_895);
x_913 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_914 = lean_array_push(x_912, x_913);
x_915 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_916 = lean_array_push(x_914, x_915);
x_917 = lean_array_push(x_893, x_113);
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_908);
lean_ctor_set(x_918, 1, x_917);
x_919 = lean_array_push(x_893, x_918);
x_920 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_921 = lean_array_push(x_919, x_920);
x_922 = lean_array_push(x_921, x_654);
x_923 = l_Lean_Parser_Term_matchAlt___closed__2;
x_924 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_922);
x_925 = lean_array_push(x_893, x_924);
x_926 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_927 = lean_array_push(x_925, x_926);
x_928 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5;
x_929 = lean_array_push(x_928, x_880);
x_930 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_930, 0, x_923);
lean_ctor_set(x_930, 1, x_929);
x_931 = lean_array_push(x_927, x_930);
x_932 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_932, 0, x_908);
lean_ctor_set(x_932, 1, x_931);
x_933 = lean_array_push(x_916, x_932);
x_934 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_935, 0, x_934);
lean_ctor_set(x_935, 1, x_933);
x_936 = lean_array_push(x_893, x_935);
x_937 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_938 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_936);
x_939 = lean_array_push(x_904, x_938);
x_940 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_940, 0, x_908);
lean_ctor_set(x_940, 1, x_939);
x_941 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_942 = lean_array_push(x_941, x_940);
x_943 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_944, 0, x_943);
lean_ctor_set(x_944, 1, x_942);
x_846 = x_944;
x_847 = x_886;
goto block_878;
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_117);
x_945 = l_Lean_Elab_Term_getCurrMacroScope(x_845, x_52);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_948 = l_Lean_Elab_Term_getMainModule___rarg(x_947);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = lean_box(0);
x_952 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_953 = l_Lean_addMacroScope(x_949, x_952, x_946);
x_954 = lean_box(0);
x_955 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_956 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_956, 0, x_951);
lean_ctor_set(x_956, 1, x_955);
lean_ctor_set(x_956, 2, x_953);
lean_ctor_set(x_956, 3, x_954);
x_957 = l_Array_empty___closed__1;
x_958 = lean_array_push(x_957, x_956);
x_959 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_960 = lean_array_push(x_958, x_959);
x_961 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_960);
x_962 = lean_array_push(x_960, x_961);
x_963 = lean_array_push(x_962, x_115);
x_964 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_963);
x_966 = lean_array_push(x_957, x_965);
x_967 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_968 = lean_array_push(x_966, x_967);
x_969 = l_Lean_mkTermIdFromIdent___closed__2;
x_970 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_960);
x_971 = lean_array_push(x_957, x_970);
x_972 = l_Lean_nullKind___closed__2;
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_972);
lean_ctor_set(x_973, 1, x_971);
x_974 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_975 = lean_array_push(x_974, x_973);
x_976 = lean_array_push(x_975, x_959);
x_977 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_978 = lean_array_push(x_976, x_977);
x_979 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_980 = lean_array_push(x_978, x_979);
x_981 = lean_array_push(x_957, x_113);
x_982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_982, 0, x_972);
lean_ctor_set(x_982, 1, x_981);
x_983 = lean_array_push(x_957, x_982);
x_984 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_985 = lean_array_push(x_983, x_984);
x_986 = lean_array_push(x_985, x_654);
x_987 = l_Lean_Parser_Term_matchAlt___closed__2;
x_988 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_988, 0, x_987);
lean_ctor_set(x_988, 1, x_986);
x_989 = lean_array_push(x_957, x_988);
x_990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_990, 0, x_972);
lean_ctor_set(x_990, 1, x_989);
x_991 = lean_array_push(x_980, x_990);
x_992 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_991);
x_994 = lean_array_push(x_957, x_993);
x_995 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_996, 0, x_995);
lean_ctor_set(x_996, 1, x_994);
x_997 = lean_array_push(x_968, x_996);
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_972);
lean_ctor_set(x_998, 1, x_997);
x_999 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1000 = lean_array_push(x_999, x_998);
x_1001 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_1000);
x_846 = x_1002;
x_847 = x_950;
goto block_878;
}
block_878:
{
uint8_t x_848; 
x_848 = lean_nat_dec_eq(x_3, x_112);
if (x_848 == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_53);
x_849 = l_Array_extract___rarg(x_2, x_112, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_850 = l_Lean_mkOptionalNode___closed__2;
x_851 = lean_array_push(x_850, x_846);
x_852 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_851);
x_854 = lean_array_push(x_849, x_853);
x_855 = l_Lean_Elab_Term_getCurrMacroScope(x_845, x_847);
lean_dec(x_845);
x_856 = lean_ctor_get(x_855, 1);
lean_inc(x_856);
lean_dec(x_855);
x_857 = l_Lean_Elab_Term_getMainModule___rarg(x_856);
x_858 = lean_ctor_get(x_857, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_859 = x_857;
} else {
 lean_dec_ref(x_857);
 x_859 = lean_box(0);
}
x_860 = l_Array_empty___closed__1;
x_861 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_854, x_854, x_112, x_860);
lean_dec(x_854);
x_862 = l_Lean_nullKind___closed__2;
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_862);
lean_ctor_set(x_863, 1, x_861);
x_864 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_865 = lean_array_push(x_864, x_863);
x_866 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_867 = lean_array_push(x_865, x_866);
x_868 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_869, 0, x_868);
lean_ctor_set(x_869, 1, x_867);
x_870 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_871 = lean_array_push(x_870, x_869);
x_872 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_873 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_873, 0, x_872);
lean_ctor_set(x_873, 1, x_871);
x_874 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_874, 0, x_873);
if (lean_is_scalar(x_859)) {
 x_875 = lean_alloc_ctor(0, 2, 0);
} else {
 x_875 = x_859;
}
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_858);
return x_875;
}
else
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_845);
lean_dec(x_3);
lean_dec(x_2);
x_876 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_876, 0, x_846);
if (lean_is_scalar(x_53)) {
 x_877 = lean_alloc_ctor(0, 2, 0);
} else {
 x_877 = x_53;
}
lean_ctor_set(x_877, 0, x_876);
lean_ctor_set(x_877, 1, x_847);
return x_877;
}
}
}
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; uint8_t x_1021; uint8_t x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; uint8_t x_1058; 
x_1003 = lean_ctor_get(x_52, 0);
x_1004 = lean_ctor_get(x_52, 1);
x_1005 = lean_ctor_get(x_52, 2);
x_1006 = lean_ctor_get(x_52, 3);
x_1007 = lean_ctor_get(x_52, 4);
x_1008 = lean_ctor_get(x_52, 5);
lean_inc(x_1008);
lean_inc(x_1007);
lean_inc(x_1006);
lean_inc(x_1005);
lean_inc(x_1004);
lean_inc(x_1003);
lean_dec(x_52);
x_1009 = lean_nat_add(x_1008, x_121);
x_1010 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1010, 0, x_1003);
lean_ctor_set(x_1010, 1, x_1004);
lean_ctor_set(x_1010, 2, x_1005);
lean_ctor_set(x_1010, 3, x_1006);
lean_ctor_set(x_1010, 4, x_1007);
lean_ctor_set(x_1010, 5, x_1009);
x_1011 = lean_ctor_get(x_4, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_4, 1);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_4, 2);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_4, 3);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_4, 4);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_4, 5);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_4, 6);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_4, 7);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_4, 8);
lean_inc(x_1019);
x_1020 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_1021 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_1022 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_1023 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1023 = lean_box(0);
}
if (lean_is_scalar(x_1023)) {
 x_1024 = lean_alloc_ctor(0, 10, 3);
} else {
 x_1024 = x_1023;
}
lean_ctor_set(x_1024, 0, x_1011);
lean_ctor_set(x_1024, 1, x_1012);
lean_ctor_set(x_1024, 2, x_1013);
lean_ctor_set(x_1024, 3, x_1014);
lean_ctor_set(x_1024, 4, x_1015);
lean_ctor_set(x_1024, 5, x_1016);
lean_ctor_set(x_1024, 6, x_1017);
lean_ctor_set(x_1024, 7, x_1018);
lean_ctor_set(x_1024, 8, x_1019);
lean_ctor_set(x_1024, 9, x_1008);
lean_ctor_set_uint8(x_1024, sizeof(void*)*10, x_1020);
lean_ctor_set_uint8(x_1024, sizeof(void*)*10 + 1, x_1021);
lean_ctor_set_uint8(x_1024, sizeof(void*)*10 + 2, x_1022);
x_1058 = l_Lean_Syntax_isNone(x_117);
if (x_1058 == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1059 = l_Lean_Syntax_getArg(x_117, x_121);
lean_dec(x_117);
x_1060 = l_Lean_Elab_Term_getCurrMacroScope(x_1024, x_1010);
x_1061 = lean_ctor_get(x_1060, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1060, 1);
lean_inc(x_1062);
lean_dec(x_1060);
x_1063 = l_Lean_Elab_Term_getMainModule___rarg(x_1062);
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = lean_box(0);
x_1067 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_1068 = l_Lean_addMacroScope(x_1064, x_1067, x_1061);
x_1069 = lean_box(0);
x_1070 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_1071 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1071, 0, x_1066);
lean_ctor_set(x_1071, 1, x_1070);
lean_ctor_set(x_1071, 2, x_1068);
lean_ctor_set(x_1071, 3, x_1069);
x_1072 = l_Array_empty___closed__1;
x_1073 = lean_array_push(x_1072, x_1071);
x_1074 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1075 = lean_array_push(x_1073, x_1074);
x_1076 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_1075);
x_1077 = lean_array_push(x_1075, x_1076);
x_1078 = lean_array_push(x_1077, x_115);
x_1079 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_1080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1080, 0, x_1079);
lean_ctor_set(x_1080, 1, x_1078);
x_1081 = lean_array_push(x_1072, x_1080);
x_1082 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_1083 = lean_array_push(x_1081, x_1082);
x_1084 = l_Lean_mkTermIdFromIdent___closed__2;
x_1085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1085, 0, x_1084);
lean_ctor_set(x_1085, 1, x_1075);
x_1086 = lean_array_push(x_1072, x_1085);
x_1087 = l_Lean_nullKind___closed__2;
x_1088 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1088, 0, x_1087);
lean_ctor_set(x_1088, 1, x_1086);
x_1089 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_1090 = lean_array_push(x_1089, x_1088);
x_1091 = lean_array_push(x_1090, x_1074);
x_1092 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_1093 = lean_array_push(x_1091, x_1092);
x_1094 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_1095 = lean_array_push(x_1093, x_1094);
x_1096 = lean_array_push(x_1072, x_113);
x_1097 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1097, 0, x_1087);
lean_ctor_set(x_1097, 1, x_1096);
x_1098 = lean_array_push(x_1072, x_1097);
x_1099 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1100 = lean_array_push(x_1098, x_1099);
x_1101 = lean_array_push(x_1100, x_654);
x_1102 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1103, 0, x_1102);
lean_ctor_set(x_1103, 1, x_1101);
x_1104 = lean_array_push(x_1072, x_1103);
x_1105 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_1106 = lean_array_push(x_1104, x_1105);
x_1107 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5;
x_1108 = lean_array_push(x_1107, x_1059);
x_1109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1109, 0, x_1102);
lean_ctor_set(x_1109, 1, x_1108);
x_1110 = lean_array_push(x_1106, x_1109);
x_1111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1111, 0, x_1087);
lean_ctor_set(x_1111, 1, x_1110);
x_1112 = lean_array_push(x_1095, x_1111);
x_1113 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1113);
lean_ctor_set(x_1114, 1, x_1112);
x_1115 = lean_array_push(x_1072, x_1114);
x_1116 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_1115);
x_1118 = lean_array_push(x_1083, x_1117);
x_1119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1119, 0, x_1087);
lean_ctor_set(x_1119, 1, x_1118);
x_1120 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1121 = lean_array_push(x_1120, x_1119);
x_1122 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1123, 0, x_1122);
lean_ctor_set(x_1123, 1, x_1121);
x_1025 = x_1123;
x_1026 = x_1065;
goto block_1057;
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_117);
x_1124 = l_Lean_Elab_Term_getCurrMacroScope(x_1024, x_1010);
x_1125 = lean_ctor_get(x_1124, 0);
lean_inc(x_1125);
x_1126 = lean_ctor_get(x_1124, 1);
lean_inc(x_1126);
lean_dec(x_1124);
x_1127 = l_Lean_Elab_Term_getMainModule___rarg(x_1126);
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1127, 1);
lean_inc(x_1129);
lean_dec(x_1127);
x_1130 = lean_box(0);
x_1131 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_1132 = l_Lean_addMacroScope(x_1128, x_1131, x_1125);
x_1133 = lean_box(0);
x_1134 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_1135 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1135, 0, x_1130);
lean_ctor_set(x_1135, 1, x_1134);
lean_ctor_set(x_1135, 2, x_1132);
lean_ctor_set(x_1135, 3, x_1133);
x_1136 = l_Array_empty___closed__1;
x_1137 = lean_array_push(x_1136, x_1135);
x_1138 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_1139 = lean_array_push(x_1137, x_1138);
x_1140 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_1139);
x_1141 = lean_array_push(x_1139, x_1140);
x_1142 = lean_array_push(x_1141, x_115);
x_1143 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_1144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1144, 0, x_1143);
lean_ctor_set(x_1144, 1, x_1142);
x_1145 = lean_array_push(x_1136, x_1144);
x_1146 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_1147 = lean_array_push(x_1145, x_1146);
x_1148 = l_Lean_mkTermIdFromIdent___closed__2;
x_1149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1149, 0, x_1148);
lean_ctor_set(x_1149, 1, x_1139);
x_1150 = lean_array_push(x_1136, x_1149);
x_1151 = l_Lean_nullKind___closed__2;
x_1152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1152, 0, x_1151);
lean_ctor_set(x_1152, 1, x_1150);
x_1153 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_1154 = lean_array_push(x_1153, x_1152);
x_1155 = lean_array_push(x_1154, x_1138);
x_1156 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_1157 = lean_array_push(x_1155, x_1156);
x_1158 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_1159 = lean_array_push(x_1157, x_1158);
x_1160 = lean_array_push(x_1136, x_113);
x_1161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1161, 0, x_1151);
lean_ctor_set(x_1161, 1, x_1160);
x_1162 = lean_array_push(x_1136, x_1161);
x_1163 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_1164 = lean_array_push(x_1162, x_1163);
x_1165 = lean_array_push(x_1164, x_654);
x_1166 = l_Lean_Parser_Term_matchAlt___closed__2;
x_1167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1167, 0, x_1166);
lean_ctor_set(x_1167, 1, x_1165);
x_1168 = lean_array_push(x_1136, x_1167);
x_1169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1169, 0, x_1151);
lean_ctor_set(x_1169, 1, x_1168);
x_1170 = lean_array_push(x_1159, x_1169);
x_1171 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_1172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1172, 0, x_1171);
lean_ctor_set(x_1172, 1, x_1170);
x_1173 = lean_array_push(x_1136, x_1172);
x_1174 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_1175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1175, 0, x_1174);
lean_ctor_set(x_1175, 1, x_1173);
x_1176 = lean_array_push(x_1147, x_1175);
x_1177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1177, 0, x_1151);
lean_ctor_set(x_1177, 1, x_1176);
x_1178 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1179 = lean_array_push(x_1178, x_1177);
x_1180 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1181, 0, x_1180);
lean_ctor_set(x_1181, 1, x_1179);
x_1025 = x_1181;
x_1026 = x_1129;
goto block_1057;
}
block_1057:
{
uint8_t x_1027; 
x_1027 = lean_nat_dec_eq(x_3, x_112);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_53);
x_1028 = l_Array_extract___rarg(x_2, x_112, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_1029 = l_Lean_mkOptionalNode___closed__2;
x_1030 = lean_array_push(x_1029, x_1025);
x_1031 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_1032 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1032, 0, x_1031);
lean_ctor_set(x_1032, 1, x_1030);
x_1033 = lean_array_push(x_1028, x_1032);
x_1034 = l_Lean_Elab_Term_getCurrMacroScope(x_1024, x_1026);
lean_dec(x_1024);
x_1035 = lean_ctor_get(x_1034, 1);
lean_inc(x_1035);
lean_dec(x_1034);
x_1036 = l_Lean_Elab_Term_getMainModule___rarg(x_1035);
x_1037 = lean_ctor_get(x_1036, 1);
lean_inc(x_1037);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1038 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1038 = lean_box(0);
}
x_1039 = l_Array_empty___closed__1;
x_1040 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1033, x_1033, x_112, x_1039);
lean_dec(x_1033);
x_1041 = l_Lean_nullKind___closed__2;
x_1042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1042, 0, x_1041);
lean_ctor_set(x_1042, 1, x_1040);
x_1043 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_1044 = lean_array_push(x_1043, x_1042);
x_1045 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_1046 = lean_array_push(x_1044, x_1045);
x_1047 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_1048 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1048, 0, x_1047);
lean_ctor_set(x_1048, 1, x_1046);
x_1049 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1050 = lean_array_push(x_1049, x_1048);
x_1051 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_1050);
x_1053 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1053, 0, x_1052);
if (lean_is_scalar(x_1038)) {
 x_1054 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1054 = x_1038;
}
lean_ctor_set(x_1054, 0, x_1053);
lean_ctor_set(x_1054, 1, x_1037);
return x_1054;
}
else
{
lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1024);
lean_dec(x_3);
lean_dec(x_2);
x_1055 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1055, 0, x_1025);
if (lean_is_scalar(x_53)) {
 x_1056 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1056 = x_53;
}
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_1026);
return x_1056;
}
}
}
}
}
}
else
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; uint8_t x_1188; 
lean_dec(x_54);
lean_dec(x_53);
x_1182 = lean_unsigned_to_nat(1u);
x_1183 = l_Lean_Syntax_getArg(x_49, x_1182);
lean_dec(x_49);
x_1184 = lean_unsigned_to_nat(2u);
x_1185 = lean_nat_add(x_3, x_1184);
x_1186 = l_Array_extract___rarg(x_2, x_1185, x_6);
lean_dec(x_6);
x_1187 = lean_array_get_size(x_1186);
x_1188 = lean_nat_dec_eq(x_1187, x_1182);
lean_dec(x_1187);
if (x_1188 == 0)
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; uint8_t x_1211; 
x_1189 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_52);
x_1190 = lean_ctor_get(x_1189, 1);
lean_inc(x_1190);
lean_dec(x_1189);
x_1191 = l_Lean_Elab_Term_getMainModule___rarg(x_1190);
x_1192 = lean_ctor_get(x_1191, 1);
lean_inc(x_1192);
lean_dec(x_1191);
x_1193 = lean_unsigned_to_nat(0u);
x_1194 = l_Array_empty___closed__1;
x_1195 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1186, x_1186, x_1193, x_1194);
lean_dec(x_1186);
x_1196 = l_Lean_nullKind___closed__2;
x_1197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1197, 0, x_1196);
lean_ctor_set(x_1197, 1, x_1195);
x_1198 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_1199 = lean_array_push(x_1198, x_1197);
x_1200 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_1201 = lean_array_push(x_1199, x_1200);
x_1202 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_1203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1203, 0, x_1202);
lean_ctor_set(x_1203, 1, x_1201);
x_1204 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1205 = lean_array_push(x_1204, x_1203);
x_1206 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1206);
lean_ctor_set(x_1207, 1, x_1205);
x_1208 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1192);
x_1209 = lean_ctor_get(x_1208, 1);
lean_inc(x_1209);
lean_dec(x_1208);
x_1210 = l_Lean_Elab_Term_getMainModule___rarg(x_1209);
x_1211 = !lean_is_exclusive(x_1210);
if (x_1211 == 0)
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; uint8_t x_1221; 
x_1212 = lean_ctor_get(x_1210, 1);
x_1213 = lean_ctor_get(x_1210, 0);
lean_dec(x_1213);
x_1214 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_1215 = lean_array_push(x_1214, x_1183);
x_1216 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_1217 = lean_array_push(x_1215, x_1216);
x_1218 = lean_array_push(x_1217, x_1207);
x_1219 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_1220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1220, 0, x_1219);
lean_ctor_set(x_1220, 1, x_1218);
x_1221 = lean_nat_dec_eq(x_3, x_1193);
if (x_1221 == 0)
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; uint8_t x_1231; 
lean_free_object(x_1210);
x_1222 = l_Array_extract___rarg(x_2, x_1193, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_1223 = l_Lean_mkOptionalNode___closed__2;
x_1224 = lean_array_push(x_1223, x_1220);
x_1225 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_1226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1226, 0, x_1225);
lean_ctor_set(x_1226, 1, x_1224);
x_1227 = lean_array_push(x_1222, x_1226);
x_1228 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1212);
lean_dec(x_4);
x_1229 = lean_ctor_get(x_1228, 1);
lean_inc(x_1229);
lean_dec(x_1228);
x_1230 = l_Lean_Elab_Term_getMainModule___rarg(x_1229);
x_1231 = !lean_is_exclusive(x_1230);
if (x_1231 == 0)
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1232 = lean_ctor_get(x_1230, 0);
lean_dec(x_1232);
x_1233 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1227, x_1227, x_1193, x_1194);
lean_dec(x_1227);
x_1234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1234, 0, x_1196);
lean_ctor_set(x_1234, 1, x_1233);
x_1235 = lean_array_push(x_1198, x_1234);
x_1236 = lean_array_push(x_1235, x_1200);
x_1237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1237, 0, x_1202);
lean_ctor_set(x_1237, 1, x_1236);
x_1238 = lean_array_push(x_1204, x_1237);
x_1239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1239, 0, x_1206);
lean_ctor_set(x_1239, 1, x_1238);
x_1240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1240, 0, x_1239);
lean_ctor_set(x_1230, 0, x_1240);
return x_1230;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
x_1241 = lean_ctor_get(x_1230, 1);
lean_inc(x_1241);
lean_dec(x_1230);
x_1242 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1227, x_1227, x_1193, x_1194);
lean_dec(x_1227);
x_1243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1243, 0, x_1196);
lean_ctor_set(x_1243, 1, x_1242);
x_1244 = lean_array_push(x_1198, x_1243);
x_1245 = lean_array_push(x_1244, x_1200);
x_1246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1246, 0, x_1202);
lean_ctor_set(x_1246, 1, x_1245);
x_1247 = lean_array_push(x_1204, x_1246);
x_1248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1248, 0, x_1206);
lean_ctor_set(x_1248, 1, x_1247);
x_1249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1249, 0, x_1248);
x_1250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1250, 0, x_1249);
lean_ctor_set(x_1250, 1, x_1241);
return x_1250;
}
}
else
{
lean_object* x_1251; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1251, 0, x_1220);
lean_ctor_set(x_1210, 0, x_1251);
return x_1210;
}
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; 
x_1252 = lean_ctor_get(x_1210, 1);
lean_inc(x_1252);
lean_dec(x_1210);
x_1253 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_1254 = lean_array_push(x_1253, x_1183);
x_1255 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_1256 = lean_array_push(x_1254, x_1255);
x_1257 = lean_array_push(x_1256, x_1207);
x_1258 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_1259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1259, 0, x_1258);
lean_ctor_set(x_1259, 1, x_1257);
x_1260 = lean_nat_dec_eq(x_3, x_1193);
if (x_1260 == 0)
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1261 = l_Array_extract___rarg(x_2, x_1193, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_1262 = l_Lean_mkOptionalNode___closed__2;
x_1263 = lean_array_push(x_1262, x_1259);
x_1264 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_1265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1265, 0, x_1264);
lean_ctor_set(x_1265, 1, x_1263);
x_1266 = lean_array_push(x_1261, x_1265);
x_1267 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1252);
lean_dec(x_4);
x_1268 = lean_ctor_get(x_1267, 1);
lean_inc(x_1268);
lean_dec(x_1267);
x_1269 = l_Lean_Elab_Term_getMainModule___rarg(x_1268);
x_1270 = lean_ctor_get(x_1269, 1);
lean_inc(x_1270);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1271 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1271 = lean_box(0);
}
x_1272 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1266, x_1266, x_1193, x_1194);
lean_dec(x_1266);
x_1273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1273, 0, x_1196);
lean_ctor_set(x_1273, 1, x_1272);
x_1274 = lean_array_push(x_1198, x_1273);
x_1275 = lean_array_push(x_1274, x_1200);
x_1276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1276, 0, x_1202);
lean_ctor_set(x_1276, 1, x_1275);
x_1277 = lean_array_push(x_1204, x_1276);
x_1278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1278, 0, x_1206);
lean_ctor_set(x_1278, 1, x_1277);
x_1279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1279, 0, x_1278);
if (lean_is_scalar(x_1271)) {
 x_1280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1280 = x_1271;
}
lean_ctor_set(x_1280, 0, x_1279);
lean_ctor_set(x_1280, 1, x_1270);
return x_1280;
}
else
{
lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1281, 0, x_1259);
x_1282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1282, 0, x_1281);
lean_ctor_set(x_1282, 1, x_1252);
return x_1282;
}
}
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; uint8_t x_1290; 
x_1283 = l_Lean_Syntax_inhabited;
x_1284 = lean_unsigned_to_nat(0u);
x_1285 = lean_array_get(x_1283, x_1186, x_1284);
lean_dec(x_1186);
x_1286 = l_Lean_Syntax_getArg(x_1285, x_1284);
lean_dec(x_1285);
x_1287 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_52);
x_1288 = lean_ctor_get(x_1287, 1);
lean_inc(x_1288);
lean_dec(x_1287);
x_1289 = l_Lean_Elab_Term_getMainModule___rarg(x_1288);
x_1290 = !lean_is_exclusive(x_1289);
if (x_1290 == 0)
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; uint8_t x_1300; 
x_1291 = lean_ctor_get(x_1289, 1);
x_1292 = lean_ctor_get(x_1289, 0);
lean_dec(x_1292);
x_1293 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_1294 = lean_array_push(x_1293, x_1183);
x_1295 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_1296 = lean_array_push(x_1294, x_1295);
x_1297 = lean_array_push(x_1296, x_1286);
x_1298 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_1299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1299, 0, x_1298);
lean_ctor_set(x_1299, 1, x_1297);
x_1300 = lean_nat_dec_eq(x_3, x_1284);
if (x_1300 == 0)
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; uint8_t x_1310; 
lean_free_object(x_1289);
x_1301 = l_Array_extract___rarg(x_2, x_1284, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_1302 = l_Lean_mkOptionalNode___closed__2;
x_1303 = lean_array_push(x_1302, x_1299);
x_1304 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_1305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1305, 0, x_1304);
lean_ctor_set(x_1305, 1, x_1303);
x_1306 = lean_array_push(x_1301, x_1305);
x_1307 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1291);
lean_dec(x_4);
x_1308 = lean_ctor_get(x_1307, 1);
lean_inc(x_1308);
lean_dec(x_1307);
x_1309 = l_Lean_Elab_Term_getMainModule___rarg(x_1308);
x_1310 = !lean_is_exclusive(x_1309);
if (x_1310 == 0)
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
x_1311 = lean_ctor_get(x_1309, 0);
lean_dec(x_1311);
x_1312 = l_Array_empty___closed__1;
x_1313 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1306, x_1306, x_1284, x_1312);
lean_dec(x_1306);
x_1314 = l_Lean_nullKind___closed__2;
x_1315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1315, 0, x_1314);
lean_ctor_set(x_1315, 1, x_1313);
x_1316 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_1317 = lean_array_push(x_1316, x_1315);
x_1318 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_1319 = lean_array_push(x_1317, x_1318);
x_1320 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_1321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1321, 0, x_1320);
lean_ctor_set(x_1321, 1, x_1319);
x_1322 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1323 = lean_array_push(x_1322, x_1321);
x_1324 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1325, 0, x_1324);
lean_ctor_set(x_1325, 1, x_1323);
x_1326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1326, 0, x_1325);
lean_ctor_set(x_1309, 0, x_1326);
return x_1309;
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
x_1327 = lean_ctor_get(x_1309, 1);
lean_inc(x_1327);
lean_dec(x_1309);
x_1328 = l_Array_empty___closed__1;
x_1329 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1306, x_1306, x_1284, x_1328);
lean_dec(x_1306);
x_1330 = l_Lean_nullKind___closed__2;
x_1331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1331, 0, x_1330);
lean_ctor_set(x_1331, 1, x_1329);
x_1332 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_1333 = lean_array_push(x_1332, x_1331);
x_1334 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_1335 = lean_array_push(x_1333, x_1334);
x_1336 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_1337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1337, 0, x_1336);
lean_ctor_set(x_1337, 1, x_1335);
x_1338 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1339 = lean_array_push(x_1338, x_1337);
x_1340 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1341, 0, x_1340);
lean_ctor_set(x_1341, 1, x_1339);
x_1342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1342, 0, x_1341);
x_1343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1343, 0, x_1342);
lean_ctor_set(x_1343, 1, x_1327);
return x_1343;
}
}
else
{
lean_object* x_1344; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1344, 0, x_1299);
lean_ctor_set(x_1289, 0, x_1344);
return x_1289;
}
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; uint8_t x_1353; 
x_1345 = lean_ctor_get(x_1289, 1);
lean_inc(x_1345);
lean_dec(x_1289);
x_1346 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_1347 = lean_array_push(x_1346, x_1183);
x_1348 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_1349 = lean_array_push(x_1347, x_1348);
x_1350 = lean_array_push(x_1349, x_1286);
x_1351 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_1352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1352, 0, x_1351);
lean_ctor_set(x_1352, 1, x_1350);
x_1353 = lean_nat_dec_eq(x_3, x_1284);
if (x_1353 == 0)
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; 
x_1354 = l_Array_extract___rarg(x_2, x_1284, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_1355 = l_Lean_mkOptionalNode___closed__2;
x_1356 = lean_array_push(x_1355, x_1352);
x_1357 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_1358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1358, 0, x_1357);
lean_ctor_set(x_1358, 1, x_1356);
x_1359 = lean_array_push(x_1354, x_1358);
x_1360 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1345);
lean_dec(x_4);
x_1361 = lean_ctor_get(x_1360, 1);
lean_inc(x_1361);
lean_dec(x_1360);
x_1362 = l_Lean_Elab_Term_getMainModule___rarg(x_1361);
x_1363 = lean_ctor_get(x_1362, 1);
lean_inc(x_1363);
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 lean_ctor_release(x_1362, 1);
 x_1364 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1364 = lean_box(0);
}
x_1365 = l_Array_empty___closed__1;
x_1366 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1359, x_1359, x_1284, x_1365);
lean_dec(x_1359);
x_1367 = l_Lean_nullKind___closed__2;
x_1368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1368, 0, x_1367);
lean_ctor_set(x_1368, 1, x_1366);
x_1369 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2;
x_1370 = lean_array_push(x_1369, x_1368);
x_1371 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3;
x_1372 = lean_array_push(x_1370, x_1371);
x_1373 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_1374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1374, 0, x_1373);
lean_ctor_set(x_1374, 1, x_1372);
x_1375 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_1376 = lean_array_push(x_1375, x_1374);
x_1377 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_1378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1378, 0, x_1377);
lean_ctor_set(x_1378, 1, x_1376);
x_1379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1379, 0, x_1378);
if (lean_is_scalar(x_1364)) {
 x_1380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1380 = x_1364;
}
lean_ctor_set(x_1380, 0, x_1379);
lean_ctor_set(x_1380, 1, x_1363);
return x_1380;
}
else
{
lean_object* x_1381; lean_object* x_1382; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1381, 0, x_1352);
x_1382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1382, 0, x_1381);
lean_ctor_set(x_1382, 1, x_1345);
return x_1382;
}
}
}
}
}
else
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; uint8_t x_1396; 
lean_dec(x_49);
x_1383 = lean_ctor_get(x_50, 1);
lean_inc(x_1383);
lean_dec(x_50);
x_1384 = lean_ctor_get(x_51, 0);
lean_inc(x_1384);
lean_dec(x_51);
x_1385 = lean_unsigned_to_nat(1u);
x_1386 = lean_nat_add(x_3, x_1385);
x_1387 = l_Array_extract___rarg(x_2, x_1386, x_6);
lean_dec(x_6);
x_1388 = lean_unsigned_to_nat(0u);
x_1389 = l_Array_extract___rarg(x_2, x_1388, x_3);
lean_dec(x_2);
x_1390 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1384, x_1384, x_1388, x_1389);
lean_dec(x_1384);
x_1391 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1387, x_1387, x_1388, x_1390);
lean_dec(x_1387);
x_1392 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1383);
x_1393 = lean_ctor_get(x_1392, 1);
lean_inc(x_1393);
lean_dec(x_1392);
x_1394 = l_Lean_Elab_Term_getMainModule___rarg(x_1393);
x_1395 = lean_ctor_get(x_1394, 1);
lean_inc(x_1395);
lean_dec(x_1394);
x_1396 = 1;
x_1 = x_1396;
x_2 = x_1391;
x_5 = x_1395;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_8__ensureDoElemType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = l_Lean_Elab_Term_ensureHasType(x_1, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_8__ensureDoElemType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_DoNotation_8__ensureDoElemType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_Inhabited___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_ProcessedDoElem_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type former application expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 7);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 8);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 9);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 2;
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 6, x_22);
x_23 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_8);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_10);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_12);
lean_ctor_set(x_23, 7, x_13);
lean_ctor_set(x_23, 8, x_14);
lean_ctor_set(x_23, 9, x_15);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_17);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 1, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 2, x_19);
x_24 = l_Lean_Elab_Term_whnf(x_1, x_2, x_23, x_4);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
if (lean_obj_tag(x_26) == 5)
{
lean_object* x_35; 
lean_dec(x_3);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; 
lean_free_object(x_24);
x_36 = lean_box(0);
x_28 = x_36;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = l_Lean_indentExpr(x_29);
x_31 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Term_throwError___rarg(x_1, x_32, x_3, x_27);
return x_33;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
if (lean_obj_tag(x_37) == 5)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_box(0);
x_39 = x_48;
goto block_45;
}
block_45:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_41 = l_Lean_indentExpr(x_40);
x_42 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Elab_Term_throwError___rarg(x_1, x_43, x_3, x_38);
return x_44;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_6, 0);
x_54 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_55 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_56 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_57 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_58 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_59 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
lean_inc(x_53);
lean_dec(x_6);
x_60 = 2;
x_61 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_54);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 1, x_55);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 2, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 3, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 4, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 5, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 6, x_60);
lean_ctor_set(x_5, 0, x_61);
x_62 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_7);
lean_ctor_set(x_62, 2, x_8);
lean_ctor_set(x_62, 3, x_9);
lean_ctor_set(x_62, 4, x_10);
lean_ctor_set(x_62, 5, x_11);
lean_ctor_set(x_62, 6, x_12);
lean_ctor_set(x_62, 7, x_13);
lean_ctor_set(x_62, 8, x_14);
lean_ctor_set(x_62, 9, x_15);
lean_ctor_set_uint8(x_62, sizeof(void*)*10, x_17);
lean_ctor_set_uint8(x_62, sizeof(void*)*10 + 1, x_18);
lean_ctor_set_uint8(x_62, sizeof(void*)*10 + 2, x_19);
x_63 = l_Lean_Elab_Term_whnf(x_1, x_2, x_62, x_4);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
if (lean_obj_tag(x_64) == 5)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_3);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
lean_dec(x_64);
if (lean_is_scalar(x_66)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_66;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_65);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_66);
x_76 = lean_box(0);
x_67 = x_76;
goto block_73;
}
block_73:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_67);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_64);
x_69 = l_Lean_indentExpr(x_68);
x_70 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Elab_Term_throwError___rarg(x_1, x_71, x_3, x_65);
return x_72;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_79 = x_63;
} else {
 lean_dec_ref(x_63);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_81 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_82 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_83 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_84 = lean_ctor_get(x_5, 1);
x_85 = lean_ctor_get(x_5, 2);
x_86 = lean_ctor_get(x_5, 3);
x_87 = lean_ctor_get(x_5, 4);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_5);
x_88 = lean_ctor_get(x_6, 0);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_90 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_91 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_92 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_93 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_94 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_95 = x_6;
} else {
 lean_dec_ref(x_6);
 x_95 = lean_box(0);
}
x_96 = 2;
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 1, 7);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_89);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 1, x_90);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 2, x_91);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 3, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 4, x_93);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 5, x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 6, x_96);
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_84);
lean_ctor_set(x_98, 2, x_85);
lean_ctor_set(x_98, 3, x_86);
lean_ctor_set(x_98, 4, x_87);
x_99 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_7);
lean_ctor_set(x_99, 2, x_8);
lean_ctor_set(x_99, 3, x_9);
lean_ctor_set(x_99, 4, x_10);
lean_ctor_set(x_99, 5, x_11);
lean_ctor_set(x_99, 6, x_12);
lean_ctor_set(x_99, 7, x_13);
lean_ctor_set(x_99, 8, x_14);
lean_ctor_set(x_99, 9, x_15);
lean_ctor_set_uint8(x_99, sizeof(void*)*10, x_81);
lean_ctor_set_uint8(x_99, sizeof(void*)*10 + 1, x_82);
lean_ctor_set_uint8(x_99, sizeof(void*)*10 + 2, x_83);
x_100 = l_Lean_Elab_Term_whnf(x_1, x_2, x_99, x_4);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
if (lean_obj_tag(x_101) == 5)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_3);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
lean_dec(x_101);
if (lean_is_scalar(x_103)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_103;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_102);
return x_112;
}
else
{
lean_object* x_113; 
lean_dec(x_103);
x_113 = lean_box(0);
x_104 = x_113;
goto block_110;
}
block_110:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_104);
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_101);
x_106 = l_Lean_indentExpr(x_105);
x_107 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
x_108 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Elab_Term_throwError___rarg(x_1, x_108, x_3, x_102);
return x_109;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_3);
x_114 = lean_ctor_get(x_100, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_100, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_116 = x_100;
} else {
 lean_dec_ref(x_100);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_back___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Elab_Term_ProcessedDoElem_inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_15);
x_17 = l_Lean_Elab_Term_inferType(x_1, x_15, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Elab_Term_inferType(x_1, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
x_23 = l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(x_1, x_21, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_mkOptionalNode___closed__2;
x_27 = lean_array_push(x_26, x_15);
lean_inc(x_8);
x_28 = l_Lean_Elab_Term_mkLambda(x_1, x_27, x_7, x_8, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_32 = lean_array_push(x_31, x_18);
x_33 = lean_array_push(x_32, x_24);
x_34 = lean_array_push(x_33, x_16);
x_35 = lean_array_push(x_34, x_29);
lean_inc(x_3);
x_36 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_35, x_35, x_10, x_3);
lean_dec(x_35);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_36;
x_9 = x_30;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_7);
lean_ctor_set(x_54, 1, x_9);
return x_54;
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_10__mkBind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Array_back___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__1(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_6);
x_11 = l_Lean_Elab_Term_inferType(x_1, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_getLevel(x_1, x_12, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
x_17 = l_Lean_Elab_Term_decLevel(x_1, x_15, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Elab_Term_inferType(x_1, x_5, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_6);
x_23 = l_Lean_Elab_Term_getLevel(x_1, x_21, x_6, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_6);
x_26 = l_Lean_Elab_Term_decLevel(x_1, x_24, x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_33 = l_Lean_mkConst(x_32, x_31);
x_34 = l_Lean_mkAppB(x_33, x_2, x_3);
x_35 = lean_array_get_size(x_4);
x_36 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__2(x_1, x_4, x_34, x_4, x_35, lean_box(0), x_5, x_6, x_28);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_26);
if (x_37 == 0)
{
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
return x_11;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_11, 0);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_11);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
}
}
lean_object* l_Array_back___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_10__mkBind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_DoNotation_10__mkBind(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_array_push(x_3, x_13);
x_15 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main(x_4, x_5, x_6, x_7, x_12, x_14, x_9, x_10);
return x_15;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected 'do' expression element");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("the last statement in a 'do' block must be an expression");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Syntax_inhabited;
x_10 = lean_array_get(x_9, x_1, x_5);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_17 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Term_throwError___rarg(x_10, x_18, x_7, x_8);
lean_dec(x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_array_get_size(x_1);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_nat_dec_eq(x_5, x_22);
lean_dec(x_22);
lean_dec(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_10);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_10);
x_25 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Term_throwError___rarg(x_10, x_26, x_7, x_8);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Syntax_getArg(x_10, x_32);
lean_inc(x_4);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_4);
x_35 = 1;
lean_inc(x_7);
x_36 = l_Lean_Elab_Term_elabTermAux___main(x_34, x_35, x_33, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_7);
lean_inc(x_10);
x_39 = l___private_Init_Lean_Elab_DoNotation_8__ensureDoElemType(x_10, x_2, x_4, x_37, x_7, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Init_Lean_Elab_DoNotation_10__mkBind(x_10, x_2, x_3, x_6, x_40, x_7, x_41);
lean_dec(x_6);
lean_dec(x_10);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_11);
x_51 = lean_array_get_size(x_1);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_51, x_52);
lean_dec(x_51);
x_54 = lean_nat_dec_eq(x_5, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Syntax_getIdAt(x_10, x_55);
x_57 = l_Lean_Syntax_getArg(x_10, x_52);
x_58 = l_Lean_Elab_Term_expandOptType(x_10, x_57);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = l_Lean_Syntax_getArg(x_10, x_59);
lean_inc(x_7);
x_61 = l_Lean_Elab_Term_elabType(x_58, x_7, x_8);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_62);
lean_inc(x_2);
x_64 = l_Lean_mkApp(x_2, x_62);
lean_inc(x_64);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = 1;
lean_inc(x_7);
lean_inc(x_60);
x_67 = l_Lean_Elab_Term_elabTermAux___main(x_65, x_66, x_60, x_7, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_7);
x_70 = l___private_Init_Lean_Elab_DoNotation_8__ensureDoElemType(x_60, x_2, x_64, x_68, x_7, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1___boxed), 10, 7);
lean_closure_set(x_73, 0, x_5);
lean_closure_set(x_73, 1, x_71);
lean_closure_set(x_73, 2, x_6);
lean_closure_set(x_73, 3, x_1);
lean_closure_set(x_73, 4, x_2);
lean_closure_set(x_73, 5, x_3);
lean_closure_set(x_73, 6, x_4);
x_74 = l_Lean_Elab_Term_withLocalDecl___rarg(x_10, x_56, x_62, x_73, x_7, x_72);
lean_dec(x_10);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_62);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_67);
if (x_79 == 0)
{
return x_67;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_67, 0);
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_67);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_60);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_61);
if (x_83 == 0)
{
return x_61;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_61, 0);
x_85 = lean_ctor_get(x_61, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7;
x_88 = l_Lean_Elab_Term_throwError___rarg(x_10, x_87, x_7, x_8);
lean_dec(x_10);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
return x_88;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_12__processDoElems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_empty___closed__1;
x_9 = l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main(x_1, x_2, x_3, x_4, x_7, x_8, x_5, x_6);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_elabDo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabDo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_1);
x_48 = 0;
x_49 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_7);
x_50 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main(x_48, x_7, x_49, x_3, x_6);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Elab_Term_getOptions(x_3, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_elabDo___closed__1;
x_57 = l_Lean_checkTraceOption(x_54, x_56);
lean_dec(x_54);
if (x_57 == 0)
{
x_8 = x_55;
goto block_47;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_1);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_1);
x_59 = l_Lean_Elab_Term_logTrace(x_56, x_1, x_58, x_3, x_55);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_8 = x_60;
goto block_47;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_7);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_dec(x_50);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
x_63 = !lean_is_exclusive(x_3);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_3, 8);
lean_inc(x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_3, 8, x_66);
x_67 = 1;
x_68 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_67, x_62, x_3, x_61);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_69 = lean_ctor_get(x_3, 0);
x_70 = lean_ctor_get(x_3, 1);
x_71 = lean_ctor_get(x_3, 2);
x_72 = lean_ctor_get(x_3, 3);
x_73 = lean_ctor_get(x_3, 4);
x_74 = lean_ctor_get(x_3, 5);
x_75 = lean_ctor_get(x_3, 6);
x_76 = lean_ctor_get(x_3, 7);
x_77 = lean_ctor_get(x_3, 8);
x_78 = lean_ctor_get(x_3, 9);
x_79 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_80 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_81 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_3);
lean_inc(x_62);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_62);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
x_84 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_84, 0, x_69);
lean_ctor_set(x_84, 1, x_70);
lean_ctor_set(x_84, 2, x_71);
lean_ctor_set(x_84, 3, x_72);
lean_ctor_set(x_84, 4, x_73);
lean_ctor_set(x_84, 5, x_74);
lean_ctor_set(x_84, 6, x_75);
lean_ctor_set(x_84, 7, x_76);
lean_ctor_set(x_84, 8, x_83);
lean_ctor_set(x_84, 9, x_78);
lean_ctor_set_uint8(x_84, sizeof(void*)*10, x_79);
lean_ctor_set_uint8(x_84, sizeof(void*)*10 + 1, x_80);
lean_ctor_set_uint8(x_84, sizeof(void*)*10 + 2, x_81);
x_85 = 1;
x_86 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_85, x_62, x_84, x_61);
return x_86;
}
}
block_47:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_9, x_7, x_10, x_11);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l___private_Init_Lean_Elab_DoNotation_2__extractMonad(x_1, x_2, x_3, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Expr_Inhabited;
x_19 = l_Option_get_x21___rarg___closed__3;
x_20 = lean_panic_fn(x_18, x_19);
x_21 = l___private_Init_Lean_Elab_DoNotation_12__processDoElems(x_12, x_16, x_17, x_20, x_3, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
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
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l___private_Init_Lean_Elab_DoNotation_12__processDoElems(x_12, x_31, x_32, x_33, x_3, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
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
uint8_t x_87; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_5);
if (x_87 == 0)
{
return x_5;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_5, 0);
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_5);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDo");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDo), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_13__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabDo___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_TermBinders(lean_object*);
lean_object* initialize_Init_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_DoNotation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_TermBinders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1);
l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2);
l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3);
l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4 = _init_l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4);
l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__1);
l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__2);
l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_2__extractMonad___closed__3);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__1);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__2);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__3);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__4 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__4);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElems___main___closed__5);
l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1 = _init_l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1);
l_Lean_Elab_Term_ProcessedDoElem_inhabited = _init_l_Lean_Elab_Term_ProcessedDoElem_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_ProcessedDoElem_inhabited);
l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1);
l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2);
l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3);
l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1);
l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2);
l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3);
l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4 = _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4);
l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5 = _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5);
l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6 = _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6);
l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7 = _init_l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7);
l_Lean_Elab_Term_elabDo___closed__1 = _init_l_Lean_Elab_Term_elabDo___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDo___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabDo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Init_Lean_Elab_DoNotation_13__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
