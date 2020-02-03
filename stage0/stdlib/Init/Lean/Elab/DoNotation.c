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
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_6__expandLiftMethod(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3;
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
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3;
lean_object* l_Lean_Elab_Term_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeInst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_3__getDoElems___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6;
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
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_12__processDoElems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
extern lean_object* l_Lean_Elab_Term_elabLetDecl___closed__4;
extern lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__2;
extern lean_object* l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__1___boxed(lean_object*);
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
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
lean_object* l___private_Init_Lean_Elab_DoNotation_8__expandDoElems(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5;
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3;
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Init_Lean_Elab_DoNotation_10__mkBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_object* lean_environment_main_module(lean_object*);
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
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractBind(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4;
lean_object* l___private_Init_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__4;
lean_object* l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l___private_Init_Lean_Elab_DoNotation_4__hasLiftMethod___main___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_inc(x_2);
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
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
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
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
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
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid do notation, expected type is not available");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractBind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_53; uint8_t x_54; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_53 = l_Lean_Expr_getAppFn___main(x_28);
x_54 = l_Lean_Expr_isMVar(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
x_30 = x_29;
goto block_52;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_28);
x_55 = l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3;
x_56 = l_Lean_Elab_Term_throwError___rarg(x_1, x_55, x_3, x_29);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_52:
{
if (lean_obj_tag(x_28) == 5)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
x_33 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_31);
x_34 = lean_array_push(x_33, x_31);
x_35 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_36 = l_Lean_Elab_Term_mkAppM(x_1, x_35, x_34, x_3, x_30);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
x_39 = l_Lean_Elab_Term_synthesizeInst(x_1, x_37, x_3, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_28);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_32);
lean_ctor_set(x_45, 2, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_32);
lean_dec(x_31);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_32);
lean_dec(x_31);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_dec(x_36);
x_50 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_49);
return x_50;
}
}
else
{
lean_object* x_51; 
x_51 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_30);
return x_51;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_27);
if (x_61 == 0)
{
return x_27;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_27, 0);
x_63 = lean_ctor_get(x_27, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_27);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_8, 0);
x_66 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_67 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_68 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
x_69 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_70 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 4);
x_71 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 5);
lean_inc(x_65);
lean_dec(x_8);
x_72 = 2;
x_73 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_66);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 1, x_67);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 2, x_68);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 3, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 4, x_70);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 5, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1 + 6, x_72);
lean_ctor_set(x_7, 0, x_73);
x_74 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_74, 0, x_7);
lean_ctor_set(x_74, 1, x_10);
lean_ctor_set(x_74, 2, x_11);
lean_ctor_set(x_74, 3, x_12);
lean_ctor_set(x_74, 4, x_13);
lean_ctor_set(x_74, 5, x_14);
lean_ctor_set(x_74, 6, x_15);
lean_ctor_set(x_74, 7, x_16);
lean_ctor_set(x_74, 8, x_17);
lean_ctor_set(x_74, 9, x_18);
lean_ctor_set_uint8(x_74, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_74, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_74, sizeof(void*)*10 + 2, x_22);
x_75 = l_Lean_Elab_Term_whnf(x_1, x_9, x_74, x_4);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_99; uint8_t x_100; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_99 = l_Lean_Expr_getAppFn___main(x_76);
x_100 = l_Lean_Expr_isMVar(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
x_78 = x_77;
goto block_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_76);
x_101 = l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3;
x_102 = l_Lean_Elab_Term_throwError___rarg(x_1, x_101, x_3, x_77);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
block_98:
{
if (lean_obj_tag(x_76) == 5)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
x_81 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_79);
x_82 = lean_array_push(x_81, x_79);
x_83 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_84 = l_Lean_Elab_Term_mkAppM(x_1, x_83, x_82, x_3, x_78);
lean_dec(x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_3);
x_87 = l_Lean_Elab_Term_synthesizeInst(x_1, x_85, x_3, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
lean_dec(x_3);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_80);
lean_ctor_set(x_91, 2, x_88);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_80);
lean_dec(x_79);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_76, x_3, x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_80);
lean_dec(x_79);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
lean_dec(x_84);
x_96 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_76, x_3, x_95);
return x_96;
}
}
else
{
lean_object* x_97; 
x_97 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_76, x_3, x_78);
return x_97;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_107 = lean_ctor_get(x_75, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_75, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_109 = x_75;
} else {
 lean_dec_ref(x_75);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_111 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_112 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_113 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_114 = lean_ctor_get(x_7, 1);
x_115 = lean_ctor_get(x_7, 2);
x_116 = lean_ctor_get(x_7, 3);
x_117 = lean_ctor_get(x_7, 4);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_7);
x_118 = lean_ctor_get(x_8, 0);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_120 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_121 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 2);
x_122 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 3);
x_123 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 4);
x_124 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_125 = x_8;
} else {
 lean_dec_ref(x_8);
 x_125 = lean_box(0);
}
x_126 = 2;
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 1, 7);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_119);
lean_ctor_set_uint8(x_127, sizeof(void*)*1 + 1, x_120);
lean_ctor_set_uint8(x_127, sizeof(void*)*1 + 2, x_121);
lean_ctor_set_uint8(x_127, sizeof(void*)*1 + 3, x_122);
lean_ctor_set_uint8(x_127, sizeof(void*)*1 + 4, x_123);
lean_ctor_set_uint8(x_127, sizeof(void*)*1 + 5, x_124);
lean_ctor_set_uint8(x_127, sizeof(void*)*1 + 6, x_126);
x_128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_114);
lean_ctor_set(x_128, 2, x_115);
lean_ctor_set(x_128, 3, x_116);
lean_ctor_set(x_128, 4, x_117);
x_129 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_10);
lean_ctor_set(x_129, 2, x_11);
lean_ctor_set(x_129, 3, x_12);
lean_ctor_set(x_129, 4, x_13);
lean_ctor_set(x_129, 5, x_14);
lean_ctor_set(x_129, 6, x_15);
lean_ctor_set(x_129, 7, x_16);
lean_ctor_set(x_129, 8, x_17);
lean_ctor_set(x_129, 9, x_18);
lean_ctor_set_uint8(x_129, sizeof(void*)*10, x_111);
lean_ctor_set_uint8(x_129, sizeof(void*)*10 + 1, x_112);
lean_ctor_set_uint8(x_129, sizeof(void*)*10 + 2, x_113);
x_130 = l_Lean_Elab_Term_whnf(x_1, x_9, x_129, x_4);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_154; uint8_t x_155; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_154 = l_Lean_Expr_getAppFn___main(x_131);
x_155 = l_Lean_Expr_isMVar(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
x_133 = x_132;
goto block_153;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_131);
x_156 = l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3;
x_157 = l_Lean_Elab_Term_throwError___rarg(x_1, x_156, x_3, x_132);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
block_153:
{
if (lean_obj_tag(x_131) == 5)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
x_136 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_134);
x_137 = lean_array_push(x_136, x_134);
x_138 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_139 = l_Lean_Elab_Term_mkAppM(x_1, x_138, x_137, x_3, x_133);
lean_dec(x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_3);
x_142 = l_Lean_Elab_Term_synthesizeInst(x_1, x_140, x_3, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_131);
lean_dec(x_3);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_134);
lean_ctor_set(x_146, 1, x_135);
lean_ctor_set(x_146, 2, x_143);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_135);
lean_dec(x_134);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_dec(x_142);
x_149 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_131, x_3, x_148);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_135);
lean_dec(x_134);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
lean_dec(x_139);
x_151 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_131, x_3, x_150);
return x_151;
}
}
else
{
lean_object* x_152; 
x_152 = l___private_Init_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_131, x_3, x_133);
return x_152;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_3);
x_162 = lean_ctor_get(x_130, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_130, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_164 = x_130;
} else {
 lean_dec_ref(x_130);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_2__extractBind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_DoNotation_2__extractBind(x_1, x_2, x_3, x_4);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_5);
x_30 = l_Lean_Syntax_inhabited;
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_array_get(x_30, x_6, x_31);
lean_dec(x_6);
x_33 = lean_nat_add(x_4, x_31);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
lean_dec(x_36);
lean_inc(x_4);
lean_inc(x_35);
lean_ctor_set(x_3, 1, x_4);
x_37 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_32, x_2, x_3, x_33);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_box(0);
x_44 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_45 = l_Lean_addMacroScope(x_35, x_44, x_4);
x_46 = lean_box(0);
x_47 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_46);
x_49 = l_Array_empty___closed__1;
x_50 = lean_array_push(x_49, x_48);
x_51 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_52 = lean_array_push(x_50, x_51);
x_53 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_52);
x_54 = lean_array_push(x_52, x_53);
x_55 = lean_array_push(x_54, x_41);
x_56 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_56);
x_57 = lean_array_push(x_49, x_1);
x_58 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_59 = lean_array_push(x_57, x_58);
x_60 = lean_box(0);
x_61 = lean_array_push(x_59, x_60);
x_62 = l_Lean_nullKind___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_65 = lean_array_push(x_64, x_63);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_7);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_66);
lean_dec(x_66);
x_68 = lean_array_pop(x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_68, x_68, x_69, x_42);
lean_dec(x_68);
x_71 = l_Lean_mkTermIdFromIdent___closed__2;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_52);
lean_ctor_set(x_39, 1, x_70);
lean_ctor_set(x_39, 0, x_72);
return x_37;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_73 = lean_ctor_get(x_39, 0);
x_74 = lean_ctor_get(x_39, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_39);
x_75 = lean_box(0);
x_76 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_77 = l_Lean_addMacroScope(x_35, x_76, x_4);
x_78 = lean_box(0);
x_79 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_77);
lean_ctor_set(x_80, 3, x_78);
x_81 = l_Array_empty___closed__1;
x_82 = lean_array_push(x_81, x_80);
x_83 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_84 = lean_array_push(x_82, x_83);
x_85 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_84);
x_86 = lean_array_push(x_84, x_85);
x_87 = lean_array_push(x_86, x_73);
x_88 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_87);
lean_ctor_set(x_1, 0, x_88);
x_89 = lean_array_push(x_81, x_1);
x_90 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_91 = lean_array_push(x_89, x_90);
x_92 = lean_box(0);
x_93 = lean_array_push(x_91, x_92);
x_94 = l_Lean_nullKind___closed__2;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_97 = lean_array_push(x_96, x_95);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_7);
lean_ctor_set(x_98, 1, x_97);
x_99 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_98);
lean_dec(x_98);
x_100 = lean_array_pop(x_99);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_100, x_100, x_101, x_74);
lean_dec(x_100);
x_103 = l_Lean_mkTermIdFromIdent___closed__2;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_84);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_37, 0, x_105);
return x_37;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_106 = lean_ctor_get(x_37, 0);
x_107 = lean_ctor_get(x_37, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_37);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
x_111 = lean_box(0);
x_112 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_113 = l_Lean_addMacroScope(x_35, x_112, x_4);
x_114 = lean_box(0);
x_115 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 3, x_114);
x_117 = l_Array_empty___closed__1;
x_118 = lean_array_push(x_117, x_116);
x_119 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_120 = lean_array_push(x_118, x_119);
x_121 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_120);
x_122 = lean_array_push(x_120, x_121);
x_123 = lean_array_push(x_122, x_108);
x_124 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_123);
lean_ctor_set(x_1, 0, x_124);
x_125 = lean_array_push(x_117, x_1);
x_126 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_127 = lean_array_push(x_125, x_126);
x_128 = lean_box(0);
x_129 = lean_array_push(x_127, x_128);
x_130 = l_Lean_nullKind___closed__2;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_133 = lean_array_push(x_132, x_131);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_7);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_134);
lean_dec(x_134);
x_136 = lean_array_pop(x_135);
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_136, x_136, x_137, x_109);
lean_dec(x_136);
x_139 = l_Lean_mkTermIdFromIdent___closed__2;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_120);
if (lean_is_scalar(x_110)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_110;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_107);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_143 = lean_ctor_get(x_3, 0);
lean_inc(x_143);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_143);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_4);
x_145 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_32, x_2, x_144, x_33);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_151 = x_146;
} else {
 lean_dec_ref(x_146);
 x_151 = lean_box(0);
}
x_152 = lean_box(0);
x_153 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_154 = l_Lean_addMacroScope(x_143, x_153, x_4);
x_155 = lean_box(0);
x_156 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_157 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_154);
lean_ctor_set(x_157, 3, x_155);
x_158 = l_Array_empty___closed__1;
x_159 = lean_array_push(x_158, x_157);
x_160 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_161 = lean_array_push(x_159, x_160);
x_162 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_161);
x_163 = lean_array_push(x_161, x_162);
x_164 = lean_array_push(x_163, x_149);
x_165 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_164);
lean_ctor_set(x_1, 0, x_165);
x_166 = lean_array_push(x_158, x_1);
x_167 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_168 = lean_array_push(x_166, x_167);
x_169 = lean_box(0);
x_170 = lean_array_push(x_168, x_169);
x_171 = l_Lean_nullKind___closed__2;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_174 = lean_array_push(x_173, x_172);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_7);
lean_ctor_set(x_175, 1, x_174);
x_176 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_175);
lean_dec(x_175);
x_177 = lean_array_pop(x_176);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_177, x_177, x_178, x_150);
lean_dec(x_177);
x_180 = l_Lean_mkTermIdFromIdent___closed__2;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_161);
if (lean_is_scalar(x_151)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_151;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
if (lean_is_scalar(x_148)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_148;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_147);
return x_183;
}
}
}
else
{
lean_object* x_184; uint8_t x_185; 
lean_dec(x_1);
x_184 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_185 = lean_name_eq(x_5, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_186 = lean_unsigned_to_nat(0u);
x_187 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(x_186, x_6, x_2, x_3, x_4);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_5);
lean_ctor_set(x_194, 1, x_191);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_192);
if (lean_is_scalar(x_190)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_190;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_189);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_5);
x_197 = l_Lean_Syntax_inhabited;
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_array_get(x_197, x_6, x_198);
lean_dec(x_6);
x_200 = lean_nat_add(x_4, x_198);
x_201 = lean_ctor_get(x_3, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_202 = x_3;
} else {
 lean_dec_ref(x_3);
 x_202 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_201);
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_4);
x_204 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_199, x_2, x_203, x_200);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_210 = x_205;
} else {
 lean_dec_ref(x_205);
 x_210 = lean_box(0);
}
x_211 = lean_box(0);
x_212 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_213 = l_Lean_addMacroScope(x_201, x_212, x_4);
x_214 = lean_box(0);
x_215 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_216 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_216, 2, x_213);
lean_ctor_set(x_216, 3, x_214);
x_217 = l_Array_empty___closed__1;
x_218 = lean_array_push(x_217, x_216);
x_219 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_220 = lean_array_push(x_218, x_219);
x_221 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_220);
x_222 = lean_array_push(x_220, x_221);
x_223 = lean_array_push(x_222, x_208);
x_224 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
x_226 = lean_array_push(x_217, x_225);
x_227 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_228 = lean_array_push(x_226, x_227);
x_229 = lean_box(0);
x_230 = lean_array_push(x_228, x_229);
x_231 = l_Lean_nullKind___closed__2;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_234 = lean_array_push(x_233, x_232);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_7);
lean_ctor_set(x_235, 1, x_234);
x_236 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_235);
lean_dec(x_235);
x_237 = lean_array_pop(x_236);
x_238 = lean_unsigned_to_nat(0u);
x_239 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_237, x_237, x_238, x_209);
lean_dec(x_237);
x_240 = l_Lean_mkTermIdFromIdent___closed__2;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_220);
if (lean_is_scalar(x_210)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_210;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_239);
if (lean_is_scalar(x_207)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_207;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_206);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_1);
lean_ctor_set(x_244, 1, x_2);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_4);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_3);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_1);
lean_ctor_set(x_246, 1, x_2);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_4);
return x_247;
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
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1() {
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
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3() {
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
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__4;
x_2 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_35; uint8_t x_36; 
x_35 = lean_array_get_size(x_2);
x_36 = lean_nat_dec_lt(x_3, x_35);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
if (x_1 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Array_empty___closed__1;
x_41 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_39, x_40);
lean_dec(x_2);
x_42 = l_Lean_nullKind___closed__2;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_45 = lean_array_push(x_44, x_43);
x_46 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
x_47 = lean_array_push(x_45, x_46);
x_48 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_51 = lean_array_push(x_50, x_49);
x_52 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_5);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
lean_inc(x_56);
x_57 = l___private_Init_Lean_Elab_DoNotation_6__expandLiftMethod(x_56, x_4, x_5);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
lean_inc(x_56);
x_62 = l_Lean_Syntax_getKind(x_56);
x_63 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_64 = lean_name_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
lean_free_object(x_57);
x_65 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_66 = lean_name_eq(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_35, x_67);
lean_dec(x_35);
x_69 = lean_nat_dec_lt(x_3, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_62);
lean_dec(x_56);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_add(x_3, x_70);
lean_dec(x_3);
x_3 = x_71;
x_5 = x_60;
goto _start;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_74 = lean_name_eq(x_62, x_73);
lean_dec(x_62);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_56);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_nat_add(x_3, x_75);
lean_dec(x_3);
x_3 = x_76;
x_5 = x_60;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Syntax_getArg(x_56, x_78);
lean_dec(x_56);
x_80 = lean_ctor_get(x_4, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_4, 0);
lean_inc(x_81);
x_82 = lean_box(0);
x_83 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_84 = l_Lean_addMacroScope(x_81, x_83, x_80);
x_85 = lean_box(0);
x_86 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_85);
x_88 = l_Array_empty___closed__1;
x_89 = lean_array_push(x_88, x_87);
x_90 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_91 = lean_array_push(x_89, x_90);
x_92 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_93 = lean_array_push(x_91, x_92);
x_94 = lean_array_push(x_93, x_79);
x_95 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_array_push(x_88, x_96);
x_98 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_box(0);
x_101 = lean_array_push(x_99, x_100);
x_102 = l_Lean_nullKind___closed__2;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_105 = lean_array_push(x_104, x_103);
x_106 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_107);
lean_dec(x_107);
x_109 = l_Lean_Syntax_inhabited;
x_110 = lean_array_get(x_109, x_108, x_78);
lean_dec(x_108);
x_111 = lean_array_set(x_2, x_3, x_110);
x_112 = lean_unsigned_to_nat(2u);
x_113 = lean_nat_add(x_3, x_112);
lean_dec(x_3);
x_114 = 1;
x_1 = x_114;
x_2 = x_111;
x_3 = x_113;
x_5 = x_60;
goto _start;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_62);
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Lean_Syntax_getArg(x_56, x_116);
x_118 = lean_unsigned_to_nat(2u);
x_119 = l_Lean_Syntax_getArg(x_56, x_118);
x_120 = lean_unsigned_to_nat(3u);
x_121 = l_Lean_Syntax_getArg(x_56, x_120);
lean_dec(x_56);
x_122 = lean_nat_add(x_3, x_118);
x_123 = l_Array_extract___rarg(x_2, x_122, x_35);
lean_dec(x_35);
x_124 = lean_array_get_size(x_123);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_dec_eq(x_124, x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_127 = lean_nat_add(x_60, x_125);
x_128 = lean_ctor_get(x_4, 0);
lean_inc(x_128);
lean_dec(x_4);
x_129 = lean_box(0);
x_130 = l_Array_empty___closed__1;
x_131 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_123, x_123, x_116, x_130);
lean_dec(x_123);
x_132 = l_Lean_nullKind___closed__2;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_135 = lean_array_push(x_134, x_133);
x_136 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
x_137 = lean_array_push(x_135, x_136);
x_138 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_141 = lean_array_push(x_140, x_139);
x_142 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_Syntax_isNone(x_121);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_145 = l_Lean_Syntax_getArg(x_121, x_125);
lean_dec(x_121);
x_146 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_147 = l_Lean_addMacroScope(x_128, x_146, x_60);
x_148 = lean_box(0);
x_149 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_150 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_150, 0, x_129);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_147);
lean_ctor_set(x_150, 3, x_148);
x_151 = lean_array_push(x_130, x_150);
x_152 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_153 = lean_array_push(x_151, x_152);
x_154 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_153);
x_155 = lean_array_push(x_153, x_154);
x_156 = lean_array_push(x_155, x_119);
x_157 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_array_push(x_130, x_158);
x_160 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_161 = lean_array_push(x_159, x_160);
x_162 = l_Lean_mkTermIdFromIdent___closed__2;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_153);
x_164 = lean_array_push(x_130, x_163);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_132);
lean_ctor_set(x_165, 1, x_164);
x_166 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_167 = lean_array_push(x_166, x_165);
x_168 = lean_array_push(x_167, x_152);
x_169 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_170 = lean_array_push(x_168, x_169);
x_171 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_172 = lean_array_push(x_170, x_171);
x_173 = lean_array_push(x_130, x_117);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_132);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_array_push(x_130, x_174);
x_176 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_177 = lean_array_push(x_175, x_176);
x_178 = lean_array_push(x_177, x_143);
x_179 = l_Lean_Parser_Term_matchAlt___closed__2;
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_array_push(x_130, x_180);
x_182 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_183 = lean_array_push(x_181, x_182);
x_184 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5;
x_185 = lean_array_push(x_184, x_145);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_179);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_array_push(x_183, x_186);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_132);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_array_push(x_172, x_188);
x_190 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = lean_array_push(x_130, x_191);
x_193 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_array_push(x_161, x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_132);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_array_push(x_140, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_142);
lean_ctor_set(x_198, 1, x_197);
x_6 = x_198;
x_7 = x_127;
goto block_34;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_121);
x_199 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_200 = l_Lean_addMacroScope(x_128, x_199, x_60);
x_201 = lean_box(0);
x_202 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_203 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_203, 0, x_129);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set(x_203, 2, x_200);
lean_ctor_set(x_203, 3, x_201);
x_204 = lean_array_push(x_130, x_203);
x_205 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_206 = lean_array_push(x_204, x_205);
x_207 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_206);
x_208 = lean_array_push(x_206, x_207);
x_209 = lean_array_push(x_208, x_119);
x_210 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = lean_array_push(x_130, x_211);
x_213 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_214 = lean_array_push(x_212, x_213);
x_215 = l_Lean_mkTermIdFromIdent___closed__2;
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_206);
x_217 = lean_array_push(x_130, x_216);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_132);
lean_ctor_set(x_218, 1, x_217);
x_219 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_220 = lean_array_push(x_219, x_218);
x_221 = lean_array_push(x_220, x_205);
x_222 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_223 = lean_array_push(x_221, x_222);
x_224 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_225 = lean_array_push(x_223, x_224);
x_226 = lean_array_push(x_130, x_117);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_132);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_array_push(x_130, x_227);
x_229 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_230 = lean_array_push(x_228, x_229);
x_231 = lean_array_push(x_230, x_143);
x_232 = l_Lean_Parser_Term_matchAlt___closed__2;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_array_push(x_130, x_233);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_132);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_array_push(x_225, x_235);
x_237 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = lean_array_push(x_130, x_238);
x_240 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_push(x_214, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_132);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_array_push(x_140, x_243);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_142);
lean_ctor_set(x_245, 1, x_244);
x_6 = x_245;
x_7 = x_127;
goto block_34;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_246 = l_Lean_Syntax_inhabited;
x_247 = lean_array_get(x_246, x_123, x_116);
lean_dec(x_123);
x_248 = l_Lean_Syntax_getArg(x_247, x_116);
lean_dec(x_247);
x_249 = lean_nat_add(x_60, x_125);
x_250 = lean_ctor_get(x_4, 0);
lean_inc(x_250);
lean_dec(x_4);
x_251 = l_Lean_Syntax_isNone(x_121);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_252 = l_Lean_Syntax_getArg(x_121, x_125);
lean_dec(x_121);
x_253 = lean_box(0);
x_254 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_255 = l_Lean_addMacroScope(x_250, x_254, x_60);
x_256 = lean_box(0);
x_257 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_258 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_257);
lean_ctor_set(x_258, 2, x_255);
lean_ctor_set(x_258, 3, x_256);
x_259 = l_Array_empty___closed__1;
x_260 = lean_array_push(x_259, x_258);
x_261 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_262 = lean_array_push(x_260, x_261);
x_263 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_262);
x_264 = lean_array_push(x_262, x_263);
x_265 = lean_array_push(x_264, x_119);
x_266 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = lean_array_push(x_259, x_267);
x_269 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_270 = lean_array_push(x_268, x_269);
x_271 = l_Lean_mkTermIdFromIdent___closed__2;
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_262);
x_273 = lean_array_push(x_259, x_272);
x_274 = l_Lean_nullKind___closed__2;
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_277 = lean_array_push(x_276, x_275);
x_278 = lean_array_push(x_277, x_261);
x_279 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_280 = lean_array_push(x_278, x_279);
x_281 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_282 = lean_array_push(x_280, x_281);
x_283 = lean_array_push(x_259, x_117);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_274);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_array_push(x_259, x_284);
x_286 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_287 = lean_array_push(x_285, x_286);
x_288 = lean_array_push(x_287, x_248);
x_289 = l_Lean_Parser_Term_matchAlt___closed__2;
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = lean_array_push(x_259, x_290);
x_292 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_293 = lean_array_push(x_291, x_292);
x_294 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5;
x_295 = lean_array_push(x_294, x_252);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_289);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_array_push(x_293, x_296);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_274);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_array_push(x_282, x_298);
x_300 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_299);
x_302 = lean_array_push(x_259, x_301);
x_303 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
x_305 = lean_array_push(x_270, x_304);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_274);
lean_ctor_set(x_306, 1, x_305);
x_307 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_308 = lean_array_push(x_307, x_306);
x_309 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_308);
x_6 = x_310;
x_7 = x_249;
goto block_34;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_121);
x_311 = lean_box(0);
x_312 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_313 = l_Lean_addMacroScope(x_250, x_312, x_60);
x_314 = lean_box(0);
x_315 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_316 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_316, 0, x_311);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set(x_316, 2, x_313);
lean_ctor_set(x_316, 3, x_314);
x_317 = l_Array_empty___closed__1;
x_318 = lean_array_push(x_317, x_316);
x_319 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_320 = lean_array_push(x_318, x_319);
x_321 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_320);
x_322 = lean_array_push(x_320, x_321);
x_323 = lean_array_push(x_322, x_119);
x_324 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = lean_array_push(x_317, x_325);
x_327 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_328 = lean_array_push(x_326, x_327);
x_329 = l_Lean_mkTermIdFromIdent___closed__2;
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_320);
x_331 = lean_array_push(x_317, x_330);
x_332 = l_Lean_nullKind___closed__2;
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
x_334 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_335 = lean_array_push(x_334, x_333);
x_336 = lean_array_push(x_335, x_319);
x_337 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_338 = lean_array_push(x_336, x_337);
x_339 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_340 = lean_array_push(x_338, x_339);
x_341 = lean_array_push(x_317, x_117);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_332);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_array_push(x_317, x_342);
x_344 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_345 = lean_array_push(x_343, x_344);
x_346 = lean_array_push(x_345, x_248);
x_347 = l_Lean_Parser_Term_matchAlt___closed__2;
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
x_349 = lean_array_push(x_317, x_348);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_332);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_array_push(x_340, x_350);
x_352 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_array_push(x_317, x_353);
x_355 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
x_357 = lean_array_push(x_328, x_356);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_332);
lean_ctor_set(x_358, 1, x_357);
x_359 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_360 = lean_array_push(x_359, x_358);
x_361 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_360);
x_6 = x_362;
x_7 = x_249;
goto block_34;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
lean_dec(x_62);
lean_dec(x_4);
x_363 = lean_unsigned_to_nat(1u);
x_364 = l_Lean_Syntax_getArg(x_56, x_363);
lean_dec(x_56);
x_365 = lean_unsigned_to_nat(2u);
x_366 = lean_nat_add(x_3, x_365);
x_367 = l_Array_extract___rarg(x_2, x_366, x_35);
lean_dec(x_35);
x_368 = lean_array_get_size(x_367);
x_369 = lean_nat_dec_eq(x_368, x_363);
lean_dec(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_370 = lean_unsigned_to_nat(0u);
x_371 = l_Array_empty___closed__1;
x_372 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_367, x_367, x_370, x_371);
lean_dec(x_367);
x_373 = l_Lean_nullKind___closed__2;
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
x_375 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_376 = lean_array_push(x_375, x_374);
x_377 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
x_378 = lean_array_push(x_376, x_377);
x_379 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_378);
x_381 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_382 = lean_array_push(x_381, x_380);
x_383 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_386 = lean_array_push(x_385, x_364);
x_387 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_388 = lean_array_push(x_386, x_387);
x_389 = lean_array_push(x_388, x_384);
x_390 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_389);
x_392 = lean_nat_dec_eq(x_3, x_370);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_393 = l_Array_extract___rarg(x_2, x_370, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_394 = l_Lean_mkOptionalNode___closed__2;
x_395 = lean_array_push(x_394, x_391);
x_396 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_395);
x_398 = lean_array_push(x_393, x_397);
x_399 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_398, x_398, x_370, x_371);
lean_dec(x_398);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_373);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_array_push(x_375, x_400);
x_402 = lean_array_push(x_401, x_377);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_379);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_array_push(x_381, x_403);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_383);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_57, 0, x_406);
return x_57;
}
else
{
lean_object* x_407; 
lean_dec(x_3);
lean_dec(x_2);
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_391);
lean_ctor_set(x_57, 0, x_407);
return x_57;
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_408 = l_Lean_Syntax_inhabited;
x_409 = lean_unsigned_to_nat(0u);
x_410 = lean_array_get(x_408, x_367, x_409);
lean_dec(x_367);
x_411 = l_Lean_Syntax_getArg(x_410, x_409);
lean_dec(x_410);
x_412 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_413 = lean_array_push(x_412, x_364);
x_414 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_415 = lean_array_push(x_413, x_414);
x_416 = lean_array_push(x_415, x_411);
x_417 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = lean_nat_dec_eq(x_3, x_409);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_420 = l_Array_extract___rarg(x_2, x_409, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_421 = l_Lean_mkOptionalNode___closed__2;
x_422 = lean_array_push(x_421, x_418);
x_423 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_422);
x_425 = lean_array_push(x_420, x_424);
x_426 = l_Array_empty___closed__1;
x_427 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_425, x_425, x_409, x_426);
lean_dec(x_425);
x_428 = l_Lean_nullKind___closed__2;
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_427);
x_430 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_431 = lean_array_push(x_430, x_429);
x_432 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
x_433 = lean_array_push(x_431, x_432);
x_434 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_433);
x_436 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_437 = lean_array_push(x_436, x_435);
x_438 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_439, 1, x_437);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_57, 0, x_440);
return x_57;
}
else
{
lean_object* x_441; 
lean_dec(x_3);
lean_dec(x_2);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_418);
lean_ctor_set(x_57, 0, x_441);
return x_57;
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_442 = lean_ctor_get(x_57, 1);
lean_inc(x_442);
lean_dec(x_57);
lean_inc(x_56);
x_443 = l_Lean_Syntax_getKind(x_56);
x_444 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_445 = lean_name_eq(x_443, x_444);
if (x_445 == 0)
{
lean_object* x_446; uint8_t x_447; 
x_446 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_447 = lean_name_eq(x_443, x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_448 = lean_unsigned_to_nat(1u);
x_449 = lean_nat_sub(x_35, x_448);
lean_dec(x_35);
x_450 = lean_nat_dec_lt(x_3, x_449);
lean_dec(x_449);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_443);
lean_dec(x_56);
x_451 = lean_unsigned_to_nat(2u);
x_452 = lean_nat_add(x_3, x_451);
lean_dec(x_3);
x_3 = x_452;
x_5 = x_442;
goto _start;
}
else
{
lean_object* x_454; uint8_t x_455; 
x_454 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_455 = lean_name_eq(x_443, x_454);
lean_dec(x_443);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_56);
x_456 = lean_unsigned_to_nat(2u);
x_457 = lean_nat_add(x_3, x_456);
lean_dec(x_3);
x_3 = x_457;
x_5 = x_442;
goto _start;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_459 = lean_unsigned_to_nat(0u);
x_460 = l_Lean_Syntax_getArg(x_56, x_459);
lean_dec(x_56);
x_461 = lean_ctor_get(x_4, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_4, 0);
lean_inc(x_462);
x_463 = lean_box(0);
x_464 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_465 = l_Lean_addMacroScope(x_462, x_464, x_461);
x_466 = lean_box(0);
x_467 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_468 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_468, 0, x_463);
lean_ctor_set(x_468, 1, x_467);
lean_ctor_set(x_468, 2, x_465);
lean_ctor_set(x_468, 3, x_466);
x_469 = l_Array_empty___closed__1;
x_470 = lean_array_push(x_469, x_468);
x_471 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_472 = lean_array_push(x_470, x_471);
x_473 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_474 = lean_array_push(x_472, x_473);
x_475 = lean_array_push(x_474, x_460);
x_476 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_475);
x_478 = lean_array_push(x_469, x_477);
x_479 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_480 = lean_array_push(x_478, x_479);
x_481 = lean_box(0);
x_482 = lean_array_push(x_480, x_481);
x_483 = l_Lean_nullKind___closed__2;
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_486 = lean_array_push(x_485, x_484);
x_487 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_486);
x_489 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_488);
lean_dec(x_488);
x_490 = l_Lean_Syntax_inhabited;
x_491 = lean_array_get(x_490, x_489, x_459);
lean_dec(x_489);
x_492 = lean_array_set(x_2, x_3, x_491);
x_493 = lean_unsigned_to_nat(2u);
x_494 = lean_nat_add(x_3, x_493);
lean_dec(x_3);
x_495 = 1;
x_1 = x_495;
x_2 = x_492;
x_3 = x_494;
x_5 = x_442;
goto _start;
}
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
lean_dec(x_443);
x_497 = lean_unsigned_to_nat(0u);
x_498 = l_Lean_Syntax_getArg(x_56, x_497);
x_499 = lean_unsigned_to_nat(2u);
x_500 = l_Lean_Syntax_getArg(x_56, x_499);
x_501 = lean_unsigned_to_nat(3u);
x_502 = l_Lean_Syntax_getArg(x_56, x_501);
lean_dec(x_56);
x_503 = lean_nat_add(x_3, x_499);
x_504 = l_Array_extract___rarg(x_2, x_503, x_35);
lean_dec(x_35);
x_505 = lean_array_get_size(x_504);
x_506 = lean_unsigned_to_nat(1u);
x_507 = lean_nat_dec_eq(x_505, x_506);
lean_dec(x_505);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_525; 
x_508 = lean_nat_add(x_442, x_506);
x_509 = lean_ctor_get(x_4, 0);
lean_inc(x_509);
lean_dec(x_4);
x_510 = lean_box(0);
x_511 = l_Array_empty___closed__1;
x_512 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_504, x_504, x_497, x_511);
lean_dec(x_504);
x_513 = l_Lean_nullKind___closed__2;
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_512);
x_515 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_516 = lean_array_push(x_515, x_514);
x_517 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
x_518 = lean_array_push(x_516, x_517);
x_519 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_518);
x_521 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_522 = lean_array_push(x_521, x_520);
x_523 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_522);
x_525 = l_Lean_Syntax_isNone(x_502);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_526 = l_Lean_Syntax_getArg(x_502, x_506);
lean_dec(x_502);
x_527 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_528 = l_Lean_addMacroScope(x_509, x_527, x_442);
x_529 = lean_box(0);
x_530 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_531 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_531, 0, x_510);
lean_ctor_set(x_531, 1, x_530);
lean_ctor_set(x_531, 2, x_528);
lean_ctor_set(x_531, 3, x_529);
x_532 = lean_array_push(x_511, x_531);
x_533 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_534 = lean_array_push(x_532, x_533);
x_535 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_534);
x_536 = lean_array_push(x_534, x_535);
x_537 = lean_array_push(x_536, x_500);
x_538 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_537);
x_540 = lean_array_push(x_511, x_539);
x_541 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_542 = lean_array_push(x_540, x_541);
x_543 = l_Lean_mkTermIdFromIdent___closed__2;
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_534);
x_545 = lean_array_push(x_511, x_544);
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_513);
lean_ctor_set(x_546, 1, x_545);
x_547 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_548 = lean_array_push(x_547, x_546);
x_549 = lean_array_push(x_548, x_533);
x_550 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_551 = lean_array_push(x_549, x_550);
x_552 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_553 = lean_array_push(x_551, x_552);
x_554 = lean_array_push(x_511, x_498);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_513);
lean_ctor_set(x_555, 1, x_554);
x_556 = lean_array_push(x_511, x_555);
x_557 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_558 = lean_array_push(x_556, x_557);
x_559 = lean_array_push(x_558, x_524);
x_560 = l_Lean_Parser_Term_matchAlt___closed__2;
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_559);
x_562 = lean_array_push(x_511, x_561);
x_563 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_564 = lean_array_push(x_562, x_563);
x_565 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5;
x_566 = lean_array_push(x_565, x_526);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_560);
lean_ctor_set(x_567, 1, x_566);
x_568 = lean_array_push(x_564, x_567);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_513);
lean_ctor_set(x_569, 1, x_568);
x_570 = lean_array_push(x_553, x_569);
x_571 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_570);
x_573 = lean_array_push(x_511, x_572);
x_574 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_573);
x_576 = lean_array_push(x_542, x_575);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_513);
lean_ctor_set(x_577, 1, x_576);
x_578 = lean_array_push(x_521, x_577);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_523);
lean_ctor_set(x_579, 1, x_578);
x_6 = x_579;
x_7 = x_508;
goto block_34;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_502);
x_580 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_581 = l_Lean_addMacroScope(x_509, x_580, x_442);
x_582 = lean_box(0);
x_583 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_584 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_584, 0, x_510);
lean_ctor_set(x_584, 1, x_583);
lean_ctor_set(x_584, 2, x_581);
lean_ctor_set(x_584, 3, x_582);
x_585 = lean_array_push(x_511, x_584);
x_586 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_587 = lean_array_push(x_585, x_586);
x_588 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_587);
x_589 = lean_array_push(x_587, x_588);
x_590 = lean_array_push(x_589, x_500);
x_591 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_590);
x_593 = lean_array_push(x_511, x_592);
x_594 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_595 = lean_array_push(x_593, x_594);
x_596 = l_Lean_mkTermIdFromIdent___closed__2;
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_587);
x_598 = lean_array_push(x_511, x_597);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_513);
lean_ctor_set(x_599, 1, x_598);
x_600 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_601 = lean_array_push(x_600, x_599);
x_602 = lean_array_push(x_601, x_586);
x_603 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_604 = lean_array_push(x_602, x_603);
x_605 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_606 = lean_array_push(x_604, x_605);
x_607 = lean_array_push(x_511, x_498);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_513);
lean_ctor_set(x_608, 1, x_607);
x_609 = lean_array_push(x_511, x_608);
x_610 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_611 = lean_array_push(x_609, x_610);
x_612 = lean_array_push(x_611, x_524);
x_613 = l_Lean_Parser_Term_matchAlt___closed__2;
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_612);
x_615 = lean_array_push(x_511, x_614);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_513);
lean_ctor_set(x_616, 1, x_615);
x_617 = lean_array_push(x_606, x_616);
x_618 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_617);
x_620 = lean_array_push(x_511, x_619);
x_621 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_620);
x_623 = lean_array_push(x_595, x_622);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_513);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_array_push(x_521, x_624);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_523);
lean_ctor_set(x_626, 1, x_625);
x_6 = x_626;
x_7 = x_508;
goto block_34;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; 
x_627 = l_Lean_Syntax_inhabited;
x_628 = lean_array_get(x_627, x_504, x_497);
lean_dec(x_504);
x_629 = l_Lean_Syntax_getArg(x_628, x_497);
lean_dec(x_628);
x_630 = lean_nat_add(x_442, x_506);
x_631 = lean_ctor_get(x_4, 0);
lean_inc(x_631);
lean_dec(x_4);
x_632 = l_Lean_Syntax_isNone(x_502);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_633 = l_Lean_Syntax_getArg(x_502, x_506);
lean_dec(x_502);
x_634 = lean_box(0);
x_635 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_636 = l_Lean_addMacroScope(x_631, x_635, x_442);
x_637 = lean_box(0);
x_638 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_639 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_639, 0, x_634);
lean_ctor_set(x_639, 1, x_638);
lean_ctor_set(x_639, 2, x_636);
lean_ctor_set(x_639, 3, x_637);
x_640 = l_Array_empty___closed__1;
x_641 = lean_array_push(x_640, x_639);
x_642 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_643 = lean_array_push(x_641, x_642);
x_644 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_643);
x_645 = lean_array_push(x_643, x_644);
x_646 = lean_array_push(x_645, x_500);
x_647 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_646);
x_649 = lean_array_push(x_640, x_648);
x_650 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_651 = lean_array_push(x_649, x_650);
x_652 = l_Lean_mkTermIdFromIdent___closed__2;
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_643);
x_654 = lean_array_push(x_640, x_653);
x_655 = l_Lean_nullKind___closed__2;
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_654);
x_657 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_658 = lean_array_push(x_657, x_656);
x_659 = lean_array_push(x_658, x_642);
x_660 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_661 = lean_array_push(x_659, x_660);
x_662 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_663 = lean_array_push(x_661, x_662);
x_664 = lean_array_push(x_640, x_498);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_655);
lean_ctor_set(x_665, 1, x_664);
x_666 = lean_array_push(x_640, x_665);
x_667 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_668 = lean_array_push(x_666, x_667);
x_669 = lean_array_push(x_668, x_629);
x_670 = l_Lean_Parser_Term_matchAlt___closed__2;
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_669);
x_672 = lean_array_push(x_640, x_671);
x_673 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__4;
x_674 = lean_array_push(x_672, x_673);
x_675 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5;
x_676 = lean_array_push(x_675, x_633);
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_670);
lean_ctor_set(x_677, 1, x_676);
x_678 = lean_array_push(x_674, x_677);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_655);
lean_ctor_set(x_679, 1, x_678);
x_680 = lean_array_push(x_663, x_679);
x_681 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_680);
x_683 = lean_array_push(x_640, x_682);
x_684 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_685 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_683);
x_686 = lean_array_push(x_651, x_685);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_655);
lean_ctor_set(x_687, 1, x_686);
x_688 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_689 = lean_array_push(x_688, x_687);
x_690 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_6 = x_691;
x_7 = x_630;
goto block_34;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_502);
x_692 = lean_box(0);
x_693 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_694 = l_Lean_addMacroScope(x_631, x_693, x_442);
x_695 = lean_box(0);
x_696 = l_Lean_Elab_Term_elabLetDecl___closed__4;
x_697 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_697, 0, x_692);
lean_ctor_set(x_697, 1, x_696);
lean_ctor_set(x_697, 2, x_694);
lean_ctor_set(x_697, 3, x_695);
x_698 = l_Array_empty___closed__1;
x_699 = lean_array_push(x_698, x_697);
x_700 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_701 = lean_array_push(x_699, x_700);
x_702 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_701);
x_703 = lean_array_push(x_701, x_702);
x_704 = lean_array_push(x_703, x_500);
x_705 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_704);
x_707 = lean_array_push(x_698, x_706);
x_708 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_709 = lean_array_push(x_707, x_708);
x_710 = l_Lean_mkTermIdFromIdent___closed__2;
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_701);
x_712 = lean_array_push(x_698, x_711);
x_713 = l_Lean_nullKind___closed__2;
x_714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_712);
x_715 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__2;
x_716 = lean_array_push(x_715, x_714);
x_717 = lean_array_push(x_716, x_700);
x_718 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__3;
x_719 = lean_array_push(x_717, x_718);
x_720 = l___private_Init_Lean_Elab_TermBinders_10__expandFunBindersAux___main___closed__6;
x_721 = lean_array_push(x_719, x_720);
x_722 = lean_array_push(x_698, x_498);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_713);
lean_ctor_set(x_723, 1, x_722);
x_724 = lean_array_push(x_698, x_723);
x_725 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_726 = lean_array_push(x_724, x_725);
x_727 = lean_array_push(x_726, x_629);
x_728 = l_Lean_Parser_Term_matchAlt___closed__2;
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_727);
x_730 = lean_array_push(x_698, x_729);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_713);
lean_ctor_set(x_731, 1, x_730);
x_732 = lean_array_push(x_721, x_731);
x_733 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_734 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_732);
x_735 = lean_array_push(x_698, x_734);
x_736 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_735);
x_738 = lean_array_push(x_709, x_737);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_713);
lean_ctor_set(x_739, 1, x_738);
x_740 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_741 = lean_array_push(x_740, x_739);
x_742 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_743, 0, x_742);
lean_ctor_set(x_743, 1, x_741);
x_6 = x_743;
x_7 = x_630;
goto block_34;
}
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; 
lean_dec(x_443);
lean_dec(x_4);
x_744 = lean_unsigned_to_nat(1u);
x_745 = l_Lean_Syntax_getArg(x_56, x_744);
lean_dec(x_56);
x_746 = lean_unsigned_to_nat(2u);
x_747 = lean_nat_add(x_3, x_746);
x_748 = l_Array_extract___rarg(x_2, x_747, x_35);
lean_dec(x_35);
x_749 = lean_array_get_size(x_748);
x_750 = lean_nat_dec_eq(x_749, x_744);
lean_dec(x_749);
if (x_750 == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; uint8_t x_773; 
x_751 = lean_unsigned_to_nat(0u);
x_752 = l_Array_empty___closed__1;
x_753 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_748, x_748, x_751, x_752);
lean_dec(x_748);
x_754 = l_Lean_nullKind___closed__2;
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_753);
x_756 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_757 = lean_array_push(x_756, x_755);
x_758 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
x_759 = lean_array_push(x_757, x_758);
x_760 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_761, 0, x_760);
lean_ctor_set(x_761, 1, x_759);
x_762 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_763 = lean_array_push(x_762, x_761);
x_764 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_763);
x_766 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_767 = lean_array_push(x_766, x_745);
x_768 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_769 = lean_array_push(x_767, x_768);
x_770 = lean_array_push(x_769, x_765);
x_771 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_771);
lean_ctor_set(x_772, 1, x_770);
x_773 = lean_nat_dec_eq(x_3, x_751);
if (x_773 == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_774 = l_Array_extract___rarg(x_2, x_751, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_775 = l_Lean_mkOptionalNode___closed__2;
x_776 = lean_array_push(x_775, x_772);
x_777 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_776);
x_779 = lean_array_push(x_774, x_778);
x_780 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_779, x_779, x_751, x_752);
lean_dec(x_779);
x_781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_781, 0, x_754);
lean_ctor_set(x_781, 1, x_780);
x_782 = lean_array_push(x_756, x_781);
x_783 = lean_array_push(x_782, x_758);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_760);
lean_ctor_set(x_784, 1, x_783);
x_785 = lean_array_push(x_762, x_784);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_764);
lean_ctor_set(x_786, 1, x_785);
x_787 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_787, 0, x_786);
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_442);
return x_788;
}
else
{
lean_object* x_789; lean_object* x_790; 
lean_dec(x_3);
lean_dec(x_2);
x_789 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_789, 0, x_772);
x_790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_442);
return x_790;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; 
x_791 = l_Lean_Syntax_inhabited;
x_792 = lean_unsigned_to_nat(0u);
x_793 = lean_array_get(x_791, x_748, x_792);
lean_dec(x_748);
x_794 = l_Lean_Syntax_getArg(x_793, x_792);
lean_dec(x_793);
x_795 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__2;
x_796 = lean_array_push(x_795, x_745);
x_797 = l___private_Init_Lean_Elab_Quotation_7__getHeadInfo___elambda__3___closed__10;
x_798 = lean_array_push(x_796, x_797);
x_799 = lean_array_push(x_798, x_794);
x_800 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_799);
x_802 = lean_nat_dec_eq(x_3, x_792);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_803 = l_Array_extract___rarg(x_2, x_792, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_804 = l_Lean_mkOptionalNode___closed__2;
x_805 = lean_array_push(x_804, x_801);
x_806 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_807 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_805);
x_808 = lean_array_push(x_803, x_807);
x_809 = l_Array_empty___closed__1;
x_810 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_808, x_808, x_792, x_809);
lean_dec(x_808);
x_811 = l_Lean_nullKind___closed__2;
x_812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_810);
x_813 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_814 = lean_array_push(x_813, x_812);
x_815 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
x_816 = lean_array_push(x_814, x_815);
x_817 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
x_819 = l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_820 = lean_array_push(x_819, x_818);
x_821 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_820);
x_823 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_823, 0, x_822);
x_824 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_824, 0, x_823);
lean_ctor_set(x_824, 1, x_442);
return x_824;
}
else
{
lean_object* x_825; lean_object* x_826; 
lean_dec(x_3);
lean_dec(x_2);
x_825 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_825, 0, x_801);
x_826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_826, 0, x_825);
lean_ctor_set(x_826, 1, x_442);
return x_826;
}
}
}
}
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; 
lean_dec(x_56);
x_827 = lean_ctor_get(x_57, 1);
lean_inc(x_827);
lean_dec(x_57);
x_828 = lean_ctor_get(x_58, 0);
lean_inc(x_828);
lean_dec(x_58);
x_829 = lean_unsigned_to_nat(1u);
x_830 = lean_nat_add(x_3, x_829);
x_831 = l_Array_extract___rarg(x_2, x_830, x_35);
lean_dec(x_35);
x_832 = lean_unsigned_to_nat(0u);
x_833 = l_Array_extract___rarg(x_2, x_832, x_3);
lean_dec(x_2);
x_834 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_828, x_828, x_832, x_833);
lean_dec(x_828);
x_835 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_831, x_831, x_832, x_834);
lean_dec(x_831);
x_836 = 1;
x_1 = x_836;
x_2 = x_835;
x_5 = x_827;
goto _start;
}
}
block_34:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = l_Array_extract___rarg(x_2, x_8, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_Lean_mkOptionalNode___closed__2;
x_12 = lean_array_push(x_11, x_6);
x_13 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_array_push(x_10, x_14);
x_16 = l_Array_empty___closed__1;
x_17 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_15, x_15, x_8, x_16);
lean_dec(x_15);
x_18 = l_Lean_nullKind___closed__2;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_21 = lean_array_push(x_20, x_19);
x_22 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3;
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
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
return x_33;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_DoNotation_8__expandDoElems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_4, x_1, x_5, x_2, x_3);
return x_6;
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
x_14 = l_Lean_Elab_Term_getDecLevel(x_1, x_12, x_6, x_13);
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
x_17 = l_Lean_Elab_Term_inferType(x_1, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_6);
x_20 = l_Lean_Elab_Term_getDecLevel(x_1, x_18, x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_27 = l_Lean_mkConst(x_26, x_25);
x_28 = l_Lean_mkAppB(x_27, x_2, x_3);
x_29 = lean_array_get_size(x_4);
x_30 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_Elab_DoNotation_10__mkBind___spec__2(x_1, x_4, x_28, x_4, x_29, lean_box(0), x_5, x_6, x_22);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_7);
return x_47;
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
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_4);
x_35 = 1;
lean_inc(x_7);
lean_inc(x_34);
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
x_39 = l_Lean_Elab_Term_ensureHasType(x_10, x_34, x_37, x_7, x_38);
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
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
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
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = 1;
lean_inc(x_7);
lean_inc(x_60);
lean_inc(x_65);
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
x_70 = l_Lean_Elab_Term_ensureHasType(x_60, x_65, x_68, x_7, x_69);
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
lean_dec(x_65);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_48; lean_object* x_49; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Init_Lean_Elab_DoNotation_3__getDoElems(x_1);
x_84 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_6);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Term_getEnv___rarg(x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_88, 5);
x_92 = lean_environment_main_module(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_85);
x_94 = 0;
x_95 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_96 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_94, x_7, x_95, x_93, x_91);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_ctor_set(x_88, 5, x_98);
x_48 = x_97;
x_49 = x_88;
goto block_83;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_88, 0);
x_100 = lean_ctor_get(x_88, 1);
x_101 = lean_ctor_get(x_88, 2);
x_102 = lean_ctor_get(x_88, 3);
x_103 = lean_ctor_get(x_88, 4);
x_104 = lean_ctor_get(x_88, 5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_88);
x_105 = lean_environment_main_module(x_89);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_85);
x_107 = 0;
x_108 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_109 = l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_107, x_7, x_108, x_106, x_104);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_100);
lean_ctor_set(x_112, 2, x_101);
lean_ctor_set(x_112, 3, x_102);
lean_ctor_set(x_112, 4, x_103);
lean_ctor_set(x_112, 5, x_111);
x_48 = x_110;
x_49 = x_112;
goto block_83;
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
x_13 = l___private_Init_Lean_Elab_DoNotation_2__extractBind(x_1, x_2, x_3, x_8);
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
x_17 = lean_ctor_get(x_14, 2);
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
x_32 = lean_ctor_get(x_14, 2);
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
block_83:
{
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = l_Lean_Elab_Term_getOptions(x_3, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Elab_Term_elabDo___closed__1;
x_54 = l_Lean_checkTraceOption(x_51, x_53);
lean_dec(x_51);
if (x_54 == 0)
{
x_8 = x_52;
goto block_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_1);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_1);
x_56 = l_Lean_Elab_Term_logTrace(x_53, x_1, x_55, x_3, x_52);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_8 = x_57;
goto block_47;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_7);
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
lean_dec(x_48);
x_59 = !lean_is_exclusive(x_3);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_3, 8);
lean_inc(x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_3, 8, x_62);
x_63 = 1;
x_64 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_63, x_58, x_3, x_49);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_65 = lean_ctor_get(x_3, 0);
x_66 = lean_ctor_get(x_3, 1);
x_67 = lean_ctor_get(x_3, 2);
x_68 = lean_ctor_get(x_3, 3);
x_69 = lean_ctor_get(x_3, 4);
x_70 = lean_ctor_get(x_3, 5);
x_71 = lean_ctor_get(x_3, 6);
x_72 = lean_ctor_get(x_3, 7);
x_73 = lean_ctor_get(x_3, 8);
x_74 = lean_ctor_get(x_3, 9);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_77 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_3);
lean_inc(x_58);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_58);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
x_80 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_66);
lean_ctor_set(x_80, 2, x_67);
lean_ctor_set(x_80, 3, x_68);
lean_ctor_set(x_80, 4, x_69);
lean_ctor_set(x_80, 5, x_70);
lean_ctor_set(x_80, 6, x_71);
lean_ctor_set(x_80, 7, x_72);
lean_ctor_set(x_80, 8, x_79);
lean_ctor_set(x_80, 9, x_74);
lean_ctor_set_uint8(x_80, sizeof(void*)*10, x_75);
lean_ctor_set_uint8(x_80, sizeof(void*)*10 + 1, x_76);
lean_ctor_set_uint8(x_80, sizeof(void*)*10 + 2, x_77);
x_81 = 1;
x_82 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_81, x_58, x_80, x_49);
return x_82;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_5);
if (x_113 == 0)
{
return x_5;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_5, 0);
x_115 = lean_ctor_get(x_5, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_5);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
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
l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__1);
l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__2);
l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_2__extractBind___closed__3);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3);
l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4 = _init_l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__3);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__4 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__4);
l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5 = _init_l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__5);
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
