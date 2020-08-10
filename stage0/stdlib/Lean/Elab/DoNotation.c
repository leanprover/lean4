// Lean compiler output
// Module: Lean.Elab.DoNotation
// Imports: Init Lean.Elab.Term Lean.Elab.Binders Lean.Elab.Quotation
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
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind___closed__3;
lean_object* l_Lean_Elab_Term_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_DoNotation_10__mkBind___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Lean_Elab_DoNotation_10__mkBind___spec__1___boxed(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_do___elambda__1___closed__1;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_6__expandLiftMethod(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_doPat___elambda__1___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_DoNotation_12__processDoElems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
lean_object* l___private_Lean_Elab_DoNotation_3__getDoElems___boxed(lean_object*);
uint8_t l___private_Lean_Elab_DoNotation_4__hasLiftMethod(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_3__getDoElems(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
lean_object* l_Lean_Elab_Term_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1;
extern lean_object* l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1;
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_do___elambda__1___closed__2;
uint8_t l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main(lean_object*);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_DoNotation_10__mkBind___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3;
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___boxed(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ProcessedDoElem_inhabited;
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDo___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5;
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_10__mkBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
extern lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_10__mkBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_13__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_8__expandDoElems(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_4__hasLiftMethod___boxed(lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_Lean_Syntax_inhabited;
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7;
lean_object* lean_environment_main_module(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDecl___closed__2;
extern lean_object* l_Lean_Parser_Term_match___elambda__1___closed__2;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
extern lean_object* l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Array_back___at___private_Lean_Elab_DoNotation_10__mkBind___spec__1(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind___closed__1;
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabDo(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1;
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind___closed__2;
extern lean_object* l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_matchAlt___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4;
extern lean_object* l_Lean_Parser_Term_doLet___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3;
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6;
lean_object* l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
lean_object* _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Id");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hasBind");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
x_2 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
lean_inc(x_9);
x_11 = l_Lean_mkConst(x_10, x_9);
x_12 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4;
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
x_19 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2;
lean_inc(x_18);
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4;
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
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_2__extractBind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid do notation, expected type is not available");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_2__extractBind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_2__extractBind___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_2__extractBind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_2__extractBind___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_DoNotation_2__extractBind___closed__3;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn___main(x_28);
x_31 = l_Lean_Expr_isMVar(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
x_32 = x_29;
goto block_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_28);
x_55 = l___private_Lean_Elab_DoNotation_2__extractBind___closed__3;
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
block_54:
{
if (lean_obj_tag(x_28) == 5)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
x_35 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_33);
x_36 = lean_array_push(x_35, x_33);
x_37 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_38 = l_Lean_Elab_Term_mkAppM(x_1, x_37, x_36, x_3, x_32);
lean_dec(x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_3);
x_41 = l_Lean_Elab_Term_synthesizeInst(x_1, x_39, x_3, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_28);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_34);
lean_dec(x_33);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_34);
lean_dec(x_33);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_dec(x_38);
x_52 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_51);
return x_52;
}
}
else
{
lean_object* x_53; 
x_53 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_28, x_3, x_32);
return x_53;
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
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Expr_getAppFn___main(x_76);
x_79 = l_Lean_Expr_isMVar(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
x_80 = x_77;
goto block_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_76);
x_101 = l___private_Lean_Elab_DoNotation_2__extractBind___closed__3;
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
block_100:
{
if (lean_obj_tag(x_76) == 5)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
x_83 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_81);
x_84 = lean_array_push(x_83, x_81);
x_85 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_86 = l_Lean_Elab_Term_mkAppM(x_1, x_85, x_84, x_3, x_80);
lean_dec(x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_3);
x_89 = l_Lean_Elab_Term_synthesizeInst(x_1, x_87, x_3, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_76);
lean_dec(x_3);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_82);
lean_ctor_set(x_93, 2, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_82);
lean_dec(x_81);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_76, x_3, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
lean_dec(x_81);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
lean_dec(x_86);
x_98 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_76, x_3, x_97);
return x_98;
}
}
else
{
lean_object* x_99; 
x_99 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_76, x_3, x_80);
return x_99;
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
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Expr_getAppFn___main(x_131);
x_134 = l_Lean_Expr_isMVar(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
x_135 = x_132;
goto block_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_131);
x_156 = l___private_Lean_Elab_DoNotation_2__extractBind___closed__3;
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
block_155:
{
if (lean_obj_tag(x_131) == 5)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
x_138 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_136);
x_139 = lean_array_push(x_138, x_136);
x_140 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_3);
x_141 = l_Lean_Elab_Term_mkAppM(x_1, x_140, x_139, x_3, x_135);
lean_dec(x_139);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_3);
x_144 = l_Lean_Elab_Term_synthesizeInst(x_1, x_142, x_3, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
lean_dec(x_3);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_136);
lean_ctor_set(x_148, 1, x_137);
lean_ctor_set(x_148, 2, x_145);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_137);
lean_dec(x_136);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_dec(x_144);
x_151 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_131, x_3, x_150);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_137);
lean_dec(x_136);
x_152 = lean_ctor_get(x_141, 1);
lean_inc(x_152);
lean_dec(x_141);
x_153 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_131, x_3, x_152);
return x_153;
}
}
else
{
lean_object* x_154; 
x_154 = l___private_Lean_Elab_DoNotation_1__mkIdBindFor(x_1, x_131, x_3, x_135);
return x_154;
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
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_DoNotation_2__extractBind(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_DoNotation_3__getDoElems(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_DoNotation_3__getDoElems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_7);
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
uint8_t l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main(lean_object* x_1) {
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
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(x_3, x_3, x_8, x_9);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_DoNotation_4__hasLiftMethod(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_DoNotation_4__hasLiftMethod___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_DoNotation_4__hasLiftMethod(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_2, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_2, x_1, x_12);
x_14 = x_11;
lean_inc(x_4);
x_15 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_14, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = x_18;
x_23 = lean_array_fset(x_13, x_1, x_22);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_3 = x_19;
x_5 = x_17;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("←");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = x_6;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1), 5, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = x_16;
x_18 = lean_apply_3(x_17, x_2, x_3, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_20, 0, x_1);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_28);
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_1);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_5);
x_37 = l_Lean_Syntax_inhabited;
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_array_get(x_37, x_6, x_38);
lean_dec(x_6);
x_40 = lean_nat_add(x_4, x_38);
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_ctor_get(x_3, 1);
lean_dec(x_43);
lean_inc(x_4);
lean_inc(x_42);
lean_ctor_set(x_3, 1, x_4);
x_44 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_39, x_2, x_3, x_40);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_51 = l_Lean_addMacroScope(x_42, x_50, x_4);
x_52 = lean_box(0);
x_53 = l_Lean_SourceInfo_inhabited___closed__1;
x_54 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
x_56 = l_Array_empty___closed__1;
x_57 = lean_array_push(x_56, x_55);
x_58 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_59 = lean_array_push(x_57, x_58);
x_60 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_59);
x_61 = lean_array_push(x_59, x_60);
x_62 = lean_array_push(x_61, x_48);
x_63 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_63);
x_64 = lean_array_push(x_56, x_1);
x_65 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_66 = lean_array_push(x_64, x_65);
x_67 = lean_box(0);
x_68 = lean_array_push(x_66, x_67);
x_69 = l_Lean_nullKind___closed__2;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_72 = lean_array_push(x_71, x_70);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_7);
lean_ctor_set(x_73, 1, x_72);
x_74 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_73);
lean_dec(x_73);
x_75 = lean_array_pop(x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_75, x_75, x_76, x_49);
lean_dec(x_75);
x_78 = l_Lean_mkTermIdFromIdent___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_59);
lean_ctor_set(x_46, 1, x_77);
lean_ctor_set(x_46, 0, x_79);
return x_44;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_80 = lean_ctor_get(x_46, 0);
x_81 = lean_ctor_get(x_46, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_46);
x_82 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_83 = l_Lean_addMacroScope(x_42, x_82, x_4);
x_84 = lean_box(0);
x_85 = l_Lean_SourceInfo_inhabited___closed__1;
x_86 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_84);
x_88 = l_Array_empty___closed__1;
x_89 = lean_array_push(x_88, x_87);
x_90 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_91 = lean_array_push(x_89, x_90);
x_92 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_91);
x_93 = lean_array_push(x_91, x_92);
x_94 = lean_array_push(x_93, x_80);
x_95 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_94);
lean_ctor_set(x_1, 0, x_95);
x_96 = lean_array_push(x_88, x_1);
x_97 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_98 = lean_array_push(x_96, x_97);
x_99 = lean_box(0);
x_100 = lean_array_push(x_98, x_99);
x_101 = l_Lean_nullKind___closed__2;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_104 = lean_array_push(x_103, x_102);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_7);
lean_ctor_set(x_105, 1, x_104);
x_106 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_105);
lean_dec(x_105);
x_107 = lean_array_pop(x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_107, x_107, x_108, x_81);
lean_dec(x_107);
x_110 = l_Lean_mkTermIdFromIdent___closed__2;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_91);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_44, 0, x_112);
return x_44;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_113 = lean_ctor_get(x_44, 0);
x_114 = lean_ctor_get(x_44, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_44);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
x_118 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_119 = l_Lean_addMacroScope(x_42, x_118, x_4);
x_120 = lean_box(0);
x_121 = l_Lean_SourceInfo_inhabited___closed__1;
x_122 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_123 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_119);
lean_ctor_set(x_123, 3, x_120);
x_124 = l_Array_empty___closed__1;
x_125 = lean_array_push(x_124, x_123);
x_126 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_127 = lean_array_push(x_125, x_126);
x_128 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_127);
x_129 = lean_array_push(x_127, x_128);
x_130 = lean_array_push(x_129, x_115);
x_131 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_130);
lean_ctor_set(x_1, 0, x_131);
x_132 = lean_array_push(x_124, x_1);
x_133 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_134 = lean_array_push(x_132, x_133);
x_135 = lean_box(0);
x_136 = lean_array_push(x_134, x_135);
x_137 = l_Lean_nullKind___closed__2;
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_140 = lean_array_push(x_139, x_138);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_7);
lean_ctor_set(x_141, 1, x_140);
x_142 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_141);
lean_dec(x_141);
x_143 = lean_array_pop(x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_143, x_143, x_144, x_116);
lean_dec(x_143);
x_146 = l_Lean_mkTermIdFromIdent___closed__2;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_127);
if (lean_is_scalar(x_117)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_117;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_114);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_42);
lean_free_object(x_1);
lean_dec(x_4);
x_150 = !lean_is_exclusive(x_44);
if (x_150 == 0)
{
return x_44;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_44, 0);
x_152 = lean_ctor_get(x_44, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_44);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_3, 0);
lean_inc(x_154);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_154);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_4);
x_156 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_39, x_2, x_155, x_40);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_162 = x_157;
} else {
 lean_dec_ref(x_157);
 x_162 = lean_box(0);
}
x_163 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_164 = l_Lean_addMacroScope(x_154, x_163, x_4);
x_165 = lean_box(0);
x_166 = l_Lean_SourceInfo_inhabited___closed__1;
x_167 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_168 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_164);
lean_ctor_set(x_168, 3, x_165);
x_169 = l_Array_empty___closed__1;
x_170 = lean_array_push(x_169, x_168);
x_171 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_172 = lean_array_push(x_170, x_171);
x_173 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_172);
x_174 = lean_array_push(x_172, x_173);
x_175 = lean_array_push(x_174, x_160);
x_176 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_ctor_set(x_1, 1, x_175);
lean_ctor_set(x_1, 0, x_176);
x_177 = lean_array_push(x_169, x_1);
x_178 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_179 = lean_array_push(x_177, x_178);
x_180 = lean_box(0);
x_181 = lean_array_push(x_179, x_180);
x_182 = l_Lean_nullKind___closed__2;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_185 = lean_array_push(x_184, x_183);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_7);
lean_ctor_set(x_186, 1, x_185);
x_187 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_186);
lean_dec(x_186);
x_188 = lean_array_pop(x_187);
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_188, x_188, x_189, x_161);
lean_dec(x_188);
x_191 = l_Lean_mkTermIdFromIdent___closed__2;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_172);
if (lean_is_scalar(x_162)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_162;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
if (lean_is_scalar(x_159)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_159;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_158);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_154);
lean_free_object(x_1);
lean_dec(x_4);
x_195 = lean_ctor_get(x_156, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_156, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_197 = x_156;
} else {
 lean_dec_ref(x_156);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
}
else
{
lean_object* x_199; uint8_t x_200; 
lean_dec(x_1);
x_199 = l_Lean_Parser_Term_liftMethod___elambda__1___closed__2;
x_200 = lean_name_eq(x_5, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = x_6;
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___spec__1), 5, 2);
lean_closure_set(x_203, 0, x_202);
lean_closure_set(x_203, 1, x_201);
x_204 = x_203;
x_205 = lean_apply_3(x_204, x_2, x_3, x_4);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_5);
lean_ctor_set(x_212, 1, x_209);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_210);
if (lean_is_scalar(x_208)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_208;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_207);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_5);
x_215 = lean_ctor_get(x_205, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_205, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_217 = x_205;
} else {
 lean_dec_ref(x_205);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_5);
x_219 = l_Lean_Syntax_inhabited;
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_array_get(x_219, x_6, x_220);
lean_dec(x_6);
x_222 = lean_nat_add(x_4, x_220);
x_223 = lean_ctor_get(x_3, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_224 = x_3;
} else {
 lean_dec_ref(x_3);
 x_224 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_223);
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_4);
x_226 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_221, x_2, x_225, x_222);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_227, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_232 = x_227;
} else {
 lean_dec_ref(x_227);
 x_232 = lean_box(0);
}
x_233 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_234 = l_Lean_addMacroScope(x_223, x_233, x_4);
x_235 = lean_box(0);
x_236 = l_Lean_SourceInfo_inhabited___closed__1;
x_237 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_238 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_238, 2, x_234);
lean_ctor_set(x_238, 3, x_235);
x_239 = l_Array_empty___closed__1;
x_240 = lean_array_push(x_239, x_238);
x_241 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_242 = lean_array_push(x_240, x_241);
x_243 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_242);
x_244 = lean_array_push(x_242, x_243);
x_245 = lean_array_push(x_244, x_230);
x_246 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = lean_array_push(x_239, x_247);
x_249 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_250 = lean_array_push(x_248, x_249);
x_251 = lean_box(0);
x_252 = lean_array_push(x_250, x_251);
x_253 = l_Lean_nullKind___closed__2;
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_256 = lean_array_push(x_255, x_254);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_7);
lean_ctor_set(x_257, 1, x_256);
x_258 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_257);
lean_dec(x_257);
x_259 = lean_array_pop(x_258);
x_260 = lean_unsigned_to_nat(0u);
x_261 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_259, x_259, x_260, x_231);
lean_dec(x_259);
x_262 = l_Lean_mkTermIdFromIdent___closed__2;
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_242);
if (lean_is_scalar(x_232)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_232;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_261);
if (lean_is_scalar(x_229)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_229;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_228);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_223);
lean_dec(x_4);
x_266 = lean_ctor_get(x_226, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_226, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_268 = x_226;
} else {
 lean_dec_ref(x_226);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_2);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_4);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_3);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_1);
lean_ctor_set(x_272, 1, x_2);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_4);
return x_273;
}
}
}
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_DoNotation_6__expandLiftMethod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Lean_Elab_DoNotation_4__hasLiftMethod___main(x_1);
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
lean_object* x_7; lean_object* x_8; 
x_7 = l_Array_empty___closed__1;
x_8 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main(x_1, x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
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
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1;
x_2 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_44 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_45 = lean_array_push(x_44, x_43);
x_46 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_47 = lean_array_push(x_45, x_46);
x_48 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
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
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
lean_inc(x_56);
x_57 = l___private_Lean_Elab_DoNotation_6__expandLiftMethod(x_56, x_4, x_5);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
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
x_82 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_83 = l_Lean_addMacroScope(x_81, x_82, x_80);
x_84 = lean_box(0);
x_85 = l_Lean_SourceInfo_inhabited___closed__1;
x_86 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_87 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_84);
x_88 = l_Array_empty___closed__1;
x_89 = lean_array_push(x_88, x_87);
x_90 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_91 = lean_array_push(x_89, x_90);
x_92 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_93 = lean_array_push(x_91, x_92);
x_94 = lean_array_push(x_93, x_79);
x_95 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_array_push(x_88, x_96);
x_98 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_box(0);
x_101 = lean_array_push(x_99, x_100);
x_102 = l_Lean_nullKind___closed__2;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_105 = lean_array_push(x_104, x_103);
x_106 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_107);
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
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_127 = lean_nat_add(x_60, x_125);
x_128 = lean_ctor_get(x_4, 0);
lean_inc(x_128);
lean_dec(x_4);
x_129 = l_Array_empty___closed__1;
x_130 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_123, x_123, x_116, x_129);
lean_dec(x_123);
x_131 = l_Lean_nullKind___closed__2;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_134 = lean_array_push(x_133, x_132);
x_135 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_136 = lean_array_push(x_134, x_135);
x_137 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_140 = lean_array_push(x_139, x_138);
x_141 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_Syntax_isNone(x_121);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_144 = l_Lean_Syntax_getArg(x_121, x_125);
lean_dec(x_121);
x_145 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_146 = l_Lean_addMacroScope(x_128, x_145, x_60);
x_147 = lean_box(0);
x_148 = l_Lean_SourceInfo_inhabited___closed__1;
x_149 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_150 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_146);
lean_ctor_set(x_150, 3, x_147);
x_151 = lean_array_push(x_129, x_150);
x_152 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_153 = lean_array_push(x_151, x_152);
x_154 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_153);
x_155 = lean_array_push(x_153, x_154);
x_156 = lean_array_push(x_155, x_119);
x_157 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_array_push(x_129, x_158);
x_160 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_161 = lean_array_push(x_159, x_160);
x_162 = l_Lean_mkTermIdFromIdent___closed__2;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_153);
x_164 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_165 = lean_array_push(x_164, x_163);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_131);
lean_ctor_set(x_166, 1, x_165);
x_167 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_168 = lean_array_push(x_167, x_166);
x_169 = lean_array_push(x_168, x_152);
x_170 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_171 = lean_array_push(x_169, x_170);
x_172 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_173 = lean_array_push(x_171, x_172);
x_174 = lean_array_push(x_129, x_117);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_131);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_push(x_129, x_175);
x_177 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_178 = lean_array_push(x_176, x_177);
x_179 = lean_array_push(x_178, x_142);
x_180 = l_Lean_Parser_Term_matchAlt___closed__2;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_array_push(x_129, x_181);
x_183 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_184 = lean_array_push(x_182, x_183);
x_185 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_186 = lean_array_push(x_185, x_144);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_180);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_array_push(x_184, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_131);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_array_push(x_173, x_189);
x_191 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_array_push(x_129, x_192);
x_194 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_array_push(x_161, x_195);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_131);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_array_push(x_139, x_197);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_141);
lean_ctor_set(x_199, 1, x_198);
x_6 = x_199;
x_7 = x_127;
goto block_34;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_121);
x_200 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_201 = l_Lean_addMacroScope(x_128, x_200, x_60);
x_202 = lean_box(0);
x_203 = l_Lean_SourceInfo_inhabited___closed__1;
x_204 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_205 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_201);
lean_ctor_set(x_205, 3, x_202);
x_206 = lean_array_push(x_129, x_205);
x_207 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_208 = lean_array_push(x_206, x_207);
x_209 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_208);
x_210 = lean_array_push(x_208, x_209);
x_211 = lean_array_push(x_210, x_119);
x_212 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_array_push(x_129, x_213);
x_215 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_216 = lean_array_push(x_214, x_215);
x_217 = l_Lean_mkTermIdFromIdent___closed__2;
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_208);
x_219 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_220 = lean_array_push(x_219, x_218);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_131);
lean_ctor_set(x_221, 1, x_220);
x_222 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_223 = lean_array_push(x_222, x_221);
x_224 = lean_array_push(x_223, x_207);
x_225 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_226 = lean_array_push(x_224, x_225);
x_227 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_228 = lean_array_push(x_226, x_227);
x_229 = lean_array_push(x_129, x_117);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_131);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_array_push(x_129, x_230);
x_232 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_233 = lean_array_push(x_231, x_232);
x_234 = lean_array_push(x_233, x_142);
x_235 = l_Lean_Parser_Term_matchAlt___closed__2;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = lean_array_push(x_129, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_131);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_array_push(x_228, x_238);
x_240 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_push(x_129, x_241);
x_243 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_array_push(x_216, x_244);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_131);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_array_push(x_139, x_246);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_141);
lean_ctor_set(x_248, 1, x_247);
x_6 = x_248;
x_7 = x_127;
goto block_34;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_249 = l_Lean_Syntax_inhabited;
x_250 = lean_array_get(x_249, x_123, x_116);
lean_dec(x_123);
x_251 = l_Lean_Syntax_getArg(x_250, x_116);
lean_dec(x_250);
x_252 = lean_nat_add(x_60, x_125);
x_253 = lean_ctor_get(x_4, 0);
lean_inc(x_253);
lean_dec(x_4);
x_254 = l_Lean_Syntax_isNone(x_121);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_255 = l_Lean_Syntax_getArg(x_121, x_125);
lean_dec(x_121);
x_256 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_257 = l_Lean_addMacroScope(x_253, x_256, x_60);
x_258 = lean_box(0);
x_259 = l_Lean_SourceInfo_inhabited___closed__1;
x_260 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_261 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
lean_ctor_set(x_261, 2, x_257);
lean_ctor_set(x_261, 3, x_258);
x_262 = l_Array_empty___closed__1;
x_263 = lean_array_push(x_262, x_261);
x_264 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_265 = lean_array_push(x_263, x_264);
x_266 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_265);
x_267 = lean_array_push(x_265, x_266);
x_268 = lean_array_push(x_267, x_119);
x_269 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_array_push(x_262, x_270);
x_272 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_273 = lean_array_push(x_271, x_272);
x_274 = l_Lean_mkTermIdFromIdent___closed__2;
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_265);
x_276 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_277 = lean_array_push(x_276, x_275);
x_278 = l_Lean_nullKind___closed__2;
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_281 = lean_array_push(x_280, x_279);
x_282 = lean_array_push(x_281, x_264);
x_283 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_284 = lean_array_push(x_282, x_283);
x_285 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_286 = lean_array_push(x_284, x_285);
x_287 = lean_array_push(x_262, x_117);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_278);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_array_push(x_262, x_288);
x_290 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_291 = lean_array_push(x_289, x_290);
x_292 = lean_array_push(x_291, x_251);
x_293 = l_Lean_Parser_Term_matchAlt___closed__2;
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
x_295 = lean_array_push(x_262, x_294);
x_296 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_297 = lean_array_push(x_295, x_296);
x_298 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_299 = lean_array_push(x_298, x_255);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_293);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_array_push(x_297, x_300);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_278);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_array_push(x_286, x_302);
x_304 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
x_306 = lean_array_push(x_262, x_305);
x_307 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_306);
x_309 = lean_array_push(x_273, x_308);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_278);
lean_ctor_set(x_310, 1, x_309);
x_311 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_312 = lean_array_push(x_311, x_310);
x_313 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_312);
x_6 = x_314;
x_7 = x_252;
goto block_34;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_121);
x_315 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_316 = l_Lean_addMacroScope(x_253, x_315, x_60);
x_317 = lean_box(0);
x_318 = l_Lean_SourceInfo_inhabited___closed__1;
x_319 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_320 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
lean_ctor_set(x_320, 2, x_316);
lean_ctor_set(x_320, 3, x_317);
x_321 = l_Array_empty___closed__1;
x_322 = lean_array_push(x_321, x_320);
x_323 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_324 = lean_array_push(x_322, x_323);
x_325 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_324);
x_326 = lean_array_push(x_324, x_325);
x_327 = lean_array_push(x_326, x_119);
x_328 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = lean_array_push(x_321, x_329);
x_331 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_332 = lean_array_push(x_330, x_331);
x_333 = l_Lean_mkTermIdFromIdent___closed__2;
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_324);
x_335 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_336 = lean_array_push(x_335, x_334);
x_337 = l_Lean_nullKind___closed__2;
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_336);
x_339 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_340 = lean_array_push(x_339, x_338);
x_341 = lean_array_push(x_340, x_323);
x_342 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_343 = lean_array_push(x_341, x_342);
x_344 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_345 = lean_array_push(x_343, x_344);
x_346 = lean_array_push(x_321, x_117);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_337);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_array_push(x_321, x_347);
x_349 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_350 = lean_array_push(x_348, x_349);
x_351 = lean_array_push(x_350, x_251);
x_352 = l_Lean_Parser_Term_matchAlt___closed__2;
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_array_push(x_321, x_353);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_337);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_array_push(x_345, x_355);
x_357 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
x_359 = lean_array_push(x_321, x_358);
x_360 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
x_362 = lean_array_push(x_332, x_361);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_337);
lean_ctor_set(x_363, 1, x_362);
x_364 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_365 = lean_array_push(x_364, x_363);
x_366 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
x_6 = x_367;
x_7 = x_252;
goto block_34;
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
lean_dec(x_62);
lean_dec(x_4);
x_368 = lean_unsigned_to_nat(1u);
x_369 = l_Lean_Syntax_getArg(x_56, x_368);
lean_dec(x_56);
x_370 = lean_unsigned_to_nat(2u);
x_371 = lean_nat_add(x_3, x_370);
x_372 = l_Array_extract___rarg(x_2, x_371, x_35);
lean_dec(x_35);
x_373 = lean_array_get_size(x_372);
x_374 = lean_nat_dec_eq(x_373, x_368);
lean_dec(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_375 = lean_unsigned_to_nat(0u);
x_376 = l_Array_empty___closed__1;
x_377 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_372, x_372, x_375, x_376);
lean_dec(x_372);
x_378 = l_Lean_nullKind___closed__2;
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_381 = lean_array_push(x_380, x_379);
x_382 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_383 = lean_array_push(x_381, x_382);
x_384 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_387 = lean_array_push(x_386, x_385);
x_388 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_387);
x_390 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_391 = lean_array_push(x_390, x_369);
x_392 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_393 = lean_array_push(x_391, x_392);
x_394 = lean_array_push(x_393, x_389);
x_395 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
x_397 = lean_nat_dec_eq(x_3, x_375);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_398 = l_Array_extract___rarg(x_2, x_375, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_399 = l_Lean_mkOptionalNode___closed__2;
x_400 = lean_array_push(x_399, x_396);
x_401 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
x_403 = lean_array_push(x_398, x_402);
x_404 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_403, x_403, x_375, x_376);
lean_dec(x_403);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_array_push(x_380, x_405);
x_407 = lean_array_push(x_406, x_382);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_384);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_array_push(x_386, x_408);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_388);
lean_ctor_set(x_410, 1, x_409);
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_57, 0, x_411);
return x_57;
}
else
{
lean_object* x_412; 
lean_dec(x_3);
lean_dec(x_2);
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_396);
lean_ctor_set(x_57, 0, x_412);
return x_57;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_413 = l_Lean_Syntax_inhabited;
x_414 = lean_unsigned_to_nat(0u);
x_415 = lean_array_get(x_413, x_372, x_414);
lean_dec(x_372);
x_416 = l_Lean_Syntax_getArg(x_415, x_414);
lean_dec(x_415);
x_417 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_418 = lean_array_push(x_417, x_369);
x_419 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_420 = lean_array_push(x_418, x_419);
x_421 = lean_array_push(x_420, x_416);
x_422 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_421);
x_424 = lean_nat_dec_eq(x_3, x_414);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_425 = l_Array_extract___rarg(x_2, x_414, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_426 = l_Lean_mkOptionalNode___closed__2;
x_427 = lean_array_push(x_426, x_423);
x_428 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_427);
x_430 = lean_array_push(x_425, x_429);
x_431 = l_Array_empty___closed__1;
x_432 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_430, x_430, x_414, x_431);
lean_dec(x_430);
x_433 = l_Lean_nullKind___closed__2;
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_432);
x_435 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_436 = lean_array_push(x_435, x_434);
x_437 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_438 = lean_array_push(x_436, x_437);
x_439 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
x_441 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_442 = lean_array_push(x_441, x_440);
x_443 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_442);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_57, 0, x_445);
return x_57;
}
else
{
lean_object* x_446; 
lean_dec(x_3);
lean_dec(x_2);
x_446 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_446, 0, x_423);
lean_ctor_set(x_57, 0, x_446);
return x_57;
}
}
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_447 = lean_ctor_get(x_57, 1);
lean_inc(x_447);
lean_dec(x_57);
lean_inc(x_56);
x_448 = l_Lean_Syntax_getKind(x_56);
x_449 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_450 = lean_name_eq(x_448, x_449);
if (x_450 == 0)
{
lean_object* x_451; uint8_t x_452; 
x_451 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_452 = lean_name_eq(x_448, x_451);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_453 = lean_unsigned_to_nat(1u);
x_454 = lean_nat_sub(x_35, x_453);
lean_dec(x_35);
x_455 = lean_nat_dec_lt(x_3, x_454);
lean_dec(x_454);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; 
lean_dec(x_448);
lean_dec(x_56);
x_456 = lean_unsigned_to_nat(2u);
x_457 = lean_nat_add(x_3, x_456);
lean_dec(x_3);
x_3 = x_457;
x_5 = x_447;
goto _start;
}
else
{
lean_object* x_459; uint8_t x_460; 
x_459 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_460 = lean_name_eq(x_448, x_459);
lean_dec(x_448);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
lean_dec(x_56);
x_461 = lean_unsigned_to_nat(2u);
x_462 = lean_nat_add(x_3, x_461);
lean_dec(x_3);
x_3 = x_462;
x_5 = x_447;
goto _start;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_464 = lean_unsigned_to_nat(0u);
x_465 = l_Lean_Syntax_getArg(x_56, x_464);
lean_dec(x_56);
x_466 = lean_ctor_get(x_4, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_4, 0);
lean_inc(x_467);
x_468 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_469 = l_Lean_addMacroScope(x_467, x_468, x_466);
x_470 = lean_box(0);
x_471 = l_Lean_SourceInfo_inhabited___closed__1;
x_472 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_473 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
lean_ctor_set(x_473, 2, x_469);
lean_ctor_set(x_473, 3, x_470);
x_474 = l_Array_empty___closed__1;
x_475 = lean_array_push(x_474, x_473);
x_476 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_477 = lean_array_push(x_475, x_476);
x_478 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_479 = lean_array_push(x_477, x_478);
x_480 = lean_array_push(x_479, x_465);
x_481 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_480);
x_483 = lean_array_push(x_474, x_482);
x_484 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_485 = lean_array_push(x_483, x_484);
x_486 = lean_box(0);
x_487 = lean_array_push(x_485, x_486);
x_488 = l_Lean_nullKind___closed__2;
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_487);
x_490 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_491 = lean_array_push(x_490, x_489);
x_492 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
x_494 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_493);
lean_dec(x_493);
x_495 = l_Lean_Syntax_inhabited;
x_496 = lean_array_get(x_495, x_494, x_464);
lean_dec(x_494);
x_497 = lean_array_set(x_2, x_3, x_496);
x_498 = lean_unsigned_to_nat(2u);
x_499 = lean_nat_add(x_3, x_498);
lean_dec(x_3);
x_500 = 1;
x_1 = x_500;
x_2 = x_497;
x_3 = x_499;
x_5 = x_447;
goto _start;
}
}
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
lean_dec(x_448);
x_502 = lean_unsigned_to_nat(0u);
x_503 = l_Lean_Syntax_getArg(x_56, x_502);
x_504 = lean_unsigned_to_nat(2u);
x_505 = l_Lean_Syntax_getArg(x_56, x_504);
x_506 = lean_unsigned_to_nat(3u);
x_507 = l_Lean_Syntax_getArg(x_56, x_506);
lean_dec(x_56);
x_508 = lean_nat_add(x_3, x_504);
x_509 = l_Array_extract___rarg(x_2, x_508, x_35);
lean_dec(x_35);
x_510 = lean_array_get_size(x_509);
x_511 = lean_unsigned_to_nat(1u);
x_512 = lean_nat_dec_eq(x_510, x_511);
lean_dec(x_510);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; 
x_513 = lean_nat_add(x_447, x_511);
x_514 = lean_ctor_get(x_4, 0);
lean_inc(x_514);
lean_dec(x_4);
x_515 = l_Array_empty___closed__1;
x_516 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_509, x_509, x_502, x_515);
lean_dec(x_509);
x_517 = l_Lean_nullKind___closed__2;
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_516);
x_519 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_520 = lean_array_push(x_519, x_518);
x_521 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_522 = lean_array_push(x_520, x_521);
x_523 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_522);
x_525 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_526 = lean_array_push(x_525, x_524);
x_527 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_526);
x_529 = l_Lean_Syntax_isNone(x_507);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_530 = l_Lean_Syntax_getArg(x_507, x_511);
lean_dec(x_507);
x_531 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_532 = l_Lean_addMacroScope(x_514, x_531, x_447);
x_533 = lean_box(0);
x_534 = l_Lean_SourceInfo_inhabited___closed__1;
x_535 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_536 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
lean_ctor_set(x_536, 2, x_532);
lean_ctor_set(x_536, 3, x_533);
x_537 = lean_array_push(x_515, x_536);
x_538 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_539 = lean_array_push(x_537, x_538);
x_540 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_539);
x_541 = lean_array_push(x_539, x_540);
x_542 = lean_array_push(x_541, x_505);
x_543 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_542);
x_545 = lean_array_push(x_515, x_544);
x_546 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_547 = lean_array_push(x_545, x_546);
x_548 = l_Lean_mkTermIdFromIdent___closed__2;
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_539);
x_550 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_551 = lean_array_push(x_550, x_549);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_517);
lean_ctor_set(x_552, 1, x_551);
x_553 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_554 = lean_array_push(x_553, x_552);
x_555 = lean_array_push(x_554, x_538);
x_556 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_557 = lean_array_push(x_555, x_556);
x_558 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_559 = lean_array_push(x_557, x_558);
x_560 = lean_array_push(x_515, x_503);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_517);
lean_ctor_set(x_561, 1, x_560);
x_562 = lean_array_push(x_515, x_561);
x_563 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_564 = lean_array_push(x_562, x_563);
x_565 = lean_array_push(x_564, x_528);
x_566 = l_Lean_Parser_Term_matchAlt___closed__2;
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_565);
x_568 = lean_array_push(x_515, x_567);
x_569 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_570 = lean_array_push(x_568, x_569);
x_571 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_572 = lean_array_push(x_571, x_530);
x_573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_573, 0, x_566);
lean_ctor_set(x_573, 1, x_572);
x_574 = lean_array_push(x_570, x_573);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_517);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_array_push(x_559, x_575);
x_577 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_576);
x_579 = lean_array_push(x_515, x_578);
x_580 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_579);
x_582 = lean_array_push(x_547, x_581);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_517);
lean_ctor_set(x_583, 1, x_582);
x_584 = lean_array_push(x_525, x_583);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_527);
lean_ctor_set(x_585, 1, x_584);
x_6 = x_585;
x_7 = x_513;
goto block_34;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_507);
x_586 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_587 = l_Lean_addMacroScope(x_514, x_586, x_447);
x_588 = lean_box(0);
x_589 = l_Lean_SourceInfo_inhabited___closed__1;
x_590 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_591 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
lean_ctor_set(x_591, 2, x_587);
lean_ctor_set(x_591, 3, x_588);
x_592 = lean_array_push(x_515, x_591);
x_593 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_594 = lean_array_push(x_592, x_593);
x_595 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_594);
x_596 = lean_array_push(x_594, x_595);
x_597 = lean_array_push(x_596, x_505);
x_598 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_597);
x_600 = lean_array_push(x_515, x_599);
x_601 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_602 = lean_array_push(x_600, x_601);
x_603 = l_Lean_mkTermIdFromIdent___closed__2;
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_594);
x_605 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_606 = lean_array_push(x_605, x_604);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_517);
lean_ctor_set(x_607, 1, x_606);
x_608 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_609 = lean_array_push(x_608, x_607);
x_610 = lean_array_push(x_609, x_593);
x_611 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_612 = lean_array_push(x_610, x_611);
x_613 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_614 = lean_array_push(x_612, x_613);
x_615 = lean_array_push(x_515, x_503);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_517);
lean_ctor_set(x_616, 1, x_615);
x_617 = lean_array_push(x_515, x_616);
x_618 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_619 = lean_array_push(x_617, x_618);
x_620 = lean_array_push(x_619, x_528);
x_621 = l_Lean_Parser_Term_matchAlt___closed__2;
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_620);
x_623 = lean_array_push(x_515, x_622);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_517);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_array_push(x_614, x_624);
x_626 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_625);
x_628 = lean_array_push(x_515, x_627);
x_629 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_628);
x_631 = lean_array_push(x_602, x_630);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_517);
lean_ctor_set(x_632, 1, x_631);
x_633 = lean_array_push(x_525, x_632);
x_634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_634, 0, x_527);
lean_ctor_set(x_634, 1, x_633);
x_6 = x_634;
x_7 = x_513;
goto block_34;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
x_635 = l_Lean_Syntax_inhabited;
x_636 = lean_array_get(x_635, x_509, x_502);
lean_dec(x_509);
x_637 = l_Lean_Syntax_getArg(x_636, x_502);
lean_dec(x_636);
x_638 = lean_nat_add(x_447, x_511);
x_639 = lean_ctor_get(x_4, 0);
lean_inc(x_639);
lean_dec(x_4);
x_640 = l_Lean_Syntax_isNone(x_507);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_641 = l_Lean_Syntax_getArg(x_507, x_511);
lean_dec(x_507);
x_642 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_643 = l_Lean_addMacroScope(x_639, x_642, x_447);
x_644 = lean_box(0);
x_645 = l_Lean_SourceInfo_inhabited___closed__1;
x_646 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_647 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set(x_647, 1, x_646);
lean_ctor_set(x_647, 2, x_643);
lean_ctor_set(x_647, 3, x_644);
x_648 = l_Array_empty___closed__1;
x_649 = lean_array_push(x_648, x_647);
x_650 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_651 = lean_array_push(x_649, x_650);
x_652 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_651);
x_653 = lean_array_push(x_651, x_652);
x_654 = lean_array_push(x_653, x_505);
x_655 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_654);
x_657 = lean_array_push(x_648, x_656);
x_658 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_659 = lean_array_push(x_657, x_658);
x_660 = l_Lean_mkTermIdFromIdent___closed__2;
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_651);
x_662 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_663 = lean_array_push(x_662, x_661);
x_664 = l_Lean_nullKind___closed__2;
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_663);
x_666 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_667 = lean_array_push(x_666, x_665);
x_668 = lean_array_push(x_667, x_650);
x_669 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_670 = lean_array_push(x_668, x_669);
x_671 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_672 = lean_array_push(x_670, x_671);
x_673 = lean_array_push(x_648, x_503);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_664);
lean_ctor_set(x_674, 1, x_673);
x_675 = lean_array_push(x_648, x_674);
x_676 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_677 = lean_array_push(x_675, x_676);
x_678 = lean_array_push(x_677, x_637);
x_679 = l_Lean_Parser_Term_matchAlt___closed__2;
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_678);
x_681 = lean_array_push(x_648, x_680);
x_682 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_683 = lean_array_push(x_681, x_682);
x_684 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_685 = lean_array_push(x_684, x_641);
x_686 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_686, 0, x_679);
lean_ctor_set(x_686, 1, x_685);
x_687 = lean_array_push(x_683, x_686);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_664);
lean_ctor_set(x_688, 1, x_687);
x_689 = lean_array_push(x_672, x_688);
x_690 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_692 = lean_array_push(x_648, x_691);
x_693 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_692);
x_695 = lean_array_push(x_659, x_694);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_664);
lean_ctor_set(x_696, 1, x_695);
x_697 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_698 = lean_array_push(x_697, x_696);
x_699 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
x_6 = x_700;
x_7 = x_638;
goto block_34;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_507);
x_701 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_702 = l_Lean_addMacroScope(x_639, x_701, x_447);
x_703 = lean_box(0);
x_704 = l_Lean_SourceInfo_inhabited___closed__1;
x_705 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_706 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
lean_ctor_set(x_706, 2, x_702);
lean_ctor_set(x_706, 3, x_703);
x_707 = l_Array_empty___closed__1;
x_708 = lean_array_push(x_707, x_706);
x_709 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_710 = lean_array_push(x_708, x_709);
x_711 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_710);
x_712 = lean_array_push(x_710, x_711);
x_713 = lean_array_push(x_712, x_505);
x_714 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_713);
x_716 = lean_array_push(x_707, x_715);
x_717 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_718 = lean_array_push(x_716, x_717);
x_719 = l_Lean_mkTermIdFromIdent___closed__2;
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_710);
x_721 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_722 = lean_array_push(x_721, x_720);
x_723 = l_Lean_nullKind___closed__2;
x_724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_722);
x_725 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_726 = lean_array_push(x_725, x_724);
x_727 = lean_array_push(x_726, x_709);
x_728 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__5;
x_729 = lean_array_push(x_727, x_728);
x_730 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__8;
x_731 = lean_array_push(x_729, x_730);
x_732 = lean_array_push(x_707, x_503);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_723);
lean_ctor_set(x_733, 1, x_732);
x_734 = lean_array_push(x_707, x_733);
x_735 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_736 = lean_array_push(x_734, x_735);
x_737 = lean_array_push(x_736, x_637);
x_738 = l_Lean_Parser_Term_matchAlt___closed__2;
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_737);
x_740 = lean_array_push(x_707, x_739);
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_723);
lean_ctor_set(x_741, 1, x_740);
x_742 = lean_array_push(x_731, x_741);
x_743 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_742);
x_745 = lean_array_push(x_707, x_744);
x_746 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_745);
x_748 = lean_array_push(x_718, x_747);
x_749 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_749, 0, x_723);
lean_ctor_set(x_749, 1, x_748);
x_750 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_751 = lean_array_push(x_750, x_749);
x_752 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_751);
x_6 = x_753;
x_7 = x_638;
goto block_34;
}
}
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; 
lean_dec(x_448);
lean_dec(x_4);
x_754 = lean_unsigned_to_nat(1u);
x_755 = l_Lean_Syntax_getArg(x_56, x_754);
lean_dec(x_56);
x_756 = lean_unsigned_to_nat(2u);
x_757 = lean_nat_add(x_3, x_756);
x_758 = l_Array_extract___rarg(x_2, x_757, x_35);
lean_dec(x_35);
x_759 = lean_array_get_size(x_758);
x_760 = lean_nat_dec_eq(x_759, x_754);
lean_dec(x_759);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; uint8_t x_783; 
x_761 = lean_unsigned_to_nat(0u);
x_762 = l_Array_empty___closed__1;
x_763 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_758, x_758, x_761, x_762);
lean_dec(x_758);
x_764 = l_Lean_nullKind___closed__2;
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_763);
x_766 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_767 = lean_array_push(x_766, x_765);
x_768 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_769 = lean_array_push(x_767, x_768);
x_770 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set(x_771, 1, x_769);
x_772 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_773 = lean_array_push(x_772, x_771);
x_774 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_775, 0, x_774);
lean_ctor_set(x_775, 1, x_773);
x_776 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_777 = lean_array_push(x_776, x_755);
x_778 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_779 = lean_array_push(x_777, x_778);
x_780 = lean_array_push(x_779, x_775);
x_781 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_780);
x_783 = lean_nat_dec_eq(x_3, x_761);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_784 = l_Array_extract___rarg(x_2, x_761, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_785 = l_Lean_mkOptionalNode___closed__2;
x_786 = lean_array_push(x_785, x_782);
x_787 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_786);
x_789 = lean_array_push(x_784, x_788);
x_790 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_789, x_789, x_761, x_762);
lean_dec(x_789);
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_764);
lean_ctor_set(x_791, 1, x_790);
x_792 = lean_array_push(x_766, x_791);
x_793 = lean_array_push(x_792, x_768);
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_770);
lean_ctor_set(x_794, 1, x_793);
x_795 = lean_array_push(x_772, x_794);
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_774);
lean_ctor_set(x_796, 1, x_795);
x_797 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_797, 0, x_796);
x_798 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_447);
return x_798;
}
else
{
lean_object* x_799; lean_object* x_800; 
lean_dec(x_3);
lean_dec(x_2);
x_799 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_799, 0, x_782);
x_800 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_447);
return x_800;
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; uint8_t x_812; 
x_801 = l_Lean_Syntax_inhabited;
x_802 = lean_unsigned_to_nat(0u);
x_803 = lean_array_get(x_801, x_758, x_802);
lean_dec(x_758);
x_804 = l_Lean_Syntax_getArg(x_803, x_802);
lean_dec(x_803);
x_805 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_806 = lean_array_push(x_805, x_755);
x_807 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_808 = lean_array_push(x_806, x_807);
x_809 = lean_array_push(x_808, x_804);
x_810 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_809);
x_812 = lean_nat_dec_eq(x_3, x_802);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_813 = l_Array_extract___rarg(x_2, x_802, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_814 = l_Lean_mkOptionalNode___closed__2;
x_815 = lean_array_push(x_814, x_811);
x_816 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_815);
x_818 = lean_array_push(x_813, x_817);
x_819 = l_Array_empty___closed__1;
x_820 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_818, x_818, x_802, x_819);
lean_dec(x_818);
x_821 = l_Lean_nullKind___closed__2;
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_820);
x_823 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_824 = lean_array_push(x_823, x_822);
x_825 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_826 = lean_array_push(x_824, x_825);
x_827 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_826);
x_829 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_830 = lean_array_push(x_829, x_828);
x_831 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_831);
lean_ctor_set(x_832, 1, x_830);
x_833 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_833, 0, x_832);
x_834 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_447);
return x_834;
}
else
{
lean_object* x_835; lean_object* x_836; 
lean_dec(x_3);
lean_dec(x_2);
x_835 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_835, 0, x_811);
x_836 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_836, 0, x_835);
lean_ctor_set(x_836, 1, x_447);
return x_836;
}
}
}
}
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; uint8_t x_846; 
lean_dec(x_56);
x_837 = lean_ctor_get(x_57, 1);
lean_inc(x_837);
lean_dec(x_57);
x_838 = lean_ctor_get(x_58, 0);
lean_inc(x_838);
lean_dec(x_58);
x_839 = lean_unsigned_to_nat(1u);
x_840 = lean_nat_add(x_3, x_839);
x_841 = l_Array_extract___rarg(x_2, x_840, x_35);
lean_dec(x_35);
x_842 = lean_unsigned_to_nat(0u);
x_843 = l_Array_extract___rarg(x_2, x_842, x_3);
lean_dec(x_2);
x_844 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_838, x_838, x_842, x_843);
lean_dec(x_838);
x_845 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_841, x_841, x_842, x_844);
lean_dec(x_841);
x_846 = 1;
x_1 = x_846;
x_2 = x_845;
x_5 = x_837;
goto _start;
}
}
else
{
uint8_t x_848; 
lean_dec(x_56);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_848 = !lean_is_exclusive(x_57);
if (x_848 == 0)
{
return x_57;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_849 = lean_ctor_get(x_57, 0);
x_850 = lean_ctor_get(x_57, 1);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_57);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
return x_851;
}
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
x_20 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_23 = lean_array_push(x_21, x_22);
x_24 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
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
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_DoNotation_8__expandDoElems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_4, x_1, x_5, x_2, x_3);
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
lean_object* _init_l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type former application expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_31 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
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
x_42 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
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
x_70 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
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
x_107 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3;
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
lean_object* l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_back___at___private_Lean_Elab_DoNotation_10__mkBind___spec__1(lean_object* x_1) {
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
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_DoNotation_10__mkBind___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_23 = l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg(x_1, x_21, x_8, x_22);
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
x_31 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
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
lean_object* l___private_Lean_Elab_DoNotation_10__mkBind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Array_back___at___private_Lean_Elab_DoNotation_10__mkBind___spec__1(x_4);
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
x_30 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_DoNotation_10__mkBind___spec__2(x_1, x_4, x_28, x_4, x_29, lean_box(0), x_5, x_6, x_22);
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
lean_object* l_Array_back___at___private_Lean_Elab_DoNotation_10__mkBind___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at___private_Lean_Elab_DoNotation_10__mkBind___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_DoNotation_10__mkBind___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_DoNotation_10__mkBind___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_DoNotation_10__mkBind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_DoNotation_10__mkBind(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_array_push(x_3, x_13);
x_15 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main(x_4, x_5, x_6, x_7, x_12, x_14, x_9, x_10);
return x_15;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected 'do' expression element");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("the last statement in a 'do' block must be an expression");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Term_throwError___rarg(x_10, x_18, x_7, x_8);
lean_dec(x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_array_get_size(x_1);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_nat_dec_eq(x_5, x_22);
lean_dec(x_22);
lean_dec(x_5);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_10, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_4);
if (x_23 == 0)
{
uint8_t x_57; 
x_57 = 1;
x_27 = x_57;
goto block_56;
}
else
{
uint8_t x_58; 
x_58 = 0;
x_27 = x_58;
goto block_56;
}
block_56:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_54; 
x_54 = 0;
x_28 = x_54;
goto block_53;
}
else
{
uint8_t x_55; 
x_55 = 1;
x_28 = x_55;
goto block_53;
}
block_53:
{
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
x_29 = 1;
lean_inc(x_7);
lean_inc(x_26);
x_30 = l_Lean_Elab_Term_elabTermAux___main(x_26, x_29, x_29, x_25, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_10);
x_33 = l_Lean_Elab_Term_ensureHasType(x_10, x_26, x_31, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_DoNotation_10__mkBind(x_10, x_2, x_3, x_6, x_34, x_7, x_35);
lean_dec(x_6);
lean_dec(x_10);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_41; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_10);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_10);
x_46 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_Term_throwError___rarg(x_10, x_47, x_7, x_8);
lean_dec(x_10);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_11);
x_59 = lean_array_get_size(x_1);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_59, x_60);
lean_dec(x_59);
x_62 = lean_nat_dec_eq(x_5, x_61);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Syntax_getIdAt(x_10, x_63);
x_65 = l_Lean_Syntax_getArg(x_10, x_60);
x_66 = l_Lean_Elab_Term_expandOptType(x_10, x_65);
lean_dec(x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = l_Lean_Syntax_getArg(x_10, x_67);
if (x_62 == 0)
{
lean_object* x_69; 
lean_inc(x_7);
x_69 = l_Lean_Elab_Term_elabType(x_66, x_7, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_70);
lean_inc(x_2);
x_72 = l_Lean_mkApp(x_2, x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = 1;
lean_inc(x_7);
lean_inc(x_68);
lean_inc(x_73);
x_75 = l_Lean_Elab_Term_elabTermAux___main(x_73, x_74, x_74, x_68, x_7, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_7);
x_78 = l_Lean_Elab_Term_ensureHasType(x_68, x_73, x_76, x_7, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1___boxed), 10, 7);
lean_closure_set(x_81, 0, x_5);
lean_closure_set(x_81, 1, x_79);
lean_closure_set(x_81, 2, x_6);
lean_closure_set(x_81, 3, x_1);
lean_closure_set(x_81, 4, x_2);
lean_closure_set(x_81, 5, x_3);
lean_closure_set(x_81, 6, x_4);
x_82 = 0;
x_83 = l_Lean_Elab_Term_withLocalDecl___rarg(x_10, x_64, x_82, x_70, x_81, x_7, x_80);
lean_dec(x_10);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_70);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_78);
if (x_84 == 0)
{
return x_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_78, 0);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_78);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
return x_75;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_75, 0);
x_90 = lean_ctor_get(x_75, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_75);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_68);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_69);
if (x_92 == 0)
{
return x_69;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_69, 0);
x_94 = lean_ctor_get(x_69, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_69);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7;
x_97 = l_Lean_Elab_Term_throwError___rarg(x_10, x_96, x_7, x_8);
lean_dec(x_10);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
return x_97;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_DoNotation_11__processDoElemsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_DoNotation_12__processDoElems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_empty___closed__1;
x_9 = l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main(x_1, x_2, x_3, x_4, x_7, x_8, x_5, x_6);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_elabDo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabDo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_82; 
x_5 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_1);
x_82 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_83);
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
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 5);
lean_inc(x_95);
x_96 = lean_environment_main_module(x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_85);
x_98 = 0;
x_99 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_100 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main(x_98, x_5, x_99, x_97, x_95);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_88);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_88, 5);
lean_dec(x_102);
x_103 = lean_ctor_get(x_88, 4);
lean_dec(x_103);
x_104 = lean_ctor_get(x_88, 3);
lean_dec(x_104);
x_105 = lean_ctor_get(x_88, 2);
lean_dec(x_105);
x_106 = lean_ctor_get(x_88, 1);
lean_dec(x_106);
x_107 = lean_ctor_get(x_88, 0);
lean_dec(x_107);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_dec(x_100);
lean_ctor_set(x_88, 5, x_109);
x_6 = x_108;
x_7 = x_88;
goto block_81;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_88);
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_dec(x_100);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_90);
lean_ctor_set(x_112, 1, x_91);
lean_ctor_set(x_112, 2, x_92);
lean_ctor_set(x_112, 3, x_93);
lean_ctor_set(x_112, 4, x_94);
lean_ctor_set(x_112, 5, x_111);
x_6 = x_110;
x_7 = x_112;
goto block_81;
}
}
else
{
lean_object* x_113; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_100, 0);
lean_inc(x_113);
lean_dec(x_100);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Lean_Elab_Term_throwError___rarg(x_114, x_117, x_3, x_88);
lean_dec(x_114);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_3);
x_123 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_88);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_82);
if (x_128 == 0)
{
return x_82;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_82, 0);
x_130 = lean_ctor_get(x_82, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_82);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
block_81:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_8, x_5, x_9, x_10);
lean_dec(x_5);
x_48 = l_Lean_Elab_Term_getOptions(x_3, x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Term_elabDo___closed__1;
x_52 = l_Lean_checkTraceOption(x_49, x_51);
lean_dec(x_49);
if (x_52 == 0)
{
x_12 = x_50;
goto block_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_inc(x_1);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_1);
lean_inc(x_3);
x_54 = l_Lean_Elab_Term_logTrace(x_51, x_1, x_53, x_3, x_50);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_12 = x_55;
goto block_47;
}
block_47:
{
lean_object* x_13; 
lean_inc(x_3);
lean_inc(x_2);
x_13 = l___private_Lean_Elab_DoNotation_2__extractBind(x_1, x_2, x_3, x_12);
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
x_21 = l___private_Lean_Elab_DoNotation_12__processDoElems(x_11, x_16, x_17, x_20, x_3, x_15);
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
x_34 = l___private_Lean_Elab_DoNotation_12__processDoElems(x_11, x_31, x_32, x_33, x_3, x_30);
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
lean_dec(x_11);
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
lean_object* x_56; uint8_t x_57; 
lean_dec(x_5);
x_56 = lean_ctor_get(x_6, 0);
lean_inc(x_56);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_3, 8);
lean_inc(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_3, 8, x_60);
x_61 = 1;
x_62 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_61, x_61, x_56, x_3, x_7);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_63 = lean_ctor_get(x_3, 0);
x_64 = lean_ctor_get(x_3, 1);
x_65 = lean_ctor_get(x_3, 2);
x_66 = lean_ctor_get(x_3, 3);
x_67 = lean_ctor_get(x_3, 4);
x_68 = lean_ctor_get(x_3, 5);
x_69 = lean_ctor_get(x_3, 6);
x_70 = lean_ctor_get(x_3, 7);
x_71 = lean_ctor_get(x_3, 8);
x_72 = lean_ctor_get(x_3, 9);
x_73 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_74 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_3);
lean_inc(x_56);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_56);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
x_78 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_78, 0, x_63);
lean_ctor_set(x_78, 1, x_64);
lean_ctor_set(x_78, 2, x_65);
lean_ctor_set(x_78, 3, x_66);
lean_ctor_set(x_78, 4, x_67);
lean_ctor_set(x_78, 5, x_68);
lean_ctor_set(x_78, 6, x_69);
lean_ctor_set(x_78, 7, x_70);
lean_ctor_set(x_78, 8, x_77);
lean_ctor_set(x_78, 9, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*10, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*10 + 1, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*10 + 2, x_75);
x_79 = 1;
x_80 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_79, x_79, x_56, x_78, x_7);
return x_80;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDo), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabDo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDo___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_DoNotation_13__regTraceClasses(lean_object* x_1) {
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_DoNotation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1 = _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1);
l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2 = _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__2);
l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3 = _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__3);
l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4 = _init_l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__4);
l___private_Lean_Elab_DoNotation_2__extractBind___closed__1 = _init_l___private_Lean_Elab_DoNotation_2__extractBind___closed__1();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_2__extractBind___closed__1);
l___private_Lean_Elab_DoNotation_2__extractBind___closed__2 = _init_l___private_Lean_Elab_DoNotation_2__extractBind___closed__2();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_2__extractBind___closed__2);
l___private_Lean_Elab_DoNotation_2__extractBind___closed__3 = _init_l___private_Lean_Elab_DoNotation_2__extractBind___closed__3();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_2__extractBind___closed__3);
l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1 = _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1);
l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2 = _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2);
l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3 = _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__3);
l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4 = _init_l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4);
l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1 = _init_l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__1);
l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2 = _init_l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2);
l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1 = _init_l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ProcessedDoElem_inhabited___closed__1);
l_Lean_Elab_Term_ProcessedDoElem_inhabited = _init_l_Lean_Elab_Term_ProcessedDoElem_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_ProcessedDoElem_inhabited);
l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1 = _init_l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__1);
l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2 = _init_l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__2);
l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3 = _init_l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_9__extractTypeFormerAppArg___closed__3);
l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1 = _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__1);
l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2 = _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__2);
l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3 = _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__3);
l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4 = _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__4);
l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5 = _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__5);
l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6 = _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__6);
l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7 = _init_l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_DoNotation_11__processDoElemsAux___main___closed__7);
l_Lean_Elab_Term_elabDo___closed__1 = _init_l_Lean_Elab_Term_elabDo___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDo___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDo___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDo___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDo___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabDo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DoNotation_13__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
