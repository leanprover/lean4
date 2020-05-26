// Lean compiler output
// Module: Lean.Elab.DoNotation
// Imports: Lean.Elab.Term Lean.Elab.Binders Lean.Elab.Quotation
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
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
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
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
extern lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_10__mkBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__3;
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
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabDo(lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_2__extractBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__1;
lean_object* l___private_Lean_Elab_DoNotation_1__mkIdBindFor___closed__1;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4;
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
x_2 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
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
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
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
x_164 = lean_array_push(x_129, x_163);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_131);
lean_ctor_set(x_165, 1, x_164);
x_166 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_167 = lean_array_push(x_166, x_165);
x_168 = lean_array_push(x_167, x_152);
x_169 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_170 = lean_array_push(x_168, x_169);
x_171 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_172 = lean_array_push(x_170, x_171);
x_173 = lean_array_push(x_129, x_117);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_131);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_array_push(x_129, x_174);
x_176 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_177 = lean_array_push(x_175, x_176);
x_178 = lean_array_push(x_177, x_142);
x_179 = l_Lean_Parser_Term_matchAlt___closed__2;
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_array_push(x_129, x_180);
x_182 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4;
x_183 = lean_array_push(x_181, x_182);
x_184 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_185 = lean_array_push(x_184, x_144);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_179);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_array_push(x_183, x_186);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_131);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_array_push(x_172, x_188);
x_190 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = lean_array_push(x_129, x_191);
x_193 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_array_push(x_161, x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_131);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_array_push(x_139, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_141);
lean_ctor_set(x_198, 1, x_197);
x_6 = x_198;
x_7 = x_127;
goto block_34;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_121);
x_199 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_200 = l_Lean_addMacroScope(x_128, x_199, x_60);
x_201 = lean_box(0);
x_202 = l_Lean_SourceInfo_inhabited___closed__1;
x_203 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_204 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_204, 2, x_200);
lean_ctor_set(x_204, 3, x_201);
x_205 = lean_array_push(x_129, x_204);
x_206 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_207 = lean_array_push(x_205, x_206);
x_208 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_207);
x_209 = lean_array_push(x_207, x_208);
x_210 = lean_array_push(x_209, x_119);
x_211 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_array_push(x_129, x_212);
x_214 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_215 = lean_array_push(x_213, x_214);
x_216 = l_Lean_mkTermIdFromIdent___closed__2;
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_207);
x_218 = lean_array_push(x_129, x_217);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_131);
lean_ctor_set(x_219, 1, x_218);
x_220 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_221 = lean_array_push(x_220, x_219);
x_222 = lean_array_push(x_221, x_206);
x_223 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_224 = lean_array_push(x_222, x_223);
x_225 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_226 = lean_array_push(x_224, x_225);
x_227 = lean_array_push(x_129, x_117);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_131);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_array_push(x_129, x_228);
x_230 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_231 = lean_array_push(x_229, x_230);
x_232 = lean_array_push(x_231, x_142);
x_233 = l_Lean_Parser_Term_matchAlt___closed__2;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = lean_array_push(x_129, x_234);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_131);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_array_push(x_226, x_236);
x_238 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
x_240 = lean_array_push(x_129, x_239);
x_241 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_array_push(x_215, x_242);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_131);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_array_push(x_139, x_244);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_141);
lean_ctor_set(x_246, 1, x_245);
x_6 = x_246;
x_7 = x_127;
goto block_34;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_247 = l_Lean_Syntax_inhabited;
x_248 = lean_array_get(x_247, x_123, x_116);
lean_dec(x_123);
x_249 = l_Lean_Syntax_getArg(x_248, x_116);
lean_dec(x_248);
x_250 = lean_nat_add(x_60, x_125);
x_251 = lean_ctor_get(x_4, 0);
lean_inc(x_251);
lean_dec(x_4);
x_252 = l_Lean_Syntax_isNone(x_121);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_253 = l_Lean_Syntax_getArg(x_121, x_125);
lean_dec(x_121);
x_254 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_255 = l_Lean_addMacroScope(x_251, x_254, x_60);
x_256 = lean_box(0);
x_257 = l_Lean_SourceInfo_inhabited___closed__1;
x_258 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_259 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_259, 2, x_255);
lean_ctor_set(x_259, 3, x_256);
x_260 = l_Array_empty___closed__1;
x_261 = lean_array_push(x_260, x_259);
x_262 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_263 = lean_array_push(x_261, x_262);
x_264 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_263);
x_265 = lean_array_push(x_263, x_264);
x_266 = lean_array_push(x_265, x_119);
x_267 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
x_269 = lean_array_push(x_260, x_268);
x_270 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_271 = lean_array_push(x_269, x_270);
x_272 = l_Lean_mkTermIdFromIdent___closed__2;
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_263);
x_274 = lean_array_push(x_260, x_273);
x_275 = l_Lean_nullKind___closed__2;
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_278 = lean_array_push(x_277, x_276);
x_279 = lean_array_push(x_278, x_262);
x_280 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_281 = lean_array_push(x_279, x_280);
x_282 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_283 = lean_array_push(x_281, x_282);
x_284 = lean_array_push(x_260, x_117);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_array_push(x_260, x_285);
x_287 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_288 = lean_array_push(x_286, x_287);
x_289 = lean_array_push(x_288, x_249);
x_290 = l_Lean_Parser_Term_matchAlt___closed__2;
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = lean_array_push(x_260, x_291);
x_293 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4;
x_294 = lean_array_push(x_292, x_293);
x_295 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_296 = lean_array_push(x_295, x_253);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_290);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_array_push(x_294, x_297);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_array_push(x_283, x_299);
x_301 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
x_303 = lean_array_push(x_260, x_302);
x_304 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
x_306 = lean_array_push(x_271, x_305);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_275);
lean_ctor_set(x_307, 1, x_306);
x_308 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_309 = lean_array_push(x_308, x_307);
x_310 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
x_6 = x_311;
x_7 = x_250;
goto block_34;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_121);
x_312 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_313 = l_Lean_addMacroScope(x_251, x_312, x_60);
x_314 = lean_box(0);
x_315 = l_Lean_SourceInfo_inhabited___closed__1;
x_316 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_317 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
lean_ctor_set(x_317, 2, x_313);
lean_ctor_set(x_317, 3, x_314);
x_318 = l_Array_empty___closed__1;
x_319 = lean_array_push(x_318, x_317);
x_320 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_321 = lean_array_push(x_319, x_320);
x_322 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_321);
x_323 = lean_array_push(x_321, x_322);
x_324 = lean_array_push(x_323, x_119);
x_325 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_327 = lean_array_push(x_318, x_326);
x_328 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_329 = lean_array_push(x_327, x_328);
x_330 = l_Lean_mkTermIdFromIdent___closed__2;
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_321);
x_332 = lean_array_push(x_318, x_331);
x_333 = l_Lean_nullKind___closed__2;
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
x_335 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_336 = lean_array_push(x_335, x_334);
x_337 = lean_array_push(x_336, x_320);
x_338 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_339 = lean_array_push(x_337, x_338);
x_340 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_341 = lean_array_push(x_339, x_340);
x_342 = lean_array_push(x_318, x_117);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_333);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_array_push(x_318, x_343);
x_345 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_346 = lean_array_push(x_344, x_345);
x_347 = lean_array_push(x_346, x_249);
x_348 = l_Lean_Parser_Term_matchAlt___closed__2;
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_347);
x_350 = lean_array_push(x_318, x_349);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_333);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_array_push(x_341, x_351);
x_353 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = lean_array_push(x_318, x_354);
x_356 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_355);
x_358 = lean_array_push(x_329, x_357);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_333);
lean_ctor_set(x_359, 1, x_358);
x_360 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_361 = lean_array_push(x_360, x_359);
x_362 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_6 = x_363;
x_7 = x_250;
goto block_34;
}
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
lean_dec(x_62);
lean_dec(x_4);
x_364 = lean_unsigned_to_nat(1u);
x_365 = l_Lean_Syntax_getArg(x_56, x_364);
lean_dec(x_56);
x_366 = lean_unsigned_to_nat(2u);
x_367 = lean_nat_add(x_3, x_366);
x_368 = l_Array_extract___rarg(x_2, x_367, x_35);
lean_dec(x_35);
x_369 = lean_array_get_size(x_368);
x_370 = lean_nat_dec_eq(x_369, x_364);
lean_dec(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_371 = lean_unsigned_to_nat(0u);
x_372 = l_Array_empty___closed__1;
x_373 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_368, x_368, x_371, x_372);
lean_dec(x_368);
x_374 = l_Lean_nullKind___closed__2;
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_377 = lean_array_push(x_376, x_375);
x_378 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_379 = lean_array_push(x_377, x_378);
x_380 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
x_382 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_383 = lean_array_push(x_382, x_381);
x_384 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_387 = lean_array_push(x_386, x_365);
x_388 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_389 = lean_array_push(x_387, x_388);
x_390 = lean_array_push(x_389, x_385);
x_391 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
x_393 = lean_nat_dec_eq(x_3, x_371);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_394 = l_Array_extract___rarg(x_2, x_371, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_395 = l_Lean_mkOptionalNode___closed__2;
x_396 = lean_array_push(x_395, x_392);
x_397 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_396);
x_399 = lean_array_push(x_394, x_398);
x_400 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_399, x_399, x_371, x_372);
lean_dec(x_399);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_374);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_array_push(x_376, x_401);
x_403 = lean_array_push(x_402, x_378);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_380);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_array_push(x_382, x_404);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_384);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_57, 0, x_407);
return x_57;
}
else
{
lean_object* x_408; 
lean_dec(x_3);
lean_dec(x_2);
x_408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_408, 0, x_392);
lean_ctor_set(x_57, 0, x_408);
return x_57;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_409 = l_Lean_Syntax_inhabited;
x_410 = lean_unsigned_to_nat(0u);
x_411 = lean_array_get(x_409, x_368, x_410);
lean_dec(x_368);
x_412 = l_Lean_Syntax_getArg(x_411, x_410);
lean_dec(x_411);
x_413 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_414 = lean_array_push(x_413, x_365);
x_415 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_416 = lean_array_push(x_414, x_415);
x_417 = lean_array_push(x_416, x_412);
x_418 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_417);
x_420 = lean_nat_dec_eq(x_3, x_410);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_421 = l_Array_extract___rarg(x_2, x_410, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_422 = l_Lean_mkOptionalNode___closed__2;
x_423 = lean_array_push(x_422, x_419);
x_424 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_423);
x_426 = lean_array_push(x_421, x_425);
x_427 = l_Array_empty___closed__1;
x_428 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_426, x_426, x_410, x_427);
lean_dec(x_426);
x_429 = l_Lean_nullKind___closed__2;
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_432 = lean_array_push(x_431, x_430);
x_433 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_434 = lean_array_push(x_432, x_433);
x_435 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_434);
x_437 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_438 = lean_array_push(x_437, x_436);
x_439 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_57, 0, x_441);
return x_57;
}
else
{
lean_object* x_442; 
lean_dec(x_3);
lean_dec(x_2);
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_419);
lean_ctor_set(x_57, 0, x_442);
return x_57;
}
}
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_443 = lean_ctor_get(x_57, 1);
lean_inc(x_443);
lean_dec(x_57);
lean_inc(x_56);
x_444 = l_Lean_Syntax_getKind(x_56);
x_445 = l_Lean_Parser_Term_doLet___elambda__1___closed__2;
x_446 = lean_name_eq(x_444, x_445);
if (x_446 == 0)
{
lean_object* x_447; uint8_t x_448; 
x_447 = l_Lean_Parser_Term_doPat___elambda__1___closed__2;
x_448 = lean_name_eq(x_444, x_447);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_449 = lean_unsigned_to_nat(1u);
x_450 = lean_nat_sub(x_35, x_449);
lean_dec(x_35);
x_451 = lean_nat_dec_lt(x_3, x_450);
lean_dec(x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_444);
lean_dec(x_56);
x_452 = lean_unsigned_to_nat(2u);
x_453 = lean_nat_add(x_3, x_452);
lean_dec(x_3);
x_3 = x_453;
x_5 = x_443;
goto _start;
}
else
{
lean_object* x_455; uint8_t x_456; 
x_455 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_456 = lean_name_eq(x_444, x_455);
lean_dec(x_444);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; 
lean_dec(x_56);
x_457 = lean_unsigned_to_nat(2u);
x_458 = lean_nat_add(x_3, x_457);
lean_dec(x_3);
x_3 = x_458;
x_5 = x_443;
goto _start;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_460 = lean_unsigned_to_nat(0u);
x_461 = l_Lean_Syntax_getArg(x_56, x_460);
lean_dec(x_56);
x_462 = lean_ctor_get(x_4, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_4, 0);
lean_inc(x_463);
x_464 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_465 = l_Lean_addMacroScope(x_463, x_464, x_462);
x_466 = lean_box(0);
x_467 = l_Lean_SourceInfo_inhabited___closed__1;
x_468 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_469 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
lean_ctor_set(x_469, 2, x_465);
lean_ctor_set(x_469, 3, x_466);
x_470 = l_Array_empty___closed__1;
x_471 = lean_array_push(x_470, x_469);
x_472 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_473 = lean_array_push(x_471, x_472);
x_474 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
x_475 = lean_array_push(x_473, x_474);
x_476 = lean_array_push(x_475, x_461);
x_477 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_476);
x_479 = lean_array_push(x_470, x_478);
x_480 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_481 = lean_array_push(x_479, x_480);
x_482 = lean_box(0);
x_483 = lean_array_push(x_481, x_482);
x_484 = l_Lean_nullKind___closed__2;
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_483);
x_486 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_487 = lean_array_push(x_486, x_485);
x_488 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_487);
x_490 = l___private_Lean_Elab_DoNotation_3__getDoElems(x_489);
lean_dec(x_489);
x_491 = l_Lean_Syntax_inhabited;
x_492 = lean_array_get(x_491, x_490, x_460);
lean_dec(x_490);
x_493 = lean_array_set(x_2, x_3, x_492);
x_494 = lean_unsigned_to_nat(2u);
x_495 = lean_nat_add(x_3, x_494);
lean_dec(x_3);
x_496 = 1;
x_1 = x_496;
x_2 = x_493;
x_3 = x_495;
x_5 = x_443;
goto _start;
}
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; 
lean_dec(x_444);
x_498 = lean_unsigned_to_nat(0u);
x_499 = l_Lean_Syntax_getArg(x_56, x_498);
x_500 = lean_unsigned_to_nat(2u);
x_501 = l_Lean_Syntax_getArg(x_56, x_500);
x_502 = lean_unsigned_to_nat(3u);
x_503 = l_Lean_Syntax_getArg(x_56, x_502);
lean_dec(x_56);
x_504 = lean_nat_add(x_3, x_500);
x_505 = l_Array_extract___rarg(x_2, x_504, x_35);
lean_dec(x_35);
x_506 = lean_array_get_size(x_505);
x_507 = lean_unsigned_to_nat(1u);
x_508 = lean_nat_dec_eq(x_506, x_507);
lean_dec(x_506);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_525; 
x_509 = lean_nat_add(x_443, x_507);
x_510 = lean_ctor_get(x_4, 0);
lean_inc(x_510);
lean_dec(x_4);
x_511 = l_Array_empty___closed__1;
x_512 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_505, x_505, x_498, x_511);
lean_dec(x_505);
x_513 = l_Lean_nullKind___closed__2;
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_512);
x_515 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_516 = lean_array_push(x_515, x_514);
x_517 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_518 = lean_array_push(x_516, x_517);
x_519 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_518);
x_521 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_522 = lean_array_push(x_521, x_520);
x_523 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_522);
x_525 = l_Lean_Syntax_isNone(x_503);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_526 = l_Lean_Syntax_getArg(x_503, x_507);
lean_dec(x_503);
x_527 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_528 = l_Lean_addMacroScope(x_510, x_527, x_443);
x_529 = lean_box(0);
x_530 = l_Lean_SourceInfo_inhabited___closed__1;
x_531 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_532 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
lean_ctor_set(x_532, 2, x_528);
lean_ctor_set(x_532, 3, x_529);
x_533 = lean_array_push(x_511, x_532);
x_534 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_535 = lean_array_push(x_533, x_534);
x_536 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_535);
x_537 = lean_array_push(x_535, x_536);
x_538 = lean_array_push(x_537, x_501);
x_539 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_538);
x_541 = lean_array_push(x_511, x_540);
x_542 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_543 = lean_array_push(x_541, x_542);
x_544 = l_Lean_mkTermIdFromIdent___closed__2;
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_535);
x_546 = lean_array_push(x_511, x_545);
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_513);
lean_ctor_set(x_547, 1, x_546);
x_548 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_549 = lean_array_push(x_548, x_547);
x_550 = lean_array_push(x_549, x_534);
x_551 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_552 = lean_array_push(x_550, x_551);
x_553 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_554 = lean_array_push(x_552, x_553);
x_555 = lean_array_push(x_511, x_499);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_513);
lean_ctor_set(x_556, 1, x_555);
x_557 = lean_array_push(x_511, x_556);
x_558 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_559 = lean_array_push(x_557, x_558);
x_560 = lean_array_push(x_559, x_524);
x_561 = l_Lean_Parser_Term_matchAlt___closed__2;
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_560);
x_563 = lean_array_push(x_511, x_562);
x_564 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4;
x_565 = lean_array_push(x_563, x_564);
x_566 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_567 = lean_array_push(x_566, x_526);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_561);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_array_push(x_565, x_568);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_513);
lean_ctor_set(x_570, 1, x_569);
x_571 = lean_array_push(x_554, x_570);
x_572 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_573, 0, x_572);
lean_ctor_set(x_573, 1, x_571);
x_574 = lean_array_push(x_511, x_573);
x_575 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_574);
x_577 = lean_array_push(x_543, x_576);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_513);
lean_ctor_set(x_578, 1, x_577);
x_579 = lean_array_push(x_521, x_578);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_523);
lean_ctor_set(x_580, 1, x_579);
x_6 = x_580;
x_7 = x_509;
goto block_34;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_503);
x_581 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_582 = l_Lean_addMacroScope(x_510, x_581, x_443);
x_583 = lean_box(0);
x_584 = l_Lean_SourceInfo_inhabited___closed__1;
x_585 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_586 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
lean_ctor_set(x_586, 2, x_582);
lean_ctor_set(x_586, 3, x_583);
x_587 = lean_array_push(x_511, x_586);
x_588 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_589 = lean_array_push(x_587, x_588);
x_590 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_589);
x_591 = lean_array_push(x_589, x_590);
x_592 = lean_array_push(x_591, x_501);
x_593 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_592);
x_595 = lean_array_push(x_511, x_594);
x_596 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_597 = lean_array_push(x_595, x_596);
x_598 = l_Lean_mkTermIdFromIdent___closed__2;
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_589);
x_600 = lean_array_push(x_511, x_599);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_513);
lean_ctor_set(x_601, 1, x_600);
x_602 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_603 = lean_array_push(x_602, x_601);
x_604 = lean_array_push(x_603, x_588);
x_605 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_606 = lean_array_push(x_604, x_605);
x_607 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_608 = lean_array_push(x_606, x_607);
x_609 = lean_array_push(x_511, x_499);
x_610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_610, 0, x_513);
lean_ctor_set(x_610, 1, x_609);
x_611 = lean_array_push(x_511, x_610);
x_612 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_613 = lean_array_push(x_611, x_612);
x_614 = lean_array_push(x_613, x_524);
x_615 = l_Lean_Parser_Term_matchAlt___closed__2;
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_614);
x_617 = lean_array_push(x_511, x_616);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_513);
lean_ctor_set(x_618, 1, x_617);
x_619 = lean_array_push(x_608, x_618);
x_620 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_619);
x_622 = lean_array_push(x_511, x_621);
x_623 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_622);
x_625 = lean_array_push(x_597, x_624);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_513);
lean_ctor_set(x_626, 1, x_625);
x_627 = lean_array_push(x_521, x_626);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_523);
lean_ctor_set(x_628, 1, x_627);
x_6 = x_628;
x_7 = x_509;
goto block_34;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; 
x_629 = l_Lean_Syntax_inhabited;
x_630 = lean_array_get(x_629, x_505, x_498);
lean_dec(x_505);
x_631 = l_Lean_Syntax_getArg(x_630, x_498);
lean_dec(x_630);
x_632 = lean_nat_add(x_443, x_507);
x_633 = lean_ctor_get(x_4, 0);
lean_inc(x_633);
lean_dec(x_4);
x_634 = l_Lean_Syntax_isNone(x_503);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_635 = l_Lean_Syntax_getArg(x_503, x_507);
lean_dec(x_503);
x_636 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_637 = l_Lean_addMacroScope(x_633, x_636, x_443);
x_638 = lean_box(0);
x_639 = l_Lean_SourceInfo_inhabited___closed__1;
x_640 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_641 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_641, 0, x_639);
lean_ctor_set(x_641, 1, x_640);
lean_ctor_set(x_641, 2, x_637);
lean_ctor_set(x_641, 3, x_638);
x_642 = l_Array_empty___closed__1;
x_643 = lean_array_push(x_642, x_641);
x_644 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_645 = lean_array_push(x_643, x_644);
x_646 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_645);
x_647 = lean_array_push(x_645, x_646);
x_648 = lean_array_push(x_647, x_501);
x_649 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_649);
lean_ctor_set(x_650, 1, x_648);
x_651 = lean_array_push(x_642, x_650);
x_652 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_653 = lean_array_push(x_651, x_652);
x_654 = l_Lean_mkTermIdFromIdent___closed__2;
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_645);
x_656 = lean_array_push(x_642, x_655);
x_657 = l_Lean_nullKind___closed__2;
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_656);
x_659 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_660 = lean_array_push(x_659, x_658);
x_661 = lean_array_push(x_660, x_644);
x_662 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_663 = lean_array_push(x_661, x_662);
x_664 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_665 = lean_array_push(x_663, x_664);
x_666 = lean_array_push(x_642, x_499);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_657);
lean_ctor_set(x_667, 1, x_666);
x_668 = lean_array_push(x_642, x_667);
x_669 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_670 = lean_array_push(x_668, x_669);
x_671 = lean_array_push(x_670, x_631);
x_672 = l_Lean_Parser_Term_matchAlt___closed__2;
x_673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_671);
x_674 = lean_array_push(x_642, x_673);
x_675 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__4;
x_676 = lean_array_push(x_674, x_675);
x_677 = l___private_Lean_Elab_DoNotation_7__expandDoElemsAux___main___closed__2;
x_678 = lean_array_push(x_677, x_635);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_672);
lean_ctor_set(x_679, 1, x_678);
x_680 = lean_array_push(x_676, x_679);
x_681 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_681, 0, x_657);
lean_ctor_set(x_681, 1, x_680);
x_682 = lean_array_push(x_665, x_681);
x_683 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_682);
x_685 = lean_array_push(x_642, x_684);
x_686 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_685);
x_688 = lean_array_push(x_653, x_687);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_657);
lean_ctor_set(x_689, 1, x_688);
x_690 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_691 = lean_array_push(x_690, x_689);
x_692 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_692);
lean_ctor_set(x_693, 1, x_691);
x_6 = x_693;
x_7 = x_632;
goto block_34;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_503);
x_694 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__2;
x_695 = l_Lean_addMacroScope(x_633, x_694, x_443);
x_696 = lean_box(0);
x_697 = l_Lean_SourceInfo_inhabited___closed__1;
x_698 = l_Lean_Elab_Term_elabLetDecl___closed__2;
x_699 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
lean_ctor_set(x_699, 2, x_695);
lean_ctor_set(x_699, 3, x_696);
x_700 = l_Array_empty___closed__1;
x_701 = lean_array_push(x_700, x_699);
x_702 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_703 = lean_array_push(x_701, x_702);
x_704 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__4;
lean_inc(x_703);
x_705 = lean_array_push(x_703, x_704);
x_706 = lean_array_push(x_705, x_501);
x_707 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_706);
x_709 = lean_array_push(x_700, x_708);
x_710 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_711 = lean_array_push(x_709, x_710);
x_712 = l_Lean_mkTermIdFromIdent___closed__2;
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_703);
x_714 = lean_array_push(x_700, x_713);
x_715 = l_Lean_nullKind___closed__2;
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_714);
x_717 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__2;
x_718 = lean_array_push(x_717, x_716);
x_719 = lean_array_push(x_718, x_702);
x_720 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__3;
x_721 = lean_array_push(x_719, x_720);
x_722 = l___private_Lean_Elab_Binders_11__expandFunBindersAux___main___closed__6;
x_723 = lean_array_push(x_721, x_722);
x_724 = lean_array_push(x_700, x_499);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_715);
lean_ctor_set(x_725, 1, x_724);
x_726 = lean_array_push(x_700, x_725);
x_727 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_728 = lean_array_push(x_726, x_727);
x_729 = lean_array_push(x_728, x_631);
x_730 = l_Lean_Parser_Term_matchAlt___closed__2;
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_729);
x_732 = lean_array_push(x_700, x_731);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_715);
lean_ctor_set(x_733, 1, x_732);
x_734 = lean_array_push(x_723, x_733);
x_735 = l_Lean_Parser_Term_match___elambda__1___closed__2;
x_736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_734);
x_737 = lean_array_push(x_700, x_736);
x_738 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_737);
x_740 = lean_array_push(x_711, x_739);
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_715);
lean_ctor_set(x_741, 1, x_740);
x_742 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_743 = lean_array_push(x_742, x_741);
x_744 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_743);
x_6 = x_745;
x_7 = x_632;
goto block_34;
}
}
}
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; uint8_t x_752; 
lean_dec(x_444);
lean_dec(x_4);
x_746 = lean_unsigned_to_nat(1u);
x_747 = l_Lean_Syntax_getArg(x_56, x_746);
lean_dec(x_56);
x_748 = lean_unsigned_to_nat(2u);
x_749 = lean_nat_add(x_3, x_748);
x_750 = l_Array_extract___rarg(x_2, x_749, x_35);
lean_dec(x_35);
x_751 = lean_array_get_size(x_750);
x_752 = lean_nat_dec_eq(x_751, x_746);
lean_dec(x_751);
if (x_752 == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; uint8_t x_775; 
x_753 = lean_unsigned_to_nat(0u);
x_754 = l_Array_empty___closed__1;
x_755 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_750, x_750, x_753, x_754);
lean_dec(x_750);
x_756 = l_Lean_nullKind___closed__2;
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_755);
x_758 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_759 = lean_array_push(x_758, x_757);
x_760 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_761 = lean_array_push(x_759, x_760);
x_762 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_761);
x_764 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_765 = lean_array_push(x_764, x_763);
x_766 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_765);
x_768 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_769 = lean_array_push(x_768, x_747);
x_770 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_771 = lean_array_push(x_769, x_770);
x_772 = lean_array_push(x_771, x_767);
x_773 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_772);
x_775 = lean_nat_dec_eq(x_3, x_753);
if (x_775 == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_776 = l_Array_extract___rarg(x_2, x_753, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_777 = l_Lean_mkOptionalNode___closed__2;
x_778 = lean_array_push(x_777, x_774);
x_779 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_778);
x_781 = lean_array_push(x_776, x_780);
x_782 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_781, x_781, x_753, x_754);
lean_dec(x_781);
x_783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_783, 0, x_756);
lean_ctor_set(x_783, 1, x_782);
x_784 = lean_array_push(x_758, x_783);
x_785 = lean_array_push(x_784, x_760);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_762);
lean_ctor_set(x_786, 1, x_785);
x_787 = lean_array_push(x_764, x_786);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_766);
lean_ctor_set(x_788, 1, x_787);
x_789 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_789, 0, x_788);
x_790 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_443);
return x_790;
}
else
{
lean_object* x_791; lean_object* x_792; 
lean_dec(x_3);
lean_dec(x_2);
x_791 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_791, 0, x_774);
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_443);
return x_792;
}
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
x_793 = l_Lean_Syntax_inhabited;
x_794 = lean_unsigned_to_nat(0u);
x_795 = lean_array_get(x_793, x_750, x_794);
lean_dec(x_750);
x_796 = l_Lean_Syntax_getArg(x_795, x_794);
lean_dec(x_795);
x_797 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_798 = lean_array_push(x_797, x_747);
x_799 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_800 = lean_array_push(x_798, x_799);
x_801 = lean_array_push(x_800, x_796);
x_802 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_801);
x_804 = lean_nat_dec_eq(x_3, x_794);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_805 = l_Array_extract___rarg(x_2, x_794, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_806 = l_Lean_mkOptionalNode___closed__2;
x_807 = lean_array_push(x_806, x_803);
x_808 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
x_809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_807);
x_810 = lean_array_push(x_805, x_809);
x_811 = l_Array_empty___closed__1;
x_812 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_810, x_810, x_794, x_811);
lean_dec(x_810);
x_813 = l_Lean_nullKind___closed__2;
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
x_815 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
x_816 = lean_array_push(x_815, x_814);
x_817 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__7;
x_818 = lean_array_push(x_816, x_817);
x_819 = l_Lean_Parser_Term_bracketedDoSeq___elambda__1___closed__2;
x_820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_820, 0, x_819);
lean_ctor_set(x_820, 1, x_818);
x_821 = l___private_Lean_Elab_DoNotation_5__expandLiftMethodAux___main___closed__2;
x_822 = lean_array_push(x_821, x_820);
x_823 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_823);
lean_ctor_set(x_824, 1, x_822);
x_825 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_825, 0, x_824);
x_826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_826, 0, x_825);
lean_ctor_set(x_826, 1, x_443);
return x_826;
}
else
{
lean_object* x_827; lean_object* x_828; 
lean_dec(x_3);
lean_dec(x_2);
x_827 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_827, 0, x_803);
x_828 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_443);
return x_828;
}
}
}
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; 
lean_dec(x_56);
x_829 = lean_ctor_get(x_57, 1);
lean_inc(x_829);
lean_dec(x_57);
x_830 = lean_ctor_get(x_58, 0);
lean_inc(x_830);
lean_dec(x_58);
x_831 = lean_unsigned_to_nat(1u);
x_832 = lean_nat_add(x_3, x_831);
x_833 = l_Array_extract___rarg(x_2, x_832, x_35);
lean_dec(x_35);
x_834 = lean_unsigned_to_nat(0u);
x_835 = l_Array_extract___rarg(x_2, x_834, x_3);
lean_dec(x_2);
x_836 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_830, x_830, x_834, x_835);
lean_dec(x_830);
x_837 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_833, x_833, x_834, x_836);
lean_dec(x_833);
x_838 = 1;
x_1 = x_838;
x_2 = x_837;
x_5 = x_829;
goto _start;
}
}
else
{
uint8_t x_840; 
lean_dec(x_56);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_840 = !lean_is_exclusive(x_57);
if (x_840 == 0)
{
return x_57;
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_841 = lean_ctor_get(x_57, 0);
x_842 = lean_ctor_get(x_57, 1);
lean_inc(x_842);
lean_inc(x_841);
lean_dec(x_57);
x_843 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_843, 0, x_841);
lean_ctor_set(x_843, 1, x_842);
return x_843;
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
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_DoNotation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
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
